import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

open SimpleGraph
open Walk

section
variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] {x y z : V} (hG : G.LocallyFinite)

theorem takeUntil_last (p : G.Walk x y) : p.takeUntil y p.end_mem_support = p := by
  sorry

lemma dropUntil_append_of_mem_right
  {w : V} (p : G.Walk x y) (q : G.Walk y z)
  (hw : w ∈ q.support) (hw_not_p : w ∉ p.dropLast.support) :
  (p.append q).dropUntil w (subset_support_append_right _ _ hw) = q.dropUntil _ hw := by
  sorry

theorem dropUntil_takeUntil_eq_reverse {p : G.Walk x y} (hp : p.IsPath) (hz : z ∈ p.support) :
  (p.dropUntil z hz) =
  (p.reverse.takeUntil z (
    Eq.mpr (id (congrArg (fun _a ↦ z ∈ _a) (support_reverse p))) (List.mem_reverse.mpr hz)
  )).reverse := by
  induction p with
  | nil => rename_i u; rw [dropUntil_eq_drop, takeUntil_eq_take];
            simp only [support_nil, reverse_nil, reverse_copy, getVert_nil];
            apply copy.congr_simp
              (nil.drop (List.idxOf z [u])) (nil.take (List.idxOf z [u])).reverse;
            rfl
  | @cons u v t uv p' ih => rw [mem_support_iff] at hz
                            cases hz <;> simp only [reverse_cons]
                            · subst z
                              rw [dropUntil_first, takeUntil_last, reverse_append, reverse_cons]
                              rw [reverse_nil, nil_append, reverse_reverse, cons_append, nil_append]
                            have ⟨hp', u_nin_p'⟩ : p'.IsPath ∧ u ∉ p'.support := by
                              rwa [cons_isPath_iff] at hp
                            rename_i ht
                            rw [support_cons, List.tail_cons] at ht
                            specialize ih hp' ht
                            have ht_rev : z ∈ p'.reverse.support := by
                              rwa [← List.mem_reverse, ← support_reverse] at ht
                            rw [takeUntil_append_of_mem_left _ _ ht_rev, ←ih]
                            rw [←(dropUntil_append_of_mem_right (cons uv nil) p')]
                            · simp only [cons_append, nil_append]
                            simp only [penultimate_cons_nil, dropLast_cons_nil, support_nil]
                            simp only [List.mem_cons, List.not_mem_nil, or_false]
                            exact ne_of_mem_of_not_mem ht u_nin_p'


theorem exists_mem_support_forall_mem_support_imp_eq_reverse
  {p : G.Walk x y} (s : Finset V) (h : {w ∈ s | w ∈ p.support}.Nonempty) :
  ∃ w ∈ s, ∃ (hw : w ∈ p.support), ∀ t ∈ s, t ∈ (p.dropUntil w hw).support → t = w := by
  have h_rev : {w ∈ s | w ∈ p.reverse.support}.Nonempty := by
    rcases h with ⟨w, h⟩
    exists w
    rw [Finset.mem_filter] at h
    rwa [Finset.mem_filter, support_reverse, List.mem_reverse]
  obtain ⟨w, w_in_s, w_in_p_rev, ht⟩ :=
    exists_mem_support_forall_mem_support_imp_eq s h_rev
  have w_in_p : w ∈ p.support := by
    rwa [← List.mem_reverse, ← support_reverse]
  exists w, w_in_s, w_in_p
  intro t t_in_s t_in_take
  rw [dropUntil_takeUntil_eq_reverse, support_reverse, List.mem_reverse] at t_in_take
  · specialize ht t t_in_s t_in_take
    assumption
  sorry

theorem deg3_vertex
  (p : G.Walk x y) (q : G.Walk x z)
  (hp : p.IsPath) (hq : q.IsPath)
  (dx : G.degree x = 1) (dy : G.degree y = 1) (dz : G.degree z = 1)
  (xNy : x ≠ y) (xNz : x ≠ z) (yNz : y ≠ z) :
  ∃ w, 3 ≤ G.degree w := by
  -- split p and q at the second vertex, w
  have ⟨w, xw, p', p_xw_p'⟩
    : ∃ (w : V) (xw : G.Adj x w) (p' : G.Walk w y), p = cons xw p' := by
    apply exists_eq_cons_of_ne xNy
  have ⟨q', q_xw_q'⟩ : ∃ (q' : G.Walk w z), q = cons xw q' := by
    obtain ⟨w₀, xw₀, q', q_xw_q'⟩
    : ∃ (w : V) (xw : G.Adj x w) (q' : G.Walk w z), q = cons xw q' := by
      apply exists_eq_cons_of_ne xNz
    rw [degree_eq_one_iff_existsUnique_adj] at dx
    have wEw₀ : w = w₀ := ExistsUnique.unique dx xw xw₀
    subst wEw₀
    exists q'
  -- to apply next thm, need to show p' and q' have nonempty overlap
  have shared_support : {v ∈ q'.support.toFinset | v ∈ p'.support}.Nonempty := by
    exists w
    rw [Finset.mem_filter, List.mem_toFinset]
    constructor <;>
    apply start_mem_support
  obtain ⟨w', w'_in_q', w'_in_p', hsplit⟩ :=
    exists_mem_support_forall_mem_support_imp_eq_reverse q'.support.toFinset shared_support
  have w'_in_p : w' ∈ p.support := by
    sorry
  -- have three paths at w'
  let r := p.takeUntil w' w'_in_p
  have hr : r.IsPath := by apply IsPath.takeUntil hp
  let p'' := p.dropUntil w' w'_in_p
  have p_r_p'' : p = r.append p'' := Eq.symm (take_spec p w'_in_p)
  let q'' := q'.dropUntil w' (List.mem_toFinset.mp w'_in_q')
  -- this will give us three edges adjacent to w'
  have ⟨w₁, r'', ww₁, r_r''_ww₁⟩
    : ∃ (w₁ : V) (r'' : G.Walk x w₁) (ww₁ : G.Adj w₁ w'), r = concat r'' ww₁ := by
    sorry
  have ⟨w₂, ww₂, p''', p''_ww₂_p'''⟩
    : ∃ (w₂ : V) (ww₂ : G.Adj w' w₂) (p''' : G.Walk w₂ y), p'' = cons ww₂ p''' := by
    sorry
  have ⟨w₃, ww₃, q''', q''_ww₃_q'''⟩
    : ∃ (w₃ : V) (ww₃ : G.Adj w' w₃) (q''' : G.Walk w₃ z), q'' = cons ww₃ q''' := by
    sorry
  -- w' will be the vertex of degree (at least) 3
  exists w'
  unfold degree
  rw [Finset.le_card_iff_exists_subset_card]
  exists {w₁, w₂, w₃}
  -- show these vertices are adjacent to w'
  constructor
  · unfold neighborFinset neighborSet
    apply Finset.insert_subset
    · simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      apply adj_symm
      assumption
    apply Finset.insert_subset <;>
    try rw [Finset.singleton_subset_iff]
    all_goals
      simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      assumption
  -- finally, show w₁ ≠ w₂ ≠ w₃, so cardinality is 3
  rw [Finset.card_eq_three]
  exists w₁, w₂, w₃
  constructor
  · apply (@IsPath.ne_of_mem_support_of_append _ _ _ _ _ r p'')
    · rw [←p_r_p'']
      assumption
    · exact Adj.ne' ww₂
    · rw [r_r''_ww₁, concat_eq_append, mem_support_append_iff]
      left
      apply end_mem_support
    rw [p''_ww₂_p''', ← cons_nil_append, mem_support_append_iff]
    right
    apply start_mem_support
  constructor
  · sorry
  constructor
  · sorry
  exact Finset.val_inj.mp rfl

theorem split_paths
  (p : G.Path x y) (q : G.Path x z)
  (dx : G.degree x = 1) (dy : G.degree y = 1) (dz : G.degree z = 1)
  (xNy : x ≠ y) (xNz : x ≠ z) (yNz : y ≠ z) :
  ∃ (w : V) (r : G.Path x w) (p' : G.Path w y) (q' : G.Path w z),
  p = r.1.append p'.1 ∧ q = r.1.append q'.1  ∧ (p'.reverse.1.append q'.1).IsPath := by
  sorry

end
