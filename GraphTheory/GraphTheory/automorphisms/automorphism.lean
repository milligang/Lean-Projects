import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Logic.Equiv.Finset
import Mathlib.Data.Finset.Prod

-- shorthand, since we reference this graph a lot
abbrev K₅ := SimpleGraph.completeGraph (Fin 5)

section autGroup
/- define vertex & edge automorphism groups for graphs -/

-- working with finite graphs
variable {V : Type _} [inst : Fintype V] (G : SimpleGraph V)

-- vertex automorphism if the graphs are equal up to permutation of vertices
def autGroupVert : Subgroup (Equiv.Perm V) where
  carrier := {γ | G = (G.comap γ)}
  mul_mem' := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_mul]
    intros γ₁ γ₂ hγ₁ hγ₂
    rwa [← SimpleGraph.comap_comap γ₂ γ₁, ← hγ₁]
  one_mem' := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_one, SimpleGraph.comap_id]
  inv_mem' := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_inv]
    intros γ hγ
    rw [hγ, SimpleGraph.comap_comap]
    simp only [Equiv.self_comp_symm, SimpleGraph.comap_id]
    exact hγ.symm

-- definition of vertex transitivity
def vertex_transitive {V : Type _} (G : SimpleGraph V) : Prop :=
  MulAction.IsPretransitive (autGroupVert G) V

-- edge automorphism if the graphs are equal up to permutation of edges
-- utilize the equivalence between edges and vertices of the line graph
def autGroupEdge : Subgroup (Equiv.Perm G.edgeSet) := autGroupVert G.lineGraph

-- similarly, edge transitivity
def edge_transitive {V : Type _} (G : SimpleGraph V) : Prop :=
  MulAction.IsPretransitive (autGroupEdge G) G.edgeSet

-- vertex automorphism equals complement
omit inst in
lemma autGroup_compl : autGroupVert G = autGroupVert Gᶜ := by
  dsimp [autGroupVert]
  simp only [Subgroup.mk.injEq, Submonoid.mk.injEq, Subsemigroup.mk.injEq]
  apply Set.setOf_inj.mpr
  ext γ
  rw [←SimpleGraph.adj_inj, ←SimpleGraph.adj_inj]
  constructor <;> intro h <;> ext u v
  · rw [SimpleGraph.comap_adj, SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, and_congr_right_iff]
    intro _
    apply not_congr
    rw [← SimpleGraph.comap_adj, h]
  rw [SimpleGraph.comap_adj]
  by_cases eq_u_v : (u = v)
  · simp only [eq_u_v, SimpleGraph.irrefl]
  revert eq_u_v
  rw [← not_iff_not, ←and_congr_right_iff, ←SimpleGraph.compl_adj]
  rw [← @EmbeddingLike.apply_eq_iff_eq _ _ _ _ _ γ, ←SimpleGraph.compl_adj]
  rw [← SimpleGraph.comap_adj, h]

-- if G and H are isomorphic, so are the corresponding vert autGroups
def eq_iso_autGroup {W : Type _} {H : SimpleGraph W} (φ : G ≃g H) :
  autGroupVert G ≃* autGroupVert H where
  toFun := by
    rintro ⟨γ, hγ⟩
    use φ.toEquiv.symm.trans (γ.trans φ.toEquiv) -- φ ∘ γ ∘ φ⁻¹
    simp only [autGroupVert, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
              Set.mem_setOf_eq, Equiv.coe_trans, RelIso.coe_fn_toEquiv] at *
    ext u v
    simp only [SimpleGraph.comap_adj, Function.comp_apply, φ.map_rel_iff]
    rw [←SimpleGraph.comap_adj, ←hγ, ←φ.symm.map_rel_iff]
    trivial
  invFun := by
    rintro ⟨γ, hγ⟩
    use φ.toEquiv.trans (γ.trans φ.toEquiv.symm) -- φ⁻¹ ∘ γ ∘ φ
    simp only [autGroupVert, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
              Set.mem_setOf_eq, Equiv.coe_trans, RelIso.coe_fn_toEquiv] at *
    ext u v
    rw [SimpleGraph.comap_adj]
    simp only [Function.comp_apply]
    rw [←φ.map_rel_iff, ←φ.map_rel_iff, ←RelIso.coe_fn_toEquiv, φ.toEquiv.apply_symm_apply,
        φ.toEquiv.apply_symm_apply, RelIso.coe_fn_toEquiv]
    nth_rw 2 [←SimpleGraph.comap_adj]
    rw [←hγ]
  left_inv := by
    rintro ⟨γ, hγ⟩
    ext u
    simp only [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl, Equiv.trans_apply]
    rw [φ.toEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨γ, hγ⟩
    ext u
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  map_mul' := by
    rintro ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
    ext u
    simp only [MulMemClass.mk_mul_mk, Equiv.trans_apply, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [φ.toEquiv.symm_apply_apply]

-- for five vertices, vert group equals edge group
def autGroup_vert_eq_edge : 5 ≤ Fintype.card V → autGroupVert G ≃* autGroupEdge G := by sorry

-- vert group of complete graph is symmetric group (i.e., includes every permutation of vertices)
lemma autGroup_complete_eq_symm (n : ℕ) :
  autGroupVert (SimpleGraph.completeGraph (Fin n)) = ⊤ := by
  rw [SimpleGraph.completeGraph_eq_top]
  ext γ
  apply iff_of_true _ (Subgroup.mem_top _)
  ext u v
  rw [SimpleGraph.comap_adj, SimpleGraph.top_adj, SimpleGraph.top_adj]
  apply not_congr
  rw [EmbeddingLike.apply_eq_iff_eq]

end autGroup


namespace Petersen
/- Defining the Petersen graph analgously to
the Königsberg graph in the mathlib archive Wiedijk100Theorems
Explicity listing vertices and edges
-/

-- The vertices for the Petersen graph
inductive Verts : Type
  | V1 | V2 | V3 | V4 | V5
  | U1 | U2 | U3 | U4 | U5
  deriving DecidableEq, Fintype

open Verts

-- Each of the connections in the graph
--These are ordered pairs, but the data becomes symmetric in `Petersen.adj`.
def edges : List (Verts × Verts) :=
  [(V1, V3), (V1, V4), (V2, V4), (V2, V5), (V3, V5),
   (U1, U2), (U2, U3), (U3, U4), (U4, U5), (U5, U1),
   (V1, U1), (V2, U2), (V3, U3), (V4, U4), (V5, U5)]

-- The adjacency relation for the Petersen graph.
def adj (v w : Verts) : Bool := (v, w) ∈ edges || (w, v) ∈ edges

@[simps]
def pet : SimpleGraph Verts where
  Adj v w := adj v w
  symm := by
    dsimp [Symmetric, adj]
    decide
  loopless := ⟨by decide⟩

instance : DecidableRel pet.Adj := fun a b => inferInstanceAs <| Decidable (adj a b)


section permutations
/- a few permutations of the Petersen graph -/

def perm_γ₁ : Equiv.Perm Verts :=
  c[V1, V2, V3, V4, V5] * c[U1, U2, U3, U4, U5]

def pet_γ₁ : SimpleGraph Verts := pet.comap perm_γ₁

def iso_γ₁ : pet ≃g pet_γ₁ where
  toEquiv      := perm_γ₁.symm
  map_rel_iff' := by simp [pet_γ₁, SimpleGraph.comap_adj]

def perm_γ₂ : Equiv.Perm Verts :=
  c[V1, U1] * c[V2, U4, V5, U3] * c[V3, U2, V4, U5]

def pet_γ₂ : SimpleGraph Verts := pet.comap perm_γ₂

def iso_γ₂ : pet ≃g pet_γ₂ where
  toEquiv      := perm_γ₂.symm
  map_rel_iff' := by simp [pet_γ₂, SimpleGraph.comap_adj]

-- γ₁ and γ₂ are in the automorphism group of pet
lemma auto_γ₁ : perm_γ₁ ∈ autGroupVert pet := by
  ext u v
  simp only [pet_adj, SimpleGraph.comap_adj, Bool.coe_iff_coe]
  decide +revert

lemma auto_γ₂ : perm_γ₂ ∈ autGroupVert pet := by
  ext u v
  simp only [pet_adj, SimpleGraph.comap_adj, Bool.coe_iff_coe]
  decide +revert

end permutations

/- various methods to relate our custom Verts to the numbers 0 through 9 -/
def verts_to_fin10 (v : Verts) : (Fin 10) :=
  match v with
  | .V1 => 0
  | .V2 => 1
  | .V3 => 2
  | .V4 => 3
  | .V5 => 4
  | .U1 => 5
  | .U2 => 6
  | .U3 => 7
  | .U4 => 8
  | .U5 => 9

lemma verts_eq_fin10_nonempty : Nonempty (Verts ≃ Fin 10) := by
  rw [← Cardinal.mk_eq_nat_iff]
  simp only [Cardinal.mk_fintype, Nat.cast_ofNat]
  rfl

def verts_eq_fin10_trunc : Trunc (Verts ≃ Fin 10) := by
  apply Fintype.truncEquivFinOfCardEq
  rfl

-- can only get this to work by marking it noncomputable
-- two options (one with classical logic)
noncomputable def verts_eq_fin10_classical : Verts ≃ Fin 10 := by
  exact Classical.choice verts_eq_fin10_nonempty

-- without classical logic, explicity give the bijection
noncomputable def verts_eq_fin10 : Verts ≃ Fin 10 := by
  apply Equiv.ofBijective verts_to_fin10
  rw [Fintype.bijective_iff_injective_and_card]
  constructor <;> decide

-- K₅ edges ≃ Fin 10 so Verts ≃ K₅ edges
lemma K₅_eq_fin10_nonempty : Nonempty (K₅.edgeSet ≃ Fin 10) := by
  rw [← Cardinal.mk_eq_nat_iff]
  simp only [Cardinal.mk_fintype, Nat.cast_ofNat]
  rw [K₅.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  rfl

noncomputable def verts_eq_K₅ : Verts ≃ K₅.edgeSet := by
  apply Equiv.trans verts_eq_fin10_classical
  apply Equiv.symm
  exact Classical.choice K₅_eq_fin10_nonempty

end Petersen

namespace altPetersen
/- an alternate definition of the petersen graph
designed to more naturally conclude reslts such as relationship to L(K₅)ᶜ
-/

-- vertices are all unique (unordered) pairings of numbers 0 - 4
-- excluding with itself, e.g. (0,1) is included but (0,0) is not
def Verts : Finset (Sym2 (Fin 5)) :=
  Finset.univ.sym2.filter (not ·.IsDiag)

-- vertices are adjacent if their intersection is empty
def adj (u v : Verts) : Bool := Disjoint u.val.toFinset v.val.toFinset

def pet : SimpleGraph Verts where
  Adj u v := adj u v
  symm := by
    dsimp [Symmetric, adj]
    decide
  loopless := ⟨by decide⟩

instance : DecidableRel pet.Adj := fun a b => inferInstanceAs <| Decidable (adj a b)

-- check on our definitions
lemma verts_card : Fintype.card Verts = 10 := by rfl
lemma edges_card : Fintype.card pet.edgeFinset = 15 := by rfl

/- this version of the petersen graph is equivalent to the trivial definition -/
-- apparently, need to include proof too for map
def verts_to_verts (v : Petersen.Verts) : Verts :=
  match v with
  | .V1 => ⟨s(2,4), by trivial⟩
  | .V2 => ⟨s(1,4), by trivial⟩
  | .V3 => ⟨s(1,3), by trivial⟩
  | .V4 => ⟨s(0,3), by trivial⟩
  | .V5 => ⟨s(0,2), by trivial⟩
  | .U1 => ⟨s(0,1), by trivial⟩
  | .U2 => ⟨s(2,3), by trivial⟩
  | .U3 => ⟨s(0,4), by trivial⟩
  | .U4 => ⟨s(1,2), by trivial⟩
  | .U5 => ⟨s(3,4), by trivial⟩

noncomputable def verts_eq_verts : Petersen.Verts ≃ Verts := by
  apply Equiv.ofBijective verts_to_verts
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro u v
    fin_cases u <;> fin_cases v <;>
    dsimp [verts_to_verts] <;>
    trivial
  · rw [verts_card]
    exact Nat.eq_of_beq_eq_true rfl -- from "apply?"

noncomputable def pet_to_alt_pet : Petersen.pet ≃g pet where
  toEquiv := verts_eq_verts
  map_rel_iff' := by
    intro u v
    -- this method generates 10 × 10 = 100 goals
    -- is there a more efficient proof?
    fin_cases u <;>
    fin_cases v <;>
    trivial

/- proof Petersen is isomorphic to  L(K₅)ᶜ -/
-- custom K₅ line graph, slightly easier to work with later -/
def K₅_line : SimpleGraph Verts where
  Adj u v := u ≠ v ∧ ¬(Disjoint u.val.toFinset v.val.toFinset)
  symm := by
    rintro u v ⟨neq, h⟩
    constructor
    · apply Ne.symm; assumption
    intro neg
    apply Disjoint.symm at neg
    contradiction
  loopless := ⟨by
    intro v
    push Not
    rw [ne_self_iff_false]
    intro
    contradiction
  ⟩

def K₅_line_verts : Verts ≃ K₅.edgeSet := by
  simp [Verts]
  rfl

-- our custom line graph is isomorphic to the library's K₅ line graph
def K₅_line_to_K₅_line : K₅_line ≃g K₅.lineGraph where
  toEquiv := K₅_line_verts
  map_rel_iff' := by
    intro u v
    rw [K₅_line, SimpleGraph.lineGraph]
    dsimp
    rw [Set.inter_nonempty, Finset.disjoint_iff_ne]
    push Not
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, SetLike.mem_coe,
      ↓existsAndEq, Sym2.mem_toFinset, and_true, and_congr_right_iff]
    intro neq
    sorry

-- petereson is isomorphic to custom line graph compl
def pet_to_custom_line : pet ≃g K₅_lineᶜ where
  toEquiv := by rfl
  map_rel_iff' := by
    intro u v
    rw [SimpleGraph.compl_adj, pet, K₅_line]
    dsimp
    rw [adj, decide_eq_true_eq]
    push Not
    constructor
    · rintro ⟨neq, h⟩
      exact h neq
    decide +revert

-- hence, isomorphic to library's K₅ line graph compl
def pet_to_comp_line : pet ≃g K₅.lineGraphᶜ := by
  apply SimpleGraph.Iso.comp _ pet_to_custom_line
  constructor
  · intro u v
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, and_congr_right_iff]
    intro neq
    apply not_congr
    exact (SimpleGraph.Iso.map_adj_iff K₅_line_to_K₅_line)

end altPetersen

/- vertex autmorphism group of petersen is S₅ -/
noncomputable def eq_autGroup_pet_symm : autGroupVert Petersen.pet ≃* Equiv.Perm (Fin 5) := by
  apply MulEquiv.trans (eq_iso_autGroup Petersen.pet altPetersen.pet_to_alt_pet)
  apply MulEquiv.trans (eq_iso_autGroup altPetersen.pet altPetersen.pet_to_comp_line)
  rw [←autGroup_compl K₅.lineGraph]
  have :
    (autGroupVert K₅.lineGraph) =
    (autGroupEdge K₅) :=
    by trivial
  rw [this]
  have K₅_five_verts : 5 ≤ Fintype.card (Fin 5) := by trivial
  apply MulEquiv.trans
    (autGroup_vert_eq_edge K₅ K₅_five_verts).symm
  have := autGroup_complete_eq_symm 5
  rw [this]
  exact Subgroup.topEquiv
