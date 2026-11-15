/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.Genus.BaseChange
public import TauCeti.AlgebraicGeometry.Curves.Node.NormalizedComponent
import Mathlib.Tactic.FinCases
import TauCeti.AlgebraicGeometry.FiniteEtale.SepClosed
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk

/-!
# The scheme-theoretic dual graph of a nodal curve

Let `X` be a proper connected nodal curve over a separably closed field `K`, equipped with smooth
`K`-valued markings `s : ι → (Spec (.of K) ⟶ X)`. Blowing up the singular subscheme `Sing(X/K)`
produces a finite surjective regular modification `ν : Bl X ⟶ X` that is an isomorphism over the
smooth locus (`AlgebraicGeometry.Scheme.isRegular_blowup_singularLocus`). Because `K` is separably
closed, both the singular subscheme `Sing(X/K)` and the rank-two branch scheme
`E = Sing(X/K) ×_X Bl X` split over `K`: every node is a `K`-point of `Sing(X/K)` with two distinct
branches in `E`.

This file assembles those geometric data into a combinatorial `TauCeti.DualGraph`
(`AlgebraicGeometry.Scheme.dualGraph`):

* **Vertices**: the irreducible components of `Bl X`, corresponding bijectively to the irreducible
  components of `X` via `AlgebraicGeometry.Scheme.dualGraphIrreducibleComponentsEquiv`. Each vertex
  `v` carries the cohomological genus `(X.dualGraphComponent hnodal v).genus K` of its normalized
  component.
* **Edges and endpoints**: the points of `Sing(X/K)`, with the two endpoints of `e` given by the
  components of `Bl X` containing the two branches of `E` over `e`.
* **Markings**: each smooth marking lifts uniquely to `Bl X` and records the component containing
  its image (`AlgebraicGeometry.Scheme.marking_dualGraph_eq_iff`).
* **Connectedness**: topological connectedness of `X` forces the component-node incidence graph to
  be connected (`AlgebraicGeometry.Scheme.connected_dualGraphEndpoint`).

All combinatorial invariants of `X.dualGraph` are then read directly off the geometry of `X`: the
valence of `v` counts the branches (equivalently, the preimages of nodes) lying on `v`
(`AlgebraicGeometry.Scheme.valence_dualGraph`), and `v` carries no self-node loop if and only if
the normalization map `ν` is injective on `v`
(`AlgebraicGeometry.Scheme.forall_endpoint_dualGraph_one_ne_iff_injOn`). When `X` is smooth, the
dual graph has a single vertex, no edges, and arithmetic genus equal to `X.genus K`
(`AlgebraicGeometry.Scheme.arithmeticGenus_dualGraph_eq_genus_of_smooth`).

Finally, because `Sing(X/K)`, `E`, the irreducible components of `Bl X`, and the genera of proper
curves are all preserved under base change from a separably closed field `K` to any separably closed
extension `L / K` (even an inseparable one), base change induces a canonical isomorphism of dual
graphs (`AlgebraicGeometry.Scheme.dualGraphIsoOfIsPullback`). Specializing to `L = K` yields
isomorphism invariance and functoriality for pointed nodal curves over `K`
(`AlgebraicGeometry.Scheme.dualGraphIsoOfIso`).

## References

* [The Stacks Project, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodal curves and
  separation of branches.
* [The Stacks Project, Tag 0E6X](https://stacks.math.columbia.edu/tag/0E6X): semistable and stable
  curves via rational tails and bridges.
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, §2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- Over a separably closed field, a proper nodal curve has finitely many singular points. -/
theorem finite_singularLocus_subscheme [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    Finite (X.singularLocus K).subscheme := by
  have := hnodal.syntomic
  have := X.isFinite_singularLocus_subschemeι_comp hnodal
  have := X.etale_singularLocus_subschemeι_comp hnodal
  exact ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))).finite_of_isSepClosed

/-- Over a separably closed field, every singular point of a proper nodal curve has two branches in
the branch scheme. -/
theorem natCard_branchFiber_eq_two [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme) :
    letI := hnodal.syntomic
    Nat.card {b : X.branchScheme K // X.branchSchemeToSingularLocus K b = e} = 2 := by
  have := hnodal.syntomic
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  have := X.isFinite_singularLocus_subschemeι_comp hnodal
  have := X.etale_singularLocus_subschemeι_comp hnodal
  exact ((X.branchSchemeToSingularLocus K).natCard_preimage_eq_finrank_of_isSepClosed
    ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) e).trans
      (X.finrank_branchSchemeToSingularLocus hnodal e)

/-- Choice of ordering of the two branches of `X` over a node `e`, used to populate the ordered
`endpoint : Edge → Fin 2 → Vertex` field of `DualGraph`. All downstream statements pass immediately
through `sym2_dualGraphEndpoint_eq_of_ne`, which is independent of this ordering. -/
private def branchFiberEquiv [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme) :
    letI := hnodal.syntomic
    Fin 2 ≃ {b : X.branchScheme K // X.branchSchemeToSingularLocus K b = e} := by
  letI := hnodal.syntomic
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  have := X.isFinite_singularLocus_subschemeι_comp hnodal
  have := X.etale_singularLocus_subschemeι_comp hnodal
  have : Finite (X.branchScheme K) :=
    (X.branchSchemeToSingularLocus K ≫ (X.singularLocus K).subschemeι ≫
      (X ↘ Spec (.of K))).finite_of_isSepClosed
  let _ : Fintype {b : X.branchScheme K // X.branchSchemeToSingularLocus K b = e} :=
    Fintype.ofFinite _
  exact (Fintype.equivFinOfCardEq
    (Nat.card_eq_fintype_card.symm.trans (X.natCard_branchFiber_eq_two hnodal e))).symm

/-- Endpoint map of the dual graph of `X`, sending `(e, i)` to the irreducible component of `Bl X`
containing the `i`-th branch over `e`. -/
def dualGraphEndpoint [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme) (i : Fin 2) :
    letI := hnodal.syntomic
    irreducibleComponents (X.singularLocus K).blowup :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  IsRegular.componentOf (X.singularLocus K).blowup
    (X.branchSchemeToBlowup K (X.branchFiberEquiv hnodal e i).1)

/-- Whenever `b₀ ≠ b₁` are two branches over the same node `e`, the unordered pair of endpoints of
`e` is the pair of components of `Bl X` containing `b₀` and `b₁`. -/
private theorem sym2_dualGraphEndpoint_eq_of_ne [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme)
    {b₀ b₁ : letI := hnodal.syntomic; X.branchScheme K}
    (hb₀ : letI := hnodal.syntomic; X.branchSchemeToSingularLocus K b₀ = e)
    (hb₁ : letI := hnodal.syntomic; X.branchSchemeToSingularLocus K b₁ = e)
    (hne : b₀ ≠ b₁) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    s(X.dualGraphEndpoint hnodal e 0, X.dualGraphEndpoint hnodal e 1) =
      s(IsRegular.componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₀),
        IsRegular.componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₁)) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  let eqv := X.branchFiberEquiv hnodal e
  let i₀ : Fin 2 := eqv.symm ⟨b₀, hb₀⟩
  let i₁ : Fin 2 := eqv.symm ⟨b₁, hb₁⟩
  have hi : i₀ ≠ i₁ := fun h ↦ hne (congrArg Subtype.val (eqv.symm.injective h))
  have h₀ : (eqv i₀).1 = b₀ := congrArg Subtype.val (eqv.apply_symm_apply ⟨b₀, hb₀⟩)
  have h₁ : (eqv i₁).1 = b₁ := congrArg Subtype.val (eqv.apply_symm_apply ⟨b₁, hb₁⟩)
  have hswap : ∀ a b : Fin 2, a ≠ b →
      s(X.dualGraphEndpoint hnodal e 0, X.dualGraphEndpoint hnodal e 1) =
        s(X.dualGraphEndpoint hnodal e a, X.dualGraphEndpoint hnodal e b) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hab
  rw [hswap i₀ i₁ hi]
  simp only [dualGraphEndpoint, eqv, h₀, h₁]

/-- Topological connectedness of a proper nodal curve `X` over a separably closed field forces its
component-node incidence graph to be connected. -/
theorem connected_dualGraphEndpoint [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    ∀ v w : irreducibleComponents (X.singularLocus K).blowup,
      Relation.ReflTransGen
        (fun v w ↦ ∃ e,
          (X.dualGraphEndpoint hnodal e 0 = v ∧ X.dualGraphEndpoint hnodal e 1 = w) ∨
            (X.dualGraphEndpoint hnodal e 0 = w ∧ X.dualGraphEndpoint hnodal e 1 = v))
        v w := by
  have := hnodal.syntomic
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective ν := X.surjective_blowupToBase_singularLocus hnodal
  have : Finite (irreducibleComponents Bl) :=
    X.finite_irreducibleComponents_blowup_singularLocus hnodal
  have hfin : (Set.univ : Set (irreducibleComponents Bl)).Finite := Set.finite_univ
  intro v₀ w₀
  by_contra hw₀
  -- 1. Partition `X` into the union `A` of components reachable from `v₀` and the union `B`
  --    of the remaining components.
  let R : irreducibleComponents Bl → irreducibleComponents Bl → Prop := fun v w ↦
    ∃ e, (X.dualGraphEndpoint hnodal e 0 = v ∧ X.dualGraphEndpoint hnodal e 1 = w) ∨
      (X.dualGraphEndpoint hnodal e 0 = w ∧ X.dualGraphEndpoint hnodal e 1 = v)
  let S : Set (irreducibleComponents Bl) := {w | Relation.ReflTransGen R v₀ w}
  let A : Set X := ⋃ v ∈ S, ν '' (v : Set Bl)
  let B : Set X := ⋃ v ∈ Sᶜ, ν '' (v : Set Bl)
  have hA_closed : IsClosed A :=
    (hfin.subset (Set.subset_univ S)).isClosed_biUnion fun v _ ↦
      ν.isClosedMap v.1 (isClosed_of_mem_irreducibleComponents v.1 v.2)
  have hB_closed : IsClosed B :=
    (hfin.subset (Set.subset_univ Sᶜ)).isClosed_biUnion fun v _ ↦
      ν.isClosedMap v.1 (isClosed_of_mem_irreducibleComponents v.1 v.2)
  have hcov : (Set.univ : Set X) ⊆ A ∪ B := by
    intro x _
    obtain ⟨y, rfl⟩ := ν.surjective x
    let v := IsRegular.componentOf Bl y
    by_cases hv : v ∈ S
    · exact Or.inl (Set.mem_biUnion hv ⟨y, IsRegular.mem_componentOf y, rfl⟩)
    · exact Or.inr (Set.mem_biUnion hv ⟨y, IsRegular.mem_componentOf y, rfl⟩)
  have hA_ne : (Set.univ ∩ A).Nonempty := by
    obtain ⟨y, hy⟩ := v₀.2.1.nonempty
    exact ⟨ν y, Set.mem_univ _, Set.mem_biUnion Relation.ReflTransGen.refl ⟨y, hy, rfl⟩⟩
  have hB_ne : (Set.univ ∩ B).Nonempty := by
    obtain ⟨y, hy⟩ := w₀.2.1.nonempty
    exact ⟨ν y, Set.mem_univ _, Set.mem_biUnion hw₀ ⟨y, hy, rfl⟩⟩
  obtain ⟨x, -, hxA, hxB⟩ :=
    isPreconnected_closed_iff.mp isPreconnected_univ A B hA_closed hB_closed hcov hA_ne hB_ne
  obtain ⟨v, hvS, y₁, hy₁, rfl⟩ := Set.mem_iUnion₂.mp hxA
  obtain ⟨w, hwS, y₂, hy₂, hy₂_eq⟩ := Set.mem_iUnion₂.mp hxB
  have hvw : v ≠ w := fun h ↦ hwS (h ▸ hvS)
  have hy_ne : y₁ ≠ y₂ := fun h ↦ hvw <|
    (IsRegular.componentOf_eq_iff.mpr hy₁).symm.trans (IsRegular.componentOf_eq_iff.mpr (h ▸ hy₂))
  -- Since `y₁ ≠ y₂` map to the same point of `X`, that point cannot lie in the smooth locus, so it
  -- comes from a node `e` of `Sing(X/K)` whose two branches lie on `v` and `w`.
  have hx_sing : ν y₁ ∈ (X.singularLocus K).support := by
    rw [X.mem_support_singularLocus_iff_notMem_smoothLocus]
    intro hxU
    have hy₂U : y₂ ∈ ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
      rw [Set.mem_preimage, hy₂_eq]
      exact hxU
    exact hy_ne (X.injOn_preimage_smoothLocus_blowupToBase hnodal hxU hy₂U hy₂_eq.symm)
  obtain ⟨e, he⟩ := (IdealSheafData.range_subschemeι (X.singularLocus K)).ge hx_sing
  have hfib := image_preimage_eq_of_isPullback (X.isPullback_branchScheme K) {e}
  rw [Set.image_singleton, he] at hfib
  have hy₁_br : y₁ ∈ X.branchSchemeToBlowup K '' (X.branchSchemeToSingularLocus K ⁻¹' {e}) := by
    rw [hfib]
    exact rfl
  have hy₂_br : y₂ ∈ X.branchSchemeToBlowup K '' (X.branchSchemeToSingularLocus K ⁻¹' {e}) := by
    rw [hfib]
    exact hy₂_eq
  obtain ⟨b₁, hb₁, hb₁_eq⟩ := hy₁_br
  obtain ⟨b₂, hb₂, hb₂_eq⟩ := hy₂_br
  have hb_ne : b₁ ≠ b₂ := fun h ↦ hy_ne (hb₁_eq ▸ hb₂_eq ▸ congrArg _ h)
  have hends := X.sym2_dualGraphEndpoint_eq_of_ne hnodal e hb₁ hb₂ hb_ne
  rw [hb₁_eq, hb₂_eq, IsRegular.componentOf_eq_iff.mpr hy₁,
    IsRegular.componentOf_eq_iff.mpr hy₂] at hends
  exact hwS (hvS.tail ⟨e, Sym2.eq_iff.mp hends⟩)

/-- **The dual graph of a proper connected nodal curve over a separably closed field**, equipped
with smooth markings `s : ι → (Spec (.of K) ⟶ X)`. -/
def dualGraph [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus) :
    DualGraph.{u} ι :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  letI : Fintype (irreducibleComponents (X.singularLocus K).blowup) :=
    @Fintype.ofFinite _ (X.finite_irreducibleComponents_blowup_singularLocus hnodal)
  letI : DecidableEq (irreducibleComponents (X.singularLocus K).blowup) := Classical.decEq _
  letI : Nonempty (irreducibleComponents (X.singularLocus K).blowup) :=
    X.nonempty_irreducibleComponents_blowup_singularLocus hnodal
  letI : Fintype (X.singularLocus K).subscheme :=
    @Fintype.ofFinite _ (X.finite_singularLocus_subscheme hnodal)
  letI : DecidableEq (X.singularLocus K).subscheme := Classical.decEq _
  { Vertex := irreducibleComponents (X.singularLocus K).blowup
    Edge := (X.singularLocus K).subscheme
    endpoint := X.dualGraphEndpoint hnodal
    genus := fun v ↦ (X.normalizedComponent hnodal v).genus K
    marking := fun i ↦ IsRegular.componentOf (X.singularLocus K).blowup
      (X.markingLift hnodal (s i) (hs i) default)
    connected := X.connected_dualGraphEndpoint hnodal }

/-- **The unpointed dual graph of a proper connected nodal curve** over a separably closed field. -/
abbrev unpointedDualGraph [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    DualGraph.{u} PEmpty :=
  X.dualGraph hnodal PEmpty.elim fun i ↦ i.elim

section Invariants

variable [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
  (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
  {ι : Type v} (s : ι → (Spec (.of K) ⟶ X))
  (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)

/-- Canonical identification of the vertices of `X.dualGraph` with the irreducible components of
the normalization `Bl X`. -/
def dualGraphVertexEquiv :
    letI := hnodal.syntomic
    (X.dualGraph hnodal s hs).Vertex ≃ irreducibleComponents (X.singularLocus K).blowup :=
  Equiv.refl _

/-- Canonical identification of the edges of `X.dualGraph` with the points of the singular
subscheme `Sing(X/K)`. -/
def dualGraphEdgeEquiv :
    letI := hnodal.syntomic
    (X.dualGraph hnodal s hs).Edge ≃ (X.singularLocus K).subscheme :=
  Equiv.refl _

/-- Canonical bijection between the vertices of `X.dualGraph` and the irreducible components of
`X`. -/
def dualGraphIrreducibleComponentsEquiv :
    (X.dualGraph hnodal s hs).Vertex ≃ irreducibleComponents X :=
  letI := hnodal.syntomic
  (X.dualGraphVertexEquiv hnodal s hs).trans (X.irreducibleComponentsBlowupEquiv hnodal)

@[simp]
theorem coe_dualGraphIrreducibleComponentsEquiv (v : (X.dualGraph hnodal s hs).Vertex) :
    letI := hnodal.syntomic
    (X.dualGraphIrreducibleComponentsEquiv hnodal s hs v : Set X) =
      (X.singularLocus K).blowupToBase ''
        (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup) :=
  X.coe_irreducibleComponentsBlowupEquiv hnodal _

/-- The normalized component scheme attached to a vertex `v` of `X.dualGraph`. -/
abbrev dualGraphComponent
    {s : ι → (Spec (.of K) ⟶ X)}
    {hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus}
    (v : (X.dualGraph hnodal s hs).Vertex) :
    Scheme.{u} :=
  X.normalizedComponent hnodal (X.dualGraphVertexEquiv hnodal s hs v)

@[simp]
theorem genus_dualGraph (v : (X.dualGraph hnodal s hs).Vertex) :
    (X.dualGraph hnodal s hs).genus v = (X.dualGraphComponent hnodal v).genus K :=
  (rfl)

@[simp]
theorem reindex_dualGraph {κ : Type*} (f : κ → ι) :
    (X.dualGraph hnodal s hs).reindex f = X.dualGraph hnodal (s ∘ f) (fun j ↦ hs (f j)) :=
  (rfl)

@[simp]
theorem dualGraphVertexEquiv_marking (i : ι) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    X.dualGraphVertexEquiv hnodal s hs ((X.dualGraph hnodal s hs).marking i) =
      IsRegular.componentOf (X.singularLocus K).blowup
        (X.markingLift hnodal (s i) (hs i) default) :=
  (rfl)

@[simp]
theorem dualGraphVertexEquiv_endpoint (e : (X.dualGraph hnodal s hs).Edge) (i : Fin 2) :
    letI := hnodal.syntomic
    X.dualGraphVertexEquiv hnodal s hs ((X.dualGraph hnodal s hs).endpoint e i) =
      X.dualGraphEndpoint hnodal (X.dualGraphEdgeEquiv hnodal s hs e) i :=
  (rfl)

/-- The `i`-th marking of `X.dualGraph` is the unique component of `X` containing the image of
`s i`. -/
theorem marking_dualGraph_eq_iff (i : ι) (v : (X.dualGraph hnodal s hs).Vertex) :
    (X.dualGraph hnodal s hs).marking i = v ↔
      s i default ∈ (X.dualGraphIrreducibleComponentsEquiv hnodal s hs v : Set X) := by
  have := hnodal.syntomic
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  rw [← (X.dualGraphVertexEquiv hnodal s hs).injective.eq_iff,
    X.dualGraphVertexEquiv_marking hnodal s hs i, IsRegular.componentOf_eq_iff,
    X.coe_dualGraphIrreducibleComponentsEquiv]
  have hlift : ν (X.markingLift hnodal (s i) (hs i) default) = s i default := by
    rw [← Scheme.Hom.comp_apply, X.markingLift_blowupToBase]
  refine ⟨fun h ↦ ⟨_, h, hlift⟩, ?_⟩
  rintro ⟨y, hyv, hy_eq⟩
  have hsU : s i default ∈ (X ↘ Spec (.of K)).smoothLocus := hs i ⟨default, rfl⟩
  have h₁ : X.markingLift hnodal (s i) (hs i) default ∈
      ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    rw [Set.mem_preimage, hlift]
    exact hsU
  have h₂ : y ∈ ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    rw [Set.mem_preimage, hy_eq]
    exact hsU
  rwa [X.injOn_preimage_smoothLocus_blowupToBase hnodal h₁ h₂ (hlift.trans hy_eq.symm)]

/-- Whenever `b₀ ≠ b₁` are the two branches of `X` over a node `e`, the unordered pair of endpoints
of `e` in `X.dualGraph` is the pair of components of `Bl X` containing `b₀` and `b₁`. -/
theorem ends_dualGraph_eq_of_ne
    (e : (X.dualGraph hnodal s hs).Edge)
    {b₀ b₁ : letI := hnodal.syntomic; X.branchScheme K}
    (hb₀ : letI := hnodal.syntomic
      X.branchSchemeToSingularLocus K b₀ = X.dualGraphEdgeEquiv hnodal s hs e)
    (hb₁ : letI := hnodal.syntomic
      X.branchSchemeToSingularLocus K b₁ = X.dualGraphEdgeEquiv hnodal s hs e)
    (hne : b₀ ≠ b₁) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    (X.dualGraph hnodal s hs).ends e =
      s((X.dualGraphVertexEquiv hnodal s hs).symm
          (IsRegular.componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₀)),
        (X.dualGraphVertexEquiv hnodal s hs).symm
          (IsRegular.componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₁))) := by
  rw [DualGraph.ends_def]
  exact X.sym2_dualGraphEndpoint_eq_of_ne hnodal (X.dualGraphEdgeEquiv hnodal s hs e) hb₀ hb₁ hne

/-- A vertex `v` lies on an edge `e` of `X.dualGraph` if and only if one of the branches over `e`
lies on `v`. -/
theorem mem_ends_dualGraph_iff (v : (X.dualGraph hnodal s hs).Vertex)
    (e : (X.dualGraph hnodal s hs).Edge) :
    letI := hnodal.syntomic
    v ∈ (X.dualGraph hnodal s hs).ends e ↔
      ∃ b : X.branchScheme K,
        X.branchSchemeToSingularLocus K b = X.dualGraphEdgeEquiv hnodal s hs e ∧
          X.branchSchemeToBlowup K b ∈
            (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  let e₀ := X.dualGraphEdgeEquiv hnodal s hs e
  rw [DualGraph.mem_ends_iff]
  simp only [← (X.dualGraphVertexEquiv hnodal s hs).injective.eq_iff,
    X.dualGraphVertexEquiv_endpoint, dualGraphEndpoint, IsRegular.componentOf_eq_iff]
  refine ⟨fun ⟨i, hi⟩ ↦
      ⟨(X.branchFiberEquiv hnodal e₀ i).1, (X.branchFiberEquiv hnodal e₀ i).2, hi⟩,
    fun ⟨b, hb, hbv⟩ ↦ ⟨(X.branchFiberEquiv hnodal e₀).symm ⟨b, hb⟩, ?_⟩⟩
  simpa only [e₀, Equiv.apply_symm_apply] using hbv

/-- The number of vertices of `X.dualGraph` equals the number of irreducible components of `X`. -/
theorem card_vertex_dualGraph :
    Fintype.card (X.dualGraph hnodal s hs).Vertex = Nat.card (irreducibleComponents X) :=
  Fintype.card_eq_nat_card.trans
    (Nat.card_congr (X.dualGraphIrreducibleComponentsEquiv hnodal s hs))

/-- The number of edges of `X.dualGraph` equals the number of singular points of `X`. -/
theorem card_edge_dualGraph :
    letI := hnodal.syntomic
    Fintype.card (X.dualGraph hnodal s hs).Edge = Nat.card (X.singularLocus K).support := by
  have := hnodal.syntomic
  have hrange := IdealSheafData.range_subschemeι (X.singularLocus K)
  have hinj := (X.singularLocus K).subschemeι.isClosedEmbedding.injective
  exact Fintype.card_eq_nat_card.trans <|
    (Nat.card_congr (X.dualGraphEdgeEquiv hnodal s hs)).trans <|
      (Nat.card_congr (Equiv.ofInjective (X.singularLocus K).subschemeι hinj)).trans
        (Nat.card_congr (Set.equivOfEq hrange))

/-- **The valence of a vertex counts the branches of `X` lying on that normalized component.** -/
theorem valence_dualGraph (v : (X.dualGraph hnodal s hs).Vertex) :
    letI := hnodal.syntomic
    (X.dualGraph hnodal s hs).valence v =
      Nat.card {b : X.branchScheme K //
        X.branchSchemeToBlowup K b ∈
          (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup)} := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  let v₀ := X.dualGraphVertexEquiv hnodal s hs v
  let pairEquivBr : (X.dualGraph hnodal s hs).Edge × Fin 2 ≃ X.branchScheme K :=
    ((X.dualGraphEdgeEquiv hnodal s hs).prodCongr (Equiv.refl (Fin 2))).trans <|
      (Equiv.sigmaEquivProd (X.singularLocus K).subscheme (Fin 2)).symm.trans <|
        (Equiv.sigmaCongrRight (X.branchFiberEquiv hnodal)).trans
          (Equiv.sigmaFiberEquiv (X.branchSchemeToSingularLocus K))
  let subEquiv :
      {h : (X.dualGraph hnodal s hs).Edge × Fin 2 //
          (X.dualGraph hnodal s hs).endpoint h.1 h.2 = v} ≃
        {b : X.branchScheme K //
          X.branchSchemeToBlowup K b ∈
            (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup)} :=
    pairEquivBr.subtypeEquiv fun ⟨e, i⟩ ↦ by
      let e₀ := X.dualGraphEdgeEquiv hnodal s hs e
      dsimp only [dualGraph, v₀, e₀, dualGraphVertexEquiv, dualGraphEdgeEquiv, pairEquivBr,
        Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Equiv.sigmaEquivProd_symm_apply,
        Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
      exact IsRegular.componentOf_eq_iff
  rw [DualGraph.valence_def, ← Fintype.card_subtype]
  exact Fintype.card_eq_nat_card.trans (Nat.card_congr subEquiv)

/-- **The valence of a vertex also counts the points of that normalized component lying over nodes
of `X`.** -/
theorem valence_dualGraph_eq_natCard_preimage_singularLocus
    (v : (X.dualGraph hnodal s hs).Vertex) :
    letI := hnodal.syntomic
    (X.dualGraph hnodal s hs).valence v =
      Nat.card {y : (X.singularLocus K).blowup //
        y ∈ (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup) ∧
          (X.singularLocus K).blowupToBase y ∈ (X.singularLocus K).support} := by
  have := hnodal.syntomic
  have : IsClosedImmersion (X.branchSchemeToBlowup K) :=
    MorphismProperty.of_isPullback (X.isPullback_branchScheme K) inferInstance
  have hinj : Function.Injective (X.branchSchemeToBlowup K) :=
    (X.branchSchemeToBlowup K).isClosedEmbedding.injective
  have hrange : Set.range (X.branchSchemeToBlowup K) =
      (X.singularLocus K).blowupToBase ⁻¹' ((X.singularLocus K).support : Set X) := by
    have h := image_preimage_eq_of_isPullback (X.isPullback_branchScheme K) Set.univ
    simpa only [Set.preimage_univ, Set.image_univ, IdealSheafData.range_subschemeι] using h
  rw [X.valence_dualGraph hnodal s hs v]
  refine Nat.card_congr
    { toFun := fun b ↦ ⟨X.branchSchemeToBlowup K b.1, b.2, by
        rw [← SetLike.mem_coe, ← Set.mem_preimage, ← hrange]
        exact ⟨b.1, rfl⟩⟩
      invFun := fun y ↦
        have hy : y.1 ∈ Set.range (X.branchSchemeToBlowup K) := by
          rw [hrange]
          exact y.2.2
        ⟨hy.choose, by simpa only [hy.choose_spec] using y.2.1⟩
      left_inv := fun b ↦ Subtype.ext (hinj (Set.mem_range_self b.1).choose_spec)
      right_inv := fun y ↦ by
        have hy : y.1 ∈ Set.range (X.branchSchemeToBlowup K) := hrange ▸ y.2.2
        exact Subtype.ext hy.choose_spec }

/-- **A vertex carries no loop in `X.dualGraph` if and only if the normalization map is injective on
that component** (equivalently, the corresponding irreducible component of `X` has no
self-nodes). -/
theorem forall_endpoint_dualGraph_one_ne_iff_injOn (v : (X.dualGraph hnodal s hs).Vertex) :
    letI := hnodal.syntomic
    (∀ e, (X.dualGraph hnodal s hs).endpoint e 0 = v →
      (X.dualGraph hnodal s hs).endpoint e 1 ≠ v) ↔
      Set.InjOn (X.singularLocus K).blowupToBase
        (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  let ν := (X.singularLocus K).blowupToBase
  let v₀ := X.dualGraphVertexEquiv hnodal s hs v
  have : IsClosedImmersion (X.branchSchemeToBlowup K) :=
    MorphismProperty.of_isPullback (X.isPullback_branchScheme K) inferInstance
  have hinj_br : Function.Injective (X.branchSchemeToBlowup K) :=
    (X.branchSchemeToBlowup K).isClosedEmbedding.injective
  rw [DualGraph.forall_endpoint_one_ne_iff]
  constructor
  · -- Forward: two distinct points on `v` with the same image in `X` come from distinct branches
    -- over a node, producing a self-loop on `v`.
    intro hnoloop y₁ hy₁ y₂ hy₂ heq
    by_contra hne
    have hx_sing : ν y₁ ∈ (X.singularLocus K).support := by
      rw [X.mem_support_singularLocus_iff_notMem_smoothLocus]
      intro hxU
      have hy₂U : y₂ ∈ ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
        rw [Set.mem_preimage, ← heq]
        exact hxU
      exact hne (X.injOn_preimage_smoothLocus_blowupToBase hnodal hxU hy₂U heq)
    obtain ⟨e₀, he⟩ := (IdealSheafData.range_subschemeι (X.singularLocus K)).ge hx_sing
    have hfib := image_preimage_eq_of_isPullback (X.isPullback_branchScheme K) {e₀}
    rw [Set.image_singleton, he] at hfib
    obtain ⟨b₁, hb₁, hb₁_eq⟩ : y₁ ∈ X.branchSchemeToBlowup K ''
        (X.branchSchemeToSingularLocus K ⁻¹' {e₀}) := by
      rw [hfib]
      exact rfl
    obtain ⟨b₂, hb₂, hb₂_eq⟩ : y₂ ∈ X.branchSchemeToBlowup K ''
        (X.branchSchemeToSingularLocus K ⁻¹' {e₀}) := by
      rw [hfib]
      exact heq.symm
    have hb_ne : b₁ ≠ b₂ := fun h ↦ hne (hb₁_eq ▸ hb₂_eq ▸ congrArg _ h)
    let e : (X.dualGraph hnodal s hs).Edge := (X.dualGraphEdgeEquiv hnodal s hs).symm e₀
    have hends := X.ends_dualGraph_eq_of_ne hnodal s hs e hb₁ hb₂ hb_ne
    rw [hb₁_eq, hb₂_eq, IsRegular.componentOf_eq_iff.mpr hy₁,
      IsRegular.componentOf_eq_iff.mpr hy₂] at hends
    exact hnoloop e hends
  · -- Converse: a self-loop at `e` gives two distinct branches on `v` over the same node.
    intro hinj e hends
    rw [DualGraph.ends_def] at hends
    let e₀ := X.dualGraphEdgeEquiv hnodal s hs e
    let eqv := X.branchFiberEquiv hnodal e₀
    have h01 : (eqv 0).1 ≠ (eqv 1).1 :=
      fun h ↦ Fin.zero_ne_one (eqv.injective (Subtype.ext h))
    have h0 : X.dualGraphEndpoint hnodal e₀ 0 = v₀ :=
      (Sym2.eq_iff.mp hends).elim And.left And.left
    have h1 : X.dualGraphEndpoint hnodal e₀ 1 = v₀ :=
      (Sym2.eq_iff.mp hends).elim And.right And.right
    have hy₀ : X.branchSchemeToBlowup K (eqv 0).1 ∈ (v₀ : Set _) :=
      IsRegular.componentOf_eq_iff.mp h0
    have hy₁ : X.branchSchemeToBlowup K (eqv 1).1 ∈ (v₀ : Set _) :=
      IsRegular.componentOf_eq_iff.mp h1
    have hν : ν (X.branchSchemeToBlowup K (eqv 0).1) =
        ν (X.branchSchemeToBlowup K (eqv 1).1) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        ← X.branchSchemeToSingularLocus_subschemeι K, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
        (eqv 0).2, (eqv 1).2]
    exact h01 (hinj_br (hinj hy₀ hy₁ hν))

/-- **Geometric characterization of a rational tail**: a normalized component of genus zero meeting
the singular locus in a single branch. -/
theorem isRationalTail_dualGraph_iff (v : (X.dualGraph hnodal s hs).Vertex) :
    letI := hnodal.syntomic
    (X.dualGraph hnodal s hs).IsRationalTail v ↔
      (X.dualGraphComponent hnodal v).genus K = 0 ∧
        Nat.card {b : X.branchScheme K //
          X.branchSchemeToBlowup K b ∈
            (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup)} = 1 := by
  rw [DualGraph.isRationalTail_iff, X.genus_dualGraph, X.valence_dualGraph]

/-- **Geometric characterization of a rational bridge**: a normalized component of genus zero on
which the normalization map is injective and which carries two branches of the singular locus. -/
theorem isRationalBridge_dualGraph_iff (v : (X.dualGraph hnodal s hs).Vertex) :
    letI := hnodal.syntomic
    (X.dualGraph hnodal s hs).IsRationalBridge v ↔
      (X.dualGraphComponent hnodal v).genus K = 0 ∧
        Nat.card {b : X.branchScheme K //
          X.branchSchemeToBlowup K b ∈
            (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup)} = 2 ∧
        Set.InjOn (X.singularLocus K).blowupToBase
          (X.dualGraphVertexEquiv hnodal s hs v : Set (X.singularLocus K).blowup) := by
  rw [DualGraph.isRationalBridge_iff, X.genus_dualGraph, X.valence_dualGraph,
    X.forall_endpoint_dualGraph_one_ne_iff_injOn]

/-- **Validation on smooth curves.** When `X` is smooth, its dual graph has no edges, first Betti
number zero, and combinatorial arithmetic genus equal to the cohomological genus `X.genus K`. -/
theorem arithmeticGenus_dualGraph_eq_genus_of_smooth [Smooth (X ↘ Spec (.of K))] :
    letI := X.smoothOfRelativeDimension_one_of_smooth hnodal
    letI := finiteDimensional_cohomology_one_trivial_of_smooth K X
    (X.dualGraph hnodal s hs).firstBetti = 0 ∧
      (X.dualGraph hnodal s hs).arithmeticGenus = X.genus K := by
  have := hnodal.syntomic
  let G := X.dualGraph hnodal s hs
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of K))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have := X.smoothOfRelativeDimension_one_of_smooth hnodal
  have := finiteDimensional_cohomology_one_trivial_of_smooth K X
  -- 1. Smoothness forces `Sing(X/K) = ⊤`, so the dual graph has 0 edges, 1 vertex, and `b₁ = 0`.
  have hsing_top : X.singularLocus K = ⊤ :=
    (X.singularLocus_eq_top_iff_smooth (R := K)).mpr ‹_›
  have hempty_edge : IsEmpty G.Edge := by
    refine ⟨fun e ↦ ?_⟩
    let e₀ := X.dualGraphEdgeEquiv hnodal s hs e
    have hmem : (X.singularLocus K).subschemeι e₀ ∈ ((X.singularLocus K).support : Set X) := by
      rw [← IdealSheafData.range_subschemeι]
      exact ⟨e₀, rfl⟩
    rw [(IdealSheafData.support_eq_bot_iff _).mpr hsing_top] at hmem
    exact hmem
  have hcard_edge : Fintype.card G.Edge = 0 := Fintype.card_eq_zero
  have hcard_vert : Fintype.card G.Vertex = 1 := by
    rw [X.card_vertex_dualGraph hnodal s hs, irreducibleComponents_eq_singleton, Nat.card_unique]
  have hb₁ : G.firstBetti = 0 := by
    rw [DualGraph.firstBetti_def, hcard_edge, hcard_vert]
  obtain ⟨v₀⟩ := G.vertexNonempty
  have huniq : ∀ w : G.Vertex, w = v₀ := fun w ↦ Fintype.card_le_one_iff.mp hcard_vert.le w v₀
  let v₀' : irreducibleComponents Bl := X.dualGraphVertexEquiv hnodal s hs v₀
  have hv₀_univ : (v₀' : Set Bl) = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ by
      have hy := congrArg (X.dualGraphVertexEquiv hnodal s hs)
        (huniq ((X.dualGraphVertexEquiv hnodal s hs).symm (IsRegular.componentOf Bl y)))
      rw [Equiv.apply_symm_apply] at hy
      exact IsRegular.componentOf_eq_iff.mp hy
  -- 2. Both `Bl X ⟶ X` and `C_{v₀} ⟶ Bl X` are isomorphisms, identifying the component genus
  --    with `X.genus K`.
  have hU_top : (X ↘ Spec (.of K)).smoothLocus = ⊤ :=
    Scheme.Hom.smoothLocus_eq_top_iff.mpr ‹_›
  have : IsIso (ν ∣_ (⊤ : X.Opens)) := by
    rw [← hU_top]
    exact X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have : IsIso ((ν ⁻¹ᵁ (⊤ : X.Opens)).ι ≫ ν) := by
    rw [← morphismRestrict_ι]
    have : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
    infer_instance
  have hpre_top : ν ⁻¹ᵁ (⊤ : X.Opens) = ⊤ := rfl
  have : IsIso ((⊤ : Bl.Opens).ι ≫ ν) := by
    rwa [← hpre_top]
  have : IsIso ν := by
    have : IsIso (⊤ : Bl.Opens).ι := Bl.topIso.isIso_hom
    exact IsIso.of_isIso_comp_left (⊤ : Bl.Opens).ι ν
  have : IsIso (X.normalizedComponentι hnodal v₀') :=
    X.isIso_normalizedComponentι_of_eq_univ hnodal v₀' hv₀_univ
  let g₀ : X.dualGraphComponent hnodal v₀ ⟶ X := X.normalizedComponentι hnodal v₀' ≫ ν
  let _ : Algebra K K := Algebra.id K
  have hSpec_id : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by simp
  have hpb : IsPullback g₀
      (X.dualGraphComponent hnodal v₀ ↘ Spec (.of K))
      (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    rw [hSpec_id]
    exact IsPullback.of_horiz_isIso ⟨by simp [g₀, v₀', ν]⟩
  have hgen : (X.dualGraphComponent hnodal v₀).genus K = X.genus K :=
    genus_eq_of_isPullback_of_isProper hpb
  refine ⟨hb₁, ?_⟩
  rw [DualGraph.arithmeticGenus_def, hb₁, add_zero,
    Fintype.sum_eq_single v₀ (fun w hw ↦ absurd (huniq w) hw),
    X.genus_dualGraph hnodal s hs v₀, hgen]

end Invariants

end SepClosed

/-! ### Invariance under extensions of separably closed fields and curve isomorphisms -/

section BaseChange

/-- **Invariance of the dual graph under extensions of separably closed fields.** Let `L / K` be an
extension of separably closed fields (possibly inseparable), and let `X'` over `L` be a base change
of a proper connected nodal curve `X` over `K` along `Spec L ⟶ Spec K`, compatibly with smooth
markings `s` and `s'`. Then `X'.dualGraph` and `X.dualGraph` are canonically isomorphic. -/
def dualGraphIsoOfIsPullback {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
    [Algebra K L] {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i) :
    (X'.dualGraph hnodal' s' hs').Iso (X.dualGraph hnodal s hs) := by
  letI := hnodal.syntomic
  letI := hnodal'.syntomic
  let I := X.singularLocus K
  let I' := X'.singularLocus L
  letI : IsRegular I.blowup := X.isRegular_blowup_singularLocus hnodal
  letI : IsRegular I'.blowup := X'.isRegular_blowup_singularLocus hnodal'
  -- 1. Base change of the normalization `Bl' ⟶ Bl` and bijection of vertices.
  let g_Bl : I'.blowup ⟶ I.blowup := blowupSingularLocusMap hnodal hnodal' H
  have hg_Bl_ν : g_Bl ≫ I.blowupToBase = I'.blowupToBase ≫ g :=
    blowupSingularLocusMap_blowupToBase hnodal hnodal' H
  have H_Bl0 : IsPullback I'.blowupToBase g_Bl g I.blowupToBase :=
    isPullback_blowupSingularLocusMap hnodal hnodal' H
  have H_Bl := isPullback_blowupSingularLocusMap_over hnodal hnodal' H
  let vertexEquiv : (X'.dualGraph hnodal' s' hs').Vertex ≃ (X.dualGraph hnodal s hs).Vertex :=
    (X'.dualGraphVertexEquiv hnodal' s' hs').trans <|
      (irreducibleComponentsEquivOfIsPullback H_Bl).trans
        (X.dualGraphVertexEquiv hnodal s hs).symm
  -- 2. Base change of the singular subscheme `Sing(X'/L) ⟶ Sing(X/K)` and bijection of edges.
  have hI : I' = I.comap g := Scheme.singularLocus_eq_comap_of_isPullback H
  have hle_I : I ≤ I'.map g := IdealSheafData.le_map_iff_comap_le.mpr hI.ge
  let g_Sing : I'.subscheme ⟶ I.subscheme := I'.subschemeMap I g hle_I
  have H_Sing0 : IsPullback I'.subschemeι g_Sing g I.subschemeι :=
    Scheme.isPullback_singularLocus_subschemeι H
  have H_Sing : IsPullback g_Sing (I'.subschemeι ≫ (X' ↘ Spec (.of L)))
      (I.subschemeι ≫ (X ↘ Spec (.of K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    H_Sing0.flip.paste_vert H
  have := X.isFinite_singularLocus_subschemeι_comp hnodal
  have := X.etale_singularLocus_subschemeι_comp hnodal
  have hbij_Sing : Function.Bijective g_Sing :=
    Scheme.Hom.bijective_of_isPullback_algebraMap_of_isSepClosed H_Sing
  let edgeEquiv : (X'.dualGraph hnodal' s' hs').Edge ≃ (X.dualGraph hnodal s hs).Edge :=
    (X'.dualGraphEdgeEquiv hnodal' s' hs').trans <|
      (Equiv.ofBijective g_Sing hbij_Sing).trans (X.dualGraphEdgeEquiv hnodal s hs).symm
  -- 3. Base change of the branch scheme `E' ⟶ E`, commuting with both `Sing` and `Bl`.
  have hBr_comm : (X'.branchSchemeToSingularLocus L ≫ g_Sing) ≫ I.subschemeι =
      (X'.branchSchemeToBlowup L ≫ g_Bl) ≫ I.blowupToBase := by
    rw [Category.assoc, IdealSheafData.subschemeMap_subschemeι _ _ _ hle_I,
      ← Category.assoc, X'.branchSchemeToSingularLocus_subschemeι L, Category.assoc,
      Category.assoc, hg_Bl_ν]
  let g_Br : X'.branchScheme L ⟶ X.branchScheme K :=
    (X.isPullback_branchScheme K).lift (X'.branchSchemeToSingularLocus L ≫ g_Sing)
      (X'.branchSchemeToBlowup L ≫ g_Bl) hBr_comm
  have hg_Br_sing : g_Br ≫ X.branchSchemeToSingularLocus K =
      X'.branchSchemeToSingularLocus L ≫ g_Sing :=
    (X.isPullback_branchScheme K).lift_fst _ _ _
  have hg_Br_bl : g_Br ≫ X.branchSchemeToBlowup K = X'.branchSchemeToBlowup L ≫ g_Bl :=
    (X.isPullback_branchScheme K).lift_snd _ _ _
  have H_Br0 : IsPullback g_Br (X'.branchSchemeToSingularLocus L)
      (X.branchSchemeToSingularLocus K) g_Sing := by
    have hout := (X'.isPullback_branchScheme L).flip.paste_horiz H_Bl0.flip
    rw [← hg_Br_bl, ← IdealSheafData.subschemeMap_subschemeι _ _ _ hle_I] at hout
    exact IsPullback.of_right hout hg_Br_sing (X.isPullback_branchScheme K).flip
  have H_Br : IsPullback g_Br
      (X'.branchSchemeToSingularLocus L ≫ I'.subschemeι ≫ (X' ↘ Spec (.of L)))
      (X.branchSchemeToSingularLocus K ≫ I.subschemeι ≫ (X ↘ Spec (.of K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    H_Br0.paste_vert H_Sing
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  have hbij_Br : Function.Bijective g_Br :=
    Scheme.Hom.bijective_of_isPullback_algebraMap_of_isSepClosed H_Br
  -- 4. Verify the three compatibility axioms of `DualGraph.Iso`.
  refine
    { vertexEquiv := vertexEquiv
      edgeEquiv := edgeEquiv
      ends_edgeEquiv := fun e' ↦ ?_
      genus_vertexEquiv := fun v' ↦ ?_
      vertexEquiv_marking := fun i ↦ ?_ }
  · -- Compatibility with unordered endpoints `ends`.
    let e'₀ := X'.dualGraphEdgeEquiv hnodal' s' hs' e'
    let eqv' := X'.branchFiberEquiv hnodal' e'₀
    have h01 : (eqv' 0).1 ≠ (eqv' 1).1 :=
      fun h ↦ Fin.zero_ne_one (eqv'.injective (Subtype.ext h))
    have hne_Br : g_Br (eqv' 0).1 ≠ g_Br (eqv' 1).1 :=
      fun h ↦ h01 (hbij_Br.injective h)
    have hb₀ : X.branchSchemeToSingularLocus K (g_Br (eqv' 0).1) =
        X.dualGraphEdgeEquiv hnodal s hs (edgeEquiv e') := by
      rw [← Scheme.Hom.comp_apply, hg_Br_sing, Scheme.Hom.comp_apply, (eqv' 0).2]
      rfl
    have hb₁ : X.branchSchemeToSingularLocus K (g_Br (eqv' 1).1) =
        X.dualGraphEdgeEquiv hnodal s hs (edgeEquiv e') := by
      rw [← Scheme.Hom.comp_apply, hg_Br_sing, Scheme.Hom.comp_apply, (eqv' 1).2]
      rfl
    rw [X.ends_dualGraph_eq_of_ne hnodal s hs (edgeEquiv e') hb₀ hb₁ hne_Br]
    have hcomp (j : Fin 2) :
        (X.dualGraphVertexEquiv hnodal s hs).symm
            (IsRegular.componentOf I.blowup (X.branchSchemeToBlowup K (g_Br (eqv' j).1))) =
          vertexEquiv ((X'.dualGraph hnodal' s' hs').endpoint e' j) := by
      dsimp only [dualGraph, vertexEquiv, e'₀, dualGraphVertexEquiv, dualGraphEdgeEquiv,
        Equiv.trans_apply, Equiv.refl_apply, Equiv.refl_symm]
      rw [← Scheme.Hom.comp_apply, hg_Br_bl, Scheme.Hom.comp_apply,
        IsRegular.componentOf_apply_of_isPullback H_Bl]
      rfl
    rw [hcomp 0, hcomp 1, DualGraph.ends_def, Sym2.map_mk]
  · -- Compatibility with component genera via flat base change of `H¹(C_v, 𝒪)`.
    let v'₀ := X'.dualGraphVertexEquiv hnodal' s' hs' v'
    obtain ⟨g_v, -, H_v⟩ := exists_isPullback_normalizedComponent hnodal hnodal' H v'₀
    have hv_eq : X.dualGraphVertexEquiv hnodal s hs (vertexEquiv v') =
        irreducibleComponentsEquivOfIsPullback H_Bl v'₀ := by
      dsimp only [vertexEquiv, v'₀, Equiv.trans_apply]
      rw [Equiv.apply_symm_apply]
    rw [X.genus_dualGraph hnodal s hs (vertexEquiv v'), X'.genus_dualGraph hnodal' s' hs' v']
    have hgen_eq : ∀ u : irreducibleComponents I.blowup,
        u = irreducibleComponentsEquivOfIsPullback H_Bl v'₀ →
          (X.normalizedComponent hnodal u).genus K =
            (X'.normalizedComponent hnodal' v'₀).genus L := by
      rintro _ rfl
      exact (genus_eq_of_isPullback_of_isProper H_v).symm
    exact hgen_eq (X.dualGraphVertexEquiv hnodal s hs (vertexEquiv v')) hv_eq
  · -- Compatibility with smooth markings.
    rw [eq_comm, X.marking_dualGraph_eq_iff hnodal s hs]
    let y' : I'.blowup := X'.markingLift hnodal' (s' i) (hs' i) default
    have hy' : X'.dualGraphVertexEquiv hnodal' s' hs' ((X'.dualGraph hnodal' s' hs').marking i) =
        IsRegular.componentOf I'.blowup y' := rfl
    have hcomp : X.dualGraphVertexEquiv hnodal s hs
          (vertexEquiv ((X'.dualGraph hnodal' s' hs').marking i)) =
        IsRegular.componentOf I.blowup (g_Bl y') := by
      dsimp only [vertexEquiv, Equiv.trans_apply]
      rw [Equiv.apply_symm_apply, hy']
      exact (IsRegular.componentOf_apply_of_isPullback H_Bl y').symm
    rw [X.coe_dualGraphIrreducibleComponentsEquiv, hcomp]
    refine ⟨g_Bl y', IsRegular.mem_componentOf (g_Bl y'), ?_⟩
    calc
      I.blowupToBase (g_Bl y') = (g_Bl ≫ I.blowupToBase) y' := rfl
      _ = (I'.blowupToBase ≫ g) y' := by rw [hg_Bl_ν]
      _ = g (I'.blowupToBase y') := rfl
      _ = g (s' i default) :=
        congrArg g (congrArg (fun f : Spec (.of L) ⟶ X' ↦ f default)
          (X'.markingLift_blowupToBase hnodal' (s' i) (hs' i)))
      _ = (s' i ≫ g) default := rfl
      _ = (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i) default := by rw [hmark i]
      _ = s i default := by
        rw [Scheme.Hom.comp_apply]
        exact congrArg (s i) (Subsingleton.elim _ default)

/-- On edges, `dualGraphIsoOfIsPullback` sends a singular point `e'` of `X'` to the unique singular
point `e` of `X` beneath `g (e')`. -/
theorem subschemeι_dualGraphIsoOfIsPullback_edgeEquiv
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
    [Algebra K L] {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i)
    (e' : (X'.dualGraph hnodal' s' hs').Edge) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    (X.singularLocus K).subschemeι
        (X.dualGraphEdgeEquiv hnodal s hs
          ((dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark).edgeEquiv e')) =
      g ((X'.singularLocus L).subschemeι (X'.dualGraphEdgeEquiv hnodal' s' hs' e')) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  dsimp only [dualGraphIsoOfIsPullback, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply, ← Scheme.Hom.comp_apply,
    IdealSheafData.subschemeMap_subschemeι, Scheme.Hom.comp_apply]

/-- **Geometric characterization of `dualGraphIsoOfIsPullback` on vertices**: it sends a component
`v'` of `X'` to the unique component `w` of `X` containing the image under `g` of the irreducible
component corresponding to `v'`. -/
theorem vertexEquiv_dualGraphIsoOfIsPullback_eq_iff
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
    [Algebra K L] {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i)
    (v' : (X'.dualGraph hnodal' s' hs').Vertex)
    (w : (X.dualGraph hnodal s hs).Vertex) :
    (dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark).vertexEquiv v' = w ↔
      g '' (X'.dualGraphIrreducibleComponentsEquiv hnodal' s' hs' v' : Set X') ⊆
        (X.dualGraphIrreducibleComponentsEquiv hnodal s hs w : Set X) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  let I := X.singularLocus K
  let I' := X'.singularLocus L
  have : IsRegular I.blowup := X.isRegular_blowup_singularLocus hnodal
  have : IsRegular I'.blowup := X'.isRegular_blowup_singularLocus hnodal'
  have hI : I' = I.comap g := Scheme.singularLocus_eq_comap_of_isPullback H
  let g_Bl : I'.blowup ⟶ I.blowup := blowupSingularLocusMap hnodal hnodal' H
  have hg_Bl_ν : g_Bl ≫ I.blowupToBase = I'.blowupToBase ≫ g :=
    blowupSingularLocusMap_blowupToBase hnodal hnodal' H
  have H_Bl := isPullback_blowupSingularLocusMap_over hnodal hnodal' H
  let iso := dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark
  let v'₀ := X'.dualGraphVertexEquiv hnodal' s' hs' v'
  let u₀ := X.dualGraphVertexEquiv hnodal s hs (iso.vertexEquiv v')
  have hiso_v : X.dualGraphVertexEquiv hnodal s hs (iso.vertexEquiv v') =
      irreducibleComponentsEquivOfIsPullback H_Bl v'₀ := by
    dsimp only [iso, dualGraphIsoOfIsPullback, v'₀, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply]
  have hsub₀ : g '' (X'.dualGraphIrreducibleComponentsEquiv hnodal' s' hs' v' : Set X') ⊆
      (X.dualGraphIrreducibleComponentsEquiv hnodal s hs (iso.vertexEquiv v') : Set X) := by
    rw [X'.coe_dualGraphIrreducibleComponentsEquiv, X.coe_dualGraphIrreducibleComponentsEquiv]
    rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
    refine ⟨g_Bl y', ?_, ?_⟩
    · rw [← IsRegular.componentOf_eq_iff, hiso_v,
        IsRegular.componentOf_apply_of_isPullback H_Bl, IsRegular.componentOf_eq_iff.mpr hy']
    · exact congrArg (fun f : I'.blowup ⟶ X ↦ f y') hg_Bl_ν
  refine ⟨fun h ↦ h ▸ hsub₀, fun hsub ↦ ?_⟩
  obtain ⟨y', hy'_v', hy'_U'⟩ := (X'.dense_preimage_smoothLocus_blowupToBase hnodal')
    |>.inter_open_nonempty (v'₀ : Set I'.blowup)
      (IsRegular.isOpen_of_mem_irreducibleComponents v'₀.2) v'₀.2.1.nonempty
  have hg_smooth : g (I'.blowupToBase y') ∈ (X ↘ Spec (.of K)).smoothLocus := by
    by_contra hns
    have hmem : g (I'.blowupToBase y') ∈ I.support :=
      (X.mem_support_singularLocus_iff_notMem_smoothLocus _).mpr hns
    have hsupp : (I'.support : Set X') = ((I.comap g).support : Set X') :=
      congrArg (fun J : X'.IdealSheafData ↦ (J.support : Set X')) hI
    have hmem' : I'.blowupToBase y' ∈ I'.support := by
      rw [← SetLike.mem_coe, hsupp, IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage]
      exact hmem
    exact (X'.mem_support_singularLocus_iff_notMem_smoothLocus _).mp hmem' hy'_U'
  have hx_mem : g (I'.blowupToBase y') ∈
      g '' (X'.dualGraphIrreducibleComponentsEquiv hnodal' s' hs' v' : Set X') := by
    rw [X'.coe_dualGraphIrreducibleComponentsEquiv]
    exact ⟨I'.blowupToBase y', ⟨y', hy'_v', rfl⟩, rfl⟩
  have h₀ : g (I'.blowupToBase y') ∈ I.blowupToBase '' (u₀ : Set I.blowup) := by
    rw [← X.coe_dualGraphIrreducibleComponentsEquiv]
    exact hsub₀ hx_mem
  have h₁ : g (I'.blowupToBase y') ∈
      I.blowupToBase '' (X.dualGraphVertexEquiv hnodal s hs w : Set I.blowup) := by
    rw [← X.coe_dualGraphIrreducibleComponentsEquiv]
    exact hsub hx_mem
  obtain ⟨y₀, hy₀, hy₀_eq⟩ := h₀
  obtain ⟨y₁, hy₁, hy₁_eq⟩ := h₁
  have hy₀_U : y₀ ∈ I.blowupToBase ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    rw [Set.mem_preimage, hy₀_eq]
    exact hg_smooth
  have hy₁_U : y₁ ∈ I.blowupToBase ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    rw [Set.mem_preimage, hy₁_eq]
    exact hg_smooth
  have hy_eq : y₀ = y₁ :=
    X.injOn_preimage_smoothLocus_blowupToBase hnodal hy₀_U hy₁_U (hy₀_eq.trans hy₁_eq.symm)
  apply (X.dualGraphVertexEquiv hnodal s hs).injective
  exact (IsRegular.componentOf_eq_iff.mpr hy₀).symm.trans
    (IsRegular.componentOf_eq_iff.mpr (hy_eq ▸ hy₁))

private theorem isPullback_of_iso_over {K : Type u} [Field K]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    (e : X' ≅ X) (he : e.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K)) :
    letI : Algebra K K := Algebra.id K
    IsPullback e.hom (X' ↘ Spec (.of K)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
  let _ : Algebra K K := Algebra.id K
  have hSpec_id : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by simp
  rw [hSpec_id]
  exact IsPullback.of_horiz_isIso ⟨by simp [he]⟩

private theorem hmark_of_iso_over {K : Type u} [Field K] {X X' : Scheme.{u}}
    (e : X' ≅ X) {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of K) ⟶ X'))
    (hmark : ∀ i, s' i ≫ e.hom = s i) (i : ι) :
    letI : Algebra K K := Algebra.id K
    s' i ≫ e.hom = Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ s i := by
  let _ : Algebra K K := Algebra.id K
  have hSpec_id : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by simp
  rw [hSpec_id, Category.id_comp, hmark i]

/-- **Isomorphism invariance of the dual graph.** An isomorphism `e : X' ≅ X` of proper connected
nodal curves over a separably closed field `K` compatible with smooth markings induces an
isomorphism of their dual graphs. -/
def dualGraphIsoOfIso {K : Type u} [Field K] [IsSepClosed K]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of K))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)))
    (e : X' ≅ X) (he : e.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of K) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of K)).smoothLocus)
    (hmark : ∀ i, s' i ≫ e.hom = s i) :
    (X'.dualGraph hnodal' s' hs').Iso (X.dualGraph hnodal s hs) :=
  letI : Algebra K K := Algebra.id K
  dualGraphIsoOfIsPullback hnodal hnodal' (isPullback_of_iso_over e he) s s' hs hs'
    (hmark_of_iso_over e s s' hmark)

/-- On edges, `dualGraphIsoOfIso` sends a singular point `e'` of `X'` to the singular point of `X`
mapped onto `e.hom (e')`. -/
theorem subschemeι_dualGraphIsoOfIso_edgeEquiv {K : Type u} [Field K] [IsSepClosed K]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of K))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)))
    (e : X' ≅ X) (he : e.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of K) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of K)).smoothLocus)
    (hmark : ∀ i, s' i ≫ e.hom = s i)
    (e' : (X'.dualGraph hnodal' s' hs').Edge) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    (X.singularLocus K).subschemeι
        (X.dualGraphEdgeEquiv hnodal s hs
          ((dualGraphIsoOfIso hnodal hnodal' e he s s' hs hs' hmark).edgeEquiv e')) =
      e.hom ((X'.singularLocus K).subschemeι (X'.dualGraphEdgeEquiv hnodal' s' hs' e')) :=
  letI : Algebra K K := Algebra.id K
  subschemeι_dualGraphIsoOfIsPullback_edgeEquiv hnodal hnodal' (isPullback_of_iso_over e he)
    s s' hs hs' (hmark_of_iso_over e s s' hmark) e'

/-- On vertices, `dualGraphIsoOfIso` sends a component `v'` of `X'` to the unique component `w` of
`X` containing the image under `e.hom` of the irreducible component corresponding to `v'`. -/
theorem vertexEquiv_dualGraphIsoOfIso_eq_iff {K : Type u} [Field K] [IsSepClosed K]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of K))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)))
    (e : X' ≅ X) (he : e.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of K) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of K)).smoothLocus)
    (hmark : ∀ i, s' i ≫ e.hom = s i)
    (v' : (X'.dualGraph hnodal' s' hs').Vertex)
    (w : (X.dualGraph hnodal s hs).Vertex) :
    (dualGraphIsoOfIso hnodal hnodal' e he s s' hs hs' hmark).vertexEquiv v' = w ↔
      e.hom '' (X'.dualGraphIrreducibleComponentsEquiv hnodal' s' hs' v' : Set X') ⊆
        (X.dualGraphIrreducibleComponentsEquiv hnodal s hs w : Set X) :=
  letI : Algebra K K := Algebra.id K
  vertexEquiv_dualGraphIsoOfIsPullback_eq_iff hnodal hnodal' (isPullback_of_iso_over e he)
    s s' hs hs' (hmark_of_iso_over e s s' hmark) v' w

@[simp]
theorem dualGraphIsoOfIso_refl {K : Type u} [Field K] [IsSepClosed K]
    {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus) :
    dualGraphIsoOfIso hnodal hnodal (Iso.refl X) (Category.id_comp _) s s hs hs
        (fun _ ↦ Category.comp_id _) =
      DualGraph.Iso.refl (X.dualGraph hnodal s hs) := by
  have := hnodal.syntomic
  ext x
  · rw [DualGraph.Iso.refl_vertexEquiv, Equiv.refl_apply, vertexEquiv_dualGraphIsoOfIso_eq_iff]
    simp [Iso.refl_hom]
  · apply (X.dualGraphEdgeEquiv hnodal s hs).injective
    apply (X.singularLocus K).subschemeι.isClosedEmbedding.injective
    rw [DualGraph.Iso.refl_edgeEquiv, Equiv.refl_apply, subschemeι_dualGraphIsoOfIso_edgeEquiv]
    simp [Iso.refl_hom]

theorem dualGraphIsoOfIso_trans {K : Type u} [Field K] [IsSepClosed K]
    {X X' X'' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    [X''.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of K))] [ConnectedSpace X']
    [IsProper (X'' ↘ Spec (.of K))] [ConnectedSpace X'']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)))
    (hnodal'' : AtWorstNodalOfRelativeDimensionOne (X'' ↘ Spec (.of K)))
    (e₁ : X'' ≅ X') (he₁ : e₁.hom ≫ (X' ↘ Spec (.of K)) = X'' ↘ Spec (.of K))
    (e₂ : X' ≅ X) (he₂ : e₂.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of K) ⟶ X'))
    (s'' : ι → (Spec (.of K) ⟶ X''))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of K)).smoothLocus)
    (hs'' : ∀ i, Set.range (s'' i) ⊆ (X'' ↘ Spec (.of K)).smoothLocus)
    (hmark₁ : ∀ i, s'' i ≫ e₁.hom = s' i) (hmark₂ : ∀ i, s' i ≫ e₂.hom = s i) :
    dualGraphIsoOfIso hnodal hnodal'' (e₁ ≪≫ e₂)
        (by rw [Iso.trans_hom, Category.assoc, he₂, he₁]) s s'' hs hs''
        (fun i ↦ by rw [Iso.trans_hom, ← Category.assoc, hmark₁ i, hmark₂ i]) =
      (dualGraphIsoOfIso hnodal' hnodal'' e₁ he₁ s' s'' hs' hs'' hmark₁).trans
        (dualGraphIsoOfIso hnodal hnodal' e₂ he₂ s s' hs hs' hmark₂) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := hnodal''.syntomic
  let iso₁ := dualGraphIsoOfIso hnodal' hnodal'' e₁ he₁ s' s'' hs' hs'' hmark₁
  let iso₂ := dualGraphIsoOfIso hnodal hnodal' e₂ he₂ s s' hs hs' hmark₂
  ext x
  · rw [DualGraph.Iso.trans_vertexEquiv, Equiv.trans_apply, vertexEquiv_dualGraphIsoOfIso_eq_iff]
    have h₁ := (vertexEquiv_dualGraphIsoOfIso_eq_iff hnodal' hnodal'' e₁ he₁ s' s'' hs' hs''
      hmark₁ x (iso₁.vertexEquiv x)).mp rfl
    have h₂ := (vertexEquiv_dualGraphIsoOfIso_eq_iff hnodal hnodal' e₂ he₂ s s' hs hs'
      hmark₂ (iso₁.vertexEquiv x) (iso₂.vertexEquiv (iso₁.vertexEquiv x))).mp rfl
    calc
      (e₁ ≪≫ e₂).hom '' (X''.dualGraphIrreducibleComponentsEquiv hnodal'' s'' hs'' x : Set X'')
        = e₂.hom '' (e₁.hom ''
            (X''.dualGraphIrreducibleComponentsEquiv hnodal'' s'' hs'' x : Set X'')) := by
          ext z
          simp [Set.mem_image]
      _ ⊆ e₂.hom ''
            (X'.dualGraphIrreducibleComponentsEquiv hnodal' s' hs' (iso₁.vertexEquiv x) : Set X') :=
          Set.image_mono h₁
      _ ⊆ (X.dualGraphIrreducibleComponentsEquiv hnodal s hs
            (iso₂.vertexEquiv (iso₁.vertexEquiv x)) : Set X) := h₂
  · apply (X.dualGraphEdgeEquiv hnodal s hs).injective
    apply (X.singularLocus K).subschemeι.isClosedEmbedding.injective
    rw [DualGraph.Iso.trans_edgeEquiv, Equiv.trans_apply,
      subschemeι_dualGraphIsoOfIso_edgeEquiv, subschemeι_dualGraphIsoOfIso_edgeEquiv,
      subschemeι_dualGraphIsoOfIso_edgeEquiv, Iso.trans_hom, Scheme.Hom.comp_apply]

theorem dualGraphIsoOfIso_symm {K : Type u} [Field K] [IsSepClosed K]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of K))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)))
    (e : X' ≅ X) (he : e.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of K) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of K)).smoothLocus)
    (hmark : ∀ i, s' i ≫ e.hom = s i) :
    dualGraphIsoOfIso hnodal' hnodal e.symm
        (by rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]) s' s hs' hs
        (fun i ↦ by rw [← hmark i, Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id]) =
      (dualGraphIsoOfIso hnodal hnodal' e he s s' hs hs' hmark).symm := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have he_symm : e.symm.hom ≫ (X' ↘ Spec (.of K)) = X ↘ Spec (.of K) := by
    rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]
  have hmark_symm (i : ι) : s i ≫ e.symm.hom = s' i := by
    rw [← hmark i, Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id]
  let iso := dualGraphIsoOfIso hnodal hnodal' e he s s' hs hs' hmark
  let iso_symm := dualGraphIsoOfIso hnodal' hnodal e.symm he_symm s' s hs' hs hmark_symm
  ext x
  · rw [DualGraph.Iso.symm_vertexEquiv]
    apply iso.vertexEquiv.injective
    rw [iso.vertexEquiv.apply_symm_apply]
    have h₁ := (vertexEquiv_dualGraphIsoOfIso_eq_iff hnodal' hnodal e.symm he_symm s' s hs' hs
      hmark_symm x (iso_symm.vertexEquiv x)).mp rfl
    have h₂ := (vertexEquiv_dualGraphIsoOfIso_eq_iff hnodal hnodal' e he s s' hs hs' hmark
      (iso_symm.vertexEquiv x) (iso.vertexEquiv (iso_symm.vertexEquiv x))).mp rfl
    let Z_x := X.dualGraphIrreducibleComponentsEquiv hnodal s hs x
    let Z_w := X.dualGraphIrreducibleComponentsEquiv hnodal s hs
      (iso.vertexEquiv (iso_symm.vertexEquiv x))
    have hsub : (Z_x : Set X) ⊆ (Z_w : Set X) := by
      intro z hz
      have hzw : e.hom (e.symm.hom z) ∈ (Z_w : Set X) := h₂ ⟨e.symm.hom z, h₁ ⟨z, hz, rfl⟩, rfl⟩
      have hid : e.hom (e.symm.hom z) = z := congrArg (fun f : X ⟶ X ↦ f z) e.inv_hom_id
      rwa [hid] at hzw
    exact (X.dualGraphIrreducibleComponentsEquiv hnodal s hs).injective <|
      Subtype.ext (hsub.antisymm (Z_x.2.2 Z_w.2.1 hsub)).symm
  · rw [DualGraph.Iso.symm_edgeEquiv]
    apply iso.edgeEquiv.injective
    apply (X.dualGraphEdgeEquiv hnodal s hs).injective
    apply (X.singularLocus K).subschemeι.isClosedEmbedding.injective
    rw [iso.edgeEquiv.apply_symm_apply, subschemeι_dualGraphIsoOfIso_edgeEquiv,
      subschemeι_dualGraphIsoOfIso_edgeEquiv]
    exact congrArg (fun f : X ⟶ X ↦
      f ((X.singularLocus K).subschemeι (X.dualGraphEdgeEquiv hnodal s hs x))) e.inv_hom_id

/-- Base change between separably closed fields preserves the first Betti number of the dual
graph. -/
theorem firstBetti_dualGraph_eq_of_isPullback
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i) :
    (X'.dualGraph hnodal' s' hs').firstBetti = (X.dualGraph hnodal s hs).firstBetti :=
  (dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark).firstBetti_eq

/-- Base change between separably closed fields preserves the combinatorial arithmetic genus of the
dual graph. -/
theorem arithmeticGenus_dualGraph_eq_of_isPullback
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i) :
    (X'.dualGraph hnodal' s' hs').arithmeticGenus =
      (X.dualGraph hnodal s hs).arithmeticGenus :=
  (dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark).arithmeticGenus_eq

/-- Base change between separably closed fields preserves stability of the dual graph. -/
theorem isStable_dualGraph_iff_of_isPullback
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} [Fintype ι] (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i) :
    (X'.dualGraph hnodal' s' hs').IsStable ↔ (X.dualGraph hnodal s hs).IsStable :=
  (dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark).isStable_iff

/-- Base change between separably closed fields preserves semistability of the dual graph. -/
theorem isSemistable_dualGraph_iff_of_isPullback
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} [Fintype ι] (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i) :
    (X'.dualGraph hnodal' s' hs').IsSemistable ↔ (X.dualGraph hnodal s hs).IsSemistable :=
  (dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark).isSemistable_iff

end BaseChange

end AlgebraicGeometry.Scheme
