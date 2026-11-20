/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.Genus.BaseChange
public import TauCeti.AlgebraicGeometry.Curves.Node.NormalizedComponent
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import Mathlib.Tactic.FinCases
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
  be connected.

All combinatorial invariants of `X.dualGraph` are then read directly off the geometry of `X`: the
valence of `v` counts the branches (equivalently, the preimages of nodes) lying on `v`
(`AlgebraicGeometry.Scheme.valence_dualGraph`), and `v` carries no self-node loop if and only if
the normalization map `ν` is injective on `v`
(`AlgebraicGeometry.Scheme.forall_endpoint_dualGraph_one_ne_iff_injOn`). When `X` is smooth, the
dual graph has first Betti number zero (`AlgebraicGeometry.Scheme.firstBetti_dualGraph_of_smooth`)
and arithmetic genus equal to `X.genus K`
(`AlgebraicGeometry.Scheme.arithmeticGenus_dualGraph_eq_genus_of_smooth`).

Finally, because `Sing(X/K)`, `E`, the irreducible components of `Bl X`, and the genera of proper
curves are all preserved under base change from a separably closed field `K` to any separably closed
extension `L / K` (even an inseparable one), base change induces a canonical isomorphism of dual
graphs (`TauCeti.AlgebraicGeometry.dualGraphIsoOfIsPullback`, functorial along field towers via
`TauCeti.AlgebraicGeometry.dualGraphIsoOfIsPullback_trans`). Specializing to `L = K` yields
isomorphism invariance and functoriality for pointed nodal curves over `K`
(`TauCeti.AlgebraicGeometry.dualGraphIsoOfIso`).

## References

* [The Stacks Project, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodal curves and
  separation of branches.
* [The Stacks Project, Tag 0E6X](https://stacks.math.columbia.edu/tag/0E6X) and
  [Tag 0E73](https://stacks.math.columbia.edu/tag/0E73): semistable and stable curves via rational
  tails and bridges.
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

/-- Choice of ordering of the two branches of `X` over a node `e`, used to populate the ordered
`endpoint : Edge → Fin 2 → Vertex` field of `DualGraph`. All downstream statements pass immediately
through `sym2_dualGraphEndpoint_eq_of_ne`, which is independent of this ordering. -/
private def branchFiberEquiv
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme) :
    letI := hnodal.syntomic
    Fin 2 ≃ {b : X.branchScheme K // X.branchSchemeToSingularLocus K b = e} := by
  letI := hnodal.syntomic
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have : Finite {b : X.branchScheme K // X.branchSchemeToSingularLocus K b = e} :=
    ((X.branchSchemeToSingularLocus K).finite_preimage_singleton e).to_subtype
  let _ : Fintype {b : X.branchScheme K // X.branchSchemeToSingularLocus K b = e} :=
    Fintype.ofFinite _
  exact (Fintype.equivFinOfCardEq
    (Nat.card_eq_fintype_card.symm.trans (X.natCard_branchFiber_eq_two hnodal e))).symm

/-- Endpoint map of the dual graph of `X`, sending `(e, i)` to the irreducible component of `Bl X`
containing the `i`-th branch over `e`. -/
private def dualGraphEndpoint
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme) (i : Fin 2) :
    letI := hnodal.syntomic
    irreducibleComponents (X.singularLocus K).blowup :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  componentOf (X.singularLocus K).blowup
    (X.branchSchemeToBlowup K (X.branchFiberEquiv hnodal e i).1)

/-- Whenever `b₀ ≠ b₁` are two branches over the same node `e`, the unordered pair of endpoints of
`e` is the pair of components of `Bl X` containing `b₀` and `b₁`. -/
private theorem sym2_dualGraphEndpoint_eq_of_ne
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme)
    {b₀ b₁ : letI := hnodal.syntomic; X.branchScheme K}
    (hb₀ : letI := hnodal.syntomic; X.branchSchemeToSingularLocus K b₀ = e)
    (hb₁ : letI := hnodal.syntomic; X.branchSchemeToSingularLocus K b₁ = e)
    (hne : b₀ ≠ b₁) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    s(X.dualGraphEndpoint hnodal e 0, X.dualGraphEndpoint hnodal e 1) =
      s(componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₀),
        componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₁)) := by
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

/-- Two distinct points of `Bl X` mapping to the same point of `X` come from the two branches over
some node `e` of `Sing(X/K)`, whose unordered endpoints are the components containing those two
points. -/
private theorem exists_dualGraphEndpoint_eq_of_blowupToBase_eq
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {y₁ y₂ : letI := hnodal.syntomic; (X.singularLocus K).blowup}
    (hne : y₁ ≠ y₂)
    (heq : letI := hnodal.syntomic
      (X.singularLocus K).blowupToBase y₁ = (X.singularLocus K).blowupToBase y₂) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    ∃ e : (X.singularLocus K).subscheme,
      s(X.dualGraphEndpoint hnodal e 0, X.dualGraphEndpoint hnodal e 1) =
        s(componentOf (X.singularLocus K).blowup y₁,
          componentOf (X.singularLocus K).blowup y₂) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  let ν := (X.singularLocus K).blowupToBase
  have hx_sing : ν y₁ ∈ (X.singularLocus K).support := by
    rw [X.mem_support_singularLocus_iff_notMem_smoothLocus]
    intro hxU
    have hy₂U : y₂ ∈ ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
      rw [Set.mem_preimage, ← heq]
      exact hxU
    exact hne (X.injOn_preimage_smoothLocus_blowupToBase hxU hy₂U heq)
  obtain ⟨e, he⟩ := (IdealSheafData.range_subschemeι (X.singularLocus K)).ge hx_sing
  have hfib := image_preimage_eq_of_isPullback (X.isPullback_branchScheme K) {e}
  rw [Set.image_singleton, he] at hfib
  obtain ⟨b₁, hb₁, hb₁_eq⟩ : y₁ ∈ X.branchSchemeToBlowup K ''
      (X.branchSchemeToSingularLocus K ⁻¹' {e}) := by
    rw [hfib]
    exact rfl
  obtain ⟨b₂, hb₂, hb₂_eq⟩ : y₂ ∈ X.branchSchemeToBlowup K ''
      (X.branchSchemeToSingularLocus K ⁻¹' {e}) := by
    rw [hfib]
    exact heq.symm
  have hb_ne : b₁ ≠ b₂ := fun h ↦ hne (hb₁_eq ▸ hb₂_eq ▸ congrArg _ h)
  refine ⟨e, ?_⟩
  have hends := X.sym2_dualGraphEndpoint_eq_of_ne hnodal e hb₁ hb₂ hb_ne
  rwa [hb₁_eq, hb₂_eq] at hends

/-- Topological connectedness of a quasi-compact nodal curve `X` over a separably closed field
forces its component-node incidence graph to be connected. -/
private theorem connected_dualGraphEndpoint [QuasiCompact (X ↘ Spec (.of K))] [ConnectedSpace X]
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
  -- Partition `X` into the union `A` of components reachable from `v₀` and the union `B` of the
  -- remaining components; connectedness of `X` produces an intersection point over a node.
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
    let v := componentOf Bl y
    by_cases hv : v ∈ S
    · exact Or.inl (Set.mem_biUnion hv ⟨y, mem_componentOf y, rfl⟩)
    · exact Or.inr (Set.mem_biUnion hv ⟨y, mem_componentOf y, rfl⟩)
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
    (componentOf_eq_iff.mpr hy₁).symm.trans (componentOf_eq_iff.mpr (h ▸ hy₂))
  obtain ⟨e, hends⟩ :=
    X.exists_dualGraphEndpoint_eq_of_blowupToBase_eq hnodal hy_ne hy₂_eq.symm
  rw [componentOf_eq_iff.mpr hy₁, componentOf_eq_iff.mpr hy₂] at hends
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
    marking := fun i ↦ componentOf (X.singularLocus K).blowup
      (X.blowupSingularLocusLift (s i) (hs i) default)
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

/-- The identification `dualGraphVertexEquiv` does not depend on the markings: vertices equal up to
`HEq` across two marking families represent the same irreducible component of `Bl X`. -/
theorem dualGraphVertexEquiv_eq_of_heq {ι' : Type*} {s' : ι' → (Spec (.of K) ⟶ X)}
    {hs' : ∀ i, Set.range (s' i) ⊆ (X ↘ Spec (.of K)).smoothLocus}
    {v : (X.dualGraph hnodal s hs).Vertex}
    {w : (X.dualGraph hnodal s' hs').Vertex}
    (h : HEq v w) :
    letI := hnodal.syntomic
    X.dualGraphVertexEquiv hnodal s hs v = X.dualGraphVertexEquiv hnodal s' hs' w := by
  cases h
  rfl

/-- The identification `dualGraphEdgeEquiv` does not depend on the markings: edges equal up to
`HEq` across two marking families represent the same singular point of `X`. -/
theorem dualGraphEdgeEquiv_eq_of_heq {ι' : Type*} {s' : ι' → (Spec (.of K) ⟶ X)}
    {hs' : ∀ i, Set.range (s' i) ⊆ (X ↘ Spec (.of K)).smoothLocus}
    {e₁ : (X.dualGraph hnodal s hs).Edge}
    {e₂ : (X.dualGraph hnodal s' hs').Edge}
    (h : HEq e₁ e₂) :
    letI := hnodal.syntomic
    X.dualGraphEdgeEquiv hnodal s hs e₁ = X.dualGraphEdgeEquiv hnodal s' hs' e₂ := by
  cases h
  rfl

@[simp]
theorem dualGraphVertexEquiv_marking (i : ι) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    X.dualGraphVertexEquiv hnodal s hs ((X.dualGraph hnodal s hs).marking i) =
      componentOf (X.singularLocus K).blowup
        (X.blowupSingularLocusLift (s i) (hs i) default) :=
  (rfl)

private theorem dualGraphVertexEquiv_endpoint (e : (X.dualGraph hnodal s hs).Edge) (i : Fin 2) :
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
    X.dualGraphVertexEquiv_marking hnodal s hs i, componentOf_eq_iff,
    X.coe_dualGraphIrreducibleComponentsEquiv]
  have hlift : ν (X.blowupSingularLocusLift (s i) (hs i) default) = s i default := by
    rw [← Scheme.Hom.comp_apply, X.blowupSingularLocusLift_blowupToBase]
  refine ⟨fun h ↦ ⟨_, h, hlift⟩, ?_⟩
  rintro ⟨y, hyv, hy_eq⟩
  have hsU : s i default ∈ (X ↘ Spec (.of K)).smoothLocus := hs i ⟨default, rfl⟩
  have h₁ : X.blowupSingularLocusLift (s i) (hs i) default ∈
      ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    rw [Set.mem_preimage, hlift]
    exact hsU
  have h₂ : y ∈ ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    rw [Set.mem_preimage, hy_eq]
    exact hsU
  rwa [X.injOn_preimage_smoothLocus_blowupToBase h₁ h₂ (hlift.trans hy_eq.symm)]

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
          (componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₀)),
        (X.dualGraphVertexEquiv hnodal s hs).symm
          (componentOf (X.singularLocus K).blowup (X.branchSchemeToBlowup K b₁))) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  apply Sym2.map.injective (X.dualGraphVertexEquiv hnodal s hs).injective
  rw [DualGraph.ends_def, Sym2.map_mk, Sym2.map_mk,
    X.dualGraphVertexEquiv_endpoint, X.dualGraphVertexEquiv_endpoint,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
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
    X.dualGraphVertexEquiv_endpoint, dualGraphEndpoint, componentOf_eq_iff]
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
      rw [← (X.dualGraphVertexEquiv hnodal s hs).injective.eq_iff,
        X.dualGraphVertexEquiv_endpoint]
      simp [pairEquivBr, dualGraphEndpoint, componentOf_eq_iff]
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
  exact Nat.card_congr <|
    ((Equiv.ofInjective (X.branchSchemeToBlowup K) hinj).subtypeEquiv (fun _ ↦ Iff.rfl)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
        (Equiv.subtypeEquivRight fun _ ↦ by
          rw [hrange, Set.mem_preimage, SetLike.mem_coe, and_comm]))

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
    obtain ⟨e₀, hends₀⟩ := X.exists_dualGraphEndpoint_eq_of_blowupToBase_eq hnodal hne heq
    rw [componentOf_eq_iff.mpr hy₁, componentOf_eq_iff.mpr hy₂] at hends₀
    let e : (X.dualGraph hnodal s hs).Edge := (X.dualGraphEdgeEquiv hnodal s hs).symm e₀
    refine hnoloop e ?_
    apply Sym2.map.injective (X.dualGraphVertexEquiv hnodal s hs).injective
    rw [DualGraph.ends_def, Sym2.map_mk, Sym2.map_mk,
      X.dualGraphVertexEquiv_endpoint, X.dualGraphVertexEquiv_endpoint,
      Equiv.apply_symm_apply]
    exact hends₀
  · -- Converse: a self-loop at `e` gives two distinct branches on `v` over the same node.
    intro hinj e hends
    have hends₀ := congrArg (Sym2.map (X.dualGraphVertexEquiv hnodal s hs)) hends
    rw [DualGraph.ends_def, Sym2.map_mk, Sym2.map_mk,
      X.dualGraphVertexEquiv_endpoint, X.dualGraphVertexEquiv_endpoint] at hends₀
    let e₀ := X.dualGraphEdgeEquiv hnodal s hs e
    let eqv := X.branchFiberEquiv hnodal e₀
    have h01 : (eqv 0).1 ≠ (eqv 1).1 :=
      fun h ↦ Fin.zero_ne_one (eqv.injective (Subtype.ext h))
    have h0 : X.dualGraphEndpoint hnodal e₀ 0 = v₀ :=
      (Sym2.eq_iff.mp hends₀).elim And.left And.left
    have h1 : X.dualGraphEndpoint hnodal e₀ 1 = v₀ :=
      (Sym2.eq_iff.mp hends₀).elim And.right And.right
    have hy₀ : X.branchSchemeToBlowup K (eqv 0).1 ∈ (v₀ : Set _) :=
      componentOf_eq_iff.mp h0
    have hy₁ : X.branchSchemeToBlowup K (eqv 1).1 ∈ (v₀ : Set _) :=
      componentOf_eq_iff.mp h1
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

/-- **Validation on smooth curves (first Betti number).** When `X` is smooth, its dual graph has
first Betti number zero. -/
theorem firstBetti_dualGraph_of_smooth [Smooth (X ↘ Spec (.of K))] :
    (X.dualGraph hnodal s hs).firstBetti = 0 := by
  have := hnodal.syntomic
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of K))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have hsing_top : X.singularLocus K = ⊤ :=
    (X.singularLocus_eq_top_iff_smooth (R := K)).mpr ‹_›
  have hempty_edge : IsEmpty (X.dualGraph hnodal s hs).Edge := by
    refine ⟨fun e ↦ ?_⟩
    let e₀ := X.dualGraphEdgeEquiv hnodal s hs e
    have hmem : (X.singularLocus K).subschemeι e₀ ∈ ((X.singularLocus K).support : Set X) := by
      rw [← IdealSheafData.range_subschemeι]
      exact ⟨e₀, rfl⟩
    rw [(IdealSheafData.support_eq_bot_iff _).mpr hsing_top] at hmem
    exact hmem
  have hcard_edge : Fintype.card (X.dualGraph hnodal s hs).Edge = 0 := Fintype.card_eq_zero
  have hcard_vert : Fintype.card (X.dualGraph hnodal s hs).Vertex = 1 := by
    rw [X.card_vertex_dualGraph hnodal s hs, irreducibleComponents_eq_singleton, Nat.card_unique]
  rw [DualGraph.firstBetti_def, hcard_edge, hcard_vert]

/-- **Validation on smooth curves (arithmetic genus).** When `X` is smooth, the combinatorial
arithmetic genus of its dual graph equals the cohomological genus `X.genus K`. -/
theorem arithmeticGenus_dualGraph_eq_genus_of_smooth [Smooth (X ↘ Spec (.of K))] :
    letI : SmoothOfRelativeDimension 1 (X ↘ Spec (.of K)) :=
      (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension _).mpr
        ⟨‹_›, letI := hnodal.syntomic; inferInstance⟩
    letI := finiteDimensional_cohomology_one_trivial_of_smooth K X
    (X.dualGraph hnodal s hs).arithmeticGenus = X.genus K := by
  have := hnodal.syntomic
  let G := X.dualGraph hnodal s hs
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of K))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension _).mpr ⟨‹_›, inferInstance⟩
  have := finiteDimensional_cohomology_one_trivial_of_smooth K X
  have hcard_vert : Fintype.card G.Vertex = 1 := by
    rw [X.card_vertex_dualGraph hnodal s hs, irreducibleComponents_eq_singleton, Nat.card_unique]
  obtain ⟨v₀⟩ := G.vertexNonempty
  have huniq : ∀ w : G.Vertex, w = v₀ := fun w ↦ Fintype.card_le_one_iff.mp hcard_vert.le w v₀
  let v₀' : irreducibleComponents Bl := X.dualGraphVertexEquiv hnodal s hs v₀
  have hv₀_univ : (v₀' : Set Bl) = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ by
      have hy := congrArg (X.dualGraphVertexEquiv hnodal s hs)
        (huniq ((X.dualGraphVertexEquiv hnodal s hs).symm (componentOf Bl y)))
      rw [Equiv.apply_symm_apply] at hy
      exact componentOf_eq_iff.mp hy
  have : IsIso ν := X.isIso_blowupToBase_singularLocus_of_smooth
  have : IsIso (X.normalizedComponentι hnodal v₀') :=
    X.isIso_normalizedComponentι_of_eq_univ hnodal v₀' hv₀_univ
  let g₀ : X.dualGraphComponent hnodal v₀ ⟶ X := X.normalizedComponentι hnodal v₀' ≫ ν
  have hgen : (X.dualGraphComponent hnodal v₀).genus K = X.genus K := by
    let _ : Algebra K K := Algebra.id K
    have hpb : IsPullback g₀ (X.dualGraphComponent hnodal v₀ ↘ Spec (.of K))
        (X ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
      rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) by simp]
      exact IsPullback.of_horiz_isIso ⟨by simp [g₀, v₀', ν]⟩
    exact genus_eq_of_isPullback_of_isProper hpb
  rw [DualGraph.arithmeticGenus_def, X.firstBetti_dualGraph_of_smooth hnodal s hs, add_zero,
    Fintype.sum_eq_single v₀ (fun w hw ↦ absurd (huniq w) hw),
    X.genus_dualGraph hnodal s hs v₀, hgen]

end Invariants

end SepClosed

end AlgebraicGeometry.Scheme

/-! ### Invariance under extensions of separably closed fields and curve isomorphisms -/

namespace TauCeti.AlgebraicGeometry

section BaseChange

private def dualGraphIsoOfIsPullbackVertexEquiv
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
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus) :
    (X'.dualGraph hnodal' s' hs').Vertex ≃ (X.dualGraph hnodal s hs).Vertex :=
  letI := hnodal.syntomic
  letI := hnodal'.syntomic
  (X'.dualGraphVertexEquiv hnodal' s' hs').trans <|
    (irreducibleComponentsEquivOfIsPullback (isPullback_blowupSingularLocusMap_over H)).trans
      (X.dualGraphVertexEquiv hnodal s hs).symm

private theorem bijective_singularLocus_subschemeMap
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    Function.Bijective
      ((X'.singularLocus L).subschemeMap (X.singularLocus K) g
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.singularLocus_eq_comap_of_isPullback H).ge)) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := X.etale_singularLocus_subschemeι_comp hnodal
  exact bijective_of_isPullback_algebraMap_of_isSepClosed
    ((Scheme.isPullback_singularLocus_subschemeι H).flip.paste_vert H)

private def dualGraphIsoOfIsPullbackEdgeEquiv
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
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus) :
    (X'.dualGraph hnodal' s' hs').Edge ≃ (X.dualGraph hnodal s hs).Edge :=
  letI := hnodal.syntomic
  letI := hnodal'.syntomic
  (X'.dualGraphEdgeEquiv hnodal' s' hs').trans <|
    (Equiv.ofBijective _ (bijective_singularLocus_subschemeMap hnodal hnodal' H)).trans
      (X.dualGraphEdgeEquiv hnodal s hs).symm

private theorem bijective_branchSchemeMap
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    Function.Bijective (branchSchemeMap H) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := X.etale_singularLocus_subschemeι_comp hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  exact bijective_of_isPullback_algebraMap_of_isSepClosed
    ((isPullback_branchSchemeMap H).paste_vert
      ((Scheme.isPullback_singularLocus_subschemeι H).flip.paste_vert H))

private theorem dualGraphIsoOfIsPullback_ends_edgeEquiv
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
    (e' : (X'.dualGraph hnodal' s' hs').Edge) :
    (X.dualGraph hnodal s hs).ends
        (dualGraphIsoOfIsPullbackEdgeEquiv hnodal hnodal' H s s' hs hs' e') =
      Sym2.map (dualGraphIsoOfIsPullbackVertexEquiv hnodal hnodal' H s s' hs hs')
        ((X'.dualGraph hnodal' s' hs').ends e') := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  have := X'.isRegular_blowup_singularLocus hnodal'
  let e'₀ := X'.dualGraphEdgeEquiv hnodal' s' hs' e'
  let eqv' := X'.branchFiberEquiv hnodal' e'₀
  have h01 : (eqv' 0).1 ≠ (eqv' 1).1 :=
    fun h ↦ Fin.zero_ne_one (eqv'.injective (Subtype.ext h))
  have hne_Br : branchSchemeMap H (eqv' 0).1 ≠ branchSchemeMap H (eqv' 1).1 :=
    fun h ↦ h01 ((bijective_branchSchemeMap hnodal hnodal' H).injective h)
  have hb (j : Fin 2) :
      X.branchSchemeToSingularLocus K (branchSchemeMap H (eqv' j).1) =
        X.dualGraphEdgeEquiv hnodal s hs
          (dualGraphIsoOfIsPullbackEdgeEquiv hnodal hnodal' H s s' hs hs' e') := by
    rw [← Scheme.Hom.comp_apply, branchSchemeMap_branchSchemeToSingularLocus H,
      Scheme.Hom.comp_apply, (eqv' j).2]
    dsimp only [dualGraphIsoOfIsPullbackEdgeEquiv, e'₀, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply]
  rw [X.ends_dualGraph_eq_of_ne hnodal s hs _ (hb 0) (hb 1) hne_Br]
  have hcomp (j : Fin 2) :
      (X.dualGraphVertexEquiv hnodal s hs).symm
          (componentOf (X.singularLocus K).blowup
            (X.branchSchemeToBlowup K (branchSchemeMap H (eqv' j).1))) =
        dualGraphIsoOfIsPullbackVertexEquiv hnodal hnodal' H s s' hs hs'
          ((X'.dualGraph hnodal' s' hs').endpoint e' j) := by
    dsimp only [dualGraphIsoOfIsPullbackVertexEquiv, Equiv.trans_apply]
    rw [X'.dualGraphVertexEquiv_endpoint, Scheme.dualGraphEndpoint,
      ← Scheme.Hom.comp_apply, branchSchemeMap_branchSchemeToBlowup H, Scheme.Hom.comp_apply,
      componentOf_apply_of_isPullback (isPullback_blowupSingularLocusMap_over H)]
  rw [hcomp 0, hcomp 1, DualGraph.ends_def, Sym2.map_mk]

private theorem dualGraphIsoOfIsPullback_genus_vertexEquiv
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
    (v' : (X'.dualGraph hnodal' s' hs').Vertex) :
    (X.dualGraph hnodal s hs).genus
        (dualGraphIsoOfIsPullbackVertexEquiv hnodal hnodal' H s s' hs hs' v') =
      (X'.dualGraph hnodal' s' hs').genus v' := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  let v'₀ := X'.dualGraphVertexEquiv hnodal' s' hs' v'
  obtain ⟨_, -, H_v⟩ := exists_isPullback_normalizedComponent hnodal hnodal' H v'₀
  have hv_eq :
      X.dualGraphVertexEquiv hnodal s hs
          (dualGraphIsoOfIsPullbackVertexEquiv hnodal hnodal' H s s' hs hs' v') =
        irreducibleComponentsEquivOfIsPullback (isPullback_blowupSingularLocusMap_over H) v'₀ := by
    dsimp only [dualGraphIsoOfIsPullbackVertexEquiv, v'₀, Equiv.trans_apply]
    exact Equiv.apply_symm_apply _ _
  rw [X.genus_dualGraph, X'.genus_dualGraph]
  have hgen_eq : ∀ u : irreducibleComponents (X.singularLocus K).blowup,
      u = irreducibleComponentsEquivOfIsPullback (isPullback_blowupSingularLocusMap_over H) v'₀ →
        (X.normalizedComponent hnodal u).genus K =
          (X'.normalizedComponent hnodal' v'₀).genus L := by
    rintro _ rfl
    exact (genus_eq_of_isPullback_of_isProper H_v).symm
  exact hgen_eq _ hv_eq

private theorem dualGraphIsoOfIsPullback_vertexEquiv_marking
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
    (hmark : ∀ i, s' i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i)
    (i : ι) :
    dualGraphIsoOfIsPullbackVertexEquiv hnodal hnodal' H s s' hs hs'
        ((X'.dualGraph hnodal' s' hs').marking i) =
      (X.dualGraph hnodal s hs).marking i := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  have := X'.isRegular_blowup_singularLocus hnodal'
  rw [eq_comm, X.marking_dualGraph_eq_iff hnodal s hs, X.coe_dualGraphIrreducibleComponentsEquiv]
  let y' : (X'.singularLocus L).blowup := X'.blowupSingularLocusLift (s' i) (hs' i) default
  have hcomp :
      X.dualGraphVertexEquiv hnodal s hs
          (dualGraphIsoOfIsPullbackVertexEquiv hnodal hnodal' H s s' hs hs'
            ((X'.dualGraph hnodal' s' hs').marking i)) =
        componentOf (X.singularLocus K).blowup (blowupSingularLocusMap H y') := by
    dsimp only [dualGraphIsoOfIsPullbackVertexEquiv, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply, X'.dualGraphVertexEquiv_marking]
    exact (componentOf_apply_of_isPullback (isPullback_blowupSingularLocusMap_over H) y').symm
  rw [hcomp]
  refine ⟨blowupSingularLocusMap H y', mem_componentOf (blowupSingularLocusMap H y'), ?_⟩
  rw [← Scheme.Hom.comp_apply, blowupSingularLocusMap_blowupToBase H, Scheme.Hom.comp_apply]
  have hy' : (X'.singularLocus L).blowupToBase y' = s' i default := by
    rw [← Scheme.Hom.comp_apply, X'.blowupSingularLocusLift_blowupToBase]
  rw [hy', ← Scheme.Hom.comp_apply, hmark i, Scheme.Hom.comp_apply]
  exact congrArg (s i) (Subsingleton.elim _ default)

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
    (X'.dualGraph hnodal' s' hs').Iso (X.dualGraph hnodal s hs) where
  vertexEquiv := dualGraphIsoOfIsPullbackVertexEquiv hnodal hnodal' H s s' hs hs'
  edgeEquiv := dualGraphIsoOfIsPullbackEdgeEquiv hnodal hnodal' H s s' hs hs'
  ends_edgeEquiv := dualGraphIsoOfIsPullback_ends_edgeEquiv hnodal hnodal' H s s' hs hs'
  genus_vertexEquiv := dualGraphIsoOfIsPullback_genus_vertexEquiv hnodal hnodal' H s s' hs hs'
  vertexEquiv_marking :=
    dualGraphIsoOfIsPullback_vertexEquiv_marking hnodal hnodal' H s s' hs hs' hmark

/-- `dualGraphIsoOfIsPullback` acts on vertices via `irreducibleComponentsEquivOfIsPullback` on the
irreducible components of `Bl X'` and `Bl X`. -/
@[simp]
theorem dualGraphVertexEquiv_dualGraphIsoOfIsPullback_vertexEquiv
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
    (v' : (X'.dualGraph hnodal' s' hs').Vertex) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    X.dualGraphVertexEquiv hnodal s hs
        ((dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark).vertexEquiv v') =
      irreducibleComponentsEquivOfIsPullback (isPullback_blowupSingularLocusMap_over H)
        (X'.dualGraphVertexEquiv hnodal' s' hs' v') := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  dsimp only [dualGraphIsoOfIsPullback, dualGraphIsoOfIsPullbackVertexEquiv, Equiv.trans_apply]
  exact Equiv.apply_symm_apply _ _

/-- On edges, `dualGraphIsoOfIsPullback` sends a singular point `e'` of `X'` to the unique singular
point `e` of `X` lying beneath `e'` under `g`. -/
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
  dsimp only [dualGraphIsoOfIsPullback, dualGraphIsoOfIsPullbackEdgeEquiv, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply, ← Scheme.Hom.comp_apply,
    Scheme.IdealSheafData.subschemeMap_subschemeι, Scheme.Hom.comp_apply]

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
  let iso := dualGraphIsoOfIsPullback hnodal hnodal' H s s' hs hs' hmark
  have himg : g '' (X'.dualGraphIrreducibleComponentsEquiv hnodal' s' hs' v' : Set X') =
      (X.dualGraphIrreducibleComponentsEquiv hnodal s hs (iso.vertexEquiv v') : Set X) := by
    rw [X'.coe_dualGraphIrreducibleComponentsEquiv, X.coe_dualGraphIrreducibleComponentsEquiv,
      dualGraphVertexEquiv_dualGraphIsoOfIsPullback_vertexEquiv,
      coe_irreducibleComponentsEquivOfIsPullback, ← Set.image_comp, ← Set.image_comp]
    congr 1
    ext y'
    rw [Function.comp_apply, Function.comp_apply, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, blowupSingularLocusMap_blowupToBase H]
  rw [himg]
  refine ⟨fun h ↦ h ▸ Set.Subset.rfl, fun hsub ↦ ?_⟩
  let Z₁ := X.dualGraphIrreducibleComponentsEquiv hnodal s hs (iso.vertexEquiv v')
  let Z₂ := X.dualGraphIrreducibleComponentsEquiv hnodal s hs w
  exact (X.dualGraphIrreducibleComponentsEquiv hnodal s hs).injective
    (Subtype.ext (hsub.antisymm (Z₁.2.2 Z₂.2.1 hsub)))

/-- **Functoriality of `dualGraphIsoOfIsPullback` along towers of separably closed fields.** Given a
tower `M / L / K` of separably closed fields and compatible base-change squares `X'' ⟶ X' ⟶ X`,
the composite base-change isomorphism of dual graphs is the composition of the two step
isomorphisms. -/
theorem dualGraphIsoOfIsPullback_trans
    {K L M : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L] [Field M] [IsSepClosed M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {X X' X'' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    [X''.Over (Spec (.of M))]
    [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]
    [IsProper (X' ↘ Spec (.of L))] [ConnectedSpace X']
    [IsProper (X'' ↘ Spec (.of M))] [ConnectedSpace X'']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    (hnodal'' : AtWorstNodalOfRelativeDimensionOne (X'' ↘ Spec (.of M)))
    {g₁ : X'' ⟶ X'} {g₂ : X' ⟶ X}
    (H₁ : IsPullback g₁ (X'' ↘ Spec (.of M)) (X' ↘ Spec (.of L))
      (Spec.map (CommRingCat.ofHom (algebraMap L M))))
    (H₂ : IsPullback g₂ (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {ι : Type v} (s : ι → (Spec (.of K) ⟶ X)) (s' : ι → (Spec (.of L) ⟶ X'))
    (s'' : ι → (Spec (.of M) ⟶ X''))
    (hs : ∀ i, Set.range (s i) ⊆ (X ↘ Spec (.of K)).smoothLocus)
    (hs' : ∀ i, Set.range (s' i) ⊆ (X' ↘ Spec (.of L)).smoothLocus)
    (hs'' : ∀ i, Set.range (s'' i) ⊆ (X'' ↘ Spec (.of M)).smoothLocus)
    (hmark₁ : ∀ i, s'' i ≫ g₁ = Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫ s' i)
    (hmark₂ : ∀ i, s' i ≫ g₂ = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ s i)
    (H₁₂ : IsPullback (g₁ ≫ g₂) (X'' ↘ Spec (.of M)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K M))) := (by
      have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K L)) =
            Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]
      simpa only [hcomp] using H₁.paste_horiz H₂))
    (hmark₁₂ : ∀ i, s'' i ≫ (g₁ ≫ g₂) =
      Spec.map (CommRingCat.ofHom (algebraMap K M)) ≫ s i := fun i ↦ by
      rw [← Category.assoc, hmark₁ i, Category.assoc, hmark₂ i, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]) :
    dualGraphIsoOfIsPullback hnodal hnodal'' H₁₂ s s'' hs hs'' hmark₁₂ =
      (dualGraphIsoOfIsPullback hnodal' hnodal'' H₁ s' s'' hs' hs'' hmark₁).trans
        (dualGraphIsoOfIsPullback hnodal hnodal' H₂ s s' hs hs' hmark₂) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := hnodal''.syntomic
  let iso₁ := dualGraphIsoOfIsPullback hnodal' hnodal'' H₁ s' s'' hs' hs'' hmark₁
  let iso₂ := dualGraphIsoOfIsPullback hnodal hnodal' H₂ s s' hs hs' hmark₂
  ext x
  · rw [DualGraph.Iso.trans_vertexEquiv, Equiv.trans_apply,
      vertexEquiv_dualGraphIsoOfIsPullback_eq_iff]
    have h₁ := (vertexEquiv_dualGraphIsoOfIsPullback_eq_iff hnodal' hnodal'' H₁ s' s'' hs' hs''
      hmark₁ x (iso₁.vertexEquiv x)).mp rfl
    have h₂ := (vertexEquiv_dualGraphIsoOfIsPullback_eq_iff hnodal hnodal' H₂ s s' hs hs'
      hmark₂ (iso₁.vertexEquiv x) (iso₂.vertexEquiv (iso₁.vertexEquiv x))).mp rfl
    have hcomp_img :
        (g₁ ≫ g₂) '' (X''.dualGraphIrreducibleComponentsEquiv hnodal'' s'' hs'' x : Set X'') =
          g₂ '' (g₁ ''
            (X''.dualGraphIrreducibleComponentsEquiv hnodal'' s'' hs'' x : Set X'')) := by
      rw [← Set.image_comp]
      rfl
    exact hcomp_img ▸ (Set.image_mono h₁).trans h₂
  · apply (X.dualGraphEdgeEquiv hnodal s hs).injective
    apply (X.singularLocus K).subschemeι.isClosedEmbedding.injective
    rw [DualGraph.Iso.trans_edgeEquiv, Equiv.trans_apply,
      subschemeι_dualGraphIsoOfIsPullback_edgeEquiv,
      subschemeι_dualGraphIsoOfIsPullback_edgeEquiv,
      subschemeι_dualGraphIsoOfIsPullback_edgeEquiv, Scheme.Hom.comp_apply]

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
  dualGraphIsoOfIsPullback hnodal hnodal' (g := e.hom)
    (by
      rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) by simp]
      exact IsPullback.of_horiz_isIso ⟨by simp [he]⟩)
    s s' hs hs' (fun i ↦ by simp [hmark i])

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
  subschemeι_dualGraphIsoOfIsPullback_edgeEquiv hnodal hnodal' (g := e.hom)
    (by
      rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) by simp]
      exact IsPullback.of_horiz_isIso ⟨by simp [he]⟩)
    s s' hs hs' (fun i ↦ by simp [hmark i]) e'

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
  vertexEquiv_dualGraphIsoOfIsPullback_eq_iff hnodal hnodal' (g := e.hom)
    (by
      rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) by simp]
      exact IsPullback.of_horiz_isIso ⟨by simp [he]⟩)
    s s' hs hs' (fun i ↦ by simp [hmark i]) v' w

/-- The identity isomorphism of a pointed nodal curve induces the identity isomorphism of its dual
graph. -/
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

/-- `dualGraphIsoOfIso` respects composition of pointed curve isomorphisms. -/
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
  let _ : Algebra K K := Algebra.id K
  have : IsScalarTower K K K := ⟨fun x y z ↦ mul_assoc x y z⟩
  have hSpec_id : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by simp
  exact dualGraphIsoOfIsPullback_trans hnodal hnodal' hnodal'' (g₁ := e₁.hom) (g₂ := e₂.hom)
    (by rw [hSpec_id]; exact IsPullback.of_horiz_isIso ⟨by simp [he₁]⟩)
    (by rw [hSpec_id]; exact IsPullback.of_horiz_isIso ⟨by simp [he₂]⟩)
    s s' s'' hs hs' hs''
    (fun i ↦ by simp [hmark₁ i]) (fun i ↦ by simp [hmark₂ i])

/-- `dualGraphIsoOfIso` commutes with symmetry of pointed curve isomorphisms. -/
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
  have he_symm : e.symm.hom ≫ (X' ↘ Spec (.of K)) = X ↘ Spec (.of K) := by
    rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]
  have hmark_symm (i : ι) : s i ≫ e.symm.hom = s' i := by
    rw [← hmark i, Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id]
  let iso := dualGraphIsoOfIso hnodal hnodal' e he s s' hs hs' hmark
  let iso_symm := dualGraphIsoOfIso hnodal' hnodal e.symm he_symm s' s hs' hs hmark_symm
  have h_eq_refl : ∀ (e₀ : X ≅ X) (he₀ : e₀.hom ≫ (X ↘ Spec (.of K)) = X ↘ Spec (.of K))
      (hm₀ : ∀ i, s i ≫ e₀.hom = s i),
      e₀ = Iso.refl X →
        dualGraphIsoOfIso hnodal hnodal e₀ he₀ s s hs hs hm₀ =
          DualGraph.Iso.refl (X.dualGraph hnodal s hs) := by
    rintro _ _ _ rfl
    exact dualGraphIsoOfIso_refl hnodal s hs
  have htrans : iso_symm.trans iso = DualGraph.Iso.refl (X.dualGraph hnodal s hs) :=
    (dualGraphIsoOfIso_trans hnodal hnodal' hnodal e.symm he_symm e he s s' s hs hs' hs
      hmark_symm hmark).symm.trans (h_eq_refl (e.symm ≪≫ e) _ _ (Iso.symm_self_id e))
  ext x
  · apply iso.vertexEquiv.injective
    rw [DualGraph.Iso.symm_vertexEquiv, Equiv.apply_symm_apply]
    simpa using congrArg (fun φ : (X.dualGraph hnodal s hs).Iso _ ↦ φ.vertexEquiv x) htrans
  · apply iso.edgeEquiv.injective
    rw [DualGraph.Iso.symm_edgeEquiv, Equiv.apply_symm_apply]
    simpa using congrArg (fun φ : (X.dualGraph hnodal s hs).Iso _ ↦ φ.edgeEquiv x) htrans

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

end TauCeti.AlgebraicGeometry
