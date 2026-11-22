/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.DeformationSpace
public import TauCeti.Topology.ImplicitAtlas.Boundary
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.UnitInterval
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Geometry.Manifold.Boundary.Charts
import TauCeti.Geometry.Manifold.Boundary.Invariance
import TauCeti.Topology.Homeomorph.Prod

/-!
# Examples of implicit atlases

This file constructs the basic examples of `TauCeti.ImplicitAtlas`, which are the test inputs
for the virtual fundamental class.

* **The manifold atlas** (`TauCeti.ImplicitAtlas.ofChartedSpace`). A Hausdorff space charted on
  `ℝⁿ` is an implicit atlas of virtual dimension `n` with an empty index set: the only thickening
  is `X_∅ = X`, it is regular everywhere, and its charts give the product model. In particular
  the regular locus of an atlas is part of its data and may be all of `X`. Everything except the
  charts is `TauCeti.ImplicitAtlas.Core.ofIsEmpty`, shared with the atlas with boundary below.
* **The manifold atlas with boundary** (`TauCeti.ImplicitAtlasWithBoundary.ofChartedSpace`). A
  Hausdorff space charted on the half-space `EuclideanHalfSpace (n + 1)`, such as the interval
  `[0, 1]`, is an implicit atlas with boundary of virtual dimension `n + 1` with an empty index set,
  whose boundary is its manifold boundary. Every chart is a half-space chart, in which the
  boundary is the hyperplane `x₀ = 0` (`ModelWithCorners.mem_boundary_euclideanHalfSpace_iff`).
  Its restriction to the boundary is an implicit atlas of virtual dimension `n` on the boundary.
* **The interval atlas** (`TauCeti.ImplicitAtlasWithBoundary.unitIntervalAtlas`). The interval
  `[0, 1]` is an implicit atlas with boundary `{0, 1}` of virtual dimension `1` with an empty index
  set: the manifold atlas with boundary of `[0, 1]`, whose manifold boundary is `{0, 1}`. Its
  boundary restriction, an atlas of virtual dimension `0` on `{0, 1}`, is regular everywhere
  (`TauCeti.ImplicitAtlasWithBoundary.regLocus_boundaryAtlas_unitIntervalAtlas`).
* **Single-chart atlases on a point** (`TauCeti.ImplicitAtlas.pointAtlas`). Let a finite group
  `Γ` act on a Hausdorff topological `n`-manifold `Y` and on a finite-dimensional real
  representation `E`, and let `s : Y → E` be a continuous equivariant map whose only zero is
  `y₀`. Then the point `X = {y₀}` carries an implicit atlas of virtual dimension `n - dim E`, with
  one index `α`, group `Γ_α = Γ`, obstruction space `E_α = E`, thickening `X_α = Y` and Kuranishi
  map `s_α = s`. The regular locus of `X_∅ = X` is empty, so the footprint `V_∅` is empty
  (`TauCeti.ImplicitAtlas.footprint_pointAtlas_empty`), while `X_α` is regular; the zero set
  `Z_∅α = {y₀}` (`TauCeti.ImplicitAtlas.kuranishiZeroSet_pointKuranishi_empty`) maps onto `X`, so
  the footprint `V_α = X` covers. The thickenings are the subtypes `{y : Y // I = ∅ → y = y₀}`
  (`TauCeti.ImplicitAtlas.PointThickening`): the point `{y₀}` for `I = ∅` and `Y` for `I = {α}`.

The single-chart atlases on a point realize the following test atlases.

* **`s(x) = xᵐ` on `ℝ`** (`TauCeti.ImplicitAtlas.powAtlas`, Pardon, Example 2.3.2), with trivial
  group, `E_α = ℝ` and `m ≥ 1`. For `m ≥ 2` the zero `0` of `s_α` is not transverse, so `X` is
  not cut out transversally by `s_α`; the atlas describes it through the regular thickening `X_α`.
  As `X_∅^reg` is empty, the deformation space `D_(∅,α,α)` is empty
  (`TauCeti.ImplicitAtlas.deformationSpace_powAtlas_empty`), and `D_(α,α,α)` is
  `{(e, t, x) | t > 0, xᵐ = t e}` (`TauCeti.ImplicitAtlas.mem_deformationSpace_powAtlas_iff`): the
  points with `t = 0` are missing. Its support `Z_X` is the half-line `x = 0, e = 0, t > 0`,
  without its endpoint (`TauCeti.ImplicitAtlas.mem_deformationSupport_powAtlas_iff`).
* **`s(z) = zᵐ` on `ℂ`** (`TauCeti.ImplicitAtlas.complexPowAtlas`), the complex analogue, with
  `X_α = E_α = ℂ`.
* **The reflection atlas** (`TauCeti.ImplicitAtlas.reflectionAtlas`): `s(x) = x²` on `X_α = ℝ`,
  with `Γ_α = ℤˣ = {±1}` acting on `X_α` by `x ↦ ±x` and trivially on `E_α = ℝ`. The regular
  point `0` of `X_α` is fixed by the reflection
  (`TauCeti.ImplicitAtlas.coe_pointAct_unitsIntAction_neg_one`), which reverses the orientation of
  `X_α` and preserves that of `E_α`.
* **The ineffective point** (`TauCeti.ImplicitAtlas.ineffectivePointAtlas`): `Γ_α = ℤˣ` acting
  trivially on the point `X_α = ℝ⁰`, with `E_α = 0`. The regular locus of `X_∅` cannot be all of
  `X_∅`: in every implicit atlas with these thickenings and this action whose Kuranishi map
  vanishes at the point (automatic when `E_α = 0`) it is empty, by the freeness of `Γ_α` over
  `ψ_∅α⁻¹(X_∅^reg)`
  (`TauCeti.ImplicitAtlas.regLocus_empty_eq_empty_of_kuranishi_eq_zero`).
* **A point of virtual dimension `-1`** (`TauCeti.ImplicitAtlas.obstructedPointAtlas`): the point
  `X_α = ℝ⁰` with `E_α = ℝ` and `s_α = 0`. A nonempty space may carry an atlas of negative
  virtual dimension, as long as some expected dimension `d + m_I` is nonnegative
  (`TauCeti.ImplicitAtlas.isEmpty_of_forall_neg`).

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Example 2.3.2, §2.3.3 and
  Definitions 3.1.1 and 3.2.1 (implicit atlases with boundary). The atlas `s(x) = xᵐ` on `ℝ`
  is Pardon's Example 2.3.2, and `s(z) = zᵐ` on `ℂ` is its complex analogue. The ineffective
  point, a trivial `ℤ/2` action on a point, is Pardon's example in §2.3.3 (p. 20). The
  reflection atlas, the point of virtual dimension `-1` and the isotropy theorem are constructed
  here as implicit atlases in the sense of Definition 3.1.1; they are not taken from a numbered
  example of Pardon.
-/

public section

open Set Topology

namespace TauCeti.ImplicitAtlas

/-! ### The manifold atlas -/

section ChartedSpace

variable {A : Type*} [IsEmpty A] [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
  [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
  [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
  (ρ : ∀ α, Representation ℝ (Γ α) (E α)) (n : ℕ) (X : Type*) [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- With an empty index set, a Hausdorff space `X` carries all the data and axioms of an implicit
atlas except the local product model: its only thickening is `X_∅ = X`, regular everywhere, and its
footprint maps are inclusions. The manifold atlases `TauCeti.ImplicitAtlas.ofChartedSpace` and
`TauCeti.ImplicitAtlasWithBoundary.ofChartedSpace` extend it by their charts. -/
def Core.ofIsEmpty : ImplicitAtlas.Core Γ E ρ (fun _ ↦ X) (fun _ ↦ 1) X where
  baseHomeomorph := Homeomorph.refl X
  kuranishi _ α _ := (IsEmpty.false α.val).elim
  continuous_kuranishi _ α := (IsEmpty.false α.val).elim
  kuranishi_act _ α := (IsEmpty.false α.val).elim
  regLocus _ := univ
  isOpen_regLocus _ := isOpen_univ
  act_mem_regLocus _ _ _ _ := mem_univ _
  footprintMap _ _ _ x := x.val
  continuous_footprintMap _ _ _ := continuous_subtypeVal
  footprintMap_act _ _ _ _ _ _ := rfl
  footprintMap_self _ _ := rfl
  footprintMap_footprintMap _ _ _ _ _ _ _ _ := rfl
  kuranishi_footprintMap _ _ _ _ α := (IsEmpty.false α.val).elim
  isOpen_range_footprintMap _ _ _ := by
    rw [Subtype.range_coe, kuranishiZeroSet_eq_univ _ fun α ↦ (IsEmpty.false α).elim]
    exact isOpen_univ
  range_footprintMap_inter _ _ _ _ _ := by
    ext
    simp
  footprintMap_mem_range_iff _ _ _ _ _ _ := by simp
  isQuotientMap_footprintMap I J _ :=
    IsQuotientMap.of_inverse
      (f := fun y ↦ ⟨y.val, by simp⟩)
      (continuous_subtypeVal.subtype_mk _) continuous_subtypeVal.rangeFactorization
      fun _ ↦ rfl
  footprintMap_eq_footprintMap_iff _ _ _ x y :=
    ⟨fun h ↦ ⟨1, rfl, h⟩, fun ⟨_, _, h⟩ ↦ h⟩
  mem_regLocus_of_footprintMap_mem _ _ _ _ _ := mem_univ _
  eq_one_of_act_eq _ _ _ _ _ _ _ _ := funext fun α ↦ (IsEmpty.false α.val).elim
  exists_footprintMap_eq y :=
    ⟨∅, ⟨y, by simp⟩, mem_univ _, rfl⟩

/-- The regular locus of `TauCeti.ImplicitAtlas.Core.ofIsEmpty` is the whole space. -/
@[simp]
theorem Core.regLocus_ofIsEmpty (I : Finset A) : (Core.ofIsEmpty Γ E ρ X).regLocus I = univ :=
  (rfl)

/-- **The manifold atlas.** A Hausdorff space charted on `ℝⁿ` is an implicit atlas of virtual
dimension `n` with an empty index set, whose only thickening `X_∅ = X` is regular everywhere. -/
noncomputable def ofChartedSpace :
    ImplicitAtlas Γ E ρ (fun _ ↦ X) (fun _ ↦ 1) X n where
  toCore := Core.ofIsEmpty Γ E ρ X
  exists_openPartialHomeomorph I J _ x _ := by
    have : IsEmpty ↥(J \ I) := ⟨fun α ↦ IsEmpty.false α.val⟩
    refine ⟨n, by simp [Finset.eq_empty_of_isEmpty I],
      (chartAt (EuclideanSpace ℝ (Fin n)) x.val).transHomeomorph (Homeomorph.prodUnique _ _).symm,
      by simp, fun _ _ ↦ funext fun α ↦ (IsEmpty.false α.val).elim⟩

/-- The regular locus of the manifold atlas is the whole space. -/
@[simp]
theorem regLocus_ofChartedSpace (I : Finset A) : (ofChartedSpace Γ E ρ n X).regLocus I = univ :=
  (rfl)

/-- The regular footprint of the manifold atlas is the whole space. -/
@[simp]
theorem footprint_ofChartedSpace (I : Finset A) : (ofChartedSpace Γ E ρ n X).footprint I = univ :=
  eq_univ_of_forall fun y ↦ (ofChartedSpace Γ E ρ n X).mem_footprint.2
    ⟨⟨y, by simp⟩, mem_univ _, rfl⟩

end ChartedSpace

end TauCeti.ImplicitAtlas

/-! ### The manifold atlas with boundary -/

namespace TauCeti.ImplicitAtlasWithBoundary

section ChartedSpace

open scoped Manifold

variable {A : Type*} [IsEmpty A] [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
  [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
  [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
  (ρ : ∀ α, Representation ℝ (Γ α) (E α)) (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- **The manifold atlas with boundary.** A Hausdorff space charted on the half-space
`EuclideanHalfSpace (n + 1)` is an implicit atlas with boundary of virtual dimension `n + 1`, whose
boundary is its manifold boundary, with an empty index set. Its only thickening `X_∅ = M` is
regular everywhere, and every chart is a half-space chart. -/
noncomputable def ofChartedSpace :
    ImplicitAtlasWithBoundary Γ E ρ (fun _ ↦ M) (fun _ ↦ 1) M ((𝓡∂ (n + 1)).boundary M)
      (n + 1 : ℕ) where
  toCore := ImplicitAtlas.Core.ofIsEmpty Γ E ρ M
  boundary _ := (𝓡∂ (n + 1)).boundary M
  isClosed_boundary _ := (𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional M
  act_mem_boundary _ _ _ h := h
  boundary_empty := (rfl)
  footprintMap_mem_boundary_iff _ _ _ _ := Iff.rfl
  exists_openPartialHomeomorph I J _ x _ := by
    have : IsEmpty ↥(J \ I) := ⟨fun α ↦ IsEmpty.false α.val⟩
    refine Or.inr ⟨n, by simp [Finset.eq_empty_of_isEmpty I],
      (chartAt (EuclideanHalfSpace (n + 1)) x.val).transHomeomorph (Homeomorph.prodUnique _ _).symm,
      by simp, mem_boundary_iff_transHomeomorph_prodUnique _,
      fun _ _ ↦ funext fun α ↦ (IsEmpty.false α.val).elim⟩

/-- The boundaries of the thickenings of the manifold atlas with boundary are the manifold
boundary. -/
@[simp]
theorem boundary_ofChartedSpace (I : Finset A) :
    (ofChartedSpace Γ E ρ n M).boundary I = (𝓡∂ (n + 1)).boundary M :=
  (rfl)

/-- The regular locus of the manifold atlas with boundary is the whole space. -/
@[simp]
theorem regLocus_ofChartedSpace (I : Finset A) :
    (ofChartedSpace Γ E ρ n M).regLocus I = univ :=
  (rfl)

end ChartedSpace

/-! ### The interval `[0, 1]` -/

section UnitInterval

open scoped Manifold

variable {A : Type*} [IsEmpty A] [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
  [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
  [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
  (ρ : ∀ α, Representation ℝ (Γ α) (E α))

/-- **The interval atlas.** The interval `[0, 1]` is an implicit atlas with boundary `{0, 1}` of
virtual dimension `1` with an empty index set: the only thickening is `X_∅ = [0, 1]`, regular
everywhere, and its half-space charts are those of the manifold atlas with boundary
`TauCeti.ImplicitAtlasWithBoundary.ofChartedSpace`, whose manifold boundary is `{0, 1}`. -/
noncomputable def unitIntervalAtlas :
    ImplicitAtlasWithBoundary Γ E ρ (fun _ ↦ unitInterval) (fun _ ↦ 1) unitInterval {0, 1} 1 where
  toCore := ImplicitAtlas.Core.ofIsEmpty Γ E ρ unitInterval
  boundary _ := {0, 1}
  isClosed_boundary _ := (toFinite _).isClosed
  act_mem_boundary _ _ _ h := h
  boundary_empty := (rfl)
  footprintMap_mem_boundary_iff _ _ _ _ := Iff.rfl
  exists_openPartialHomeomorph _ _ h x hx := by
    let : ChartedSpace (EuclideanHalfSpace (0 + 1)) unitInterval := instIccChartedSpace 0 1
    -- The manifold boundary of `[0, 1]` is `{0, 1}`.
    have hbd : (𝓡∂ (0 + 1)).boundary unitInterval = {0, 1} := boundary_Icc
    rcases (ofChartedSpace Γ E ρ 0 unitInterval).exists_openPartialHomeomorph h x hx with
      ⟨n, hn, e, hxe, hdisj, he⟩ | ⟨n, hn, e, hxe, hbde, he⟩
    · exact Or.inl ⟨n, by simpa using hn, e, hxe, hbd ▸ hdisj, he⟩
    · exact Or.inr ⟨n, by simpa using hn, e, hxe, hbd ▸ hbde, he⟩

@[simp]
theorem regLocus_unitIntervalAtlas (I : Finset A) : (unitIntervalAtlas Γ E ρ).regLocus I = univ :=
  (rfl)

@[simp]
theorem boundary_unitIntervalAtlas (I : Finset A) :
    (unitIntervalAtlas Γ E ρ).boundary I = {0, 1} :=
  (rfl)

/-- The boundary restriction of the interval atlas, an atlas of virtual dimension `1 - 1` on
`{0, 1}`, is regular everywhere. -/
theorem regLocus_boundaryAtlas_unitIntervalAtlas (I : Finset A) :
    (unitIntervalAtlas Γ E ρ).boundaryAtlas.regLocus I = univ := by
  simp

end UnitInterval

end TauCeti.ImplicitAtlasWithBoundary

namespace TauCeti.ImplicitAtlas

/-! ### Single-chart atlases on a point -/

section Point

/-- The thickenings of a single-chart atlas on a point (`TauCeti.ImplicitAtlas.pointAtlas`): the
point `{y₀}` of `Y` for `I = ∅` and all of `Y` for `I = {α}`. -/
abbrev PointThickening (Y : Type*) (y₀ : Y) (I : Finset Unit) : Type _ :=
  {y : Y // I = ∅ → y = y₀}

/-- A finite set of indices that misses the only index is empty. -/
private theorem eq_empty_of_notMem {I : Finset Unit} {α : Unit} (hα : α ∉ I) : I = ∅ :=
  Finset.eq_empty_of_forall_notMem fun β hβ ↦ hα (Subsingleton.elim β α ▸ hβ)

variable {Γ : Type*} [Group Γ]

variable (Γ) in
/-- The component in `Γ` of an element `g` of `Γ_I = ∏_(α ∈ I) Γ`, for `I ⊆ {α}`: the value
`g α` if `α ∈ I`, and `1` if `I = ∅`. -/
def pointComponent (I : Finset Unit) : ((α : I) → Γ) →* Γ :=
  if h : () ∈ I then Pi.evalMonoidHom (fun _ : I ↦ Γ) ⟨(), h⟩ else 1

/-- The component of `g ∈ Γ_I` is its value at the index, when `α ∈ I`. -/
@[simp]
theorem pointComponent_of_mem {I : Finset Unit} (h : () ∈ I) (g : (α : I) → Γ) :
    pointComponent Γ I g = g ⟨(), h⟩ := by
  simp [pointComponent, h]

/-- The component of the only element of `Γ_∅` is `1`. -/
@[simp]
theorem pointComponent_of_notMem {I : Finset Unit} (h : () ∉ I) (g : (α : I) → Γ) :
    pointComponent Γ I g = 1 := by
  simp [pointComponent, h]

variable {Y : Type*} {y₀ : Y}

/-- The Kuranishi map `s_α = s : X_J → E` of a single-chart atlas on a point. -/
def pointKuranishi {E : Type*} (y₀ : Y) (s : Y → E) (J : Finset Unit) (_ : J)
    (y : PointThickening Y y₀ J) : E :=
  s y

@[simp]
theorem pointKuranishi_apply {E : Type*} (s : Y → E) (J : Finset Unit) (α : J)
    (y : PointThickening Y y₀ J) : pointKuranishi y₀ s J α y = s y :=
  (rfl)

section ZeroSet

variable {E : Type*} [Zero E] {s : Y → E}

/-- If `y₀` is the only zero of `s`, a point of the zero set `Z_IJ` of a single-chart atlas on a
point is `y₀` unless `α ∈ I`. -/
theorem coe_eq_of_mem_kuranishiZeroSet_pointKuranishi (hs₀ : ∀ y, s y = 0 ↔ y = y₀)
    {I J : Finset Unit} (hI : () ∉ I) {y : PointThickening Y y₀ J}
    (hy : y ∈ kuranishiZeroSet (E := fun _ ↦ E) (pointKuranishi y₀ s) I J) : (y : Y) = y₀ := by
  by_cases hJ : () ∈ J
  · exact (hs₀ _).1 (mem_kuranishiZeroSet.1 hy ⟨(), hJ⟩ hI)
  · exact y.property (eq_empty_of_notMem hJ)

/-- If `y₀` is the only zero of `s`, the zero set `Z_∅J` of a single-chart atlas on a point is
`{y₀}`. -/
theorem kuranishiZeroSet_pointKuranishi_empty (hs₀ : ∀ y, s y = 0 ↔ y = y₀) (J : Finset Unit) :
    kuranishiZeroSet (E := fun _ ↦ E) (pointKuranishi y₀ s) ∅ J =
      {y : PointThickening Y y₀ J | (y : Y) = y₀} := by
  ext y
  exact ⟨coe_eq_of_mem_kuranishiZeroSet_pointKuranishi hs₀ (Finset.notMem_empty _),
    fun hy ↦ mem_kuranishiZeroSet.2 fun _ _ ↦ (hs₀ _).2 hy⟩

/-- The footprint map of a single-chart atlas on a point keeps the point of `Y`. -/
private def pointFootprintMap (hs₀ : ∀ y, s y = 0 ↔ y = y₀) {I J : Finset Unit} (_ : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ ↦ E) (pointKuranishi y₀ s) I J) :
    PointThickening Y y₀ I :=
  ⟨x.val.val, fun hI ↦ coe_eq_of_mem_kuranishiZeroSet_pointKuranishi hs₀ (by simp [hI]) x.property⟩

private theorem coe_pointFootprintMap (hs₀ : ∀ y, s y = 0 ↔ y = y₀) {I J : Finset Unit}
    (h : I ⊆ J) (x : kuranishiZeroSet (E := fun _ ↦ E) (pointKuranishi y₀ s) I J) :
    (pointFootprintMap hs₀ h x : Y) = x.val.val :=
  rfl

/-- A continuous section of `pointFootprintMap`, so that it is onto and a quotient map. -/
private def pointSection (hs₀ : ∀ y, s y = 0 ↔ y = y₀) {I J : Finset Unit} (h : I ⊆ J)
    (y : PointThickening Y y₀ I) :
    kuranishiZeroSet (E := fun _ ↦ E) (pointKuranishi y₀ s) I J :=
  ⟨⟨y.val, fun hJ ↦ y.property (Finset.subset_empty.1 (hJ ▸ h))⟩,
    mem_kuranishiZeroSet.2 fun _ hα ↦ (hs₀ _).2 (y.property (eq_empty_of_notMem hα))⟩

private theorem pointFootprintMap_pointSection (hs₀ : ∀ y, s y = 0 ↔ y = y₀) {I J : Finset Unit}
    (h : I ⊆ J) (y : PointThickening Y y₀ I) :
    pointFootprintMap hs₀ h (pointSection hs₀ h y) = y :=
  rfl

private theorem range_pointFootprintMap (hs₀ : ∀ y, s y = 0 ↔ y = y₀) {I J : Finset Unit}
    (h : I ⊆ J) : range (pointFootprintMap hs₀ h) = univ :=
  eq_univ_of_forall fun y ↦ ⟨_, pointFootprintMap_pointSection hs₀ h y⟩

variable [TopologicalSpace Y] in
private theorem continuous_pointSection (hs₀ : ∀ y, s y = 0 ↔ y = y₀) {I J : Finset Unit}
    (h : I ⊆ J) : Continuous (pointSection hs₀ h) :=
  (continuous_subtypeVal.subtype_mk _).subtype_mk _

end ZeroSet

variable [TopologicalSpace Y]

/-- The action of `Γ_I` on the thickening `X_I` of a single-chart atlas on a point, through an
action `σ` of `Γ` on `Y` by homeomorphisms fixing `y₀`: on `X_α = Y` an element `g` acts by
`σ (g α)`, and on `X_∅ = {y₀}` every element acts trivially. -/
def pointAct (σ : Γ →* (Y ≃ₜ Y)) (hσ : ∀ g, σ g y₀ = y₀) (I : Finset Unit) :
    ((α : I) → Γ) →* (PointThickening Y y₀ I ≃ₜ PointThickening Y y₀ I) where
  toFun g := (σ (pointComponent Γ I g)).subtype fun _ ↦ imp_congr_right fun _ ↦
    ⟨fun h ↦ by rw [h, hσ], fun h ↦ (σ _).injective (h.trans (hσ _).symm)⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
theorem coe_pointAct_apply (σ : Γ →* (Y ≃ₜ Y)) (hσ : ∀ g, σ g y₀ = y₀) (I : Finset Unit)
    (g : (α : I) → Γ) (y : PointThickening Y y₀ I) :
    (pointAct σ hσ I g y : Y) = σ (pointComponent Γ I g) y :=
  (rfl)

/-- The trivial action of `Γ` on `Y` induces the trivial action on every thickening. -/
@[simp]
theorem pointAct_one (hσ : ∀ g, (1 : Γ →* (Y ≃ₜ Y)) g y₀ = y₀) :
    pointAct (1 : Γ →* (Y ≃ₜ Y)) hσ = fun _ ↦ 1 := by
  ext I g y
  simp

/-- A thickening at a nonempty index set is all of `Y`. -/
private def pointThickeningHomeomorph {J : Finset Unit} (hJ : J.Nonempty) :
    PointThickening Y y₀ J ≃ₜ Y where
  toFun := Subtype.val
  invFun y := ⟨y, fun h ↦ (hJ.ne_empty h).elim⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtypeVal
  continuous_invFun := continuous_id.subtype_mk _

/-- An equivariant map `s` whose only zero is `y₀` forces `y₀` to be a fixed point. -/
theorem apply_eq_self_of_equivariant {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ρ : Representation ℝ Γ E} {σ : Γ →* (Y ≃ₜ Y)} {s : Y → E} (hsσ : ∀ g y, s (σ g y) = ρ g (s y))
    (hs₀ : ∀ y, s y = 0 ↔ y = y₀) (g : Γ) : σ g y₀ = y₀ :=
  (hs₀ _).1 (by rw [hsσ, (hs₀ y₀).2 rfl, map_zero])

variable [Finite Γ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [T2Space Y]

/-- **Single-chart implicit atlas on a point.** Let a finite group `Γ` act on a Hausdorff
topological `n`-manifold `Y` through `σ` and on a finite-dimensional real representation `E`
through `ρ`, and let `s : Y → E` be a continuous equivariant map whose only zero is `y₀`. This is
the implicit atlas of virtual dimension `d = n - dim E` on the point `X = {y₀}`, with one index
`α`, group `Γ_α = Γ`, obstruction space `E_α = E`, thickening `X_α = Y` and Kuranishi map
`s_α = s`. The regular locus of `X_∅ = X` is empty, while `X_α` is regular. The zero set
`Z_∅α = {y₀}` (`TauCeti.ImplicitAtlas.kuranishiZeroSet_pointKuranishi_empty`) maps onto `X`, so
the footprint `V_α = X` covers. Since `X_∅` has no regular point, `Γ` need not act freely: the
point `y₀` is fixed by all of `Γ` (`TauCeti.ImplicitAtlas.apply_eq_self_of_equivariant`). -/
noncomputable def pointAtlas (ρ : Representation ℝ Γ E) (σ : Γ →* (Y ≃ₜ Y)) (s : Y → E)
    (hs : Continuous s) (hsσ : ∀ g y, s (σ g y) = ρ g (s y)) (hs₀ : ∀ y, s y = 0 ↔ y = y₀) (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {d : ℤ} (hd : (n : ℤ) = d + Module.finrank ℝ E) :
    ImplicitAtlas (fun _ : Unit ↦ Γ) (fun _ ↦ E) (fun _ ↦ ρ) (PointThickening Y y₀)
      (pointAct σ (apply_eq_self_of_equivariant hsσ hs₀)) (PointThickening Y y₀ ∅) d where
  baseHomeomorph := Homeomorph.refl _
  kuranishi := pointKuranishi y₀ s
  continuous_kuranishi _ _ := hs.comp continuous_subtypeVal
  kuranishi_act J α g y := by
    rw [pointKuranishi_apply, pointKuranishi_apply, coe_pointAct_apply, hsσ,
      pointComponent_of_mem α.property]
  regLocus I := {_y | I.Nonempty}
  isOpen_regLocus _ := isOpen_const
  act_mem_regLocus _ _ _ h := h
  footprintMap _ _ := pointFootprintMap hs₀
  continuous_footprintMap _ _ _ :=
    (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  footprintMap_act I J h g x hx := by
    ext
    simp only [coe_pointFootprintMap, coe_pointAct_apply]
    by_cases hI : () ∈ I
    · rw [pointComponent_of_mem (h hI), pointComponent_of_mem hI, Finset.restrict₂_def]
    · rw [coe_eq_of_mem_kuranishiZeroSet_pointKuranishi hs₀ hI x.property,
        apply_eq_self_of_equivariant hsσ hs₀, apply_eq_self_of_equivariant hsσ hs₀]
  footprintMap_self _ _ := rfl
  footprintMap_footprintMap _ _ _ _ _ _ _ _ := rfl
  kuranishi_footprintMap _ _ _ _ _ := rfl
  isOpen_range_footprintMap _ _ h := by
    rw [range_pointFootprintMap hs₀ h]
    exact isOpen_univ
  range_footprintMap_inter _ _ _ _ _ := by simp only [range_pointFootprintMap, inter_self]
  footprintMap_mem_range_iff _ _ _ _ _ _ := by simp only [range_pointFootprintMap, mem_univ]
  isQuotientMap_footprintMap _ _ h :=
    IsQuotientMap.of_inverse
      (f := fun y : range (pointFootprintMap (s := s) hs₀ h) ↦ pointSection hs₀ h y.val)
      ((continuous_pointSection hs₀ h).comp continuous_subtypeVal)
      (((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _).rangeFactorization)
      fun y ↦ Subtype.ext (pointFootprintMap_pointSection hs₀ h y.val)
  footprintMap_eq_footprintMap_iff I J h x y := by
    refine ⟨fun hxy ↦ ⟨1, funext fun _ ↦ rfl, ?_⟩, fun ⟨g, hg, hgx⟩ ↦ Subtype.ext ?_⟩
    · rw [map_one, Homeomorph.one_apply]
      exact Subtype.ext (by simpa only [coe_pointFootprintMap] using congrArg Subtype.val hxy)
    · rw [coe_pointFootprintMap, coe_pointFootprintMap]
      by_cases hI : () ∈ I
      · have hg₁ : pointComponent Γ J g = 1 := by
          rw [pointComponent_of_mem (h hI)]
          simpa [Finset.restrict₂_def] using congrFun hg ⟨(), hI⟩
        rw [← hgx, coe_pointAct_apply, hg₁, map_one, Homeomorph.one_apply]
      · rw [coe_eq_of_mem_kuranishiZeroSet_pointKuranishi hs₀ hI x.property,
          coe_eq_of_mem_kuranishiZeroSet_pointKuranishi hs₀ hI y.property]
  mem_regLocus_of_footprintMap_mem _ _ h _ hx := Finset.Nonempty.mono h hx
  eq_one_of_act_eq I J h x hx g hg _ := by
    obtain ⟨⟨⟩, hI⟩ := hx
    funext ⟨⟨⟩, _⟩
    simpa [Finset.restrict₂_def] using congrFun hg ⟨(), hI⟩
  exists_openPartialHomeomorph I J h x hx := by
    have hJ : J.Nonempty := Finset.Nonempty.mono h hx
    obtain rfl : I = Finset.univ := Finset.Nonempty.eq_univ hx
    have : IsEmpty ↥(J \ Finset.univ) := ⟨fun α ↦ (Finset.mem_sdiff.1 α.property).2
        (Finset.mem_univ _)⟩
    refine ⟨n, by simpa using hd, (pointThickeningHomeomorph hJ).transOpenPartialHomeomorph
      ((chartAt (EuclideanSpace ℝ (Fin n)) x.val.val).transHomeomorph
        (Homeomorph.prodUnique _ _).symm),
      by simp [pointThickeningHomeomorph], fun _ _ ↦ Subsingleton.elim _ _⟩
  exists_footprintMap_eq y :=
    ⟨Finset.univ, pointSection hs₀ (Finset.empty_subset _) y, Finset.univ_nonempty, rfl⟩

variable (ρ : Representation ℝ Γ E) (σ : Γ →* (Y ≃ₜ Y)) (s : Y → E) (hs : Continuous s)
  (hsσ : ∀ g y, s (σ g y) = ρ g (s y)) (hs₀ : ∀ y, s y = 0 ↔ y = y₀) (n : ℕ)
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {d : ℤ}
  (hd : (n : ℤ) = d + Module.finrank ℝ E)

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.pointAtlas` is everything for `I = {α}`
and empty for `I = ∅`. -/
theorem regLocus_pointAtlas (I : Finset Unit) :
    (pointAtlas ρ σ s hs hsσ hs₀ n hd).regLocus I = {_y | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.pointAtlas` is empty. -/
@[simp]
theorem regLocus_pointAtlas_empty : (pointAtlas ρ σ s hs hsσ hs₀ n hd).regLocus ∅ = ∅ := by
  simp [regLocus_pointAtlas]

/-- The footprint `V_∅` of `TauCeti.ImplicitAtlas.pointAtlas` is empty, since the regular locus of
`X_∅` is. So the footprints of the subsets of the empty set of indices do not cover the point. -/
@[simp]
theorem footprint_pointAtlas_empty : (pointAtlas ρ σ s hs hsσ hs₀ n hd).footprint ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hy ↦ by
    obtain ⟨x, hx, -⟩ := (pointAtlas ρ σ s hs hsσ hs₀ n hd).mem_footprint.1 hy
    simp at hx

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.pointAtlas` is `s`. -/
@[simp]
theorem kuranishi_pointAtlas : (pointAtlas ρ σ s hs hsσ hs₀ n hd).kuranishi = pointKuranishi y₀ s :=
  (rfl)

/-- The footprint maps of `TauCeti.ImplicitAtlas.pointAtlas` keep the point of `Y`. -/
@[simp]
theorem coe_footprintMap_pointAtlas {I J : Finset Unit} (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ E)
      (pointAtlas ρ σ s hs hsσ hs₀ n hd).kuranishi I J) :
    ((pointAtlas ρ σ s hs hsσ hs₀ n hd).footprintMap h x : Y) =
      ((x : PointThickening Y y₀ J) : Y) :=
  (rfl)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.pointAtlas` is the whole point. -/
@[simp]
theorem footprint_pointAtlas_singleton :
    (pointAtlas ρ σ s hs hsσ hs₀ n hd).footprint {()} = univ :=
  eq_univ_of_forall fun y ↦ (pointAtlas ρ σ s hs hsσ hs₀ n hd).mem_footprint.2
    ⟨pointSection hs₀ (Finset.empty_subset _) y, by simp [regLocus_pointAtlas],
      Subtype.ext (coe_footprintMap_pointAtlas ρ σ s hs hsσ hs₀ n hd (Finset.empty_subset _) _)⟩

end Point

/-! ### Examples of single-chart atlases on a point -/

section PointExamples

/-- The real line with its global chart `ℝ ≃ₜ ℝ¹`. -/
@[instance_reducible]
private noncomputable def realChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ℝ :=
  OpenPartialHomeomorph.singletonChartedSpace
    ((Homeomorph.funUnique (Fin 1) ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 1) ℝ).symm.toHomeomorph).toOpenPartialHomeomorph (by simp)

/-- The complex line with its global chart `ℂ ≃ₜ ℝ²` in the basis `1, i`. -/
@[instance_reducible]
private noncomputable def complexChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ℂ :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace
    (by simp)

variable {m : ℕ}

/-- **Pardon's Example 2.3.2.** The implicit atlas of virtual dimension `0` on the point
`X = {0}` with one index `α`, trivial group, obstruction space `E_α = ℝ`, thickening `X_α = ℝ`
and Kuranishi map `s_α(x) = xᵐ`, `m ≠ 0`. The regular locus of `X_∅ = X` is empty and `X_α` is
regular. -/
noncomputable def powAtlas (hm : m ≠ 0) :
    ImplicitAtlas (fun _ : Unit ↦ Unit) (fun _ ↦ ℝ) (fun _ ↦ Representation.trivial ℝ Unit ℝ)
      (PointThickening ℝ 0) (pointAct 1 fun _ ↦ rfl) (PointThickening ℝ 0 ∅) 0 :=
  letI := realChartedSpace
  pointAtlas (Representation.trivial ℝ Unit ℝ) 1 (fun x : ℝ ↦ x ^ m) (continuous_pow m)
    (fun _ _ ↦ by simp) (fun _ ↦ pow_eq_zero_iff hm) 1 (by simp)

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.powAtlas` is `s_α(x) = xᵐ`. -/
@[simp]
theorem kuranishi_powAtlas (hm : m ≠ 0) :
    (powAtlas hm).kuranishi = pointKuranishi 0 fun x : ℝ ↦ x ^ m :=
  (rfl)

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.powAtlas` is everything for `I = {α}`
and empty for `I = ∅`. -/
theorem regLocus_powAtlas (hm : m ≠ 0) (I : Finset Unit) :
    (powAtlas hm).regLocus I = {_x | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.powAtlas` is empty. -/
@[simp]
theorem regLocus_powAtlas_empty (hm : m ≠ 0) : (powAtlas hm).regLocus ∅ = ∅ :=
  letI := realChartedSpace
  regLocus_pointAtlas_empty ..

/-- The footprint maps of `TauCeti.ImplicitAtlas.powAtlas` keep the real coordinate. -/
@[simp]
theorem coe_footprintMap_powAtlas (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ ℝ) (powAtlas hm).kuranishi I J) :
    ((powAtlas hm).footprintMap h x : ℝ) = ((x : PointThickening ℝ 0 J) : ℝ) :=
  (rfl)

/-- The footprint `V_∅` of `TauCeti.ImplicitAtlas.powAtlas` is empty, since the regular locus of
`X_∅` is. So the footprints of the subsets of the empty set of indices do not cover the point. -/
@[simp]
theorem footprint_powAtlas_empty (hm : m ≠ 0) : (powAtlas hm).footprint ∅ = ∅ :=
  letI := realChartedSpace
  footprint_pointAtlas_empty ..

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.powAtlas` is the whole point. -/
@[simp]
theorem footprint_powAtlas_singleton (hm : m ≠ 0) : (powAtlas hm).footprint {()} = univ :=
  letI := realChartedSpace
  footprint_pointAtlas_singleton ..

/-! #### Deformation spaces of `powAtlas` -/

/-- For the atlas `s(x) = xᵐ` on a point, whose `X_∅^reg` is empty, the deformation space
`D_(∅,α,α)` is empty. -/
theorem deformationSpace_powAtlas_empty (hm : m ≠ 0) :
    (powAtlas hm).deformationSpace ∅ (subset_refl (Finset.univ : Finset Unit)) = ∅ :=
  deformationSpace_eq_empty fun S hS ↦ by
    rw [Finset.subset_empty.1 hS, regLocus_powAtlas_empty]

/-- For the atlas `s(x) = xᵐ` on a point, the deformation space `D_(α,α,α)` is
`{(e, t, x) | t > 0, xᵐ = t e}`. The points with `t = 0` are missing because `X_∅^reg = ∅`. -/
theorem mem_deformationSpace_powAtlas_iff (hm : m ≠ 0)
    {p : ((α : (Finset.univ : Finset Unit)) → ℝ) × (↥(Finset.univ : Finset Unit) → ℝ) ×
      PointThickening ℝ 0 Finset.univ} :
    p ∈ (powAtlas hm).deformationSpace Finset.univ (subset_refl (Finset.univ : Finset Unit)) ↔
      0 < p.2.1 ⟨(), Finset.mem_univ _⟩ ∧
        (p.2.2 : ℝ) ^ m = p.2.1 ⟨(), Finset.mem_univ _⟩ * p.1 ⟨(), Finset.mem_univ _⟩ := by
  rw [mem_deformationSpace]
  constructor
  · rintro ⟨-, -, hs, h, hx, hreg⟩
    refine ⟨?_, by simpa using hs ⟨(), Finset.mem_univ _⟩⟩
    rw [regLocus_powAtlas] at hreg
    obtain ⟨α, hα⟩ := hreg
    exact (mem_positiveIndices.1 hα).2
  · rintro ⟨hpos, hs⟩
    have hT : positiveIndices p.2.1 = Finset.univ :=
      Finset.eq_univ_of_forall fun _ ↦ mem_positiveIndices.2 ⟨Finset.mem_univ _, hpos⟩
    refine ⟨fun ⟨(), _⟩ ↦ hpos.le, fun α hα ↦ (hα (Finset.mem_univ _)).elim,
      fun ⟨(), _⟩ ↦ by simpa using hs, ?_⟩
    rw [hT]
    refine ⟨subset_refl _, mem_kuranishiZeroSet_self _ _, ?_⟩
    rw [regLocus_powAtlas]
    exact Finset.univ_nonempty

/-- For the atlas `s(x) = xᵐ` on a point, the support `Z_X ⊆ D_(α,α,α)` is the half-line
`x = 0`, `e = 0`, `t > 0`, which does not contain its endpoint `t = 0`. -/
theorem mem_deformationSupport_powAtlas_iff (hm : m ≠ 0)
    {p : (powAtlas hm).deformationSpace Finset.univ (subset_refl (Finset.univ : Finset Unit))} :
    p ∈ (powAtlas hm).deformationSupport Finset.univ (subset_refl (Finset.univ : Finset Unit))
        univ ↔
      (p.val.2.2 : ℝ) = 0 := by
  obtain ⟨hpos, hs⟩ := (mem_deformationSpace_powAtlas_iff hm).1 p.property
  rw [mem_deformationSupport]
  constructor
  · rintro ⟨he, -⟩
    rw [he, Pi.zero_apply, mul_zero] at hs
    exact (pow_eq_zero_iff hm).1 hs
  · intro hx
    rw [hx, zero_pow hm] at hs
    have he : p.val.1 = 0 := funext fun ⟨(), _⟩ ↦
      (mul_eq_zero.1 hs.symm).resolve_left hpos.ne'
    exact ⟨he, mem_kuranishiZeroSet_empty_of_eq_zero p.property he, mem_univ _⟩

/-- The implicit atlas of virtual dimension `0` on the point `X = {0}` with one index `α`,
trivial group, obstruction space `E_α = ℂ`, thickening `X_α = ℂ` and Kuranishi map
`s_α(z) = zᵐ`, `m ≠ 0`, the complex analogue of `TauCeti.ImplicitAtlas.powAtlas`. Its zero is
the zero of multiplicity `m` of a holomorphic function, which the virtual class counts with
multiplicity `m` (Pardon, Example 2.3.2). -/
noncomputable def complexPowAtlas (hm : m ≠ 0) :
    ImplicitAtlas (fun _ : Unit ↦ Unit) (fun _ ↦ ℂ) (fun _ ↦ Representation.trivial ℝ Unit ℂ)
      (PointThickening ℂ 0) (pointAct 1 fun _ ↦ rfl) (PointThickening ℂ 0 ∅) 0 :=
  letI := complexChartedSpace
  pointAtlas (Representation.trivial ℝ Unit ℂ) 1 (fun z : ℂ ↦ z ^ m) (continuous_pow m)
    (fun _ _ ↦ by simp) (fun _ ↦ pow_eq_zero_iff hm) 2 (by simp [Complex.finrank_real_complex])

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.complexPowAtlas` is `s_α(z) = zᵐ`. -/
@[simp]
theorem kuranishi_complexPowAtlas (hm : m ≠ 0) :
    (complexPowAtlas hm).kuranishi = pointKuranishi 0 fun z : ℂ ↦ z ^ m :=
  (rfl)

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.complexPowAtlas` is everything for
`I = {α}` and empty for `I = ∅`. -/
theorem regLocus_complexPowAtlas (hm : m ≠ 0) (I : Finset Unit) :
    (complexPowAtlas hm).regLocus I = {_z | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.complexPowAtlas` is empty. -/
@[simp]
theorem regLocus_complexPowAtlas_empty (hm : m ≠ 0) : (complexPowAtlas hm).regLocus ∅ = ∅ :=
  letI := complexChartedSpace
  regLocus_pointAtlas_empty ..

/-- The footprint maps of `TauCeti.ImplicitAtlas.complexPowAtlas` keep the complex coordinate. -/
@[simp]
theorem coe_footprintMap_complexPowAtlas (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ ℂ) (complexPowAtlas hm).kuranishi I J) :
    ((complexPowAtlas hm).footprintMap h x : ℂ) = ((x : PointThickening ℂ 0 J) : ℂ) :=
  (rfl)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.complexPowAtlas` is the whole point. -/
@[simp]
theorem footprint_complexPowAtlas_singleton (hm : m ≠ 0) :
    (complexPowAtlas hm).footprint {()} = univ :=
  letI := complexChartedSpace
  footprint_pointAtlas_singleton ..

/-- The action of `ℤˣ = {±1}` on `ℝ` by multiplication: `-1` acts by the reflection `x ↦ -x`. -/
noncomputable def unitsIntAction : ℤˣ →* (ℝ ≃ₜ ℝ) where
  toFun u := Homeomorph.mulLeft₀ ((u : ℤ) : ℝ) (by simp)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
theorem unitsIntAction_apply (u : ℤˣ) (x : ℝ) : unitsIntAction u x = (u : ℤ) * x :=
  (rfl)

/-- **The reflection atlas.** The implicit atlas of virtual dimension `0` on the point
`X = {0}` with one index `α`, group `Γ_α = ℤˣ = {±1}` acting on the thickening `X_α = ℝ` by the
reflection `x ↦ -x` and trivially on the obstruction space `E_α = ℝ`, and the invariant
Kuranishi map `s_α(x) = x²`. The regular locus of `X_∅ = X` is empty and `X_α` is regular. The
regular point `0` of `X_α` is fixed by the reflection
(`TauCeti.ImplicitAtlas.coe_pointAct_unitsIntAction_neg_one`), which reverses the orientation of
`X_α` while acting trivially on `E_α`. -/
noncomputable def reflectionAtlas :
    ImplicitAtlas (fun _ : Unit ↦ ℤˣ) (fun _ ↦ ℝ) (fun _ ↦ Representation.trivial ℝ ℤˣ ℝ)
      (PointThickening ℝ 0) (pointAct unitsIntAction fun _ ↦ by simp) (PointThickening ℝ 0 ∅) 0 :=
  letI := realChartedSpace
  pointAtlas (Representation.trivial ℝ ℤˣ ℝ) unitsIntAction (fun x : ℝ ↦ x ^ 2)
    (continuous_pow 2)
    (fun u _ ↦ by rcases Int.units_eq_one_or u with rfl | rfl <;> simp)
    (fun _ ↦ pow_eq_zero_iff two_ne_zero) 1 (by simp)

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.reflectionAtlas` is `s_α(x) = x²`. -/
@[simp]
theorem kuranishi_reflectionAtlas :
    reflectionAtlas.kuranishi = pointKuranishi 0 fun x : ℝ ↦ x ^ 2 :=
  (rfl)

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.reflectionAtlas` is everything for
`I = {α}` and empty for `I = ∅`. -/
theorem regLocus_reflectionAtlas (I : Finset Unit) :
    reflectionAtlas.regLocus I = {_x | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.reflectionAtlas` is empty. -/
@[simp]
theorem regLocus_reflectionAtlas_empty : reflectionAtlas.regLocus ∅ = ∅ :=
  letI := realChartedSpace
  regLocus_pointAtlas_empty ..

/-- The footprint maps of `TauCeti.ImplicitAtlas.reflectionAtlas` keep the real coordinate. -/
@[simp]
theorem coe_footprintMap_reflectionAtlas {I J : Finset Unit} (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ ℝ) reflectionAtlas.kuranishi I J) :
    (reflectionAtlas.footprintMap h x : ℝ) = ((x : PointThickening ℝ 0 J) : ℝ) :=
  (rfl)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.reflectionAtlas` is the whole point. -/
@[simp]
theorem footprint_reflectionAtlas_singleton : reflectionAtlas.footprint {()} = univ :=
  letI := realChartedSpace
  footprint_pointAtlas_singleton ..

/-- In `TauCeti.ImplicitAtlas.reflectionAtlas` the element `-1` of `Γ_α` acts on the thickening
`X_α = ℝ` by the reflection `x ↦ -x`. -/
theorem coe_pointAct_unitsIntAction_neg_one (hσ : ∀ u, unitsIntAction u 0 = 0)
    (x : PointThickening ℝ 0 {()}) :
    (pointAct unitsIntAction hσ {()} (fun _ ↦ -1) x : ℝ) = -x := by
  simp [pointComponent_of_mem (Finset.mem_singleton_self ())]

/-- **The ineffective point** (Pardon, §2.3.3). The implicit atlas of virtual dimension `0` on
the point `X = {0}` with one index `α`, group `Γ_α = ℤˣ = {±1}` acting trivially, obstruction
space `E_α = 0` and thickening `X_α = ℝ⁰`, a point. The regular locus of `X_∅ = X` is empty and
`X_α` is regular. It has to be: in every atlas with these thickenings and this action whose
Kuranishi map vanishes at the point, as it must for `E_α = 0`, `X_∅` has no regular point
(`TauCeti.ImplicitAtlas.regLocus_empty_eq_empty_of_kuranishi_eq_zero`). -/
noncomputable def ineffectivePointAtlas :
    ImplicitAtlas (fun _ : Unit ↦ ℤˣ) (fun _ ↦ EuclideanSpace ℝ (Fin 0))
      (fun _ ↦ Representation.trivial ℝ ℤˣ (EuclideanSpace ℝ (Fin 0)))
      (PointThickening (EuclideanSpace ℝ (Fin 0)) 0) (pointAct 1 fun _ ↦ rfl)
      (PointThickening (EuclideanSpace ℝ (Fin 0)) 0 ∅) 0 :=
  pointAtlas (Representation.trivial ℝ ℤˣ (EuclideanSpace ℝ (Fin 0))) 1 0 continuous_const
    (fun _ _ ↦ by simp) (fun _ ↦ iff_of_true rfl (Subsingleton.elim _ _)) 0 (by simp)

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.ineffectivePointAtlas` is zero. -/
@[simp]
theorem kuranishi_ineffectivePointAtlas :
    ineffectivePointAtlas.kuranishi =
      pointKuranishi 0 (0 : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) :=
  (rfl)

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.ineffectivePointAtlas` is everything
for `I = {α}` and empty for `I = ∅`. -/
theorem regLocus_ineffectivePointAtlas (I : Finset Unit) :
    ineffectivePointAtlas.regLocus I = {_x | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.ineffectivePointAtlas` is empty. -/
@[simp]
theorem regLocus_ineffectivePointAtlas_empty : ineffectivePointAtlas.regLocus ∅ = ∅ :=
  regLocus_pointAtlas_empty ..

/-- The footprint maps of `TauCeti.ImplicitAtlas.ineffectivePointAtlas` keep the point of
`ℝ⁰`. -/
@[simp]
theorem coe_footprintMap_ineffectivePointAtlas {I J : Finset Unit} (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ EuclideanSpace ℝ (Fin 0))
      ineffectivePointAtlas.kuranishi I J) :
    (ineffectivePointAtlas.footprintMap h x : EuclideanSpace ℝ (Fin 0)) =
      ((x : PointThickening (EuclideanSpace ℝ (Fin 0)) 0 J) : EuclideanSpace ℝ (Fin 0)) :=
  (rfl)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.ineffectivePointAtlas` is the whole point. -/
@[simp]
theorem footprint_ineffectivePointAtlas_singleton : ineffectivePointAtlas.footprint {()} = univ :=
  footprint_pointAtlas_singleton ..

/-- **A point of negative virtual dimension.** The implicit atlas of virtual dimension `-1` on
the point `X = {0}` with one index `α`, trivial group, obstruction space `E_α = ℝ`, thickening
`X_α = ℝ⁰`, a point, and the zero Kuranishi map. The regular locus of `X_∅ = X` is empty and
`X_α` is a manifold of dimension `d + dim E_α = 0`. So a nonempty space can carry an atlas of
negative virtual dimension, although it carries none whose expected dimensions `d + m_I` are all
negative (`TauCeti.ImplicitAtlas.isEmpty_of_forall_neg`). -/
noncomputable def obstructedPointAtlas :
    ImplicitAtlas (fun _ : Unit ↦ Unit) (fun _ ↦ ℝ) (fun _ ↦ Representation.trivial ℝ Unit ℝ)
      (PointThickening (EuclideanSpace ℝ (Fin 0)) 0) (pointAct 1 fun _ ↦ rfl)
      (PointThickening (EuclideanSpace ℝ (Fin 0)) 0 ∅) (-1) :=
  pointAtlas (Representation.trivial ℝ Unit ℝ) 1 0 continuous_const (fun _ _ ↦ by simp)
    (fun _ ↦ iff_of_true rfl (Subsingleton.elim _ _)) 0 (by simp)

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.obstructedPointAtlas` is zero. -/
@[simp]
theorem kuranishi_obstructedPointAtlas :
    obstructedPointAtlas.kuranishi = pointKuranishi 0 (0 : EuclideanSpace ℝ (Fin 0) → ℝ) :=
  (rfl)

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.obstructedPointAtlas` is everything for
`I = {α}` and empty for `I = ∅`. -/
theorem regLocus_obstructedPointAtlas (I : Finset Unit) :
    obstructedPointAtlas.regLocus I = {_x | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.obstructedPointAtlas` is empty. -/
@[simp]
theorem regLocus_obstructedPointAtlas_empty : obstructedPointAtlas.regLocus ∅ = ∅ :=
  regLocus_pointAtlas_empty ..

/-- The footprint maps of `TauCeti.ImplicitAtlas.obstructedPointAtlas` keep the point of
`ℝ⁰`. -/
@[simp]
theorem coe_footprintMap_obstructedPointAtlas {I J : Finset Unit} (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ ℝ) obstructedPointAtlas.kuranishi I J) :
    (obstructedPointAtlas.footprintMap h x : EuclideanSpace ℝ (Fin 0)) =
      ((x : PointThickening (EuclideanSpace ℝ (Fin 0)) 0 J) : EuclideanSpace ℝ (Fin 0)) :=
  (rfl)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.obstructedPointAtlas` is the whole point. -/
@[simp]
theorem footprint_obstructedPointAtlas_singleton : obstructedPointAtlas.footprint {()} = univ :=
  footprint_pointAtlas_singleton ..

end PointExamples

/-! ### Nontrivial isotropy over `X_∅` -/

section Isotropy

variable {Γ : Type*} [Group Γ] [Finite Γ] [Nontrivial Γ] {Y : Type*} [TopologicalSpace Y]
  [T2Space Y] {y₀ : Y} {E : Unit → Type*} [∀ α, NormedAddCommGroup (E α)]
  [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
  {ρ : ∀ α, Representation ℝ Γ (E α)} {X : Type*} [TopologicalSpace X] {d : ℤ}
  {σ : Γ →* (Y ≃ₜ Y)} {hσ : ∀ g, σ g y₀ = y₀}

/-- **A nontrivial isotropy group forbids a regular `X_∅`.** Let a nontrivial finite group `Γ`
act on the thickenings `X_∅ = {y₀}` and `X_α = Y` of a single-chart atlas on a point, through an
action on `Y` fixing `y₀`. In every implicit atlas with these thickenings and this action whose
Kuranishi map `s_α` vanishes at `y₀`, the regular locus of `X_∅` is empty. Indeed `y₀` lies in
the zero set `Z_∅α` and is fixed by `Γ_α`, so a regular point of `X_∅` would contradict the
freeness of `Γ_α` over `ψ_∅α⁻¹(X_∅^reg)`. This is why the regular loci of
`TauCeti.ImplicitAtlas.reflectionAtlas` and `TauCeti.ImplicitAtlas.ineffectivePointAtlas` cannot
be enlarged to all of `X_∅`. -/
theorem regLocus_empty_eq_empty_of_kuranishi_eq_zero
    (𝒜 : ImplicitAtlas (fun _ : Unit ↦ Γ) E ρ (PointThickening Y y₀) (pointAct σ hσ) X d)
    (h₀ : 𝒜.kuranishi {()} ⟨(), Finset.mem_singleton_self _⟩
      ⟨y₀, fun h ↦ ((Finset.singleton_nonempty _).ne_empty h).elim⟩ = 0) :
    𝒜.regLocus ∅ = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨g, hg⟩ := exists_ne (1 : Γ)
  let z : kuranishiZeroSet 𝒜.kuranishi ∅ {()} :=
    ⟨⟨y₀, fun h ↦ ((Finset.singleton_nonempty _).ne_empty h).elim⟩,
      mem_kuranishiZeroSet.2 fun ⟨⟨⟩, _⟩ _ ↦ h₀⟩
  have hz : 𝒜.footprintMap (Finset.empty_subset _) z = x :=
    Subtype.ext (((𝒜.footprintMap _ z).property rfl).trans (x.property rfl).symm)
  have h₁ := 𝒜.eq_one_of_act_eq (Finset.empty_subset _) z (hz ▸ hx) (fun _ ↦ g)
    (funext fun α ↦ (Finset.notMem_empty _ α.property).elim)
    (Subtype.ext (by rw [coe_pointAct_apply]; exact hσ _))
  exact hg (congrFun h₁ ⟨(), Finset.mem_singleton_self _⟩)

end Isotropy

end TauCeti.ImplicitAtlas
