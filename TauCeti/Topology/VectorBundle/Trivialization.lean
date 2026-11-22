/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Trivializations over the whole base

A trivialization `e` of a fibre bundle `E` whose base set is the whole base is a homeomorphism
`E ≃ₜ B × F` (`Bundle.Trivialization.toHomeomorphOfBaseSetEqUniv`), which is `e` with inverse
the partial inverse of `e` (`Bundle.Trivialization.coe_toHomeomorphOfBaseSetEqUniv`,
`Bundle.Trivialization.coe_toHomeomorphOfBaseSetEqUniv_symm`).
Read through `Bundle.Trivial.homeomorphProd`, it is a homeomorphism of total spaces
`E ≃ₜ TotalSpace F (Bundle.Trivial B F)` onto the trivial bundle
(`Bundle.Trivialization.homeomorphTrivial`). It covers the identity of the base, sends `v` to the
fibre coordinate of `e v`, and its inverse is the partial inverse of `e`
(`Bundle.Trivialization.homeomorphTrivial_apply`,
`Bundle.Trivialization.homeomorphTrivial_symm_apply`). For a linear trivialization of a
vector bundle over a nontrivially normed field `𝕜`, on the fibre over `b` it is the continuous
linear equivalence `e.continuousLinearEquivAt 𝕜 b`, with inverse its symmetric
(`Bundle.Trivialization.homeomorphTrivial_apply_eq_continuousLinearEquivAt`,
`Bundle.Trivialization.homeomorphTrivial_symm_apply_eq_continuousLinearEquivAt`).

For scalar coordinates `q : F ≃L[𝕜] 𝕜` of a rank-one model,
`Bundle.Trivialization.scalarCoordChange` computes the actual scalar transition. Its
application, nonvanishing, identity and cocycle laws follow from the native linear changes.

More generally, any linear trivialization sends a vector over its base set to a nonzero vector
exactly when the vector is nonzero (`Bundle.Trivialization.snd_apply_ne_zero_iff`), and likewise
for its inverse over the base set (`Bundle.Trivialization.symm_apply_ne_zero_iff`); both commute
with scalar multiplication over the base set (`Bundle.Trivialization.snd_apply_mk_smul`,
`Bundle.Trivialization.symm_apply_smul`). Near a point whose image under a map continuous there
lies in the base set, a linear pretrivialization, in particular a linear trivialization, carries a
fibrewise operation on sections along that map to an operation on their coordinates, provided every
linear equivalence from a fibre to the model fibre carries the first operation to the second; the
sum and the difference are examples
(`Bundle.Pretrivialization.snd_apply_mk_op_eventuallyEq_and_eq`). Over the base set, the
fibrewise linear inverse `e.symmₗ R b` of a linear trivialization is the inverse of the fibrewise
linear equivalence (`Bundle.Trivialization.coe_linearEquivAt_symm`), hence injective
(`Bundle.Trivialization.symmₗ_injective`). For two linear
trivializations whose base sets contain `b`, the fibre equivalence `E_b ≃ F` of the second is that
of the first followed by the coordinate change from the first to the second
(`Bundle.Trivialization.continuousLinearEquivAt_trans_coordChangeL`). Linear coordinate changes
satisfy the identity and cocycle laws over the relevant base sets
(`Bundle.Trivialization.coordChangeL_same_apply`,
`Bundle.Trivialization.coordChangeL_coordChangeL_apply`), equal the identity outside the overlap
(`Bundle.Trivialization.coordChangeL_of_notMem`), and send the coordinate of a point in
the first trivialization to its coordinate in the second
(`Bundle.Trivialization.coordChangeL_apply_snd`); the fibrewise inverse of the second, after the
coordinate change from the first, is the fibrewise inverse of the first
(`Bundle.Trivialization.symmL_coordChangeL`). Convergence in the total space of a vector bundle
is convergence of base points and of fibre coordinates in any linear trivialization over the limit
point (`Bundle.Trivialization.tendsto_mk_nhds_mk_iff`). Over the base set, pulling continuous
linear maps on the model fibre back to a fibre through a linear trivialization is injective
(`Bundle.Trivialization.injective_comp_continuousLinearMapAt`).

Transport through a preferred fibre equivalence also shows that a family spanning a fibre with
nontrivial model has a nonzero member (`VectorBundle.exists_ne_zero_of_span_range_eq_top`).
The family and fibre may be infinite, with no continuity or manifold assumption on the family.

We also record the product trivialization's fibrewise inverse
(`Bundle.Trivialization.prod_symm_apply'`), the preferred trivialization of a direct-sum fibre
bundle (`FiberBundle.trivializationAt_prod`), and scalar restriction of linear trivializations
and coordinate changes (`Bundle.Trivialization.isLinear_restrictScalars`,
`Bundle.Trivialization.restrictScalars_coordChangeL`). A trivialization that is linear over two
fields has the same continuous linear map at every point over either field
(`Bundle.Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt`); when the two
scalar actions are compatible, the one over `𝕜'` is the scalar restriction of the one over `𝕜`,
including its zero extension off the base set
(`Bundle.Trivialization.restrictScalars_continuousLinearMapAt`). Subspaces of the fibres of a
vector bundle with finite-dimensional model fibre are closed (`VectorBundle.isClosed_submodule`).

Reconstruction at equal base points agrees with the equality cast between fibres
(`Bundle.Trivialization.symmL_continuousLinearMapAt_eq_cast`).
-/

public section

noncomputable section

open Bundle
open scoped Topology

namespace Bundle.Pretrivialization

variable {B : Type*} [TopologicalSpace B] (R : Type*) [Semiring R] {F : Type*} [TopologicalSpace F]
  [AddCommMonoid F] [Module R F] {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  (e : Pretrivialization F (π F E)) [e.IsLinear R]

/-- Let `e` be a pretrivialization that is linear on the fibres, such as a linear trivialization
read through `Bundle.Trivialization.toPretrivialization`, and `b` a map continuous at `x₀` within
`u`, with `b x₀` in the base set of `e`. For a fibrewise operation `op` that every linear
equivalence `E y ≃ₗ[R] F` carries to `opF`, the `e`-coordinate of `op (s x) (t x)` is `opF` of the
`e`-coordinates of `s x` and `t x`, both for `x` near `x₀` within `u` and at `x₀` itself. Only
linear equivalences are needed because over the base set `e` is the linear equivalence
`e.linearEquivAt R`. No topology on the total space is needed. This is the coordinate step in the
regularity of fibrewise sums and differences of sections along a map. -/
theorem snd_apply_mk_op_eventuallyEq_and_eq {X : Type*} [TopologicalSpace X] {b : X → B}
    {s t : ∀ x, E (b x)} {u : Set X} {x₀ : X} {op : ∀ y, E y → E y → E y} {opF : F → F → F}
    (hop : ∀ y (g : E y ≃ₗ[R] F) v w, g (op y v w) = opF (g v) (g w))
    (hb : ContinuousWithinAt b u x₀) (hx₀ : b x₀ ∈ e.baseSet) :
    (fun x ↦ (e ⟨b x, op (b x) (s x) (t x)⟩).2) =ᶠ[𝓝[u] x₀]
        (fun x ↦ opF (e ⟨b x, s x⟩).2 (e ⟨b x, t x⟩).2) ∧
      (e ⟨b x₀, op (b x₀) (s x₀) (t x₀)⟩).2 = opF (e ⟨b x₀, s x₀⟩).2 (e ⟨b x₀, t x₀⟩).2 := by
  have key {y : B} (hy : y ∈ e.baseSet) (v w : E y) :
      (e ⟨y, op y v w⟩).2 = opF (e ⟨y, v⟩).2 (e ⟨y, w⟩).2 := by
    simpa only [linearEquivAt_apply] using hop y (e.linearEquivAt R y hy) v w
  refine ⟨?_, key hx₀ _ _⟩
  filter_upwards [hb.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx₀)] with x hx
  exact key hx _ _

end Bundle.Pretrivialization

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))

/-- A trivialization over the whole base is a homeomorphism `E ≃ₜ B × F` of the total space onto
the product. -/
def toHomeomorphOfBaseSetEqUniv (he : e.baseSet = Set.univ) : TotalSpace F E ≃ₜ B × F :=
  e.toHomeomorphOfSourceEqUnivTargetEqUniv (by simp [e.source_eq, he])
    (by simp [e.target_eq, he])

/-- The homeomorphism of a trivialization over the whole base is the trivialization. -/
@[simp]
theorem coe_toHomeomorphOfBaseSetEqUniv (he : e.baseSet = Set.univ) :
    ⇑(e.toHomeomorphOfBaseSetEqUniv he) = e := by
  rw [toHomeomorphOfBaseSetEqUniv,
    OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv_apply, coe_coe]

/-- The inverse of the homeomorphism of a trivialization over the whole base is the partial
inverse of the trivialization. -/
@[simp]
theorem coe_toHomeomorphOfBaseSetEqUniv_symm (he : e.baseSet = Set.univ) :
    ⇑(e.toHomeomorphOfBaseSetEqUniv he).symm = e.toOpenPartialHomeomorph.symm := by
  rw [toHomeomorphOfBaseSetEqUniv,
    OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv_symm_apply]

/-- The homeomorphism `E ≃ₜ B × F` of a trivialization over the whole base, read as a
homeomorphism onto the total space of the trivial bundle. -/
def homeomorphTrivial (he : e.baseSet = Set.univ) :
    TotalSpace F E ≃ₜ TotalSpace F (Bundle.Trivial B F) :=
  (e.toHomeomorphOfBaseSetEqUniv he).trans (Bundle.Trivial.homeomorphProd B F).symm

@[simp]
theorem homeomorphTrivial_apply (he : e.baseSet = Set.univ) (v : TotalSpace F E) :
    e.homeomorphTrivial he v = TotalSpace.mk' F v.proj (e v).2 := by
  rw [homeomorphTrivial, Homeomorph.trans_apply, Homeomorph.symm_apply_eq]
  exact Prod.ext (e.coe_fst' (he ▸ Set.mem_univ v.proj)) rfl

@[simp]
theorem homeomorphTrivial_symm_apply (he : e.baseSet = Set.univ)
    (w : TotalSpace F (Bundle.Trivial B F)) :
    (e.homeomorphTrivial he).symm w = e.toPartialHomeomorph.symm (w.proj, w.snd) := by
  rfl

section Linear

variable (R : Type*) [Semiring R] {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module R (E b)] (e : Trivialization F (π F E)) [e.IsLinear R]

include R in
/-- A linear trivialization sends a vector over its base set to a nonzero vector exactly when the
vector is nonzero. -/
theorem snd_apply_ne_zero_iff {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    (e v).2 ≠ 0 ↔ v.snd ≠ 0 := by
  simpa only [linearEquivAt_apply] using (e.linearEquivAt R v.proj hv).map_ne_zero_iff

include R in
/-- Over its base set, the inverse of a linear trivialization sends a vector of the model fibre to
a nonzero vector exactly when the vector is nonzero. -/
theorem symm_apply_ne_zero_iff {b : B} (hb : b ∈ e.baseSet) {w : F} :
    e.symm b w ≠ 0 ↔ w ≠ 0 := by
  simpa only [linearEquivAt_symm_apply] using (e.linearEquivAt R b hb).symm.map_ne_zero_iff

variable {R} in
/-- Over its base set, a linear trivialization commutes with scalar multiplication in the fibre. -/
theorem snd_apply_mk_smul {b : B} (hb : b ∈ e.baseSet) (c : R) (v : E b) :
    (e ⟨b, c • v⟩).2 = c • (e ⟨b, v⟩).2 := by
  simpa only [linearEquivAt_apply] using (e.linearEquivAt R b hb).map_smul c v

variable {R} in
/-- Over its base set, the inverse of a linear trivialization commutes with scalar
multiplication. -/
theorem symm_apply_smul {b : B} (hb : b ∈ e.baseSet) (c : R) (w : F) :
    e.symm b (c • w) = c • e.symm b w := by
  simpa only [linearEquivAt_symm_apply] using (e.linearEquivAt R b hb).symm.map_smul c w

/-- Over the base set, the fibrewise linear inverse of a linear trivialization is the inverse of
its fibrewise linear equivalence. -/
theorem coe_linearEquivAt_symm {b : B} (hb : b ∈ e.baseSet) :
    ((e.linearEquivAt R b hb).symm : F →ₗ[R] E b) = e.symmₗ R b :=
  LinearMap.ext fun u ↦ by rw [LinearEquiv.coe_coe, linearEquivAt_symm_apply, symmₗ_apply e hb]

/-- Over the base set, the fibrewise linear inverse of a linear trivialization is injective. -/
theorem symmₗ_injective {b : B} (hb : b ∈ e.baseSet) : Function.Injective (e.symmₗ R b) := by
  rw [← e.coe_linearEquivAt_symm R hb, LinearEquiv.coe_coe]
  exact (e.linearEquivAt R b hb).symm.injective

/-- Outside the overlap of two linear trivializations, their linear coordinate change is the
identity equivalence. -/
@[simp]
theorem coordChangeL_of_notMem (e' : Trivialization F (π F E)) [e'.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet ∩ e'.baseSet) :
    e.coordChangeL R e' b = ContinuousLinearEquiv.refl R F := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  -- Mathlib defines `Bundle.Trivialization.coordChangeL` via a `dite` on
  -- `b ∈ e.baseSet ∩ e'.baseSet` whose off-overlap branch is `LinearEquiv.refl R F`.
  dsimp only [coordChangeL]
  exact dite_eq_right hb

end Linear

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]

section FiberBundle

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] (e : Trivialization F (π F E))
  [e.IsLinear 𝕜]

/-- Reconstruction in a common chart agrees with the equality cast between equal fibres. -/
theorem symmL_continuousLinearMapAt_eq_cast {x₀ x₁ : B} (h : x₀ = x₁)
    (he : x₀ ∈ e.baseSet) (v : E x₀) :
    e.symmL 𝕜 x₁ (e.continuousLinearMapAt 𝕜 x₀ v) = cast (congrArg E h) v := by
  subst x₁
  exact e.symmL_continuousLinearMapAt he v

theorem homeomorphTrivial_apply_eq_continuousLinearEquivAt (he : e.baseSet = Set.univ)
    (v : TotalSpace F E) :
    e.homeomorphTrivial he v = TotalSpace.mk' F v.proj (e.continuousLinearEquivAt 𝕜 v.proj
      (he ▸ Set.mem_univ _) v.snd) :=
  congrArg (Bundle.Trivial.homeomorphProd B F).symm
    (e.apply_eq_prod_continuousLinearEquivAt 𝕜 v.proj (he ▸ Set.mem_univ _) v.snd)

theorem homeomorphTrivial_symm_apply_eq_continuousLinearEquivAt (he : e.baseSet = Set.univ)
    (w : TotalSpace F (Bundle.Trivial B F)) :
    (e.homeomorphTrivial he).symm w = TotalSpace.mk' F w.proj
      ((e.continuousLinearEquivAt 𝕜 w.proj (he ▸ Set.mem_univ _)).symm w.snd) := by
  rw [Homeomorph.symm_apply_eq, homeomorphTrivial_apply_eq_continuousLinearEquivAt 𝕜]
  exact congrArg (TotalSpace.mk' F w.proj) (ContinuousLinearEquiv.apply_symm_apply _ _).symm

/-- **Convergence in a vector bundle, read in a linear trivialization.** Vectors `ξ i` over points
`x i` converge in the total space to a vector `ξ₀` over a point `x₀` of the base set of `e`
exactly when `x i → x₀` and the fibre coordinates `e (x i) (ξ i)` converge to those of `ξ₀`. -/
theorem tendsto_mk_nhds_mk_iff {ι : Type*} {l : Filter ι} {x : ι → B} {x₀ : B}
    {ξ : ∀ i, E (x i)} {ξ₀ : E x₀} (hx₀ : x₀ ∈ e.baseSet) :
    Filter.Tendsto (fun i ↦ TotalSpace.mk' F (x i) (ξ i)) l (𝓝 (TotalSpace.mk' F x₀ ξ₀)) ↔
      Filter.Tendsto x l (𝓝 x₀) ∧ Filter.Tendsto (fun i ↦ e.continuousLinearMapAt 𝕜 (x i) (ξ i))
        l (𝓝 (e.continuousLinearMapAt 𝕜 x₀ ξ₀)) := by
  rw [e.tendsto_nhds_iff (e.mem_source.2 hx₀)]
  refine and_congr_right fun hx ↦ ?_
  -- Eventually `x i` lies in the base set, where the fibre coordinate is `continuousLinearMapAt`.
  have hb : ∀ᶠ i in l, x i ∈ e.baseSet := hx (e.open_baseSet.mem_nhds hx₀)
  rw [e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx₀]
  exact Filter.tendsto_congr' (hb.mono fun i hi ↦
    (e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hi _).symm)

/-- Over the base set of a linear trivialization `e`, pulling continuous linear maps on the model
fibre back to the fibre over `b` through `e` is injective. -/
theorem injective_comp_continuousLinearMapAt {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {b : B} (hb : b ∈ e.baseSet) :
    Function.Injective fun c : F →L[𝕜] G ↦ c ∘L e.continuousLinearMapAt 𝕜 b := by
  intro c c' h
  ext v
  simpa [e.continuousLinearMapAt_symmL hb] using DFunLike.congr_fun h (e.symmL 𝕜 b v)

variable (e' : Trivialization F (π F E)) [e'.IsLinear 𝕜] {b : B}

/-- **The fibre equivalences of two trivializations differ by the coordinate change**: for linear
trivializations `e` and `e'` whose base sets contain `b`, the equivalence `E_b ≃ F` given by `e`,
followed by the coordinate change from `e` to `e'`, is the one given by `e'`. -/
theorem continuousLinearEquivAt_trans_coordChangeL (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) :
    (e.continuousLinearEquivAt 𝕜 b hb).trans (e.coordChangeL 𝕜 e' b) =
      e'.continuousLinearEquivAt 𝕜 b hb' := by
  rw [← comp_continuousLinearEquivAt_eq_coord_change e e' ⟨hb, hb'⟩]
  ext x
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- Over the intersection of the base sets of two linear trivializations `e'` and `e`, the
fibrewise inverse `e.symmL` after the coordinate change from `e'` to `e` is `e'.symmL`. -/
theorem symmL_coordChangeL (hb : b ∈ e'.baseSet ∩ e.baseSet) (v : F) :
    e.symmL 𝕜 b (e'.coordChangeL 𝕜 e b v) = e'.symmL 𝕜 b v := by
  rw [e'.coordChangeL_apply e hb, e.symmL_apply hb.2, e.symm_apply_apply_mk hb.2,
    e'.symmL_apply hb.1]

end FiberBundle

section CoordChangeL

variable (e : Trivialization F (π F E)) [e.IsLinear 𝕜]

/-- The coordinate change from a linear trivialization to itself is the identity over its base
set. -/
@[simp]
theorem coordChangeL_same_apply {b : B} (hb : b ∈ e.baseSet) (v : F) :
    e.coordChangeL 𝕜 e b v = v := by
  rw [e.coordChangeL_apply' e ⟨hb, hb⟩]
  exact e.coordChange_same_apply hb v

variable (e' : Trivialization F (π F E)) [e'.IsLinear 𝕜] {b : B}

/-- **Cocycle law for linear coordinate changes**: over the intersection of three base sets, the
coordinate change from `e` to `e'` followed by the one from `e'` to `e''` is the coordinate change
from `e` to `e''`. -/
@[simp]
theorem coordChangeL_coordChangeL_apply (e'' : Trivialization F (π F E)) [e''.IsLinear 𝕜]
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) (hb'' : b ∈ e''.baseSet) (v : F) :
    e'.coordChangeL 𝕜 e'' b (e.coordChangeL 𝕜 e' b v) = e.coordChangeL 𝕜 e'' b v := by
  rw [e'.coordChangeL_apply' e'' ⟨hb', hb''⟩, e.coordChangeL_apply' e' ⟨hb, hb'⟩,
    e.coordChangeL_apply' e'' ⟨hb, hb''⟩]
  exact e.coordChange_coordChange e' e'' hb hb' v

/-- The linear coordinate change from `e` to `e'` sends the coordinate of a point in `e` to its
coordinate in `e'`. -/
theorem coordChangeL_apply_snd {p : TotalSpace F E} (hb : p.proj ∈ e.baseSet)
    (hb' : p.proj ∈ e'.baseSet) : e.coordChangeL 𝕜 e' p.proj (e p).2 = (e' p).2 := by
  rw [e.coordChangeL_apply' e' ⟨hb, hb'⟩]
  exact e.coordChange_apply_snd e' hb

end CoordChangeL

end Bundle.Trivialization

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B]

/-- Over `e₁.baseSet ∩ e₂.baseSet`, the fibrewise inverse `(e₁.prod e₂).symm` acts componentwise. -/
theorem prod_symm_apply' {F₁ F₂ : Type*} {E₁ E₂ : B → Type*} [TopologicalSpace F₁]
    [TopologicalSpace F₂] [TopologicalSpace (TotalSpace F₁ E₁)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)]
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂)) {x : B}
    (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) (w : F₁ × F₂) :
    (e₁.prod e₂).symm x w = (e₁.symm x w.1, e₂.symm x w.2) :=
  (TotalSpace.mk_inj (F := F₁ × F₂) (E := E₁ ×ᵇ E₂)).mp <|
    ((e₁.prod e₂).mk_symm hx w).trans (e₁.prod_symm_apply e₂ x w.1 w.2)

/-- The preferred trivialization of `E₁ ×ᵇ E₂` at `b` is `(trivializationAt F₁ E₁ b).prod
(trivializationAt F₂ E₂ b)`. -/
theorem _root_.FiberBundle.trivializationAt_prod (F₁ : Type*) (E₁ : B → Type*) (F₂ : Type*)
    (E₂ : B → Type*) [TopologicalSpace F₁] [TopologicalSpace F₂]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)] [∀ x, TopologicalSpace (E₁ x)]
    [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] (b : B) :
    FiberBundle.trivializationAt (F₁ × F₂) (E₁ ×ᵇ E₂) b =
      (FiberBundle.trivializationAt F₁ E₁ b).prod (FiberBundle.trivializationAt F₂ E₂ b) :=
  -- `FiberBundle.prod` defines `trivializationAt'` directly as `(trivializationAt F₁ E₁ b).prod …`.
  (rfl)

/-- A `𝕜`-linear trivialization is also `𝕜'`-linear for any compatible scalar action `𝕜'`. -/
theorem isLinear_restrictScalars (𝕜' 𝕜 : Type*) [Semiring 𝕜'] [Semiring 𝕜] [SMul 𝕜' 𝕜]
    {F : Type*} {E : B → Type*} [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
    [AddCommMonoid F] [Module 𝕜' F] [Module 𝕜 F] [IsScalarTower 𝕜' 𝕜 F]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, IsScalarTower 𝕜' 𝕜 (E x)] (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    e.IsLinear 𝕜' where
  linear b hb :=
    { map_add := (e.linear 𝕜 hb).map_add
      map_smul r v := by rw [← smul_one_smul 𝕜 r v, (e.linear 𝕜 hb).map_smul, smul_one_smul] }

/-- Restricting scalars of a `𝕜`-linear coordinate change recovers the `𝕜'`-linear coordinate
change. -/
theorem restrictScalars_coordChangeL (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜' 𝕜]
    {F : Type*} {E : B → Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F]
    [IsScalarTower 𝕜' 𝕜 F] [TopologicalSpace (TotalSpace F E)]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)]
    (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜'] [e'.IsLinear 𝕜'] [e.IsLinear 𝕜]
    [e'.IsLinear 𝕜] {b : B} :
    (e.coordChangeL 𝕜 e' b : F →L[𝕜] F).restrictScalars 𝕜' = e.coordChangeL 𝕜' e' b := by
  by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
  · ext v; simp [Trivialization.coordChangeL_apply' e e' hb]
  · ext v; simp [Trivialization.coordChangeL, hb]

/-- A trivialization that is linear over both `𝕜'` and `𝕜` has the same continuous linear map at
every point over either field. In particular the `𝕜'`-linear map of a trivialization of a
`VectorBundle 𝕜 F E`, restricted to `𝕜'` by `VectorBundle.restrictScalars`, is `𝕜`-linear. -/
theorem coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] {F : Type*} {E : B → Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle F E] (e : Trivialization F (π F E))
    [e.IsLinear 𝕜'] [e.IsLinear 𝕜] (b : B) :
    ⇑(e.continuousLinearMapAt 𝕜' b) = e.continuousLinearMapAt 𝕜 b := by
  ext v
  simp only [continuousLinearMapAt_apply, coe_linearMapAt]

/-- The fibre-coordinate map of a trivialization over `𝕜'` is the scalar restriction of the
fibre-coordinate map over `𝕜`, including its zero extension off the base set. Only compatibility
of the two scalar actions is needed, not a field extension. -/
@[simp]
theorem restrictScalars_continuousLinearMapAt (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] {F : Type*} {E : B → Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, LinearMap.CompatibleSMul (E x) F 𝕜' 𝕜]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜'] [e.IsLinear 𝕜] (b : B) :
    (e.continuousLinearMapAt 𝕜 b).restrictScalars 𝕜' = e.continuousLinearMapAt 𝕜' b :=
  DFunLike.coe_injective
    (coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt 𝕜' 𝕜 e b).symm

end Bundle.Trivialization

namespace VectorBundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (E : B → Type*)
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

/-- The fibres of a topological vector bundle are topological additive groups: the preferred
trivialization at `b` restricts to a linear homeomorphism of the fibre onto the model fibre. -/
protected theorem isTopologicalAddGroup [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
    [VectorBundle 𝕜 F E] (b : B) : IsTopologicalAddGroup (E b) :=
  let e := (trivializationAt F E b).continuousLinearEquivAt 𝕜 b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  e.toHomeomorph.isInducing.isTopologicalAddGroup e

/-- The fibres of a topological vector bundle have continuous scalar multiplication: the preferred
trivialization at `b` restricts to a linear homeomorphism of the fibre onto the model fibre. -/
protected theorem continuousSMul [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [VectorBundle 𝕜 F E] (b : B) : ContinuousSMul 𝕜 (E b) :=
  let e := (trivializationAt F E b).continuousLinearEquivAt 𝕜 b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  e.toHomeomorph.isInducing.continuousSMul continuous_id fun {c x} ↦ e.map_smul c x

/-- A subspace of a fibre of a topological vector bundle with finite-dimensional model fibre over a
complete field is closed: the preferred trivialization at `b` maps it onto a finite-dimensional
subspace of the model fibre. -/
theorem isClosed_submodule [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [∀ x, AddCommGroup (E x)]
    [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E] (b : B) (L : Submodule 𝕜 (E b)) :
    IsClosed (L : Set (E b)) := by
  let e := (trivializationAt F E b).continuousLinearEquivAt 𝕜 b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  rw [← e.toHomeomorph.isClosed_image]
  exact (L.map (e : E b →ₗ[𝕜] F)).isClosed_of_finiteDimensional

end VectorBundle

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  (e e' : Trivialization F (π F V)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜]

/-- The scalar change from a rank-one coordinate of `e` to one of `e'`. The coordinate
isomorphisms allow any one-dimensional normed model, with no normalization of its basis. -/
def scalarCoordChange (q q' : F ≃L[𝕜] 𝕜) (x : B) : 𝕜 :=
  q' (e.coordChangeL 𝕜 e' x (q.symm 1))

/-- The scalar coefficient is the actual linear coordinate change evaluated at the scalar unit. -/
theorem scalarCoordChange_def (q q' : F ≃L[𝕜] 𝕜) (x : B) :
    e.scalarCoordChange e' q q' x = q' (e.coordChangeL 𝕜 e' x (q.symm 1)) := by rfl

/-- A scalar coordinate change multiplies every coordinate by its value on the unit vector. -/
theorem apply_coordChangeL_eq_scalarCoordChange_mul (q q' : F ≃L[𝕜] 𝕜) (x : B) (v : F) :
    q' (e.coordChangeL 𝕜 e' x v) = e.scalarCoordChange e' q q' x * q v := by
  have hv : q v • q.symm 1 = v := by
    rw [← map_smul, smul_eq_mul, mul_one, q.symm_apply_apply]
  calc
    q' (e.coordChangeL 𝕜 e' x v) = q' (e.coordChangeL 𝕜 e' x (q v • q.symm 1)) := by rw [hv]
    _ = q v * q' (e.coordChangeL 𝕜 e' x (q.symm 1)) := by rw [map_smul, map_smul, smul_eq_mul]
    _ = _ := mul_comm _ _

/-- Scalar frame changes never vanish. -/
theorem scalarCoordChange_ne_zero (q q' : F ≃L[𝕜] 𝕜) (x : B) :
    e.scalarCoordChange e' q q' x ≠ 0 := by
  simp [scalarCoordChange]

/-- Reading a vector in the second frame multiplies its first scalar coordinate by the
actual transition scalar. -/
theorem scalarCoordChange_mul_coordinate [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
    (q q' : F ≃L[𝕜] 𝕜) {x : B}
    (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) (v : V x) :
    e.scalarCoordChange e' q q' x * q (e.continuousLinearMapAt 𝕜 x v) =
      q' (e'.continuousLinearMapAt 𝕜 x v) := by
  rw [← apply_coordChangeL_eq_scalarCoordChange_mul]
  rw [continuousLinearMapAt_apply_of_mem 𝕜 e hx v,
    continuousLinearMapAt_apply_of_mem 𝕜 e' hx' v,
    e.coordChangeL_apply_snd 𝕜 e' (p := ⟨x, v⟩) hx hx']

/-- The scalar coordinate change of a frame with itself is one on its base set. -/
@[simp]
theorem scalarCoordChange_self (q : F ≃L[𝕜] 𝕜) {x : B} (hx : x ∈ e.baseSet) :
    e.scalarCoordChange e q q x = 1 := by
  rw [scalarCoordChange, e.coordChangeL_same_apply 𝕜 hx, q.apply_symm_apply]

/-- Scalar coordinate changes satisfy the cocycle law on triple intersections. -/
theorem scalarCoordChange_mul_scalarCoordChange (e'' : Trivialization F (π F V)) [e''.IsLinear 𝕜]
    (q q' q'' : F ≃L[𝕜] 𝕜) {x : B}
    (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) (hx'' : x ∈ e''.baseSet) :
    e'.scalarCoordChange e'' q' q'' x * e.scalarCoordChange e' q q' x =
      e.scalarCoordChange e'' q q'' x := by
  simpa only [scalarCoordChange, e.coordChangeL_coordChangeL_apply 𝕜 e' e'' hx hx' hx''] using
    (e'.apply_coordChangeL_eq_scalarCoordChange_mul e'' q' q'' x
      (e.coordChangeL 𝕜 e' x (q.symm 1))).symm

end Bundle.Trivialization

namespace VectorBundle

open Set

variable {𝕜 M : Type*} (F : Type*) [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- A family spanning a fiber with nontrivial model contains a nonzero member.
Neither the index set nor the fiber needs to be finite, and no regularity is required. -/
theorem exists_ne_zero_of_span_range_eq_top [Nontrivial F] {x : M} {ι : Type*}
    {v : ι → V x} (hspan : Submodule.span 𝕜 (range v) = ⊤) : ∃ i, v i ≠ 0 := by
  have : Nontrivial (V x) := (continuousLinearEquivAt 𝕜 F V x).toEquiv.nontrivial
  by_contra! hall
  exact top_ne_bot (hspan.symm.trans (Submodule.span_eq_bot.mpr (forall_mem_range.mpr hall)))

end VectorBundle
