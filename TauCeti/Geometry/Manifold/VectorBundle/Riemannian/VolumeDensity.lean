/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Analysis.InnerProductSpace.Gram.VolumeDensity
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
public import TauCeti.LinearAlgebra.BilinearForm.DetRatio

/-!
# Relative volume densities on finite-rank vector bundles

The relative volume density of two fibre metrics is the positive square root of their
basis-independent Gram determinant ratio. Its pointwise definition needs neither regularity
nor a manifold structure on the base. Continuous metrics have continuous relative density;
smooth metric families have smooth density wherever their inner-product sections are smooth.

## Main results

* `Bundle.RiemannianMetric.relativeVolumeDensity_pos`: positivity of the relative density.
* `Module.Basis.relativeVolumeDensity_eq_sqrt_det_of_orthonormal`: the orthonormal-basis formula.
* `Bundle.ContMDiffRiemannianMetric.contMDiff_relativeVolumeDensity`: smoothness of the density.
* `Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity_rescale_right` and
  `Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity_rescale_left`: conformal rescaling laws.

The tangent-bundle measure comparison is developed in
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44 and the discussion of Riemannian densities following it.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace Bundle.RiemannianMetric

variable {B : Type*} {V : B → Type*} [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)]

/-- The **relative volume density** of a Riemannian metric `g'` with respect to a Riemannian
metric `g` at `x`: the square root of the ratio of the Gram determinants of `g'_x` and `g_x` in
any basis of `V x`. -/
def relativeVolumeDensity (g g' : RiemannianMetric V) (x : B) : ℝ :=
  √(LinearMap.BilinForm.detRatio (g.inner x).toBilinForm (g'.inner x).toBilinForm)

variable {g g' : RiemannianMetric V}

variable (g g') in
/-- The definition of the relative volume density. -/
theorem relativeVolumeDensity_def (x : B) :
    relativeVolumeDensity g g' x =
      √(LinearMap.BilinForm.detRatio (g.inner x).toBilinForm (g'.inner x).toBilinForm) :=
  (rfl)

/-- The relative volume density in a basis `b` of `V x`. -/
theorem _root_.Module.Basis.relativeVolumeDensity_eq_sqrt_div {x : B} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (V x)) :
    relativeVolumeDensity g g' x =
      √((Matrix.of fun i j ↦ g'.inner x (b i) (b j)).det /
        (Matrix.of fun i j ↦ g.inner x (b i) (b j)).det) := by
  rw [relativeVolumeDensity, b.bilinFormDetRatio_eq]
  congr 3 <;> ext i j <;> simp [LinearMap.BilinForm.toMatrix_apply]

/-- **The relative volume density in an orthonormal basis.** If `b` is a `g`-orthonormal basis of
`V x`, the relative volume density of `g'` with respect to `g` at `x` is the square root of the
Gram determinant of `g'_x` in `b`. -/
theorem _root_.Module.Basis.relativeVolumeDensity_eq_sqrt_det_of_orthonormal
    {x : B} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (V x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    relativeVolumeDensity g g' x = √(Matrix.of fun i j ↦ g'.inner x (b i) (b j)).det := by
  have hB : LinearMap.BilinForm.toMatrix b (g.inner x).toBilinForm = 1 := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, hb, Matrix.one_apply]
  rw [relativeVolumeDensity_def, b.bilinFormDetRatio_eq_det_bilinFormToMatrix_of_eq_one hB]
  congr 2
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply]

variable (g g') in
/-- The relative volume density is nonnegative. -/
@[simp]
theorem relativeVolumeDensity_nonneg (x : B) : 0 ≤ relativeVolumeDensity g g' x :=
  Real.sqrt_nonneg _

variable (g g') in
/-- The relative volume density is positive. -/
@[simp]
theorem relativeVolumeDensity_pos (x : B) : 0 < relativeVolumeDensity g g' x :=
  Real.sqrt_pos.2 <| LinearMap.BilinForm.detRatio_pos _ _
    (by simpa only [ContinuousLinearMap.toBilinForm_apply] using g.pos x)
    (by simpa only [ContinuousLinearMap.toBilinForm_apply] using g'.pos x)

variable (g) in
/-- The relative volume density of a metric with respect to itself is one. -/
@[simp]
theorem relativeVolumeDensity_self (x : B) : relativeVolumeDensity g g x = 1 := by
  have hpos := Real.sqrt_pos.1 (relativeVolumeDensity_pos g g x)
  rw [relativeVolumeDensity, LinearMap.BilinForm.detRatio_self _
    ((LinearMap.BilinForm.detRatio_ne_zero_iff _ _).1 hpos.ne').1, Real.sqrt_one]

variable (g g') in
/-- The relative volume density never vanishes. -/
@[simp]
theorem relativeVolumeDensity_ne_zero (x : B) : relativeVolumeDensity g g' x ≠ 0 :=
  (relativeVolumeDensity_pos g g' x).ne'

variable (g g') in
/-- Reversing the metrics inverts the relative volume density. -/
theorem inv_relativeVolumeDensity (x : B) :
    (relativeVolumeDensity g g' x)⁻¹ = relativeVolumeDensity g' g x := by
  rw [relativeVolumeDensity_def, relativeVolumeDensity_def, ← Real.sqrt_inv,
    LinearMap.BilinForm.inv_detRatio]

variable (g g') in
/-- The square of the relative volume density is the determinant ratio. -/
theorem relativeVolumeDensity_sq (x : B) :
    relativeVolumeDensity g g' x ^ 2 =
      (g.inner x).toBilinForm.detRatio (g'.inner x).toBilinForm := by
  rw [relativeVolumeDensity_def,
    Real.sq_sqrt (Real.sqrt_pos.1 (relativeVolumeDensity_pos g g' x)).le]

variable (g g') in
/-- The density depends only on the inner products at the given point. -/
theorem relativeVolumeDensity_congr
    {g₁ g₂ : RiemannianMetric V}
    {x : B} (h : g.inner x = g₁.inner x) (h' : g'.inner x = g₂.inner x) :
    relativeVolumeDensity g g' x = relativeVolumeDensity g₁ g₂ x := by
  rw [relativeVolumeDensity_def, relativeVolumeDensity_def, h, h']

/-- A linear equivalence preserving both inner products preserves their relative volume density. -/
theorem relativeVolumeDensity_eq_of_linearEquiv
    {C : Type*} {W : C → Type*} [∀ y, TopologicalSpace (W y)]
    [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)]
    [∀ y, FiniteDimensional ℝ (W y)]
    (g g' : RiemannianMetric V) (h h' : RiemannianMetric W)
    {x : B} {y : C} (e : V x ≃ₗ[ℝ] W y)
    (hg : ∀ v w, g.inner x v w = h.inner y (e v) (e w))
    (hg' : ∀ v w, g'.inner x v w = h'.inner y (e v) (e w)) :
    relativeVolumeDensity g g' x = relativeVolumeDensity h h' y := by
  have hB : (g.inner x).toBilinForm =
      LinearMap.BilinForm.congr e.symm (h.inner y).toBilinForm := by
    ext v w
    simpa only [ContinuousLinearMap.toBilinForm_apply, LinearMap.BilinForm.congr_apply,
      LinearEquiv.symm_symm] using hg v w
  have hB' : (g'.inner x).toBilinForm =
      LinearMap.BilinForm.congr e.symm (h'.inner y).toBilinForm := by
    ext v w
    simpa only [ContinuousLinearMap.toBilinForm_apply, LinearMap.BilinForm.congr_apply,
      LinearEquiv.symm_symm] using hg' v w
  rw [relativeVolumeDensity_def, relativeVolumeDensity_def, hB, hB',
    LinearMap.BilinForm.detRatio_congr]

variable (g g') in
/-- Changing the reference metric multiplies relative volume densities. -/
@[simp]
theorem relativeVolumeDensity_mul_relativeVolumeDensity
    {g'' : RiemannianMetric V} (x : B) :
    relativeVolumeDensity g g' x * relativeVolumeDensity g' g'' x =
      relativeVolumeDensity g g'' x := by
  have hpos := Real.sqrt_pos.1 (relativeVolumeDensity_pos g g' x)
  rw [relativeVolumeDensity_def, relativeVolumeDensity_def, relativeVolumeDensity_def,
    ← Real.sqrt_mul hpos.le, LinearMap.BilinForm.detRatio_mul_detRatio _ _ _
      ((LinearMap.BilinForm.detRatio_ne_zero_iff _ _).1 hpos.ne').2]

section Regularity

variable [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

private def innerInCoordinates (g : RiemannianMetric V) (a x : B) : F →L[ℝ] F →L[ℝ] ℝ :=
  (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ) a
    ⟨x, g.inner x⟩).2

omit [∀ x, FiniteDimensional ℝ (V x)] in
private theorem innerInCoordinates_apply (g : RiemannianMetric V) {a x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) (v w : F) :
    innerInCoordinates g a x v w =
      g.inner x ((trivializationAt F V a).symm x v)
        ((trivializationAt F V a).symm x w) := by
  simp only [innerInCoordinates, hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp

omit [∀ x, FiniteDimensional ℝ (V x)] in
private theorem innerInCoordinates_pos (g : RiemannianMetric V) {a x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) (v : F) (hv : v ≠ 0) :
    0 < innerInCoordinates g a x v v := by
  rw [innerInCoordinates_apply g hx]
  apply g.pos
  simpa only [← Trivialization.linearEquivAt_symm_apply (R := ℝ) _ x hx,
    EmbeddingLike.map_ne_zero_iff] using hv

omit [∀ x, FiniteDimensional ℝ (V x)] in
private theorem metricVolumeDensity_innerInCoordinates_pos [FiniteDimensional ℝ F]
    (g : RiemannianMetric V) {a x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) :
    0 < (Module.finBasis ℝ F).metricVolumeDensity (innerInCoordinates g a x) := by
  apply (Module.finBasis ℝ F).metricVolumeDensity_pos_of_posDef _
    (innerInCoordinates_pos g hx)
  constructor
  intro v w
  simp only [ContinuousLinearMap.toBilinForm_apply, innerInCoordinates_apply g hx, g.symm]

private theorem relativeVolumeDensity_eq_div_metricVolumeDensity [FiniteDimensional ℝ F]
    (g g' : RiemannianMetric V) {a x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) :
    relativeVolumeDensity g g' x =
      (Module.finBasis ℝ F).metricVolumeDensity (innerInCoordinates g' a x) /
        (Module.finBasis ℝ F).metricVolumeDensity (innerInCoordinates g a x) := by
  rw [Module.Basis.relativeVolumeDensity_eq_sqrt_div (g := g) (g' := g')
      ((trivializationAt F V a).basisAt (Module.finBasis ℝ F) hx),
    Module.Basis.metricVolumeDensity_def, Module.Basis.metricVolumeDensity_def,
    ← Real.sqrt_div' _ (((Module.finBasis ℝ F).metricVolumeDensity_pos _).1
      (metricVolumeDensity_innerInCoordinates_pos g hx)).le]
  congr 3 <;> ext i j <;>
    simp only [innerInCoordinates_apply _ hx, Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply, Matrix.of_apply]

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]

/-- A family of relative volume densities is smooth within a set at a point whenever the two
inner-product sections are smooth there. The metrics may vary with the parameter, and their
regularity away from that point is irrelevant. -/
theorem contMDiffWithinAt_relativeVolumeDensity
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {k : ℕ∞ω} (g g' : P → RiemannianMetric V)
    {b : P → B} {s : Set P} {p : P}
    (hg : ContMDiffWithinAt IP (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) k
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ) (b q) ((g q).inner (b q))) s p)
    (hg' : ContMDiffWithinAt IP (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) k
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ) (b q) ((g' q).inner (b q))) s p) :
    ContMDiffWithinAt IP 𝓘(ℝ) k (fun q ↦ relativeVolumeDensity (g q) (g' q) (b q)) s p := by
  classical
  have : FiniteDimensional ℝ F :=
    (VectorBundle.continuousLinearEquivAt ℝ F V (b p)).finiteDimensional
  -- Use a common trivialization and compose the existing Gram-density smoothness theorem.
  have hp : b p ∈ (trivializationAt F V (b p)).baseSet :=
    mem_baseSet_trivializationAt F V (b p)
  have hs := ((Module.finBasis ℝ F).contDiffAt_metricVolumeDensity_of_posDef
    (innerInCoordinates_pos (g' p) hp)).comp_contMDiffWithinAt
      (f := fun q ↦ innerInCoordinates (g' q) (b p) (b q))
      (contMDiffWithinAt_totalSpace_iff.mp hg').2
  have ht := ((Module.finBasis ℝ F).contDiffAt_metricVolumeDensity_of_posDef
    (innerInCoordinates_pos (g p) hp)).comp_contMDiffWithinAt
      (f := fun q ↦ innerInCoordinates (g q) (b p) (b q))
      (contMDiffWithinAt_totalSpace_iff.mp hg).2
  refine (hs.div₀ ht (metricVolumeDensity_innerInCoordinates_pos (g p) hp).ne'
    ).congr_of_eventuallyEq ?_ (relativeVolumeDensity_eq_div_metricVolumeDensity _ _ hp)
  have hb := (contMDiffWithinAt_totalSpace_iff.mp hg).1.continuousWithinAt
  filter_upwards [hb.preimage_mem_nhdsWithin
    ((trivializationAt F V (b p)).open_baseSet.mem_nhds hp)] with q hq
  exact relativeVolumeDensity_eq_div_metricVolumeDensity _ _ hq

end Regularity

end Bundle.RiemannianMetric

namespace Bundle.ContinuousRiemannianMetric

open Bundle.RiemannianMetric

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- The relative volume density of two continuous metrics on a finite-rank vector bundle
is continuous. -/
theorem continuous_relativeVolumeDensity (g g' : ContinuousRiemannianMetric F V) :
    Continuous (relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric) := by
  classical
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have : FiniteDimensional ℝ F :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).finiteDimensional
  have hx : x ∈ (trivializationAt F V x).baseSet := mem_baseSet_trivializationAt F V x
  have hs := ((Module.finBasis ℝ F).contDiffAt_metricVolumeDensity_of_posDef
    (innerInCoordinates_pos g'.toRiemannianMetric hx) (n := 0)).continuousAt.comp
      ((FiberBundle.continuousAt_totalSpace _ _).mp (g'.continuous.continuousAt (x := x))).2
  have ht := ((Module.finBasis ℝ F).contDiffAt_metricVolumeDensity_of_posDef
    (innerInCoordinates_pos g.toRiemannianMetric hx) (n := 0)).continuousAt.comp
      ((FiberBundle.continuousAt_totalSpace _ _).mp (g.continuous.continuousAt (x := x))).2
  refine (hs.div ht (metricVolumeDensity_innerInCoordinates_pos
    g.toRiemannianMetric hx).ne').congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds hx] with y hy
  exact relativeVolumeDensity_eq_div_metricVolumeDensity _ _ hy

end Bundle.ContinuousRiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

open Bundle.RiemannianMetric

variable {B : Type*} [TopologicalSpace B]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n n' : ℕ∞ω}

section Smooth

variable (g : ContMDiffRiemannianMetric IB n F V) (g' : ContMDiffRiemannianMetric IB n' F V)

/-- The relative volume density is `C^k` at every point whenever both metrics are at least
`C^k`. -/
theorem contMDiffAt_relativeVolumeDensity {k : ℕ∞ω}
    (hk : k ≤ n) (hk' : k ≤ n') (x₀ : B) :
    ContMDiffAt IB 𝓘(ℝ) k
      (relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric) x₀ :=
  RiemannianMetric.contMDiffWithinAt_relativeVolumeDensity
    (fun _ ↦ g.toRiemannianMetric) (fun _ ↦ g'.toRiemannianMetric)
    ((g.contMDiff x₀).of_le hk) ((g'.contMDiff x₀).of_le hk')

/-- The relative volume density is `C^k` on any set whenever both metrics are at least
`C^k`. -/
theorem contMDiffOn_relativeVolumeDensity {k : ℕ∞ω}
    (hk : k ≤ n) (hk' : k ≤ n') (s : Set B) :
    ContMDiffOn IB 𝓘(ℝ) k
      (relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric) s :=
  fun x _ ↦ (contMDiffAt_relativeVolumeDensity g g' hk hk' x).contMDiffWithinAt

/-- The relative volume density is `C^k` whenever both metrics are at least `C^k`. -/
theorem contMDiff_relativeVolumeDensity {k : ℕ∞ω}
    (hk : k ≤ n) (hk' : k ≤ n') :
    ContMDiff IB 𝓘(ℝ) k
      (relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric) :=
  contMDiffAt_relativeVolumeDensity g g' hk hk'

end Smooth

variable [∀ x, ContinuousConstSMul ℝ (V x)]

/-- On a rank-`N` vector bundle, rescaling the compared metric by `f` multiplies the relative
volume density by `f ^ (N / 2)`. -/
@[simp]
theorem relativeVolumeDensity_rescale_right
    (g' : ContMDiffRiemannianMetric IB n' F V) (g : RiemannianMetric V)
    {f : B → ℝ} {hf : ContMDiff IB 𝓘(ℝ) n' f} {hf_pos : ∀ x, 0 < f x} (x : B) :
    relativeVolumeDensity g (g'.rescale f hf hf_pos).toRiemannianMetric x =
      f x ^ ((Module.finrank ℝ F : ℝ) / 2) *
        relativeVolumeDensity g g'.toRiemannianMetric x := by
  have hB : ((g'.rescale f hf hf_pos).toRiemannianMetric.inner x).toBilinForm =
      f x • (g'.toRiemannianMetric.inner x).toBilinForm := by
    ext v w
    simp [ContinuousLinearMap.toBilinForm_apply, rescale_inner]
  rw [relativeVolumeDensity_def, relativeVolumeDensity_def, hB,
    LinearMap.BilinForm.detRatio_smul_right, VectorBundle.finrank_eq ℝ F V,
    Real.sqrt_mul (pow_nonneg (hf_pos x).le _), Real.sqrt_pow_eq_rpow (hf_pos x).le]

/-- On a rank-`N` vector bundle, rescaling the reference metric by `f` divides the relative
volume density by `f ^ (N / 2)`. -/
@[simp]
theorem relativeVolumeDensity_rescale_left
    (g : ContMDiffRiemannianMetric IB n F V) (g' : RiemannianMetric V)
    {f : B → ℝ} {hf : ContMDiff IB 𝓘(ℝ) n f} {hf_pos : ∀ x, 0 < f x} (x : B) :
    relativeVolumeDensity (g.rescale f hf hf_pos).toRiemannianMetric g' x =
      relativeVolumeDensity g.toRiemannianMetric g' x /
        f x ^ ((Module.finrank ℝ F : ℝ) / 2) := by
  rw [← inv_relativeVolumeDensity g' _, relativeVolumeDensity_rescale_right]
  simp only [mul_inv_rev, inv_relativeVolumeDensity, div_eq_mul_inv]

end Bundle.ContMDiffRiemannianMetric
