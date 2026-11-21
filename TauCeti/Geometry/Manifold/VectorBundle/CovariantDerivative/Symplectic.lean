/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Symplectic connections

Let `V` be a real vector bundle of finite rank with a field `Ω` of skew-symmetric bilinear forms
on its fibres that is nondegenerate, so that each `Ω♭_x : V_x → V_x^*`, `u ↦ Ω_x(u, ·)`, is
invertible, and let `∇` be a covariant derivative on `V`. In general `Ω` is not parallel. The
**symplectic part** of `∇` is the connection

`∇ˢ_v σ = ∇_v σ + A_v σ`,  where `Ω(A_v u, τ) = (1 / 2) (∇_v Ω)(u, τ)`

(`CovariantDerivative.symplecticPart`). That is, `A_v u = (1 / 2) (Ω♭)⁻¹ ((∇_v Ω)(u, ·))`; at a
point where `Ω♭` is not invertible the correction is zero, by the convention of
`ContinuousLinearMap.inverse` (`CovariantDerivative.symplecticCorrection`,
`CovariantDerivative.symplecticPart_apply`). It has the following properties.

* `Ω` is parallel for `∇ˢ`: `(∇ˢ Ω) = 0`
  (`CovariantDerivative.derivBilinearTensor_symplecticPart_eq_zero`). Indeed changing the
  connection by `A` changes `(∇_v Ω)(u, τ)` by `-Ω(A_v u, τ) - Ω(u, A_v τ)`, and both terms are
  `-(1 / 2) (∇_v Ω)(u, τ)` because `∇Ω` is again skew-symmetric.
* `∇ˢ = ∇` exactly when `Ω` is already parallel for `∇`
  (`CovariantDerivative.symplecticPart_eq_self_iff`).
* The difference `∇ˢ - ∇ = A` is `Ω`-self-adjoint, `Ω(A_v u, τ) = Ω(u, A_v τ)`
  (`CovariantDerivative.apply_difference_symplecticPart_apply_comm`). Conversely, for `Ω`
  differentiable (for instance smooth), every connection for which `Ω` is parallel and whose
  difference from `∇` is `Ω`-self-adjoint agrees with `∇ˢ` on differentiable sections
  (`CovariantDerivative.apply_eq_symplecticPart_apply`). Every endomorphism of a symplectic vector
  space is uniquely the sum of an `Ω`-skew-adjoint part, which preserves `Ω` infinitesimally, and
  an `Ω`-self-adjoint part, so for such `Ω`, `∇ˢ` is the unique connection making `Ω` parallel
  that is reached from `∇` by a self-adjoint change.
* If `∇` and `Ω` are smooth, so is `∇ˢ`
  (`CovariantDerivative.contMDiffCovariantDerivative_symplecticPart`): the inverses of the smooth
  invertible maps `Ω♭` form a smooth section, by `ContMDiff.clm_bundle_inverse`.

Consequently every smooth bundle with a smooth fibrewise symplectic form, over a σ-compact
Hausdorff manifold modelled on a finite-dimensional space, carries a smooth **symplectic
connection**, a smooth connection for which the symplectic form is parallel
(`CovariantDerivative.exists_contMDiffCovariantDerivative_derivBilinearTensor_eq_zero`). No
compatible complex structure or metric is used. A symplectic connection on a symplectic vector
bundle is the input of the minimal coupling construction of a closed two-form near its zero
section, which is nondegenerate there and gives the local model in the symplectic neighbourhood
theorem.

## References

* I. Vaisman, *Symplectic curvature tensors*, Monatsh. Math. 100 (1985), 299–327, Section 1
  (existence of symplectic connections on symplectic vector bundles).
* P. Tondeur, *Affine Zusammenhänge auf Mannigfaltigkeiten mit fast-symplektischer Struktur*,
  Comment. Math. Helv. 36 (1961), 234–244.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 3.4 (the minimal coupling form of a symplectic connection on a symplectic
  vector bundle).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V) (Ω : Π x : M, V x →L[ℝ] V x →L[ℝ] ℝ)

/-- The **correction one-form** `A` of the symplectic part,
`A_v u = (1 / 2) (Ω♭)⁻¹ ((∇_v Ω)(u, ·))`, characterised where `Ω♭` is invertible by
`Ω(A_v u, τ) = (1 / 2) (∇_v Ω)(u, τ)` (`CovariantDerivative.symplecticCorrection_apply`). Where
`Ω♭` is not invertible it is zero, by the convention of `ContinuousLinearMap.inverse`. The fibre
is finite-dimensional and Hausdorff, so the linear map `u ↦ A u` is continuous. -/
def symplecticCorrection (x : M) : V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  -- Transfer normability, the Hausdorff property and finite dimension from the model fibre.
  letI := (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  letI := (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) x).isNormableSpace
  haveI := FiberBundle.t2Space F V x
  haveI := VectorBundle.finiteDimensional ℝ F V x
  LinearMap.toContinuousLinearMap
    { toFun u := (Ω x).inverse ∘L ((2⁻¹ : ℝ) • (cov.derivBilinearTensor Ω x u).flip)
      map_add' u u' := ContinuousLinearMap.ext fun v ↦ by
        have : (cov.derivBilinearTensor Ω x (u + u')).flip v =
            (cov.derivBilinearTensor Ω x u).flip v + (cov.derivBilinearTensor Ω x u').flip v := by
          ext τ
          simp
        rw [add_apply]
        simp only [ContinuousLinearMap.comp_apply, smul_apply]
        rw [this, smul_add, map_add]
      map_smul' c u := ContinuousLinearMap.ext fun v ↦ by simp [smul_comm c] }

/-- The **symplectic part** `∇ˢ_v σ = ∇_v σ + A_v σ` of a covariant derivative `∇` with respect
to a field `Ω` of bilinear forms, where `A` is `CovariantDerivative.symplecticCorrection`,
`Ω(A_v u, τ) = (1 / 2) (∇_v Ω)(u, τ)`. When `Ω` is skew-symmetric and nondegenerate, `Ω` is
parallel for `∇ˢ` (`CovariantDerivative.derivBilinearTensor_symplecticPart_eq_zero`). -/
def symplecticPart : CovariantDerivative I F V :=
  cov.addOneForm (cov.symplecticCorrection Ω)

/-- The defining formula of the symplectic part, `∇ˢ_v σ = ∇_v σ + A_v σ`. -/
@[simp]
theorem symplecticPart_apply (σ : Π x : M, V x) (x : M) (v : TangentSpace I x) :
    cov.symplecticPart Ω σ x v = cov σ x v + cov.symplecticCorrection Ω x (σ x) v := by
  simp [symplecticPart]

/-- The difference of the symplectic part from `∇` is the correction one-form `A`. -/
@[simp]
theorem difference_symplecticPart (x : M) (u : V x) (v : TangentSpace I x) :
    (cov.symplecticPart Ω).difference cov x u v = cov.symplecticCorrection Ω x u v := by
  simp [difference_apply_eq_extend]

variable {cov Ω}

/-- The correction one-form paired with `Ω`: where `Ω♭` is invertible,
`Ω(A_v u, τ) = (1 / 2) (∇_v Ω)(u, τ)`. Since `Ω♭` is injective, this determines `A_v u`. -/
theorem symplecticCorrection_apply {x : M} (hΩ : (Ω x).IsInvertible) (u : V x)
    (v : TangentSpace I x) (τ : V x) :
    Ω x (cov.symplecticCorrection Ω x u v) τ = 2⁻¹ * cov.derivBilinearTensor Ω x u τ v := by
  simp [symplecticCorrection, hΩ.self_apply_inverse]

/-- Where `Ω♭` is not invertible, the correction one-form is zero. -/
theorem symplecticCorrection_of_not_isInvertible {x : M} (hΩ : ¬(Ω x).IsInvertible) :
    cov.symplecticCorrection Ω x = 0 := by
  ext u v
  simp [symplecticCorrection, hΩ]

/-- Where `Ω♭` is not invertible, the symplectic part agrees with `∇`. -/
theorem symplecticPart_apply_of_not_isInvertible {x : M} (hΩ : ¬(Ω x).IsInvertible)
    (σ : Π x : M, V x) : cov.symplecticPart Ω σ x = cov σ x := by
  ext v
  simp [symplecticCorrection_of_not_isInvertible hΩ]

/-- The defining formula of the symplectic part, paired with `Ω`: where `Ω♭` is invertible,
`Ω(∇ˢ_v σ, τ) = Ω(∇_v σ, τ) + (1 / 2) (∇_v Ω)(σ, τ)`. Since `Ω♭` is injective, this determines
`∇ˢ_v σ`. -/
theorem apply_symplecticPart_apply {x : M} (hΩ : (Ω x).IsInvertible) (σ : Π x : M, V x)
    (v : TangentSpace I x) (τ : V x) :
    Ω x (cov.symplecticPart Ω σ x v) τ =
      Ω x (cov σ x v) τ + 2⁻¹ * cov.derivBilinearTensor Ω x (σ x) τ v := by
  simp [symplecticCorrection_apply hΩ]

/-- The difference of the symplectic part from `∇`, paired with `Ω`: where `Ω♭` is invertible,
`Ω((∇ˢ - ∇)(u, v), τ) = (1 / 2) (∇_v Ω)(u, τ)`. -/
theorem apply_difference_symplecticPart_apply {x : M} (hΩ : (Ω x).IsInvertible) (u : V x)
    (v : TangentSpace I x) (τ : V x) :
    Ω x ((cov.symplecticPart Ω).difference cov x u v) τ =
      2⁻¹ * cov.derivBilinearTensor Ω x u τ v := by
  simp [symplecticCorrection_apply hΩ]

/-- **The difference of the symplectic part from `∇` is `Ω`-self-adjoint** for a skew-symmetric
`Ω`: `Ω((∇ˢ - ∇)(u, v), τ) = Ω(u, (∇ˢ - ∇)(τ, v))`. Where `Ω♭` is not invertible the difference
is zero. -/
theorem apply_difference_symplecticPart_apply_comm
    (hskew : ∀ y (u w : V y), Ω y u w = -Ω y w u) {x : M} (u τ : V x) (v : TangentSpace I x) :
    Ω x ((cov.symplecticPart Ω).difference cov x u v) τ =
      Ω x u ((cov.symplecticPart Ω).difference cov x τ v) := by
  by_cases hΩ : (Ω x).IsInvertible
  · rw [hskew x u, apply_difference_symplecticPart_apply hΩ,
      apply_difference_symplecticPart_apply hΩ, cov.derivBilinearTensor_apply_anticomm hskew]
    simp
  · simp [symplecticCorrection_of_not_isInvertible hΩ]

/-- **`Ω` is parallel for the symplectic part.** If `Ω` is skew-symmetric and `Ω♭` is invertible
at `x`, the covariant derivative of `Ω` for the symplectic part of any connection vanishes at
`x`. -/
theorem derivBilinearTensor_symplecticPart_eq_zero
    (hskew : ∀ y (u w : V y), Ω y u w = -Ω y w u) {x : M} (hΩ : (Ω x).IsInvertible) :
    (cov.symplecticPart Ω).derivBilinearTensor Ω x = 0 := by
  by_cases hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ Ω y (σ y) (τ y)) x
  · ext u τ v
    have h := (cov.symplecticPart Ω).derivBilinearTensor_apply_sub_derivBilinearTensor_apply
      cov hb u τ v
    rw [apply_difference_symplecticPart_apply hΩ, hskew x u,
      apply_difference_symplecticPart_apply hΩ, cov.derivBilinearTensor_apply_anticomm hskew τ u]
      at h
    simp only [neg_apply] at h
    simp only [zero_apply]
    linarith
  · exact derivBilinearTensor_eq_zero_of_not _ hb

/-- **The symplectic part of `∇` is `∇` exactly when `Ω` is parallel for `∇`**, for a field `Ω`
of bilinear forms with every `Ω♭` invertible. -/
theorem symplecticPart_eq_self_iff (hΩ : ∀ x, (Ω x).IsInvertible) :
    cov.symplecticPart Ω = cov ↔ ∀ x, cov.derivBilinearTensor Ω x = 0 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · ext u τ v
    have hd := apply_difference_symplecticPart_apply (cov := cov) (hΩ x) u v τ
    rw [h, difference_self] at hd
    simpa using hd.symm
  · ext σ x v
    -- The correction `A_v σ` pairs to zero with every vector, so it vanishes.
    rw [symplecticPart_apply, add_eq_left]
    refine (hΩ x).injective ?_
    ext τ
    simp [symplecticCorrection_apply (hΩ x), h x]

/-- **Uniqueness of the symplectic part.** Let `Ω` be differentiable at `x` with `Ω♭` invertible
there. If `Ω` is parallel at `x` for a connection `∇'` whose difference from `∇` is
`Ω`-self-adjoint at `x`, then `∇'` agrees at `x` with the symplectic part of `∇` on every section
differentiable at `x`. -/
theorem apply_eq_symplecticPart_apply {cov' : CovariantDerivative I F V} {x : M}
    (hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ Ω y (σ y) (τ y)) x)
    (hΩ : (Ω x).IsInvertible) (hpar : cov'.derivBilinearTensor Ω x = 0)
    (hsymm : ∀ (u τ : V x) (v : TangentSpace I x),
      Ω x (cov'.difference cov x u v) τ = Ω x u (cov'.difference cov x τ v))
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    cov' σ x = cov.symplecticPart Ω σ x := by
  -- Both connections differ from `∇` by tensors pairing with `Ω` to `(1 / 2) ∇Ω`.
  have hd : cov'.difference cov x = (cov.symplecticPart Ω).difference cov x := by
    ext u v
    refine hΩ.injective ?_
    ext τ
    have h := cov'.derivBilinearTensor_apply_sub_derivBilinearTensor_apply cov hb u τ v
    rw [hpar, hsymm] at h
    simp only [zero_apply] at h
    rw [apply_difference_symplecticPart_apply hΩ, hsymm]
    linarith
  have h₁ := cov'.difference_apply cov hσ
  have h₂ := (cov.symplecticPart Ω).difference_apply cov hσ
  rw [hd, h₂] at h₁
  exact (sub_left_inj.1 h₁).symm

end General

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {cov : CovariantDerivative I F V} {Ω : Π x : M, V x →L[ℝ] V x →L[ℝ] ℝ}

/-- **The symplectic part of a smooth connection is smooth**, for a smooth field `Ω` of bilinear
forms with every `Ω♭` invertible: the inverses of the `Ω♭` then form a smooth section. -/
theorem contMDiffCovariantDerivative_symplecticPart [ContMDiffCovariantDerivative cov ∞]
    (hΩs : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun y ↦ V y →L[ℝ] V y →L[ℝ] ℝ) x (Ω x)))
    (hΩ : ∀ x, (Ω x).IsInvertible) :
    ContMDiffCovariantDerivative (cov.symplecticPart Ω) ∞ where
  contMDiff.contMDiff {σ} hσ := by
    rw [contMDiffOn_univ] at hσ ⊢
    have hσ' : CMDiff ∞ (T% σ) := by simpa using hσ
    refine (TauCeti.Manifold.contMDiff_hom_iff _).2 fun X hX ↦ ?_
    -- The correction `A_X σ` is `(Ω♭)⁻¹` applied to its own pairing with `Ω`, which is the smooth
    -- covector field `(1 / 2) (∇_X Ω)(σ, ·)`.
    have hψ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ fun y ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun z ↦ V z →L[ℝ] ℝ) y
          (Ω y ((cov.symplecticPart Ω).difference cov y (σ y) (X y))) := by
      refine (TauCeti.Manifold.contMDiff_hom_iff _).2 fun τ hτ ↦ ?_
      refine Bundle.Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, ?_⟩
      exact ((contMDiff_const (c := (2⁻¹ : ℝ))).mul
        (cov.contMDiff_derivBilinearTensor_apply hΩs hσ' hτ hX)).congr
        fun y ↦ apply_difference_symplecticPart_apply (hΩ y) _ _ _
    have hA := ((ContMDiff.clm_bundle_inverse (b := id) hΩs hΩ).clm_bundle_apply hψ)
    refine ((cov.contMDiff_apply hX hσ).add_section hA).congr fun y ↦
      congrArg (TotalSpace.mk' F y) ?_
    rw [Pi.add_apply, (hΩ y).inverse_apply_self,
      (cov.symplecticPart Ω).difference_apply cov (hσ'.mdifferentiableAt (by simp)), sub_apply,
      add_sub_cancel]

/-- **Existence of symplectic connections.** A smooth field `Ω` of skew-symmetric bilinear forms
with every `Ω♭` invertible, on a smooth real vector bundle of finite rank over a σ-compact
Hausdorff manifold modelled on a finite-dimensional space, is parallel for some smooth covariant
derivative: the symplectic part of any smooth covariant derivative. -/
theorem exists_contMDiffCovariantDerivative_derivBilinearTensor_eq_zero [SigmaCompactSpace M]
    (hΩs : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun y ↦ V y →L[ℝ] V y →L[ℝ] ℝ) x (Ω x)))
    (hskew : ∀ y (u w : V y), Ω y u w = -Ω y w u) (hΩ : ∀ x, (Ω x).IsInvertible) :
    ∃ cov : CovariantDerivative I F V,
      ContMDiffCovariantDerivative cov ∞ ∧ ∀ x, cov.derivBilinearTensor Ω x = 0 := by
  obtain ⟨cov, hcov⟩ := exists_contMDiffCovariantDerivative (I := I) (F := F) (V := V) (n := ⊤)
    (k := ∞) (by simp)
  exact ⟨cov.symplecticPart Ω, contMDiffCovariantDerivative_symplecticPart hΩs hΩ,
    fun x ↦ derivBilinearTensor_symplecticPart_eq_zero hskew (hΩ x)⟩

end Smooth

end CovariantDerivative
