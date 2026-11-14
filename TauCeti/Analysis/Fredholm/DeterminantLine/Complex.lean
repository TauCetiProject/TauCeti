/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Chart
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Complex orientations of determinant lines of complex-linear Fredholm operators

The determinant line `det (ker T) ⊗ (det (coker T))^*` of a complex-linear operator `T` with
finite-dimensional kernel and cokernel carries a canonical orientation, its complex orientation
(`LinearMap.IsComplexPositiveDetLine`): kernel and cokernel are complex vector spaces, and each is
oriented by the real bases `b₀, I • b₀, b₁, I • b₁, …` underlying its complex bases. Moduli spaces
of pseudoholomorphic curves are oriented through these orientations: the linearized operator of
a holomorphic sphere is complex-linear up to a term of order zero, and the complex orientation of
the complex-linear operator is transported along the homotopy removing that term. For this to
orient a family of moduli spaces, the complex orientations themselves must vary continuously in a
family of complex-linear Fredholm operators, although kernel and cokernel jump. This file proves
that they do.

Determinant lines of a family are compared through kernel charts (see
`TauCeti.Analysis.Fredholm.DeterminantLine.Chart`): a stabilization `D₂ : Λ →L F` by a
finite-dimensional space together with a kernel coordinate `q : E × Λ →L G` for which the pair
`((T.coprod D₂).prod q)` is invertible identifies the determinant line of `T` with the fixed line
`det G ⊗ (det Λ)^*` (`ContinuousLinearMap.detLineChartEquiv`). If `T`, `D₂` and `q` are
complex-linear, this identification of the real determinant lines reads the complex orientation
of `T` as the complex orientation of `det G ⊗ (det Λ)^*`
(`ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff`). Its proof passes through
the exact sequence `0 → ker T → ker (T.coprod D₂) → Λ → coker T → 0`: for complex-linear maps its
determinant isomorphism respects complex orientations
(`TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv`), and the sequence of the underlying real
operators is isomorphic to it through the identifications of the complex kernels and cokernels
with the real ones (`TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr`). The Koszul
sign `(-1) ^ (dim (coker T) * dim Λ)` normalizing the stabilization isomorphism is `1`, because `Λ`
has even real dimension.

Complex kernel charts exist near every complex-linear Fredholm operator, by
`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates` over `ℂ`, and they are
kernel charts of the underlying real operators
(`ContinuousLinearMap.IsInvertible.restrictScalars`). Since the transitions between
kernel charts are continuous and nowhere zero
(`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`), over a preconnected
parameter space the complex orientations of a continuous family of complex-linear operators are
read in any real kernel chart as positive multiples of one fixed vector
(`ContinuousLinearMap.exists_forall_isComplexPositiveDetLine_detLineChartEquiv_eq_smul`): the
complex orientations form a continuous orientation of the determinant line bundle of the family.

## Main results

* `ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff`: complex kernel charts read
  complex orientations as complex orientations.
* `ContinuousLinearMap.exists_forall_isComplexPositiveDetLine_detLineChartEquiv_eq_smul`: the
  complex orientations of a continuous family of complex-linear operators are continuous.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (the canonical orientation of the
  determinant line bundle of a family of complex-linear Fredholm operators).
-/

public section

noncomputable section

open Module TensorProduct Complex TauCeti

namespace ContinuousLinearMap

section Real

/-! ### Complex kernels and cokernels as real ones -/

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] (T : E →L[ℂ] F)

/-- The complex kernel of `T`, with its real structure, as the kernel of `T.restrictScalars ℝ`.
This is `LinearMap.kerRestrictScalarsEquiv`, whose target is the kernel of
`(T : E →ₗ[ℂ] F).restrictScalars ℝ`; that is the linear map underlying `T.restrictScalars ℝ` by
definition (`ContinuousLinearMap.coe_restrictScalars`). Restating its type matters: with the
kernel of `(T : E →ₗ[ℂ] F).restrictScalars ℝ` as target, instance search does not find the real
finite-dimensionality of the kernel of `T.restrictScalars ℝ`. -/
private def kerEquiv : T.ker ≃ₗ[ℝ] (T.restrictScalars ℝ).ker :=
  (T : E →ₗ[ℂ] F).kerRestrictScalarsEquiv ℝ

/-- The complex cokernel of `T`, with its real structure, as the cokernel of
`T.restrictScalars ℝ`, through `LinearMap.cokerRestrictScalarsEquiv` as for `kerEquiv`. -/
private def cokerEquiv : (F ⧸ (T.restrictScalars ℝ).range) ≃ₗ[ℝ] F ⧸ T.range :=
  (T : E →ₗ[ℂ] F).cokerRestrictScalarsEquiv ℝ

private theorem coe_kerEquiv_apply (x : T.ker) : (kerEquiv T x : E) = x :=
  LinearMap.coe_kerRestrictScalarsEquiv_apply ℝ (T : E →ₗ[ℂ] F) x

private theorem cokerEquiv_mk (y : F) :
    cokerEquiv T (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  LinearMap.cokerRestrictScalarsEquiv_mk ℝ (T : E →ₗ[ℂ] F) y

/-- Complex positivity of an element of the determinant line of `T.restrictScalars ℝ`, read in the
complex kernel and cokernel of `T`. This is `LinearMap.isComplexPositiveDetLine_iff`, with
`LinearMap.detLineRestrictScalarsEquiv`, whose body is not exposed here, computed on pure tensors
and with the kernel and cokernel retyped through `kerEquiv` and `cokerEquiv`. -/
private theorem isComplexPositiveDetLine_iff_congr
    {z : (T.restrictScalars ℝ : E →ₗ[ℝ] F).detLine} :
    (T : E →ₗ[ℂ] F).IsComplexPositiveDetLine z ↔
      IsComplexPositiveTMulDual (TensorProduct.congr (kerEquiv T).symm.detLineCongr
        (cokerEquiv T).symm.detLineCongr.dualMap z) := by
  have heq : ((T : E →ₗ[ℂ] F).detLineRestrictScalarsEquiv :
      (T.restrictScalars ℝ : E →ₗ[ℝ] F).detLine ≃ₗ[ℝ] _) = TensorProduct.congr
        (kerEquiv T).symm.detLineCongr (cokerEquiv T).symm.detLineCongr.dualMap :=
    LinearEquiv.toLinearMap_injective (TensorProduct.ext' fun x φ ↦
      (LinearMap.detLineRestrictScalarsEquiv_tmul _ x φ).trans (TensorProduct.congr_tmul
        (kerEquiv T).symm.detLineCongr (cokerEquiv T).symm.detLineCongr.dualMap x φ).symm)
  exact LinearMap.isComplexPositiveDetLine_iff.trans
    (Iff.of_eq (congrArg _ (LinearEquiv.congr_fun heq z)))

end Real

section Stabilization

/-! ### Complex stabilizations -/

variable {E Λ F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module ℂ Λ] [Module ℝ Λ] [IsScalarTower ℝ ℂ Λ]
  [TopologicalSpace Λ] [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [ContinuousAdd F] {D₁ : E →L[ℂ] F} {D₂ : Λ →L[ℂ] F}
  [FiniteDimensional ℝ (D₁.restrictScalars ℝ).ker] [FiniteDimensional ℝ Λ]

/-- Complex stabilizations respect complex orientations. Let `D₁ : E →L[ℂ] F` be
complex-linear and `D₂ : Λ →L[ℂ] F` a stabilization by a finite-dimensional complex space with
`D₁.coprod D₂` onto. The normalized identification `ContinuousLinearMap.detLineStabilizationEquiv`
of `det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*` with the determinant line of `D₁`, formed for the
underlying real operators, sends complex positive elements to complex positive elements. Here
`eB` identifies the complex kernel of `D₁.coprod D₂` with the real one. -/
private theorem isComplexPositiveDetLine_detLineStabilizationEquiv
    (h : Function.Surjective ((D₁.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)))
    (eB : (D₁.coprod D₂).ker ≃ₗ[ℝ] ((D₁.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).ker)
    (heB : ∀ x, (eB x : E × Λ) = x)
    {t : detLine ℝ (D₁.coprod D₂).ker ⊗[ℝ] Dual ℝ (detLine ℝ Λ)}
    (ht : IsComplexPositiveTMulDual t) :
    (D₁ : E →ₗ[ℂ] F).IsComplexPositiveDetLine
      (detLineStabilizationEquiv (D₁.restrictScalars ℝ) (D₂.restrictScalars ℝ) h
        (LinearEquiv.rTensor _ eB.detLineCongr t)) := by
  have : FiniteDimensional ℝ D₁.ker := (kerEquiv D₁).symm.finiteDimensional
  have heven : Even (finrank ℝ (F ⧸ (D₁.restrictScalars ℝ).range) * finrank ℝ Λ) := by
    rw [finrank_real_eq_two_mul_finrank_complex (V := Λ)]
    exact (even_two_mul _).mul_left _
  refine (isComplexPositiveDetLine_iff_congr D₁).2 ?_
  rw [detLineStabilizationEquiv_apply, heven.neg_one_pow, one_smul, detLineCoprodEquiv_def]
  -- The exact sequence of the complex operators, with real scalars, and that of the real ones
  -- are isomorphic through the identifications of complex and real kernels and cokernels.
  refine isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr (kerCoprodHom_injective D₁ D₂)
    (exact_kerCoprodHom_parameterProj D₁ D₂) (exact_parameterProj_parameterToCoker D₁ D₂)
    ((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h) _ _ _ _
    (f := (kerCoprodHom D₁ D₂ : D₁.ker →ₗ[ℂ] (D₁.coprod D₂).ker))
    (g := (parameterProj D₁ D₂ : (D₁.coprod D₂).ker →ₗ[ℂ] Λ)) (h := parameterToCoker D₁ D₂)
    (kerEquiv D₁) eB (cokerEquiv D₁).symm ?_ ?_ ?_ ht
  · exact LinearMap.ext fun x ↦ Subtype.ext (by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
        LinearMap.restrictScalars_apply, kerCoprodHom_apply, heB, coe_kerEquiv_apply])
  · exact LinearMap.ext fun x ↦ by simp [parameterProj_apply, heB]
  · refine LinearMap.ext fun l ↦ ?_
    rw [LinearMap.comp_apply, eq_comm, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq,
      LinearMap.restrictScalars_apply, parameterToCoker_apply, parameterToCoker_apply,
      Submodule.mkQ_apply, Submodule.mkQ_apply, cokerEquiv_mk, coe_restrictScalars']

end Stabilization

section Chart

/-! ### Complex kernel charts -/

variable {E Λ F G : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module ℂ Λ] [Module ℝ Λ] [IsScalarTower ℝ ℂ Λ]
  [TopologicalSpace Λ] [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup G] [Module ℂ G] [Module ℝ G]
  [IsScalarTower ℝ ℂ G] [TopologicalSpace G]
  {T : E →L[ℂ] F} {D₂ : Λ →L[ℂ] F} {q : E × Λ →L[ℂ] G}

-- Real finite-dimensionality follows from the complex one through the scalar tower, but
-- `ContinuousLinearMap.detLineChartEquiv` over `ℝ` takes it as an instance argument.
variable [FiniteDimensional ℝ Λ] [FiniteDimensional ℝ G]

/-- **Complex kernel charts read complex orientations as complex orientations.** Let `(D₂, q)` be a
kernel chart of a complex-linear operator `T` with complex-linear stabilization `D₂ : Λ →L[ℂ] F`
and complex-linear kernel coordinate `q : E × Λ →L[ℂ] G`. Then the chart
`ContinuousLinearMap.detLineChartEquiv` of the underlying real operators sends an element of the
determinant line of `T` to a complex positive element of `det G ⊗ (det Λ)^*` exactly when the
element is complex positive. -/
theorem isComplexPositiveTMulDual_detLineChartEquiv_iff
    (h : (((T.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).prod
      (q.restrictScalars ℝ)).IsInvertible)
    {z : (T.restrictScalars ℝ : E →ₗ[ℝ] F).detLine} :
    IsComplexPositiveTMulDual (detLineChartEquiv (T.restrictScalars ℝ) (D₂.restrictScalars ℝ)
      (q.restrictScalars ℝ) h z) ↔ (T : E →ₗ[ℂ] F).IsComplexPositiveDetLine z := by
  have : FiniteDimensional ℝ (T.restrictScalars ℝ).ker :=
    finiteDimensional_ker_of_isInvertible_prod_coprod h
  have hs := surjective_of_isInvertible_prod h
  have : FiniteDimensional ℂ Λ := Module.Finite.of_restrictScalars_finite ℝ ℂ Λ
  -- The complex cokernel of `T` is finite-dimensional, since `Λ` maps onto it.
  have : FiniteDimensional ℝ (F ⧸ (T.restrictScalars ℝ).range) :=
    Module.Finite.of_surjective _ ((parameterToCoker_surjective_iff_coprod_surjective _ _).2 hs)
  have : FiniteDimensional ℝ (F ⧸ T.range) := (cokerEquiv T).finiteDimensional
  have : FiniteDimensional ℂ (F ⧸ T.range) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ (F ⧸ T.range)
  -- The complex kernel of the stabilized operator, identified with the real one.
  let eB : (T.coprod D₂).ker ≃ₗ[ℝ] ((T.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).ker :=
    ((T.coprod D₂).ker.restrictScalarsEquiv ℝ).symm.restrictScalars ℝ ≪≫ₗ
      LinearEquiv.ofEq _ _ (by ext; simp)
  have heB (x : (T.coprod D₂).ker) : (eB x : E × Λ) = x := rfl
  -- The kernel coordinate, read on the complex kernel, is a complex-linear isomorphism onto `G`.
  let eq : (T.coprod D₂).ker ≃ₗ[ℝ] G :=
    eB ≪≫ₗ (kerEquivOfProd _ _ h).toLinearEquiv.symm
  have heq (x : (T.coprod D₂).ker) : eq x = q x := by
    simp [eq, kerEquivOfProd_symm_apply, heB]
  have heqI (x : (T.coprod D₂).ker) : eq (I • x) = I • eq x := by
    rw [heq, heq, Submodule.coe_smul, map_smul]
  let eqC : (T.coprod D₂).ker ≃ₗ[ℂ] G :=
    .ofBijective (eq.toLinearMap.complexOfMapISmul heqI) (by simpa using eq.bijective)
  have heqC : eqC.restrictScalars ℝ = eq := LinearEquiv.ext fun _ ↦ by simp [eqC]
  -- Write `z` through the normalized stabilization isomorphism.
  obtain ⟨t, rfl⟩ : ∃ t, detLineStabilizationEquiv (T.restrictScalars ℝ) (D₂.restrictScalars ℝ)
      hs (LinearEquiv.rTensor _ eB.detLineCongr t) = z :=
    ⟨(LinearEquiv.rTensor _ eB.detLineCongr).symm
      ((detLineStabilizationEquiv _ _ hs).symm z), by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  have hchart : detLineChartEquiv (T.restrictScalars ℝ) (D₂.restrictScalars ℝ)
      (q.restrictScalars ℝ) h (detLineStabilizationEquiv (T.restrictScalars ℝ)
        (D₂.restrictScalars ℝ) hs (LinearEquiv.rTensor _ eB.detLineCongr t)) =
      TensorProduct.congr (LinearEquiv.detLineCongr (eqC.restrictScalars ℝ))
        (LinearEquiv.detLineCongr ((LinearEquiv.refl ℂ Λ).symm.restrictScalars ℝ)).dualMap t := by
    have hrefl : (LinearEquiv.refl ℂ Λ).symm.restrictScalars ℝ = LinearEquiv.refl ℝ Λ :=
      LinearEquiv.ext fun _ ↦ by simp
    rw [detLineChartEquiv_detLineStabilizationEquiv, heqC, hrefl, LinearEquiv.detLineCongr_refl,
      LinearEquiv.dualMap_refl, ← LinearEquiv.rTensor_trans_apply,
      ← LinearEquiv.detLineCongr_trans, LinearEquiv.rTensor]
  rw [hchart, isComplexPositiveTMulDual_congr_detLineCongr_iff]
  refine ⟨fun ht ↦ isComplexPositiveDetLine_detLineStabilizationEquiv hs eB heB ht,
    fun hz ↦ ?_⟩
  -- Conversely, compare `t` with a complex positive element `t₀`, whose image is complex
  -- positive too, so that the two images differ by a positive factor.
  have : FiniteDimensional ℂ G := Module.Finite.of_restrictScalars_finite ℝ ℂ G
  have : FiniteDimensional ℂ (T.coprod D₂).ker := LinearEquiv.finiteDimensional eqC.symm
  obtain ⟨t₀, ht₀⟩ := exists_isComplexPositiveTMulDual (E := (T.coprod D₂).ker) (F := Λ)
  obtain ⟨c, hc, hct⟩ :=
    (isComplexPositiveDetLine_detLineStabilizationEquiv hs eB heB ht₀).exists_pos_smul_eq hz
  let L := (LinearEquiv.rTensor _ eB.detLineCongr).trans
    (detLineStabilizationEquiv (T.restrictScalars ℝ) (D₂.restrictScalars ℝ) hs)
  have htt₀ : t = c • t₀ := L.injective (by rw [LinearEquiv.map_smul]; exact hct)
  exact htt₀ ▸ ht₀.smul hc

end Chart

section Continuity

/-! ### Continuity of complex orientations -/

variable {E Λ F G Λ₃ G₃ X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] [FiniteDimensional ℂ Λ]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup Λ₃] [NormedSpace ℝ Λ₃] [FiniteDimensional ℝ Λ₃]
  [NormedAddCommGroup G₃] [NormedSpace ℝ G₃] [FiniteDimensional ℝ G₃]
  [TopologicalSpace X] [PreconnectedSpace X] {T : X → E →L[ℂ] F}
  {D₂ : Λ →L[ℂ] F} {q : E × Λ →L[ℂ] G} {D₃ : Λ₃ →L[ℝ] F} {q₃ : E × Λ₃ →L[ℝ] G₃}

/-- **Complex orientations of a continuous family are continuous.** Let `T` be a continuous family
of complex-linear operators over a preconnected space, with a complex kernel chart `(D₂, q)`
valid at every parameter. Then in any real kernel chart `(D₃, q₃)` of the underlying real
operators valid at every parameter, the complex positive elements of all the determinant lines
of the family are read as positive multiples of one fixed vector `w`. In other words, the
complex orientations of the determinant lines form a continuous orientation of the determinant
line bundle of the family. Complex kernel charts exist near every complex-linear Fredholm
operator (`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates` over `ℂ`). -/
theorem exists_forall_isComplexPositiveDetLine_detLineChartEquiv_eq_smul (hT : Continuous T)
    (h : ∀ x, (((T x).coprod D₂).prod q).IsInvertible)
    (h₃ : ∀ x, ((((T x).restrictScalars ℝ).coprod D₃).prod q₃).IsInvertible) :
    ∃ w, ∀ x (z : ((T x).restrictScalars ℝ : E →ₗ[ℝ] F).detLine),
      (T x : E →ₗ[ℂ] F).IsComplexPositiveDetLine z →
        ∃ c : ℝ, 0 < c ∧ detLineChartEquiv ((T x).restrictScalars ℝ) D₃ q₃ (h₃ x) z = c • w := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, fun x ↦ isEmptyElim x⟩
  have hTℝ : Continuous fun x ↦ (T x).restrictScalars ℝ :=
    (restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp hT
  -- Complex kernel charts are kernel charts of the underlying real operators.
  have h' (x : X) : ((((T x).restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).prod
      (q.restrictScalars ℝ)).IsInvertible :=
    (h x).restrictScalars
  -- The elements read as a fixed complex positive `t₀` in the complex chart are complex positive.
  obtain ⟨t₀, ht₀⟩ := exists_isComplexPositiveTMulDual (E := G) (F := Λ)
  have hz₀ (x : X) : (T x : E →ₗ[ℂ] F).IsComplexPositiveDetLine
      ((detLineChartEquiv ((T x).restrictScalars ℝ) (D₂.restrictScalars ℝ)
        (q.restrictScalars ℝ) (h' x)).symm t₀) :=
    (isComplexPositiveTMulDual_detLineChartEquiv_iff (h' x)).1 (by
      rwa [LinearEquiv.apply_symm_apply])
  -- In the real chart they move by a continuous nowhere-vanishing factor, which is positive.
  obtain ⟨c, hc, hc0, hcx⟩ := exists_continuous_detLineChartEquiv_symm_eq_smul hTℝ h₃ h' x₀
  set w := detLineChartEquiv ((T x₀).restrictScalars ℝ) D₃ q₃ (h₃ x₀)
    ((detLineChartEquiv ((T x₀).restrictScalars ℝ) (D₂.restrictScalars ℝ)
      (q.restrictScalars ℝ) (h' x₀)).symm t₀)
  have hw : w ≠ 0 := by
    simp only [w, ne_eq, LinearEquiv.map_eq_zero_iff]
    exact (IsComplexPositiveTMulDual.ne_zero ht₀)
  have hc₁ : c x₀ = 1 := by
    obtain ⟨ξ, hξ⟩ := Projective.exists_dual_eq_one ℝ hw
    have h₁ : ξ w = c x₀ • ξ w := (congrArg ξ (hcx x₀ t₀)).trans (ξ.map_smul _ _)
    rw [hξ, smul_eq_mul, mul_one] at h₁
    exact h₁.symm
  have hpos (x : X) : 0 < c x := by
    by_contra hle
    obtain ⟨y, hy⟩ := intermediate_value_univ x x₀ hc ⟨not_lt.1 hle, hc₁ ▸ zero_le_one⟩
    exact hc0 y hy
  refine ⟨w, fun x z hz ↦ ?_⟩
  -- The cokernel of `T x` is finite-dimensional, since `Λ` maps onto it.
  have : FiniteDimensional ℂ (F ⧸ (T x).range) := Module.Finite.of_surjective _
    ((parameterToCoker_surjective_iff_coprod_surjective _ _).2
      (surjective_of_isInvertible_prod (h x)))
  obtain ⟨s, hs, rfl⟩ := (hz₀ x).exists_pos_smul_eq hz
  exact ⟨s * c x, mul_pos hs (hpos x),
    ((detLineChartEquiv _ _ _ (h₃ x)).map_smul s _).trans (by rw [hcx, mul_smul])⟩

end Continuity

end ContinuousLinearMap
