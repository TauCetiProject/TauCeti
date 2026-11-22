/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.Analysis.Normed.Operator.Splitting.Family

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

Kernel charts need no complex norm near an operator that is onto. Let `E` and `F` be real Banach
spaces on which the complex numbers act compatibly with the real scalars, `E` with continuous
multiplication by `i`, such as a real Banach space with a continuous almost complex structure.
At a continuous family of complex-linear operators `T x : E →L[ℂ] F` with `T x₀` onto and with
finite-dimensional kernel, a continuous complex-linear projection `P` onto the kernel of `T x₀`,
read in complex coordinates of that kernel, is a complex kernel coordinate, valid with the trivial
stabilizer throughout a neighbourhood of `x₀`
(`ContinuousLinearMap.exists_isOpen_isInvertible_prod_coprod_of_surjective`). Being complex, this
chart reads the complex orientations of all the `T x` near `x₀` as the one complex orientation of
the fixed line `det ℂᵐ ⊗ (det ℂ⁰)^*`
(`ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff`), so they form a
continuous orientation of the determinant line bundle of the family near `x₀`.

Over an arbitrary parameter space, a family of complex positive elements along a family of
complex-linear operators which is continuous and Fredholm on `s` is coherent on `s`
(`TauCeti.isDetLineCoherentOn_of_isComplexPositiveDetLine`): near each parameter, one complex
kernel chart reads any two complex positive elements as positive multiples of each other, and
coherence may be checked in that chart
(`TauCeti.isDetLineCoherentWithinAt_of_eventually_sameRay`). Hence orientation transport along a
path of complex-linear Fredholm operators carries the complex orientation
(`ContinuousLinearMap.IsFredholm.complexDetLineOrientation`) at one end to the complex
orientation at the other (`TauCeti.detLineOrientationTransport_complexDetLineOrientation`).

At a bijective complex-linear operator the complex orientation is the orientation given by
bijectivity (`LinearMap.isComplexPositiveDetLine_detLineEquivOfBijective_symm_one`), and along a
path of invertible operators transport preserves the orientations given by invertibility. Hence,
along a path of invertible operators starting at a complex-linear one, transport carries the
complex orientation to the orientation given by invertibility at the other end
(`TauCeti.detLineOrientationTransport_rayOfNeZero_detLineCongrOfEq_of_isComplexPositiveDetLine`):
an operator joined to a complex-linear reference through invertible operators has positive
determinant sign. This holds for real Banach spaces with compatible complex structures that need
not come from complex norms.

## Main definitions

* `ContinuousLinearMap.IsFredholm.complexDetLineOrientation`: the complex orientation of the
  determinant line of a complex-linear Fredholm operator.

## Main results

* `ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff`: complex kernel charts read
  complex orientations as complex orientations.
* `ContinuousLinearMap.exists_forall_isComplexPositiveDetLine_detLineChartEquiv_eq_smul`: the
  complex orientations of a continuous family of complex-linear operators are continuous.
* `ContinuousLinearMap.exists_isOpen_isInvertible_prod_coprod_of_surjective`: near an onto
  complex-linear operator with finite-dimensional kernel there is a complex kernel chart with
  trivial stabilizer, without a complex norm.
* `TauCeti.isDetLineCoherentOn_of_isComplexPositiveDetLine`: complex orientations of a continuous
  family of complex-linear Fredholm operators are coherent.
* `TauCeti.detLineOrientationTransport_complexDetLineOrientation`: transport along complex-linear
  paths preserves complex orientations.
* `TauCeti.detLineOrientationTransport_rayOfNeZero_detLineCongrOfEq_of_isComplexPositiveDetLine`:
  transport from a complex-linear operator along invertible operators gives the orientation of
  invertibility.

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
`LinearMap.detLineRestrictScalarsEquiv` unfolded by `LinearMap.detLineRestrictScalarsEquiv_eq_congr`
and with the kernel and cokernel retyped through `kerEquiv` and `cokerEquiv`. -/
private theorem isComplexPositiveDetLine_iff_congr
    {z : (T.restrictScalars ℝ : E →ₗ[ℝ] F).detLine} :
    (T : E →ₗ[ℂ] F).IsComplexPositiveDetLine z ↔
      IsComplexPositiveTMulDual (TensorProduct.congr (kerEquiv T).symm.detLineCongr
        (cokerEquiv T).symm.detLineCongr.dualMap z) := by
  exact LinearMap.isComplexPositiveDetLine_iff.trans (Iff.of_eq (congrArg _
    (LinearEquiv.congr_fun (LinearMap.detLineRestrictScalarsEquiv_eq_congr (T : E →ₗ[ℂ] F)) z)))

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

section Surjective

/-! ### Complex kernel charts at onto operators -/

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E] [ContinuousConstSMul ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [Module ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace X]
  {T : X → E →L[ℂ] F} {x₀ : X}

/-- **Complex kernel charts at an onto operator.** Let `T` be a family of complex-linear operators
between real Banach spaces with compatible complex structures, continuous at `x₀` as a family of
real operators, with `T x₀` onto and with finite-dimensional kernel, of real dimension `2 m`. Then
there is a complex-linear kernel coordinate `q : E × ℂ⁰ →L[ℂ] ℂᵐ` such that, with the zero
stabilizer, the pair `(T x).coprod 0` and `q` of underlying real operators is invertible for every
`x` in an open neighbourhood of `x₀`. The coordinate is a continuous complex-linear projection onto
the kernel of `T x₀` (`Submodule.ClosedComplemented.of_restrictScalars`), read in a complex basis
of it; neither `E` nor `F` needs a complex norm. Since the chart is complex,
`ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff` reads the complex
orientations of the determinant lines of all these `T x` as the complex orientation of
`det ℂᵐ ⊗ (det ℂ⁰)^*`. -/
theorem exists_isOpen_isInvertible_prod_coprod_of_surjective
    (hT : ContinuousAt (fun x ↦ (T x).restrictScalars ℝ) x₀)
    (h₀ : Function.Surjective ((T x₀).restrictScalars ℝ))
    [FiniteDimensional ℝ ((T x₀).restrictScalars ℝ).ker] :
    ∃ m : ℕ, finrank ℝ ((T x₀).restrictScalars ℝ).ker = 2 * m ∧
      ∃ q : E × (Fin 0 → ℂ) →L[ℂ] (Fin m → ℂ), ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∀ x ∈ U, ((((T x).restrictScalars ℝ).coprod
          ((0 : (Fin 0 → ℂ) →L[ℂ] F).restrictScalars ℝ)).prod
            (q.restrictScalars ℝ)).IsInvertible := by
  have : FiniteDimensional ℝ (T x₀).ker := (kerEquiv (T x₀)).symm.finiteDimensional
  have : FiniteDimensional ℂ (T x₀).ker := Module.Finite.of_restrictScalars_finite ℝ ℂ _
  have : FiniteDimensional ℝ ((T x₀).ker.restrictScalars ℝ) :=
    ((Submodule.restrictScalarsEquiv ℝ ℂ E (T x₀).ker).restrictScalars ℝ).symm.finiteDimensional
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_restrictScalars
    (Submodule.ClosedComplemented.of_finiteDimensional ((T x₀).ker.restrictScalars ℝ))
  -- Complex coordinates on the kernel, continuous since the kernel is finite-dimensional.
  let ε := (Module.finBasis ℂ (T x₀).ker).equivFun
  let εL : (T x₀).ker →L[ℂ] (Fin (finrank ℂ (T x₀).ker) → ℂ) :=
    ⟨ε.toLinearMap, LinearMap.continuous_of_finiteDimensional (ε.toLinearMap.restrictScalars ℝ)⟩
  have hεL (k : (T x₀).ker) : εL k = ε k := (rfl)
  refine ⟨_, ?_, εL ∘L P ∘L fst ℂ E (Fin 0 → ℂ), ?_⟩
  · rw [← (kerEquiv (T x₀)).finrank_eq, finrank_real_eq_two_mul_finrank_complex]
  let A : X → E × (Fin 0 → ℂ) →L[ℝ] F := fun x ↦
    ((T x).restrictScalars ℝ).coprod ((0 : (Fin 0 → ℂ) →L[ℂ] F).restrictScalars ℝ)
  have hA : ContinuousAt A x₀ := hT.continuousLinearMapCoprod continuousAt_const
  -- At `x₀` the pair `(e, l) ↦ (T x₀ e, ε (P e))` is bijective, hence invertible.
  let B := (A x₀).prod ((εL ∘L P ∘L fst ℂ E (Fin 0 → ℂ)).restrictScalars ℝ)
  have hB (e : E) (l : Fin 0 → ℂ) : B (e, l) = (T x₀ e, ε (P e)) := by simp [B, A, hεL]
  have hinj : B.ker = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun ⟨e, l⟩ he ↦ ?_
    rw [coe_coe, hB, Prod.mk_eq_zero, LinearEquiv.map_eq_zero_iff] at he
    have hmem : e ∈ (T x₀).ker := he.1
    have : e = 0 := by simpa [hP ⟨e, hmem⟩] using congrArg Subtype.val he.2
    exact Prod.ext this (Subsingleton.elim _ _)
  have hsurj : B.range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun ⟨f, w⟩ ↦ ?_
    obtain ⟨e, rfl⟩ := h₀ f
    refine ⟨(e - P e + ε.symm w, 0), ?_⟩
    rw [coe_coe, hB]
    refine Prod.ext ?_ ?_
    · simp
    · simp [hP]
  exact exists_isOpen_isInvertible_prod hA ⟨ContinuousLinearEquiv.ofBijective B hinj hsurj, rfl⟩

end Surjective

end ContinuousLinearMap

/-! ### Complex orientations along families -/

open Filter Set Topology ContinuousLinearMap

namespace TauCeti

section Coherence

section Chart

variable {E Λ F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup Λ]
  [NormedSpace ℂ Λ] [FiniteDimensional ℂ Λ] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] {D₂ : Λ →L[ℂ] F}
  {q : E × Λ →L[ℂ] G} {T T' : E →L[ℂ] F}

/-- A complex kernel chart reads complex positive elements of the determinant lines of two
complex-linear operators as positive multiples of each other. -/
private theorem sameRay_detLineChartEquiv_of_isComplexPositiveDetLine
    (h : (((T.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).prod
      (q.restrictScalars ℝ)).IsInvertible)
    (h' : (((T'.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).prod
      (q.restrictScalars ℝ)).IsInvertible)
    {z : (T.restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    {z' : (T'.restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    (hz : (T : E →ₗ[ℂ] F).IsComplexPositiveDetLine z)
    (hz' : (T' : E →ₗ[ℂ] F).IsComplexPositiveDetLine z') :
    SameRay ℝ (detLineChartEquiv (T'.restrictScalars ℝ) _ _ h' z')
      (detLineChartEquiv (T.restrictScalars ℝ) _ _ h z) := by
  obtain ⟨c, hc, hcz⟩ :=
    ((isComplexPositiveTMulDual_detLineChartEquiv_iff h).2 hz).exists_pos_smul_eq
      ((isComplexPositiveTMulDual_detLineChartEquiv_iff h').2 hz')
  rw [hcz]
  exact SameRay.sameRay_pos_smul_left _ hc

end Chart

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [TopologicalSpace X]
  {T : X → E →L[ℂ] F} {s : Set X}

/-- **Complex orientations are coherent.** Along a family of complex-linear operators which is
continuous and Fredholm on `s`, a family of complex positive elements of the determinant lines of
the underlying real operators is coherent on `s`: the complex orientations form a continuous
orientation of the determinant line bundle over `s`. -/
theorem isDetLineCoherentOn_of_isComplexPositiveDetLine (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, IsFredholm (T x)) {v : ∀ x, ((T x).restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    (hv : ∀ x ∈ s, (T x : E →ₗ[ℂ] F).IsComplexPositiveDetLine (v x)) :
    IsDetLineCoherentOn (fun x ↦ (T x).restrictScalars ℝ) v s := by
  refine isDetLineCoherentOn_iff.2 fun x₀ hx₀ ↦ ?_
  obtain ⟨S, hS, G, hG, q, U, hU, hxU, hinv⟩ := (hF x₀ hx₀).exists_isOpen_kernelChart
  -- A complex kernel chart of `T x₀`, valid on `U`, is a kernel chart of the real operators.
  have hinvℝ (x : X) (hx : T x ∈ U) : ((((T x).restrictScalars ℝ).coprod
      (S.subtypeL.restrictScalars ℝ)).prod (q.restrictScalars ℝ)).IsInvertible :=
    (hinv _ hx).restrictScalars
  have hTℝ : ContinuousWithinAt (fun x ↦ (T x).restrictScalars ℝ) s x₀ :=
    (restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.continuousAt.comp_continuousWithinAt
      (hT x₀ hx₀)
  have := (hF x₀ hx₀).finite_coker
  refine isDetLineCoherentWithinAt_of_eventually_sameRay hTℝ ((hF x₀ hx₀).restrictScalars ℝ)
    (hv x₀ hx₀).ne_zero (hinvℝ x₀ hxU) ?_
  filter_upwards [(hT x₀ hx₀).tendsto.eventually (hU.mem_nhds hxU), self_mem_nhdsWithin]
    with x hxU' hx
  exact ⟨hinvℝ x hxU', sameRay_detLineChartEquiv_of_isComplexPositiveDetLine _ _ (hv x₀ hx₀)
    (hv x hx)⟩

end Coherence

end TauCeti

namespace ContinuousLinearMap.IsFredholm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {A : E →L[ℂ] F}

/-- The determinant line of a complex-linear Fredholm operator has a complex positive element. -/
theorem exists_isComplexPositiveDetLine (hA : IsFredholm A) :
    ∃ z : (A.restrictScalars ℝ : E →ₗ[ℝ] F).detLine,
      (A : E →ₗ[ℂ] F).IsComplexPositiveDetLine z ∧ z ≠ 0 := by
  have := hA.finite_ker
  have := hA.finite_coker
  obtain ⟨z, hz⟩ := (A : E →ₗ[ℂ] F).exists_isComplexPositiveDetLine
  exact ⟨z, hz, hz.ne_zero⟩

/-- The **complex orientation** of the determinant line of the real operator underlying a
complex-linear Fredholm operator `A`: the orientation given by its complex positive elements
(`LinearMap.IsComplexPositiveDetLine`), which orient the complex kernel and cokernel of `A` by
their complex structures. -/
def complexDetLineOrientation (hA : IsFredholm A) :
    Module.Ray ℝ (A.restrictScalars ℝ : E →ₗ[ℝ] F).detLine :=
  rayOfNeZero ℝ hA.exists_isComplexPositiveDetLine.choose
    hA.exists_isComplexPositiveDetLine.choose_spec.2

/-- The complex orientation is the orientation of any complex positive element of the
determinant line. -/
theorem complexDetLineOrientation_eq (hA : IsFredholm A)
    {z : (A.restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    (hz : (A : E →ₗ[ℂ] F).IsComplexPositiveDetLine z) (hz0 : z ≠ 0) :
    hA.complexDetLineOrientation = rayOfNeZero ℝ z hz0 := by
  have := hA.finite_coker
  obtain ⟨c, hc, rfl⟩ := hA.exists_isComplexPositiveDetLine.choose_spec.1.exists_pos_smul_eq hz
  exact (ray_pos_smul _ hc _).symm

end ContinuousLinearMap.IsFredholm

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Transport preserves complex orientations.** Along a path of complex-linear operators which
is continuous and Fredholm between `a` and `b`, orientation transport of the determinant lines of
the underlying real operators carries the complex orientation at `a` to the complex orientation
at `b`. -/
theorem detLineOrientationTransport_complexDetLineOrientation {T : ℝ → E →L[ℂ] F} {a b : ℝ}
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) :
    detLineOrientationTransport (T := fun t ↦ (T t).restrictScalars ℝ) a b
        ((restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hT)
        (fun t ht ↦ (hF t ht).restrictScalars ℝ)
        (hF a left_mem_uIcc).complexDetLineOrientation =
      (hF b right_mem_uIcc).complexDetLineOrientation := by
  classical
  -- A family of complex positive elements along the path.
  let v : ∀ t, ((T t).restrictScalars ℝ : E →ₗ[ℝ] F).detLine := fun t ↦
    if h : IsFredholm (T t) then h.exists_isComplexPositiveDetLine.choose else 0
  have hv (t : ℝ) (ht : t ∈ uIcc a b) :
      (T t : E →ₗ[ℂ] F).IsComplexPositiveDetLine (v t) ∧ v t ≠ 0 := by
    simp only [v, dite_eq_left (hF t ht)]
    exact (hF t ht).exists_isComplexPositiveDetLine.choose_spec
  have hcoh := isDetLineCoherentOn_of_isComplexPositiveDetLine hT hF fun t ht ↦ (hv t ht).1
  rw [(hF a left_mem_uIcc).complexDetLineOrientation_eq (hv a left_mem_uIcc).1
      (hv a left_mem_uIcc).2,
    (hF b right_mem_uIcc).complexDetLineOrientation_eq (hv b right_mem_uIcc).1
      (hv b right_mem_uIcc).2]
  exact detLineOrientationTransport_rayOfNeZero _ _ hcoh

section Invertible

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]

/-- A complex positive element `z` of the determinant line of a complex-linear map `f` whose
underlying real map is an onto operator `A` is nonzero, and so is its image in the determinant line
of `A`. -/
theorem _root_.LinearMap.IsComplexPositiveDetLine.detLineCongrOfEq_ne_zero {f : E →ₗ[ℂ] F}
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) {A : E →L[ℝ] F}
    (hf : f.restrictScalars ℝ = A) (hA : Function.Surjective A) :
    LinearMap.detLineCongrOfEq hf z ≠ 0 := by
  rw [LinearEquiv.map_ne_zero_iff]
  refine hz.ne_zero_of_surjective ?_
  rw [← LinearMap.coe_restrictScalars ℝ f, hf, ContinuousLinearMap.coe_coe]
  exact hA

variable [CompleteSpace E] [CompleteSpace F]

/-- **Transport from a complex-linear operator along invertible operators.** Let `T` be a path of
invertible operators between real Banach spaces with compatible complex structures, continuous
between `a` and `b`, whose operator `T a` is complex linear: it is the real map underlying `f`.
Orientation transport carries the complex orientation of `T a`, that of any complex positive
element `z` of its determinant line (`LinearMap.IsComplexPositiveDetLine`), to the orientation of
the determinant line of `T b` given by invertibility, that of the element `1` under
`LinearMap.detLineEquivOfBijective`. So, relative to the complex orientation at `T a`, the
determinant sign of `T b` is positive. The complex structures need not come from complex norms. -/
theorem detLineOrientationTransport_rayOfNeZero_detLineCongrOfEq_of_isComplexPositiveDetLine
    {T : ℝ → E →L[ℝ] F} {a b : ℝ} (hT : ContinuousOn T (uIcc a b))
    (hinv : ∀ t ∈ uIcc a b, (T t).IsInvertible) {f : E →ₗ[ℂ] F}
    (hf : f.restrictScalars ℝ = T a) {z : (f.restrictScalars ℝ).detLine}
    (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport a b hT (fun t ht ↦ (hinv t ht).isFredholm)
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero hf (hinv a left_mem_uIcc).surjective)) =
      rayOfNeZero ℝ ((LinearMap.detLineEquivOfBijective
        (hinv b right_mem_uIcc).bijective).symm 1) (by simp) := by
  have hfb : Function.Bijective (f.restrictScalars ℝ) := by
    rw [hf, ContinuousLinearMap.coe_coe]
    exact (hinv a left_mem_uIcc).bijective
  have : Subsingleton (F ⧸ LinearMap.range f) :=
    Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hfb.2)
  -- `z` is a positive multiple of the element `1` of invertibility, which is complex positive.
  obtain ⟨c, hc, rfl⟩ :=
    (f.isComplexPositiveDetLine_detLineEquivOfBijective_symm_one hfb).exists_pos_smul_eq hz
  simp_rw [LinearEquiv.map_smul]
  rw [ray_pos_smul ((LinearEquiv.map_ne_zero_iff _).2 ((LinearEquiv.map_ne_zero_iff _).2
      one_ne_zero)) hc,
    ← detLineOrientationTransport_rayOfNeZero_detLineEquivOfBijective_symm_one hT hinv]
  congr 2
  apply (LinearMap.detLineEquivOfBijective (hinv a left_mem_uIcc).bijective).injective
  rw [LinearMap.detLineEquivOfBijective_detLineCongrOfEq, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end Invertible

end TauCeti
