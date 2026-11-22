/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Manifold.MFDeriv.Inner
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Form
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AddOneForm
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The exact prequantum line

A real one-form `θ` defines the connection `d + iθ/ℏ` on the trivial complex line.
The connection is encoded by Mathlib's `CovariantDerivative` on the real smooth bundle with
fibre `ℂ`. It is smooth, commutes with constant complex scalars, and preserves the standard
Hermitian metric. Its curvature operator at `x` is multiplication by `i dθ/ℏ`, hence by `-iω/ℏ`
when `ω = -dθ` at `x`, on fields differentiable at `x` and sections `C²` there.
Adding a one-form whose exterior derivative vanishes at `x` preserves this curvature evaluation.
The construction does not require nondegeneracy of the two-form.

This is the trivial-line construction in Schottenloher, *Lecture Notes on
Geometric Quantization*, version 15.6, Example 7.3 and Remark 7.4, pp. 96–97,
with the conjugate line convention and curvature scale `1/ℏ`.
-/

public noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

section Basic

variable [IsManifold I 1 M]

private def exactPrequantumPotential (θ : SmoothForm I M ℝ 1) (ℏ : ℝ) (x : M) :
    ℂ →L[ℝ] TangentSpace I x →L[ℝ] ℂ :=
  ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (TangentSpace I x) ℂ)
    (SmoothForm.degreeOneEquiv θ x)).comp
      (ℏ⁻¹ • ContinuousLinearMap.lsmul ℝ ℂ Complex.I)

private theorem exactPrequantumPotential_apply (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (x : M) (z : ℂ) (v : TangentSpace I x) :
    exactPrequantumPotential θ ℏ x z v = (θ.val x ![v] / ℏ) • (Complex.I * z) := by
  simp [exactPrequantumPotential, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The connection `d + iθ/ℏ` on the trivial complex line, regarded as a real
smooth vector bundle. Prequantization uses `0 < ℏ`; the formula is defined at
all real scales, with Lean's totalized inverse. -/
def exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (ℏ : ℝ) :
    CovariantDerivative I ℂ (Trivial M ℂ) :=
  (CovariantDerivative.trivial (I := I) ℂ).addOneForm (exactPrequantumPotential θ ℏ)

/-- Evaluation of the exact-line connection in its global unit frame. -/
@[simp]
theorem exactPrequantumConnection_apply (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (s : M → ℂ) (x : M) (v : TangentSpace I x) :
    exactPrequantumConnection θ ℏ s x v =
      mvfderiv I s x v + ((θ : RoughForm I M ℝ 1) x ![v] / ℏ) • (Complex.I * s x) := by
  simp [exactPrequantumConnection, CovariantDerivative.addOneForm, exactPrequantumPotential_apply]

/-- The zero primitive gives the ordinary derivative connection. -/
@[simp]
theorem exactPrequantumConnection_zero (ℏ : ℝ) :
    exactPrequantumConnection (0 : SmoothForm I M ℝ 1) ℏ =
      CovariantDerivative.trivial (I := I) ℂ := by
  ext s x v
  simp only [exactPrequantumConnection_apply, ZeroMemClass.coe_zero, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero, zero_div, zero_smul, CovariantDerivative.trivial_apply]
  exact add_zero _

/-- Changing the primitive adds precisely the corresponding imaginary one-form
to the line connection. No differentiability of the section is required. -/
theorem exactPrequantumConnection_add_apply (θ β : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (s : M → ℂ) (x : M) (v : TangentSpace I x) :
    exactPrequantumConnection (θ + β) ℏ s x v =
      exactPrequantumConnection θ ℏ s x v +
        (β.val x ![v] / ℏ) • (Complex.I * s x) := by
  simp only [exactPrequantumConnection_apply, AddMemClass.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, add_div, add_smul]
  abel

/-- The endomorphism-valued difference of two exact-line connections is multiplication by
`i(θ - β)/ℏ`. -/
theorem exactPrequantumConnection_difference_apply (θ β : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (x : M) (z : ℂ) (v : TangentSpace I x) :
    ((exactPrequantumConnection θ ℏ).difference (exactPrequantumConnection β ℏ)) x z v =
      ((θ.val x ![v] - β.val x ![v]) / ℏ) • (Complex.I * z) := by
  have hz : MDifferentiableAt I (I.prod 𝓘(ℝ, ℂ))
      (T% (fun _ ↦ z : Π y, Trivial M ℂ y)) x := by
    simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply]
    exact mdifferentiableAt_const
  rw [CovariantDerivative.difference, IsCovariantDerivativeOn.difference_apply (hσ := hz)]
  simp only [sub_apply, exactPrequantumConnection_apply, sub_div, sub_smul]
  abel

/-- The exact-line connection commutes with constant complex scalars. This also
holds for the totalized derivative on sections not differentiable at the point. -/
@[simp]
theorem exactPrequantumConnection_const_smul (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (s : M → ℂ) (c : ℂ) :
    exactPrequantumConnection θ ℏ (c • s) = c • exactPrequantumConnection θ ℏ s := by
  funext x
  ext v
  simp only [exactPrequantumConnection_apply, mvfderiv_const_smul_field, Pi.smul_apply,
    smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- The Leibniz rule for the exact-line connection with a complex-valued coefficient. -/
theorem exactPrequantumConnection_smul_apply (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    {g s : M → ℂ} {x : M} (hg : MDifferentiableAt I 𝓘(ℝ, ℂ) g x)
    (hs : MDifferentiableAt I 𝓘(ℝ, ℂ) s x) (v : TangentSpace I x) :
    exactPrequantumConnection θ ℏ (g • s) x v =
      g x * exactPrequantumConnection θ ℏ s x v + mvfderiv I g x v * s x := by
  rw [exactPrequantumConnection_apply, exactPrequantumConnection_apply, mvfderiv_smul_algebra hg hs]
  simp only [Pi.smul_apply', add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, Complex.real_smul]
  ring

/-- The exact-line connection preserves the standard Hermitian metric on `ℂ`. -/
theorem mvfderiv_inner_eq_exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    {s t : M → ℂ} {x : M}
    (hs : MDifferentiableAt I 𝓘(ℝ, ℂ) s x)
    (ht : MDifferentiableAt I 𝓘(ℝ, ℂ) t x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner ℂ (s y) (t y)) x v =
      inner ℂ (exactPrequantumConnection θ ℏ s x v) (t x) +
        inner ℂ (s x) (exactPrequantumConnection θ ℏ t x v) := by
  rw [mvfderiv_inner_apply hs ht]
  simp only [exactPrequantumConnection_apply, RCLike.inner_apply', Complex.real_smul,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The real bundle metric underlying the standard Hermitian metric is parallel. -/
theorem isMetricCompatible_exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (ℏ : ℝ) :
    (exactPrequantumConnection θ ℏ).IsMetricCompatible := by
  rw [CovariantDerivative.isMetricCompatible_iff]
  intro x X s t _ hs ht
  simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
    Trivial.trivialization_apply] at hs ht
  have hd := Complex.reCLM.mvfderiv_comp_apply
    (mdifferentiableAt_iff_differentiableAt.mpr
      ((isBoundedBilinearMap_inner (𝕜 := ℂ) (E := ℂ)).differentiableAt (s x, t x)) |>.comp x
        (hs.prodMk_space ht)) (X x)
  simp only [real_inner_eq_re_inner, RCLike.re_to_complex, Function.comp_def,
    Complex.reCLM_apply] at hd ⊢
  rw [hd, mvfderiv_inner_eq_exactPrequantumConnection θ ℏ hs ht, Complex.add_re]

/-- Pulling back the primitive along a smooth map pulls back the connection on sections
differentiable at the image point. -/
theorem exactPrequantumConnection_mpullback_apply
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold J 1 M']
    {f : M → M'} (hf : ContMDiff I J ∞ f) (θ : SmoothForm J M' ℝ 1) (ℏ : ℝ)
    {s : M' → ℂ} {x : M} (hs : MDifferentiableAt J 𝓘(ℝ, ℂ) s (f x)) (v : TangentSpace I x) :
    exactPrequantumConnection (SmoothForm.mpullback f hf θ) ℏ (s ∘ f) x v =
      exactPrequantumConnection θ ℏ s (f x) (mfderiv I J f x v) := by
  rw [exactPrequantumConnection_apply, exactPrequantumConnection_apply,
    SmoothForm.mpullback_apply_one, mvfderiv_comp_apply x hs (hf.mdifferentiableAt (by simp))]
  rfl

/-- Complex conjugation intertwines the connections from `θ` and `-θ`. -/
theorem exactPrequantumConnection_neg_conj_apply (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (s : M → ℂ) (x : M) (v : TangentSpace I x) :
    exactPrequantumConnection (-θ) ℏ (starRingEnd ℂ ∘ s) x v =
      starRingEnd ℂ (exactPrequantumConnection θ ℏ s x v) := by
  let C : ℂ →L[ℝ] ℂ := Complex.conjCLE
  have hc : (C : ℂ → ℂ) = starRingEnd ℂ := funext Complex.conjCLE_apply
  have hd : mvfderiv I (C ∘ s) x v = C (mvfderiv I s x v) := by
    by_cases hs : MDifferentiableAt I 𝓘(ℝ, ℂ) s x
    · exact C.mvfderiv_comp_apply hs v
    -- Conjugation is involutive, so both totalized derivatives vanish in this case.
    have hcs : ¬ MDifferentiableAt I 𝓘(ℝ, ℂ) (C ∘ s) x := fun hcs ↦
      hs (by simpa only [hc, Function.comp_def, starRingEnd_apply, star_star] using
        C.mdifferentiableAt.comp x hcs)
    simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hcs,
      mfderiv_zero_of_not_mdifferentiableAt hs, ContinuousLinearMap.comp_zero, zero_apply, map_zero]
  rw [exactPrequantumConnection_apply, exactPrequantumConnection_apply, ← hc, hd, hc]
  simp only [NegMemClass.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, neg_div,
    neg_smul, Function.comp_apply, Complex.real_smul, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, neg_mul, mul_neg]

end Basic

section Smooth

variable [IsManifold I 1 M]

/-- The exact-line connection is `C^n` for every finite order and for `n = ∞`. -/
instance {n : ℕ∞ω} [ENat.LEInfty n] (θ : SmoothForm I M ℝ 1) (ℏ : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (exactPrequantumConnection θ ℏ) n where
  contMDiff.contMDiff {s} hs := by
    rw [contMDiffOn_univ] at hs ⊢
    have hs' : ContMDiff I 𝓘(ℝ, ℂ) (n + 1) s := fun x ↦ by
      simpa only [contMDiffAt_section_iff, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_apply] using hs x
    have hC : ContMDiff I (I.prod 𝓘(ℝ, ℝ →L[ℝ] ℂ)) n
        (fun x ↦ TotalSpace.mk' (ℝ →L[ℝ] ℂ)
          (E := fun _ : M ↦ ℝ →L[ℝ] ℂ) x
          (ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℝ ℂ 1 (ℏ⁻¹ • (Complex.I • s x)))) := by
      intro x
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, ?_⟩
      -- Both trivializations are the identity, so the coordinates are the coefficient map.
      simpa only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
        Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, Function.comp_def,
        ContinuousLinearMap.lsmul_apply, smul_assoc] using
        ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℝ ℂ 1).contMDiff.comp
          ((ContinuousLinearMap.lsmul ℝ ℂ (ℏ⁻¹ • Complex.I)).contMDiff.comp
            (hs'.of_le le_self_add))).contMDiffAt
    have hA := hC.clm_bundle_comp ((SmoothForm.degreeOneEquiv θ).contMDiff.of_le ENat.LEInfty.out)
    have hd := hs'.contMDiff_totalSpaceMk_mvfderiv
    convert hd.add_section hA using 1
    funext x
    congr 1
    ext v
    simp [exactPrequantumConnection_apply, div_eq_mul_inv, mul_comm, mul_assoc]

end Smooth

section Curvature

variable [CompleteSpace E] [IsManifold I 2 M]

/-- Curvature of the exact-line connection at `x`, evaluated on vector fields differentiable
at `x` and a section `C²` at `x`. -/
theorem curvatureOperator_exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    {X Y : Π x : M, TangentSpace I x} {s : M → ℂ} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hs : ContMDiffAt I 𝓘(ℝ, ℂ) 2 s x) :
    (exactPrequantumConnection θ ℏ).curvatureOperator X Y s x =
      (mextDeriv (θ : RoughForm I M ℝ 1) x ![X x, Y x] / ℏ) • (Complex.I * s x) := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := 2) (by simp)
  let a (Z : Π y : M, TangentSpace I y) := fun y ↦ θ.val y ![Z y] / ℏ
  have ha {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) :
      MDifferentiableAt I 𝓘(ℝ) (a Z) x := by
    have hθ : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ θ.val y ![Z y]) x := by
      simpa only [Matrix.vec_single_eq_const] using
        θ.mdifferentiableAt_apply_vectorField (V := fun _ ↦ Z) (fun _ ↦ hZ)
    simpa only [a, div_eq_mul_inv, Pi.mul_def] using
      hθ.mul (mdifferentiableAt_const (c := ℏ⁻¹))
  have hIs : MDifferentiableAt I 𝓘(ℝ, ℂ) (Complex.I • s) x :=
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I).mdifferentiableAt.comp x
      (hs.mdifferentiableAt (by simp))
  have htriv (f : Π y : M, Trivial M ℂ y) (hf : MDifferentiableAt I 𝓘(ℝ, ℂ) f x) :
      MDifferentiableAt I (I.prod 𝓘(ℝ, ℂ)) (T% f) x := by
    simpa only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply] using hf
  have hprod (Z : Π y : M, TangentSpace I y) : a Z • (Complex.I • s) =
      (fun y ↦ exactPrequantumPotential θ ℏ y (s y) (Z y)) := by
    funext y
    simp only [a, Pi.smul_apply', Pi.smul_apply, smul_eq_mul, exactPrequantumPotential_apply]
  have hD {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) :
      MDifferentiableAt I (I.prod 𝓘(ℝ, ℂ))
        (T% (fun y ↦ CovariantDerivative.trivial ℂ s y (Z y) : Π y, Trivial M ℂ y)) x := by
    simp only [CovariantDerivative.trivial_apply]
    exact htriv _ (mdifferentiableAt_mvfderiv_apply hs le_rfl hZ)
  rw [exactPrequantumConnection, CovariantDerivative.curvatureOperator_addOneForm _ _
    (hD hX) (hD hY) (htriv _ (hprod X ▸ (ha hX).smul hIs))
    (htriv _ (hprod Y ▸ (ha hY).smul hIs)),
    CovariantDerivative.curvatureOperator_trivial hX hY (hs.of_le (by simp)),
    θ.mextDeriv_apply_one hX hY]
  simp only [CovariantDerivative.trivial_apply, zero_add, ← hprod X, ← hprod Y]
  have hdscale (Z : Π y : M, TangentSpace I y) :
      mvfderiv I (a Z) x = ℏ⁻¹ • mvfderiv I (fun y ↦ θ.val y ![Z y]) x := by
    rw [show a Z = ℏ⁻¹ • (fun y ↦ θ.val y ![Z y]) by
      funext y
      simp only [a, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm],
      mvfderiv_const_smul_field]
  rw [mvfderiv_smul (ha hY) hIs, mvfderiv_smul (ha hX) hIs, hdscale X, hdscale Y]
  simp only [mvfderiv_const_smul_field, Pi.smul_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, exactPrequantumPotential_apply, a,
    Complex.real_smul, smul_eq_mul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- If `σ = -dθ` at `x`, the curvature operator at `x` acts by `-iσ(X, Y)/ℏ` on
fields differentiable at `x` and sections `C²` there. -/
theorem curvatureOperator_exactPrequantumConnection_of_mextDeriv_eq_neg
    (θ : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) (ℏ : ℝ)
    {X Y : Π x : M, TangentSpace I x} {s : M → ℂ} {x : M}
    (hθ : mextDeriv θ.val x = -σ.val x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hs : ContMDiffAt I 𝓘(ℝ, ℂ) 2 s x) :
    (exactPrequantumConnection θ ℏ).curvatureOperator X Y s x =
      -(σ.val x ![X x, Y x] / ℏ) • (Complex.I * s x) := by
  rw [curvatureOperator_exactPrequantumConnection θ ℏ hX hY hs, hθ]
  rw [ContinuousAlternatingMap.neg_apply, neg_div]

/-- Adding a one-form whose exterior derivative vanishes at `x` preserves the curvature operator
there on fields differentiable at `x` and sections `C²` there. -/
theorem curvatureOperator_exactPrequantumConnection_add_of_mextDeriv_eq_zero
    (θ β : SmoothForm I M ℝ 1) (ℏ : ℝ)
    {X Y : Π x : M, TangentSpace I x} {s : M → ℂ} {x : M}
    (hβ : mextDeriv β.val x = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hs : ContMDiffAt I 𝓘(ℝ, ℂ) 2 s x) :
    (exactPrequantumConnection (θ + β) ℏ).curvatureOperator X Y s x =
      (exactPrequantumConnection θ ℏ).curvatureOperator X Y s x := by
  rw [curvatureOperator_exactPrequantumConnection (θ + β) ℏ hX hY hs,
    curvatureOperator_exactPrequantumConnection θ ℏ hX hY hs]
  have hd := congrArg (fun α : SmoothForm I M ℝ 2 ↦ α.val x)
    ((mextDerivₗ I (F := ℝ) 1).map_add θ β)
  simp only [mextDerivₗ_apply, AddMemClass.coe_add, Pi.add_apply] at hd
  rw [AddMemClass.coe_add, hd, hβ, add_zero]

end Curvature

section CurvatureTensor

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- The curvature tensor is multiplication by `i dθ/ℏ` on the complex fibre. -/
@[simp]
theorem curvatureTensor_exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (x : M) (u v : TangentSpace I x) (z : ℂ) :
    (exactPrequantumConnection θ ℏ).curvatureTensor x u v z =
      ((mextDerivₗ I 1 θ).val x ![u, v] / ℏ) • (Complex.I * z) := by
  obtain ⟨X, hX, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  have hz : ContMDiff I (I.prod 𝓘(ℝ, ℂ)) ∞ (T% (fun _ ↦ z : Π y, Trivial M ℂ y)) := fun y ↦ by
    simp only [contMDiffAt_section_iff, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply]
    exact contMDiffAt_const
  rw [CovariantDerivative.curvatureTensor_apply _ x hX hY hz, mextDerivₗ_apply]
  exact curvatureOperator_exactPrequantumConnection θ ℏ
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
    (contMDiffAt_const (c := z))

/-- A closed primitive gives zero endomorphism-valued curvature form. -/
theorem curvatureForm_exactPrequantumConnection_eq_zero_of_isClosed
    {θ : SmoothForm I M ℝ 1} (hθ : θ.IsClosed) (ℏ : ℝ) :
    (exactPrequantumConnection θ ℏ).curvatureForm = 0 := by
  rw [CovariantDerivative.curvatureForm_eq_iff]
  intro x u v z
  simp [(SmoothForm.isClosed_iff_mextDerivₗ_eq_zero θ).mp hθ]

end CurvatureTensor

end TauCeti
