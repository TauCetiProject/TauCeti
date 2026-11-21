/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Plane.Complex
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Planar differential calculus on open subsets of `ℂ`

This file develops the coordinate calculus for differential forms on an arbitrary open subset
`U : TopologicalSpace.Opens ℂ`:

* **Coordinate differential decompositions** (`TauCeti.mextDeriv_ofFunction_opens_complex_real_eq`,
  `TauCeti.mextDeriv_ofFunction_opens_complex_eq_wirtinger`): for any function on `U` with an
  ambient representative, its exterior derivative decomposes along `dx, dy` and along `dz, dbar z`
  without regularity assumptions.
* **Canonical two-form coefficient** (`TauCeti.planarTwoFormCoeff`): every two-form `η` on `U` is
  uniquely determined by its evaluation on the positive frame `(1, i)`
  (`TauCeti.roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy`,
  `TauCeti.roughForm_two_eq_wedgeWith_complexDz_wedgeWith_complexDzBar`,
  `TauCeti.planarTwoFormCoeff_injective`), and `C^n` forms have `C^n` coefficients
  (`TauCeti.IsSmoothForm.contMDiff_planarTwoFormCoeff`).
* **Exterior derivatives of planar one-forms**
  (`TauCeti.planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz`,
  `TauCeti.planarTwoFormCoeff_mextDeriv_wedgeWith_complexDzBar`,
  `TauCeti.planarTwoFormCoeff_mextDeriv_wedgeWith_complexDx_add_complexDy`): explicit coordinate
  formulas for `d(g dz)`, `d(f dbar z)`, and `d(a dx + b dy)` in terms of Wirtinger and real
  partial derivatives.

## References

* A. Rainer, *Advanced Complex Analysis*, §10 and Theorem 12.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I.
-/

public noncomputable section

open Complex Set TopologicalSpace
open scoped ContDiff Manifold ComplexConjugate Topology

namespace TauCeti

/-! ### Differential decompositions on an open subset `U ⊆ ℂ` -/

section Differentials

private theorem mextDeriv_ofFunction_apply_finOne {E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (x : M) (w : Fin 1 → TangentSpace I x) :
    mextDeriv (RoughForm.ofFunction I f) x w = mfderiv I 𝓘(ℝ, F) f x (w 0) := by
  have hw : w = ![w 0] := funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
  nth_rw 1 [hw]
  rw [mextDeriv_ofFunction_apply]

private theorem comp_finCast_self {α : Type*} {n : ℕ} (h : n = n) (v : Fin n → α) :
    v ∘ Fin.cast h = v := by
  ext i
  simp

/-- Real coordinate differential decomposition on an open subset `U ⊆ ℂ`: for any function
`v : U → F` into a real normed space `F` and any ambient representative `v' : ℂ → F` agreeing
with `v` on `U`, `dv = (∂_x v') dx + (∂_y v') dy`. No regularity hypothesis is required for
this identity of totalized derivatives. -/
theorem mextDeriv_ofFunction_opens_complex_real_eq {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {v : U → F} {v' : ℂ → F}
    (hv : ∀ z : U, v' z = v z) :
    mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) v) =
      RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ fderiv ℝ v' z 1)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.val) +
        RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ fderiv ℝ v' z Complex.I)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDy.val) := by
  ext z w
  rw [mextDeriv_ofFunction_apply_finOne, ← mvfderiv_apply_eq_mfderiv_apply,
    Manifold.mvfderiv_opens_eq_fderiv_apply hv z (w 0)]
  simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply, RoughForm.wedgeWith_apply_zero_left,
    comp_finCast_self, RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, mpullback_apply,
    Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe, SmoothForm.complexDx_apply,
    SmoothForm.complexDy_apply]
  set a : ℂ := NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (w 0))
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simp [Complex.real_smul]
  conv_lhs => rw [ha]
  rw [map_add, map_smul, map_smul]

/-- Complex Wirtinger differential decomposition on an open subset `U ⊆ ℂ`: for any function
`u : U → W` into a complex normed space `W` and any ambient representative `u' : ℂ → W`
agreeing with `u` on `U`, `du = (∂_z u') dz + (\bar∂ u') dbar z`. No regularity hypothesis is
required. -/
theorem mextDeriv_ofFunction_opens_complex_eq_wirtinger {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {u : U → W} {u' : ℂ → W}
    (hu : ∀ z : U, u' z = u z) :
    mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) u) =
      RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ wirtingerDeriv u' z 1)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDz.val) +
        RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ conjWirtingerDeriv u' z 1)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDzBar.val) := by
  ext z w
  rw [mextDeriv_ofFunction_apply_finOne, ← mvfderiv_apply_eq_mfderiv_apply,
    Manifold.mvfderiv_opens_eq_fderiv_apply hu z (w 0)]
  simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply, RoughForm.wedgeWith_apply_zero_left,
    comp_finCast_self, RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, mpullback_apply,
    Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe, SmoothForm.complexDz_apply,
    SmoothForm.complexDzBar_apply]
  exact fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := u') (z : ℂ) _

end Differentials

/-! ### Unique coefficient extraction for planar two-forms -/

section TwoFormCoeff

/-- The canonical `dx ∧ dy` coefficient of a `2`-form `η` on an open subset `U ⊆ ℂ` with values
in a real normed space `F`: the evaluation of `η` at the positive coordinate frame `(1, i)`. -/
def planarTwoFormCoeff {U : Opens ℂ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) : F :=
  η z ![(Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1),
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)]

/-- Evaluating `planarTwoFormCoeff η` at `z : U` applies `η z` to the positive coordinate frame
`(1, i)`. -/
theorem planarTwoFormCoeff_apply {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff η z =
      η z ![(Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
          ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1),
        (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
          ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)] := by
  rw [planarTwoFormCoeff]

private def planarCoordEquiv {U : Opens ℂ} (z : U) : TangentSpace 𝓘(ℝ, ℂ) z ≃L[ℝ] ℂ :=
  (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).trans
    (NormedSpace.fromTangentSpace (z : ℂ))

private theorem planarCoordEquiv_apply {U : Opens ℂ} (z : U) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    planarCoordEquiv z v =
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v) :=
  rfl

private theorem planarTwoFormCoeff_eq_apply_symm {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff η z =
      η z ![(planarCoordEquiv z).symm 1, (planarCoordEquiv z).symm Complex.I] := by
  simp [planarTwoFormCoeff_apply, planarCoordEquiv]

@[simp]
theorem planarTwoFormCoeff_zero {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (z : U) :
    planarTwoFormCoeff (0 : RoughForm 𝓘(ℝ, ℂ) U F 2) z = 0 := by
  simp [planarTwoFormCoeff_apply]

@[simp]
theorem planarTwoFormCoeff_add {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η₁ η₂ : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (η₁ + η₂) z =
      planarTwoFormCoeff η₁ z + planarTwoFormCoeff η₂ z := by
  simp [planarTwoFormCoeff_apply]

@[simp]
theorem planarTwoFormCoeff_smul {U : Opens ℂ} {R F : Type*} [Semiring R]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R) (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (c • η) z = c • planarTwoFormCoeff η z := by
  simp [planarTwoFormCoeff_apply]

/-- Mapping coefficients commutes with extracting `planarTwoFormCoeff`. -/
@[simp]
theorem planarTwoFormCoeff_mapCoeff {U : Opens ℂ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (RoughForm.mapCoeff L η) z = L (planarTwoFormCoeff η z) := by
  simp [planarTwoFormCoeff_apply]

/-- Every alternating two-form on `U ⊆ ℂ` with values in a real normed space `F` equals
`(planarTwoFormCoeff η) dx ∧ dy`. -/
theorem roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) :
    η = RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) (planarTwoFormCoeff η))
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val)) := by
  funext z
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  let b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z) :=
    Complex.basisOneI.map (planarCoordEquiv z).symm.toLinearEquiv
  refine b.ext_alternating fun v hv ↦ ?_
  have hv_pair : (fun i ↦ b (v i)) = ![b (v 0), b (v 1)] := by
    ext i
    fin_cases i <;> simp
  rw [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.coe_toAlternatingMap,
    hv_pair, RoughForm.wedgeWith_apply_zero_left, comp_finCast_self, mpullback_apply_pair]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    SmoothForm.complexDx_wedge_complexDy_apply]
  have hb0 : b 0 = (planarCoordEquiv z).symm 1 := by simp [b]
  have hb1 : b 1 = (planarCoordEquiv z).symm Complex.I := by simp [b]
  match h0 : v 0, h1 : v 1 with
  | 0, 0 => exact absurd (hv (h0.trans h1.symm)) (by decide)
  | 0, 1 =>
    simp only [hb0, hb1, ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply,
      planarTwoFormCoeff_eq_apply_symm]
    simp
  | 1, 0 =>
    have hswap :
        ![(planarCoordEquiv z).symm Complex.I, (planarCoordEquiv z).symm 1] =
          ![(planarCoordEquiv z).symm 1, (planarCoordEquiv z).symm Complex.I] ∘
            Equiv.swap (0 : Fin 2) 1 := by
      ext i
      fin_cases i <;> simp
    simp only [hb0, hb1, ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply,
      planarTwoFormCoeff_eq_apply_symm]
    rw [hswap, ← ContinuousAlternatingMap.coe_toAlternatingMap,
      (η z).map_swap _ (i := 0) (j := 1) (by decide),
      ContinuousAlternatingMap.coe_toAlternatingMap]
    simp
  | 1, 1 => exact absurd (hv (h0.trans h1.symm)) (by decide)

/-- Evaluating `(h dx ∧ dy)` at the positive coordinate frame recovers `h`. -/
@[simp]
theorem planarTwoFormCoeff_wedgeWith_complexDx_wedge_complexDy {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : U → F) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val))) z = h z := by
  rw [planarTwoFormCoeff_eq_apply_symm, RoughForm.wedgeWith_apply_zero_left,
    comp_finCast_self, mpullback_apply_pair]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    SmoothForm.complexDx_wedge_complexDy_apply,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

/-- Two planar `2`-forms on `U ⊆ ℂ` agree iff their `dx ∧ dy` coefficients agree. -/
theorem planarTwoFormCoeff_injective {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Function.Injective (planarTwoFormCoeff (U := U) (F := F)) := by
  intro η₁ η₂ h
  rw [roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy η₁,
    roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy η₂, h]

/-- Evaluating `(h dz ∧ dbar z)` at the positive coordinate frame gives `-2i • h`. -/
@[simp]
theorem planarTwoFormCoeff_wedgeWith_complexDz_wedgeWith_complexDzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (h : U → W) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
            SmoothForm.complexDz.val SmoothForm.complexDzBar.val))) z = (-2 * Complex.I) • h z := by
  rw [planarTwoFormCoeff_eq_apply_symm, RoughForm.wedgeWith_apply_zero_left,
    comp_finCast_self, mpullback_apply_pair]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    SmoothForm.complexDz_wedgeWith_complexDzBar_apply, SmoothForm.complexDx_wedge_complexDy_apply,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

/-- Every alternating two-form on `U ⊆ ℂ` with values in a complex normed space `W` equals
`((-2i)⁻¹ • planarTwoFormCoeff η) dz ∧ dbar z`. -/
theorem roughForm_two_eq_wedgeWith_complexDz_wedgeWith_complexDzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (η : RoughForm 𝓘(ℝ, ℂ) U W 2) :
    η = RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦
        (-2 * Complex.I)⁻¹ • planarTwoFormCoeff η z)
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
          SmoothForm.complexDz.val SmoothForm.complexDzBar.val)) := by
  apply planarTwoFormCoeff_injective
  funext z
  rw [planarTwoFormCoeff_wedgeWith_complexDz_wedgeWith_complexDzBar, smul_smul,
    mul_inv_cancel₀ (by simp [Complex.I_ne_zero]), one_smul]

/-- A `C^n` planar `2`-form on an open subset `U ⊆ ℂ` has a `C^n` coefficient function. -/
theorem IsSmoothForm.contMDiff_planarTwoFormCoeff {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {η : RoughForm 𝓘(ℝ, ℂ) U F 2} (hη : IsSmoothForm 𝓘(ℝ, ℂ) n η) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, F) n (planarTwoFormCoeff η) := by
  intro z
  have htriv :=
    (isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.1 hη) z ![1, Complex.I]
  refine htriv.congr_of_eventuallyEq ?_
  filter_upwards [Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    (I := 𝓘(ℝ, ℂ)) z] with y hy
  rw [planarTwoFormCoeff_apply]
  congr 1
  ext i
  have hi := hy (![1, Complex.I] i)
  rw [TangentBundle.symmL_model_space] at hi
  apply (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) y).injective
  rw [Function.comp_apply, hi]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, ContinuousLinearEquiv.apply_symm_apply]
    exact NormedSpace.fromTangentSpace_symm_apply (y : ℂ) 1
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      ContinuousLinearEquiv.apply_symm_apply]
    exact NormedSpace.fromTangentSpace_symm_apply (y : ℂ) Complex.I

end TwoFormCoeff

/-! ### Exterior derivatives of planar one-forms -/

section OneFormDeriv

private theorem mdifferentiableAt_mpullback_subtype_val {U : Opens ℂ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {α : RoughForm 𝓘(ℝ, ℂ) ℂ G 1}
    (hα : IsSmoothForm 𝓘(ℝ, ℂ) ∞ α) (z : U) :
    MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ [⋀^Fin 1]→L[ℝ] G))
      (fun y : U ↦ Bundle.TotalSpace.mk' (ℂ [⋀^Fin 1]→L[ℝ] G) y
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α y)) z :=
  ((hα.mpullback (contMDiff_subtypeVal (n := ∞))).contMDiff z).mdifferentiableAt (by simp)

private theorem differentiableWithinAt_inChartAt_wedgeWith_ofFunction {U : Opens ℂ}
    {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : U → F} {z : U}
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) f z) {α : RoughForm 𝓘(ℝ, ℂ) ℂ G 1}
    (hα : IsSmoothForm 𝓘(ℝ, ℂ) ∞ α) :
    DifferentiableWithinAt ℝ
      ((RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α)).inChartAt z)
      (range 𝓘(ℝ, ℂ)) (extChartAt 𝓘(ℝ, ℂ) z z) := by
  set αU := mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α
  have hf_c :=
    (RoughForm.ofFunction 𝓘(ℝ, ℂ) f).differentiableWithinAt_range_inChartAt_of_mdifferentiableAt
      (mdifferentiableAt_ofFunction hf)
  have hα_c := αU.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt
    (mdifferentiableAt_mpullback_subtype_val hα z)
  have hpair :
      DifferentiableWithinAt ℝ
        (fun w ↦ ContinuousAlternatingMap.pairedWedge B B.continuous₂
          ((RoughForm.ofFunction 𝓘(ℝ, ℂ) f).inChartAt z w) (αU.inChartAt z w))
        (range 𝓘(ℝ, ℂ)) (extChartAt 𝓘(ℝ, ℂ) z z) :=
    (differentiableWithinAt_const _).pairedWedge hf_c hα_c
  exact hpair.congr (fun w _ ↦ RoughForm.inChartAt_wedgeWith B _ αU z w)
    (RoughForm.inChartAt_wedgeWith B _ αU z _)

/-- For a differentiable function `g : U → W` into a complex normed space `W` with ambient
representative `g' : ℂ → W`, the `dx ∧ dy` coefficient of `d(g dz)` at `z` is
`2i • \bar∂ g'(z)`. -/
theorem planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {g : U → W} {g' : ℂ → W}
    (hg_eq : ∀ z : U, g' z = g z) {z : U}
    (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z) :
    planarTwoFormCoeff
      (mextDeriv (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          SmoothForm.complexDz.val))) z =
      (2 * Complex.I) • conjWirtingerDeriv g' z 1 := by
  rw [planarTwoFormCoeff_eq_apply_symm,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip (mdifferentiableAt_ofFunction hg)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDz.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDz, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    comp_finCast_self, RoughForm.wedgeWith_apply_one_one, mextDeriv_ofFunction_apply,
    Matrix.cons_val_zero, mpullback_apply, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, SmoothForm.complexDz_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, Manifold.mvfderiv_opens_eq_fderiv_apply hg_eq,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [conjWirtingerDeriv_apply, smul_smul, smul_add, smul_smul, smul_eq_mul, mul_one]
  have h1 : 2 * Complex.I * (2 : ℂ)⁻¹ = Complex.I := by ring
  rw [h1, Complex.I_mul_I, one_smul, neg_one_smul, sub_eq_add_neg]

/-- For a differentiable function `f : U → W` into a complex normed space `W` with ambient
representative `f' : ℂ → W`, the `dx ∧ dy` coefficient of `d(f dbar z)` at `z` is
`-2i • ∂_z f'(z)`. -/
theorem planarTwoFormCoeff_mextDeriv_wedgeWith_complexDzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {f : U → W} {f' : ℂ → W}
    (hf_eq : ∀ z : U, f' z = f z) {z : U}
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) f z) :
    planarTwoFormCoeff
      (mextDeriv (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          SmoothForm.complexDzBar.val))) z =
      (-2 * Complex.I) • wirtingerDeriv f' z 1 := by
  rw [planarTwoFormCoeff_eq_apply_symm,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip (mdifferentiableAt_ofFunction hf)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDzBar.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDzBar, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    comp_finCast_self, RoughForm.wedgeWith_apply_one_one, mextDeriv_ofFunction_apply,
    Matrix.cons_val_zero, mpullback_apply, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, SmoothForm.complexDzBar_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, Manifold.mvfderiv_opens_eq_fderiv_apply hf_eq,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [conj_I, (starRingEnd ℂ).map_one, wirtingerDeriv_apply, smul_smul, smul_sub,
    smul_smul, smul_eq_mul, mul_one]
  have h1 : -2 * Complex.I * (2 : ℂ)⁻¹ = -Complex.I := by ring
  rw [h1, neg_mul, Complex.I_mul_I, neg_neg]

/-- For differentiable functions `a, b : U → F` into a real normed space `F` with ambient
representatives `a', b' : ℂ → F`, the `dx ∧ dy` coefficient of `d(a dx + b dy)` at `z` is
`∂_x b'(z) - ∂_y a'(z)`. -/
theorem planarTwoFormCoeff_mextDeriv_wedgeWith_complexDx_add_complexDy {U : Opens ℂ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : U → F} {a' b' : ℂ → F}
    (ha_eq : ∀ z : U, a' z = a z) (hb_eq : ∀ z : U, b' z = b z)
    {z : U} (ha : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) a z)
    (hb : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) b z) :
    planarTwoFormCoeff
      (mextDeriv
        (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) a)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDx.val) +
          RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) b)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDy.val))) z =
      fderiv ℝ b' z 1 - fderiv ℝ a' z Complex.I := by
  rw [planarTwoFormCoeff_eq_apply_symm,
    mextDeriv_add
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ ha
        SmoothForm.complexDx.isSmoothForm)
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ hb
        SmoothForm.complexDy.isSmoothForm),
    ContinuousAlternatingMap.add_apply,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip (mdifferentiableAt_ofFunction ha)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDx.isSmoothForm z),
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip (mdifferentiableAt_ofFunction hb)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDy.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDx, mextDeriv_mpullback_subtype_val_complexDy,
    RoughForm.wedgeWith_zero_right, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    comp_finCast_self, RoughForm.wedgeWith_apply_one_one, mextDeriv_ofFunction_apply,
    Matrix.cons_val_zero, mpullback_apply, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, SmoothForm.complexDx_apply, SmoothForm.complexDy_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, Manifold.mvfderiv_opens_eq_fderiv_apply ha_eq,
    Manifold.mvfderiv_opens_eq_fderiv_apply hb_eq,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp [sub_eq_add_neg, add_comm]

end OneFormDeriv

end TauCeti
