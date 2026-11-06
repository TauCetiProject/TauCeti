/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.AbelianDeformation
public import TauCeti.Analysis.PDE.SeibergWitten.DeformationSymbol
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
public import TauCeti.LinearAlgebra.Determinant.Line
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.Riemannian.AlmostComplex

/-!
# The Atiyah–Hitchin–Singer deformation operator and symbol commutator

On an oriented Riemannian four-manifold `(M, g, o)`, the gauge-fixed linearization of the
anti-self-dual equations is the first-order Atiyah–Hitchin–Singer operator

`δ₀ : Ω¹(M) → Ω⁰(M) ⊕ Ω⁺(M)`,   `δ₀(a) = (-d*a, √2 (da)⁺)`.

With the `√2` normalization on the self-dual two-forms `Ω⁺(M)`, the principal symbol of `δ₀` at a
covector `ξ` is `‖ξ‖` times a linear isometry `T_x M → ℝ ⊕ Λ⁺_x`
(`TauCeti.SeibergWitten.deformationSymbol_fst_sq_add_norm_snd_sq`) and becomes `(J, J′)`-complex
linear whenever `J` is an orthogonal almost complex structure inducing `o`.

This file defines `δ₀` on smooth differential forms and proves two foundational bridges:

1. **Determinant line equivalence with `abelianDeformationOperator`:** the diagonal target rescaling
   `(g, η) ↦ (2 g, (√2 / 2) η)` (`TauCeti.SeibergWitten.deformationTargetRescale`) intertwines `δ₀`
   with the Seiberg–Witten abelian deformation operator `T(a) = (-2 d*a, (da)⁺)`, inducing a
   canonical linear equivalence of determinant lines
   `asdDeformationDetLineEquiv : δ₀.detLine ≃ₗ[ℝ] T.detLine`.
2. **Principal symbol via the `C^∞(M)`-commutator:** for any smooth function `f ∈ Ω⁰(M)` and smooth
   one-form `a ∈ Ω¹(M)`, the commutator `δ₀(a ∧ f) - δ₀(a) ∧ f` evaluates at `x : M` to the
   pointwise algebraic symbol `deformationSymbol (o.orientationAt x) _ (df_x)♯ (a_x)♯`
   (`TauCeti.SeibergWitten.asdDeformationOperator_commutator_eq_deformationSymbol`).

## Main definitions

* `TauCeti.SeibergWitten.asdDeformationOperator`: the operator `δ₀(a) = (-d*a, √2 (da)⁺)`.
* `TauCeti.SeibergWitten.deformationTargetRescale`,
  `TauCeti.SeibergWitten.asdDeformationDetLineEquiv`: target rescaling intertwining `δ₀` with
  `abelianDeformationOperator` and the induced isomorphism of determinant lines.
* `TauCeti.SeibergWitten.deformationTargetMulRight`: right multiplication by `f ∈ Ω⁰(M)` on
  `Ω⁰(M) × Ω⁺(M)`.

## Main results

* `TauCeti.SeibergWitten.deformationTargetRescale_comp_asdDeformationOperator`:
  `deformationTargetRescale ∘ δ₀ = abelianDeformationOperator`.
* `TauCeti.SeibergWitten.ker_asdDeformationOperator`: on a closed oriented four-manifold,
  `ker δ₀ = ker d ⊓ ker d*`.
* `TauCeti.SeibergWitten.asdDeformationOperator_commutator_eq_deformationSymbol`: the commutator of
  `δ₀` with `· ∧ f` computes `deformationSymbol` fibrewise.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*, J. Amer.
  Math. Soc. 9 (1996), 845–918, §1–2.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Bundle Module Real exteriorPower
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti.SeibergWitten

/-! ### The Atiyah–Hitchin–Singer operator `δ₀` and its determinant line -/

section ASDDeformation

private theorem sqrt_two_div_two_mul_sqrt_two : √2 / 2 * √2 = (1 : ℝ) := by
  linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- **Taubes's Atiyah–Hitchin–Singer deformation operator** `δ₀(a) = (-d*a, √2 (da)⁺)` on an
oriented Riemannian four-manifold, mapping smooth one-forms to pairs of a smooth zero-form and a
smooth self-dual two-form. With the `√2` normalization on `Ω⁺`, its principal symbol is an isometry
up to `‖ξ‖` and intertwines the domain and target almost complex structures of a compatible
almost-Kähler metric. -/
def asdDeformationOperator :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
  (-SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl)).prod
    ((√2 • (SmoothForm.selfDualPart o ∘ₗ mextDerivₗ I 1)).codRestrict _ fun a ↦ by
      rw [LinearMap.smul_apply, LinearMap.comp_apply]
      exact Submodule.smul_mem _ _ (SmoothForm.selfDualPart_mem_selfDualForms o even_two _))

/-- The function component of `δ₀(a)` is `-d*a`. -/
@[simp]
theorem asdDeformationOperator_apply_fst (a : SmoothForm I M ℝ 1) :
    (asdDeformationOperator o a).1 =
      -SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl) a :=
  (rfl)

/-- The self-dual two-form component of `δ₀(a)` is `√2 (da)⁺`. -/
@[simp]
theorem coe_asdDeformationOperator_apply_snd (a : SmoothForm I M ℝ 1) :
    ((asdDeformationOperator o a).2 : SmoothForm I M ℝ 2) =
      √2 • SmoothForm.selfDualPart o (mextDerivₗ I 1 a) :=
  (rfl)

/-- The diagonal target rescaling `(g, η) ↦ (2 g, (√2 / 2) η)` intertwining `δ₀` with the
Seiberg–Witten `abelianDeformationOperator` `T(a) = (-2 d*a, (da)⁺)`. -/
def deformationTargetRescale :
    (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) ≃ₗ[ℝ]
      (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :=
  (LinearEquiv.smulOfUnit (Units.mkOfMulEqOne (2 : ℝ) 2⁻¹ (by norm_num))).prodCongr
    (LinearEquiv.smulOfUnit
      (Units.mkOfMulEqOne (√2 / 2 : ℝ) √2 sqrt_two_div_two_mul_sqrt_two))

@[simp]
theorem deformationTargetRescale_apply_fst
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (deformationTargetRescale o p).1 = (2 : ℝ) • p.1 :=
  (rfl)

@[simp]
theorem coe_deformationTargetRescale_apply_snd
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    ((deformationTargetRescale o p).2 : SmoothForm I M ℝ 2) =
      (√2 / 2 : ℝ) • (p.2 : SmoothForm I M ℝ 2) :=
  (rfl)

@[simp]
theorem deformationTargetRescale_symm_apply_fst
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    ((deformationTargetRescale o).symm p).1 = (2⁻¹ : ℝ) • p.1 :=
  (rfl)

@[simp]
theorem coe_deformationTargetRescale_symm_apply_snd
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (((deformationTargetRescale o).symm p).2 : SmoothForm I M ℝ 2) =
      √2 • (p.2 : SmoothForm I M ℝ 2) :=
  (rfl)

/-- **Target rescaling intertwines `δ₀` with `abelianDeformationOperator`:**
`deformationTargetRescale ∘ δ₀ = T`. -/
theorem deformationTargetRescale_comp_asdDeformationOperator :
    (deformationTargetRescale o).toLinearMap ∘ₗ asdDeformationOperator o =
      abelianDeformationOperator o := by
  ext a : 1
  refine Prod.ext ?_ (Subtype.ext ?_)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, deformationTargetRescale_apply_fst,
      asdDeformationOperator_apply_fst, abelianDeformationOperator_apply_fst]
    module
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, coe_deformationTargetRescale_apply_snd,
      coe_asdDeformationOperator_apply_snd, coe_abelianDeformationOperator_apply_snd, smul_smul,
      sqrt_two_div_two_mul_sqrt_two, one_smul]

/-- **Canonical isomorphism of determinant lines** between `δ₀` and `abelianDeformationOperator`,
induced by the identity on `Ω¹(M)` and `deformationTargetRescale` on `Ω⁰(M) × Ω⁺(M)`. -/
def asdDeformationDetLineEquiv :
    (asdDeformationOperator o).detLine ≃ₗ[ℝ] (abelianDeformationOperator o).detLine :=
  LinearMap.detLineCongr (asdDeformationOperator o) (LinearEquiv.refl ℝ _)
    (deformationTargetRescale o)
    (by rw [LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
      deformationTargetRescale_comp_asdDeformationOperator])

section ClosedManifold

variable [CompactSpace M] [BoundarylessManifold I M] [T2Space M]

/-- On a closed oriented Riemannian four-manifold, `δ₀(a) = (-d*a, √2 (da)⁺)` vanishes if and only
if `a` is closed and coclosed. -/
theorem asdDeformationOperator_eq_zero_iff (a : SmoothForm I M ℝ 1) :
    asdDeformationOperator o a = 0 ↔
      mextDerivₗ I 1 a = 0 ∧
        SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl) a = 0 := by
  rw [← abelianDeformationOperator_eq_zero_iff o a,
    ← deformationTargetRescale_comp_asdDeformationOperator o, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]

/-- On a closed oriented Riemannian four-manifold, `ker δ₀ = ker T = ker d ⊓ ker d*`. -/
theorem ker_asdDeformationOperator :
    LinearMap.ker (asdDeformationOperator o) =
      LinearMap.ker (mextDerivₗ I (F := ℝ) 1) ⊓
        LinearMap.ker (SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl)) := by
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_inf, asdDeformationOperator_eq_zero_iff]

end ClosedManifold

end ASDDeformation

/-! ### `C^∞(M)`-commutator and identification with `deformationSymbol` -/

section SymbolCommutator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- Right multiplication `(g, η) ↦ (g ∧ f, η ∧ f)` by a smooth function `f ∈ Ω⁰(M)` on the target
`Ω⁰(M) × Ω⁺(M)` of the deformation operator. -/
def deformationTargetMulRight (f : SmoothForm I M ℝ 0) :
    Module.End ℝ (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :=
  (SmoothForm.wedge.flip f).prodMap <|
    (SmoothForm.wedge.flip f).restrict fun _ hη ↦ by
      rw [LinearMap.flip_apply, SmoothForm.mem_selfDualForms,
        SmoothForm.hodgeStar_wedge_zero_right, SmoothForm.mem_selfDualForms.1 hη]

@[simp]
theorem deformationTargetMulRight_apply_fst (f : SmoothForm I M ℝ 0)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (deformationTargetMulRight o f p).1 = SmoothForm.wedge p.1 f :=
  (rfl)

@[simp]
theorem coe_deformationTargetMulRight_apply_snd (f : SmoothForm I M ℝ 0)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    ((deformationTargetMulRight o f p).2 : SmoothForm I M ℝ 2) =
      SmoothForm.wedge (p.2 : SmoothForm I M ℝ 2) f :=
  (rfl)

/-- **Function component of `[δ₀, · ∧ f]`:** `-d*(a ∧ f) - (-d*a) ∧ f = ⟨df, a⟩` at every point. -/
theorem asdDeformationOperator_wedge_sub_fst_apply (a : SmoothForm I M ℝ 1)
    (f : SmoothForm I M ℝ 0) (x : M) (u : Fin 0 → TangentSpace I x) :
    ((asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a)).1).1 x u =
      alternatingFormInner (TangentSpace I x) 1 ((mextDerivₗ I 0 f).1 x) (a.1 x) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have h13 : 0 + 1 + 3 = 2 + 2 := rfl
  have h310 : 3 + 1 + 0 = 2 + 2 := rfl
  have hcod (b : SmoothForm I M ℝ 1) :
      -SmoothForm.codifferential o h13 b =
        SmoothForm.hodgeStar o h310 (mextDerivₗ I 3 (SmoothForm.hodgeStar o h13 b)) := by
    rw [SmoothForm.codifferential_apply o h13 h310]
    have hs : (-1 : ℝ) ^ ((2 + 2) * (0 + 2) + 1) = -1 := by norm_num
    rw [hs]
    module
  have hwcomm : SmoothForm.wedge (SmoothForm.hodgeStar o h13 a) (mextDerivₗ I 0 f) =
      -SmoothForm.wedge (mextDerivₗ I 0 f) (SmoothForm.hodgeStar o h13 a) := by
    rw [SmoothForm.wedge_eq_smul_cast_wedge_comm, LinearEquiv.cast_apply, cast_eq]
    have hpow : (-1 : ℝ) ^ (3 * (0 + 1)) = -1 := by norm_num
    rw [hpow]
    module
  have hsub : (asdDeformationOperator o (SmoothForm.wedge a f) -
      deformationTargetMulRight o f (asdDeformationOperator o a)).1 =
      SmoothForm.innerZeroForm (k := 1) (l := 3) o (mextDerivₗ I 0 f) a := by
    rw [Prod.fst_sub, asdDeformationOperator_apply_fst, deformationTargetMulRight_apply_fst,
      asdDeformationOperator_apply_fst, hcod, hcod, SmoothForm.hodgeStar_wedge_zero_right o h13 a f,
      SmoothForm.mextDerivₗ_wedge (I := I) (k := 3) (l := 0), LinearEquiv.cast_apply, cast_eq,
      LinearEquiv.cast_apply, cast_eq, map_add, map_smul,
      SmoothForm.hodgeStar_wedge_zero_right o h310 _ f, hwcomm, map_neg]
    have hpow : (-1 : ℝ) ^ 3 = -1 := by norm_num
    rw [hpow, SmoothForm.innerZeroForm_def]
    module
  rw [hsub, SmoothForm.innerZeroForm_apply]

/-- **Self-dual two-form component of `[δ₀, · ∧ f]`:**
`√2 (d(a ∧ f))⁺ - √2 (da)⁺ ∧ f = √2 (df ∧ a)⁺`. -/
theorem coe_asdDeformationOperator_wedge_sub_snd (a : SmoothForm I M ℝ 1)
    (f : SmoothForm I M ℝ 0) :
    ((asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a)).2 : SmoothForm I M ℝ 2) =
      √2 • SmoothForm.selfDualPart o (SmoothForm.wedge (mextDerivₗ I 0 f) a) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have hwcomm : SmoothForm.wedge a (mextDerivₗ I 0 f) =
      -SmoothForm.wedge (mextDerivₗ I 0 f) a := by
    rw [SmoothForm.wedge_eq_smul_cast_wedge_comm, LinearEquiv.cast_apply, cast_eq]
    have hpow : (-1 : ℝ) ^ (1 * (0 + 1)) = -1 := by norm_num
    rw [hpow]
    module
  have hneg : (-1 : ℝ) ^ 1 • (-SmoothForm.wedge (mextDerivₗ I 0 f) a) =
      SmoothForm.wedge (mextDerivₗ I 0 f) a := by module
  rw [Prod.snd_sub, Submodule.coe_sub, coe_asdDeformationOperator_apply_snd,
    coe_deformationTargetMulRight_apply_snd, coe_asdDeformationOperator_apply_snd,
    SmoothForm.mextDerivₗ_wedge (I := I) (k := 1) (l := 0), LinearEquiv.cast_apply, cast_eq,
    LinearEquiv.cast_apply, cast_eq, hwcomm, hneg, map_add, smul_add,
    SmoothForm.selfDualPart_wedge_zero_right, SmoothForm.wedge.map_smul, LinearMap.smul_apply,
    add_sub_cancel_left]

/-- **The `C^∞(M)`-commutator of `δ₀` computes `deformationSymbol` fibrewise:** at every `x : M`,
reading `(df)_x` and `a_x` as tangent vectors via `Riemannian.Tensor.rieszDual` and two-forms as
bivectors via `(alternatingFormEquiv (TangentSpace I x) 2).symm`, the commutator
`δ₀(a ∧ f) - δ₀(a) ∧ f` equals `deformationSymbol (o.orientationAt x) _ (df_x)♯ (a_x)♯`. -/
theorem asdDeformationOperator_commutator_eq_deformationSymbol (a : SmoothForm I M ℝ 1)
    (f : SmoothForm I M ℝ 0) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     (((asdDeformationOperator o (SmoothForm.wedge a f) -
          deformationTargetMulRight o f (asdDeformationOperator o a)).1).1 x 0,
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         (((asdDeformationOperator o (SmoothForm.wedge a f) -
            deformationTargetMulRight o f
              (asdDeformationOperator o a)).2 : SmoothForm I M ℝ 2).1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       deformationSymbol (o.orientationAt x) (o.fact_finrank_tangentSpace x).out.symm
         (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x))
         (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x))) := by
  let _ := o.fact_finrank_tangentSpace x
  set ξ := Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)
  set v := Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)
  have hξ := SmoothForm.alternatingFormEquiv_rieszDual_degreeOneEquiv (mextDerivₗ I 0 f) x
  have hv := SmoothForm.alternatingFormEquiv_rieszDual_degreeOneEquiv a x
  have hzv : (alternatingFormEquiv (TangentSpace I x) 2).symm
      ((SmoothForm.wedge (mextDerivₗ I 0 f) a).1 x) = ιMulti ℝ 2 ![ξ, v] := by
    apply (alternatingFormEquiv (TangentSpace I x) 2).injective
    rw [LinearEquiv.apply_symm_apply]
    ext w
    have hw : ![w 0, w 1] = w := funext fun i ↦ by fin_cases i <;> rfl
    rw [← hw, SmoothForm.wedge_apply_one_one, alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ← SmoothForm.degreeOneEquiv_apply_apply_vec, ← Riemannian.Tensor.inner_rieszDual, ξ, v]
    ring
  refine Prod.ext ?_ ?_
  · rw [asdDeformationOperator_wedge_sub_fst_apply, deformationSymbol_apply_fst,
      ← hξ, ← hv, alternatingFormInner_alternatingFormEquiv, inner_ιMulti_ιMulti,
      Matrix.det_fin_one]
    simp [ξ, v]
  · rw [coe_asdDeformationOperator_wedge_sub_snd, Submodule.coe_smul, Pi.smul_apply, map_smul,
      SmoothForm.alternatingFormEquiv_symm_selfDualPart, hzv, smul_smul, ← div_eq_mul_inv,
      deformationSymbol_apply_snd]

end SymbolCommutator

end TauCeti.SeibergWitten
