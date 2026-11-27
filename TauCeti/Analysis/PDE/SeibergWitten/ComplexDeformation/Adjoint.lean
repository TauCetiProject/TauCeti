/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ASDDeformation.Hodge
public import TauCeti.Analysis.PDE.SeibergWitten.ComplexDeformation.Basic
import TauCeti.Geometry.Manifold.DeRham.CompactSupport
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Riemannian.FormMetric

/-!
# The formal adjoint of Taubes's complex-linear deformation operator

On an oriented Riemannian four-manifold `(M, g, o)` with a compatible almost complex structure
`J`, Taubes's complex-linear deformation operator is the complex-linear part

`δ_ω = (δ₀ - J′ ∘ δ₀ ∘ J₁) / 2`

of `δ₀ a = (-d*a, √2 (da)⁺)` (`TauCeti.SeibergWitten.complexDeformationOperator`), and the
straight path `δ_t = (1 - t) δ₀ + t δ_ω` (`TauCeti.SeibergWitten.deformationHomotopy`) joins the
two through operators with the principal symbol of `δ₀`. Orienting `det δ_ω` complexly and
transporting that orientation along `δ_t` uses the cokernels of these operators, modelled by the
kernels of their formal adjoints. This file constructs those adjoints.

Both complex structures are orthogonal: `J₁` on one-forms pointwise
(`TauCeti.SmoothAlmostComplexStructure.alternatingFormInner_covectorComplexStructure`) and `J′`
on `Ω⁰(M) × Ω⁺(M)` pointwise (`TauCeti.SeibergWitten.inner_deformationTargetComplexStructure`),
so both are skew-adjoint. The formal adjoint of `J′ ∘ δ₀ ∘ J₁` is therefore `J₁ ∘ δ₀* ∘ J′`, and the
formal adjoint of `δ_ω` is the complex-linear part of `δ₀*` for the reversed pair `(J′, J₁)`,

`δ_ω* = (δ₀* - J₁ ∘ δ₀* ∘ J′) / 2`

(`TauCeti.SeibergWitten.complexDeformationFormalAdjoint`). It is complex linear
(`TauCeti.SeibergWitten.isComplexLinearMap_complexDeformationFormalAdjoint`), so its kernel is
`J′`-invariant, and the kernel of `δ_ω` is `J₁`-invariant. Along the path, the formal adjoint of
`δ_t` is `(1 - t) δ₀* + t δ_ω*` (`TauCeti.SeibergWitten.deformationHomotopyFormalAdjoint`).

On a closed manifold these are formal adjoints for the `L²` pairings, with the target pairing
ordered as the scalar pairing followed by the self-dual pairing, as in Green's formula for `δ₀`
(`integralTopForm_inner_asdDeformationOperator_eq_inner_asdDeformationFormalAdjoint`).
In particular a smooth target pair is `L²`-orthogonal to the range of `δ_t` exactly when the
formal adjoint of `δ_t` annihilates it
(`TauCeti.SeibergWitten.forall_integralTopForm_inner_deformationHomotopy_eq_zero_iff`). These are
identities on smooth forms: no Sobolev completion, closed range or Fredholm property is asserted.

## Main definitions

* `TauCeti.SeibergWitten.complexDeformationFormalAdjoint`: the formal adjoint
  `δ_ω* = complexLinearPart J′ J₁ δ₀*` of `δ_ω`.
* `TauCeti.SeibergWitten.deformationHomotopyFormalAdjoint`: the formal adjoint
  `(1 - t) δ₀* + t δ_ω*` of `δ_t`.

## Main results

* `TauCeti.SeibergWitten.isComplexLinearMap_complexDeformationFormalAdjoint`: `δ_ω*` is
  `(J′, J₁)`-complex linear.
* `integralTopForm_inner_complexDeformationOperator_eq_inner_complexDeformationFormalAdjoint` and
  `integralTopForm_inner_deformationHomotopy_eq_inner_deformationHomotopyFormalAdjoint`, in
  `TauCeti.SeibergWitten`: Green's formulas for `δ_ω` and `δ_t` on a closed four-manifold.
* `TauCeti.SeibergWitten.forall_integralTopForm_inner_complexDeformationOperator_eq_zero_iff` and
  `TauCeti.SeibergWitten.forall_integralTopForm_inner_deformationHomotopy_eq_zero_iff`: the smooth
  annihilators of the ranges of `δ_ω` and `δ_t` are the kernels of their formal adjoints.
* `complexDeformationOperator_covectorComplexStructure_eq_zero_iff` and
  `complexDeformationFormalAdjoint_deformationTargetComplexStructure_eq_zero_iff`, in
  `TauCeti.SeibergWitten`: the kernels of `δ_ω` and `δ_ω*` are invariant under `J₁` and `J′`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*, J. Amer.
  Math. Soc. 9 (1996), 845–918, §1–2.
* C. H. Taubes, *GR = SW: Counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Bundle Real
open scoped Manifold ContDiff

namespace TauCeti.SeibergWitten

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2))) (J : SmoothAlmostComplexStructure I M)
  (hJo : J.IsCompatibleOrientation o)

/-- **The formal adjoint of Taubes's complex-linear deformation operator**
`δ_ω* = complexLinearPart J′ J₁ δ₀* = (δ₀* - J₁ ∘ δ₀* ∘ J′) / 2`, from `Ω⁰(M) × Ω⁺(M)` to smooth
one-forms. -/
def complexDeformationFormalAdjoint :
    (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) →ₗ[ℝ]
      SmoothForm I M ℝ 1 :=
  TauCeti.complexLinearPart (deformationTargetComplexStructure o J hJo).toLinearMap
    J.covectorComplexStructure.toLinearMap (asdDeformationFormalAdjoint o)

/-- Unfolding `complexDeformationFormalAdjoint` as `(2⁻¹ : ℝ) • (δ₀* p - J₁ (δ₀* (J′ p)))`. -/
theorem complexDeformationFormalAdjoint_apply
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    complexDeformationFormalAdjoint o J hJo p =
      (2⁻¹ : ℝ) • (asdDeformationFormalAdjoint o p -
        J.covectorComplexStructure
          (asdDeformationFormalAdjoint o (deformationTargetComplexStructure o J hJo p))) :=
  TauCeti.complexLinearPart_apply _ _ _ p

/-- **`δ_ω*` is complex linear** with respect to `deformationTargetComplexStructure o J hJo` on
`Ω⁰(M) × Ω⁺(M)` and `J.covectorComplexStructure` on `Ω¹(M)`. -/
theorem isComplexLinearMap_complexDeformationFormalAdjoint :
    IsComplexLinearMap (deformationTargetComplexStructure o J hJo) J.covectorComplexStructure
      (complexDeformationFormalAdjoint o J hJo) :=
  (isComplexLinearMap_iff_isComplexLinear _ _ _).mpr <|
    TauCeti.isComplexLinear_complexLinearPart
      (deformationTargetComplexStructure o J hJo).square_neg J.covectorComplexStructure.square_neg
      (asdDeformationFormalAdjoint o)

/-- **The formal adjoint of the deformation homotopy** `(1 - t) δ₀* + t δ_ω*`, the formal adjoint of
`δ_t = (1 - t) δ₀ + t δ_ω`. -/
def deformationHomotopyFormalAdjoint (t : ℝ) :
    (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) →ₗ[ℝ]
      SmoothForm I M ℝ 1 :=
  (1 - t) • asdDeformationFormalAdjoint o + t • complexDeformationFormalAdjoint o J hJo

/-- Unfolding `deformationHomotopyFormalAdjoint` as `(1 - t) • δ₀* p + t • δ_ω* p`. -/
theorem deformationHomotopyFormalAdjoint_apply (t : ℝ)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    deformationHomotopyFormalAdjoint o J hJo t p =
      (1 - t) • asdDeformationFormalAdjoint o p + t • complexDeformationFormalAdjoint o J hJo p :=
  (rfl)

@[simp]
theorem deformationHomotopyFormalAdjoint_zero :
    deformationHomotopyFormalAdjoint o J hJo 0 = asdDeformationFormalAdjoint o := by
  simp [deformationHomotopyFormalAdjoint]

@[simp]
theorem deformationHomotopyFormalAdjoint_one :
    deformationHomotopyFormalAdjoint o J hJo 1 = complexDeformationFormalAdjoint o J hJo := by
  simp [deformationHomotopyFormalAdjoint]

/-- **The kernel of `δ_ω` is `J₁`-invariant:** `δ_ω (J₁ a) = 0` exactly when `δ_ω a = 0`. -/
theorem complexDeformationOperator_covectorComplexStructure_eq_zero_iff (a : SmoothForm I M ℝ 1) :
    complexDeformationOperator o J hJo (J.covectorComplexStructure a) = 0 ↔
      complexDeformationOperator o J hJo a = 0 := by
  rw [(isComplexLinearMap_iff_apply _ _ _).mp
    (isComplexLinearMap_complexDeformationOperator o J hJo)]
  exact AlmostComplexStructure.map_eq_zero_iff _

/-- **The kernel of `δ_ω*` is `J′`-invariant:** `δ_ω* (J′ p) = 0` exactly when `δ_ω* p = 0`. -/
theorem complexDeformationFormalAdjoint_deformationTargetComplexStructure_eq_zero_iff
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    complexDeformationFormalAdjoint o J hJo (deformationTargetComplexStructure o J hJo p) = 0 ↔
      complexDeformationFormalAdjoint o J hJo p = 0 := by
  rw [(isComplexLinearMap_iff_apply _ _ _).mp
    (isComplexLinearMap_complexDeformationFormalAdjoint o J hJo)]
  exact AlmostComplexStructure.map_eq_zero_iff _

/-! ### Green's formulas on a closed four-manifold -/

section ClosedManifold

variable [CompactSpace M] [BoundarylessManifold I M] [T2Space M]

/-- The `L²` pairing of `Ω⁰(M) × Ω⁺(M)`: the scalar pairing followed by the self-dual pairing. -/
private def targetPairing
    (q p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) : ℝ :=
  integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0 (q.1.val x) (p.1.val x) •
      riemannianVolumeForm o x) +
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      ((q.2 : SmoothForm I M ℝ 2).val x) ((p.2 : SmoothForm I M ℝ 2).val x) •
        riemannianVolumeForm o x)

/-- The `L²` pairing of smooth one-forms. -/
private def oneFormPairing (a b : SmoothForm I M ℝ 1) : ℝ :=
  integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1 (a.val x) (b.val x) •
    riemannianVolumeForm o x)

/-- The pointwise inner product of `Ω⁰(M) × Ω⁺(M)` at `x`. -/
private def targetInnerAt
    (q p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) : ℝ :=
  alternatingFormInner (TangentSpace I x) 0 (q.1.val x) (p.1.val x) +
    alternatingFormInner (TangentSpace I x) 2 ((q.2 : SmoothForm I M ℝ 2).val x)
      ((p.2 : SmoothForm I M ℝ 2).val x)

omit [BoundarylessManifold I M] [T2Space M] in
private theorem targetPairing_eq
    (q p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    targetPairing o q p =
      integralTopForm o (fun x ↦ targetInnerAt o q p x • riemannianVolumeForm o x) :=
  (integralTopForm_add_smul_of_compactSpace o (isSmoothForm_riemannianVolumeForm (n := ∞) o)
    (q.1.isSmoothForm.contMDiff_alternatingFormInner p.1.isSmoothForm).continuous
    ((q.2 : SmoothForm I M ℝ 2).isSmoothForm.contMDiff_alternatingFormInner
      (p.2 : SmoothForm I M ℝ 2).isSmoothForm).continuous).symm

omit [BoundarylessManifold I M] [T2Space M] in
/-- The target pairing is linear in its first argument. -/
private theorem targetPairing_add_smul (c₁ c₂ : ℝ)
    (q₁ q₂ p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    targetPairing o (c₁ • q₁ + c₂ • q₂) p =
      c₁ * targetPairing o q₁ p + c₂ * targetPairing o q₂ p := by
  have h₀ := SmoothForm.integralTopForm_inner_add_left o (show 0 + 4 = 2 + 2 from rfl)
    (c₁ • q₁.1) (c₂ • q₂.1) p.1 (.inr (by simp [compactlySupportedForms_eq_top]))
  have h₂ := SmoothForm.integralTopForm_inner_add_left o (show 2 + 2 = 2 + 2 from rfl)
    (c₁ • (q₁.2 : SmoothForm I M ℝ 2)) (c₂ • (q₂.2 : SmoothForm I M ℝ 2)) p.2
    (.inr (by simp [compactlySupportedForms_eq_top]))
  rw [SmoothForm.integralTopForm_inner_smul_left, SmoothForm.integralTopForm_inner_smul_left]
    at h₀ h₂
  simp only [targetPairing, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Submodule.coe_add, Submodule.coe_smul] at h₀ h₂ ⊢
  rw [h₀, h₂]
  ring

omit [BoundarylessManifold I M] [T2Space M] in
/-- The one-form pairing is linear in its second argument. -/
private theorem oneFormPairing_add_smul (c₁ c₂ : ℝ) (a b₁ b₂ : SmoothForm I M ℝ 1) :
    oneFormPairing o a (c₁ • b₁ + c₂ • b₂) =
      c₁ * oneFormPairing o a b₁ + c₂ * oneFormPairing o a b₂ := by
  have h := SmoothForm.integralTopForm_inner_add_left o (show 1 + 3 = 2 + 2 from rfl)
    (c₁ • b₁) (c₂ • b₂) a (.inr (by simp [compactlySupportedForms_eq_top]))
  rw [SmoothForm.integralTopForm_inner_smul_left, SmoothForm.integralTopForm_inner_smul_left]
    at h
  rw [oneFormPairing, oneFormPairing, oneFormPairing,
    RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm o a.val
      (c₁ • b₁ + c₂ • b₂).val, h,
    RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm o b₁.val a.val,
    RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm o b₂.val a.val]

omit [BoundarylessManifold I M] [T2Space M] in
/-- `J′` is skew-adjoint for the target pairing. -/
private theorem targetPairing_deformationTargetComplexStructure_left
    (q p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    targetPairing o (deformationTargetComplexStructure o J hJo q) p =
      -targetPairing o q (deformationTargetComplexStructure o J hJo p) := by
  rw [targetPairing_eq, targetPairing_eq, ← neg_one_mul, ← integralTopForm_smul]
  congr 1
  funext x
  have h : targetInnerAt o (deformationTargetComplexStructure o J hJo q) p x =
      -targetInnerAt o q (deformationTargetComplexStructure o J hJo p) x := by
    simp only [targetInnerAt, alternatingFormInner_zero_apply _ _ (0 : Fin 0 → TangentSpace I x)]
    exact inner_deformationTargetComplexStructure_left o J hJo q p x
  rw [h, Pi.smul_apply, smul_smul, neg_one_mul]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [CompactSpace M]
  [BoundarylessManifold I M] [T2Space M] in
include hJo in
/-- `J₁` is skew-adjoint for the one-form pairing. -/
private theorem oneFormPairing_covectorComplexStructure_left (a b : SmoothForm I M ℝ 1) :
    oneFormPairing o (J.covectorComplexStructure a) b =
      -oneFormPairing o a (J.covectorComplexStructure b) := by
  rw [oneFormPairing, oneFormPairing, ← neg_one_mul, ← integralTopForm_smul]
  congr 1
  funext x
  rw [SmoothAlmostComplexStructure.alternatingFormInner_covectorComplexStructure_left
    hJo.inner_apply_apply, Pi.smul_apply, smul_smul, neg_one_mul]

/-- Green's formula for `δ₀` in terms of the private pairings. -/
private theorem targetPairing_asdDeformationOperator (a : SmoothForm I M ℝ 1)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    targetPairing o (asdDeformationOperator o a) p =
      oneFormPairing o a (asdDeformationFormalAdjoint o p) :=
  integralTopForm_inner_asdDeformationOperator_eq_inner_asdDeformationFormalAdjoint o a p

/-- Green's formula for `J′ ∘ δ₀ ∘ J₁`, whose formal adjoint is `J₁ ∘ δ₀* ∘ J′`. -/
private theorem targetPairing_conj_asdDeformationOperator (a : SmoothForm I M ℝ 1)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    targetPairing o (deformationTargetComplexStructure o J hJo
        (asdDeformationOperator o (J.covectorComplexStructure a))) p =
      oneFormPairing o a (J.covectorComplexStructure
        (asdDeformationFormalAdjoint o (deformationTargetComplexStructure o J hJo p))) := by
  rw [targetPairing_deformationTargetComplexStructure_left, targetPairing_asdDeformationOperator,
    oneFormPairing_covectorComplexStructure_left o J hJo, neg_neg]

/-- Green's formula for `δ_ω` in terms of the private pairings. -/
private theorem targetPairing_complexDeformationOperator (a : SmoothForm I M ℝ 1)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    targetPairing o (complexDeformationOperator o J hJo a) p =
      oneFormPairing o a (complexDeformationFormalAdjoint o J hJo p) := by
  have hδ : complexDeformationOperator o J hJo a = (2⁻¹ : ℝ) • asdDeformationOperator o a +
      (-2⁻¹ : ℝ) • deformationTargetComplexStructure o J hJo
        (asdDeformationOperator o (J.covectorComplexStructure a)) := by
    rw [complexDeformationOperator_apply]
    module
  have hδ' : complexDeformationFormalAdjoint o J hJo p =
      (2⁻¹ : ℝ) • asdDeformationFormalAdjoint o p + (-2⁻¹ : ℝ) • J.covectorComplexStructure
        (asdDeformationFormalAdjoint o (deformationTargetComplexStructure o J hJo p)) := by
    rw [complexDeformationFormalAdjoint_apply]
    module
  rw [hδ, hδ', targetPairing_add_smul, oneFormPairing_add_smul,
    targetPairing_asdDeformationOperator, targetPairing_conj_asdDeformationOperator]

/-- **Green's formula for `δ_ω` and `δ_ω*`** on a closed four-manifold, with the target pairing
ordered as the scalar pairing followed by the self-dual pairing. -/
theorem integralTopForm_inner_complexDeformationOperator_eq_inner_complexDeformationFormalAdjoint
    (a : SmoothForm I M ℝ 1)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0
      ((complexDeformationOperator o J hJo a).1.val x) (p.1.val x) • riemannianVolumeForm o x) +
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      (((complexDeformationOperator o J hJo a).2 : SmoothForm I M ℝ 2).val x)
      ((p.2 : SmoothForm I M ℝ 2).val x) • riemannianVolumeForm o x) =
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1
      (a.val x) ((complexDeformationFormalAdjoint o J hJo p).val x) •
        riemannianVolumeForm o x) :=
  -- The two sides are `targetPairing` and `oneFormPairing` unfolded.
  targetPairing_complexDeformationOperator o J hJo a p

/-- **Green's formula for `δ_t` and its formal adjoint** `(1 - t) δ₀* + t δ_ω*` on a closed
four-manifold, with the target pairing ordered as the scalar pairing followed by the self-dual
pairing. -/
theorem integralTopForm_inner_deformationHomotopy_eq_inner_deformationHomotopyFormalAdjoint
    (t : ℝ) (a : SmoothForm I M ℝ 1)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0
      ((deformationHomotopy o J hJo t a).1.val x) (p.1.val x) • riemannianVolumeForm o x) +
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      (((deformationHomotopy o J hJo t a).2 : SmoothForm I M ℝ 2).val x)
      ((p.2 : SmoothForm I M ℝ 2).val x) • riemannianVolumeForm o x) =
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1
      (a.val x) ((deformationHomotopyFormalAdjoint o J hJo t p).val x) •
        riemannianVolumeForm o x) := by
  -- The two sides are `targetPairing` and `oneFormPairing` unfolded.
  change targetPairing o _ p = oneFormPairing o a _
  have h : deformationHomotopy o J hJo t a =
      (1 - t) • asdDeformationOperator o a + t • complexDeformationOperator o J hJo a := by
    rw [deformationHomotopy_eq_add_smul_sub, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sub_apply]
    module
  rw [h, deformationHomotopyFormalAdjoint_apply, targetPairing_add_smul, oneFormPairing_add_smul,
    targetPairing_asdDeformationOperator, targetPairing_complexDeformationOperator]

/-- **The smooth annihilator of the range of `δ_t`** on a closed four-manifold is the kernel of
its formal adjoint `(1 - t) δ₀* + t δ_ω*`. This does not assert closed range or regularity of
distributional annihilators. -/
theorem forall_integralTopForm_inner_deformationHomotopy_eq_zero_iff (t : ℝ)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (∀ a : SmoothForm I M ℝ 1,
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0
        ((deformationHomotopy o J hJo t a).1.val x) (p.1.val x) • riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        (((deformationHomotopy o J hJo t a).2 : SmoothForm I M ℝ 2).val x)
        ((p.2 : SmoothForm I M ℝ 2).val x) • riemannianVolumeForm o x) = 0) ↔
      deformationHomotopyFormalAdjoint o J hJo t p = 0 := by
  simp_rw [integralTopForm_inner_deformationHomotopy_eq_inner_deformationHomotopyFormalAdjoint]
  refine ⟨fun h ↦ ?_, fun h a ↦ ?_⟩
  · exact (SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o
      (show 1 + 3 = 2 + 2 from rfl) (by simp [compactlySupportedForms_eq_top])).mp
        (h (deformationHomotopyFormalAdjoint o J hJo t p))
  · simp only [h, ZeroMemClass.coe_zero, Pi.zero_apply, LinearMap.map_zero, zero_smul]
    exact integralTopForm_zero o

/-- **The smooth annihilator of the range of `δ_ω`** on a closed four-manifold is the kernel of
`δ_ω*`. This does not assert closed range or regularity of distributional annihilators. -/
theorem forall_integralTopForm_inner_complexDeformationOperator_eq_zero_iff
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (∀ a : SmoothForm I M ℝ 1,
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0
        ((complexDeformationOperator o J hJo a).1.val x) (p.1.val x) • riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        (((complexDeformationOperator o J hJo a).2 : SmoothForm I M ℝ 2).val x)
        ((p.2 : SmoothForm I M ℝ 2).val x) • riemannianVolumeForm o x) = 0) ↔
      complexDeformationFormalAdjoint o J hJo p = 0 := by
  simpa using forall_integralTopForm_inner_deformationHomotopy_eq_zero_iff o J hJo 1 p

end ClosedManifold

end TauCeti.SeibergWitten
