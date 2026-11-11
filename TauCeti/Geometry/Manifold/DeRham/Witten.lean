/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.DeRham.DegreeZero

/-!
# The Witten deformation of the de Rham complex

For a smooth function `f` on a manifold `M` and a real parameter `t`, Witten's deformation of the
exterior derivative is the conjugate

`d_t = e^{-t f} ∘ d ∘ e^{t f}`

of `d` by multiplication with the positive function `e^{t f}`. By the Leibniz rule it is the
local operator `d_t φ = dφ + t df ∧ φ` (`TauCeti.wittenExtDerivₗ_apply`,
`TauCeti.wittenExtDerivₗ_eq_add_smul`), which at `t = 0` is `d`. Since it is conjugate to `d`,
it squares to zero, and the smooth forms with `d_t` form a cochain complex, the *Witten complex*.
Multiplication by `e^{t f}` is an isomorphism from the Witten complex onto the de Rham complex
(`TauCeti.wittenComplexIso`), so the cohomology of `d_t` is de Rham cohomology for every `t`
(`TauCeti.wittenCohomologyIso`).

The point of the deformation is analytic. Once a Riemannian metric is chosen, the Laplacian
`d_t d_t^* + d_t^* d_t` of `d_t` is the Witten Laplacian, whose low-lying spectrum concentrates
near the critical points of a Morse function `f` as `t → ∞`; together with the isomorphism above,
this recovers the Morse inequalities and compares de Rham cohomology with Morse cohomology. The
metric, adjoint and spectral analysis are not treated here.

In degree zero, `d_t g = 0` exactly when `e^{t f} g` is locally constant
(`TauCeti.wittenExtDerivₗ_apply_eq_zero_iff_isLocallyConstant`). In particular `d_t` annihilates
`e^{-t f}` (`TauCeti.wittenExtDerivₗ_expSMulEquiv_neg_ofFunction_one`); for `f = x²` on the line
and `t > 0` this is the Gaussian `e^{-t x²}`, which for the standard Euclidean metric is the ground
state of the harmonic oscillator obtained from the Witten Laplacian at a nondegenerate minimum.

## Main definitions

* `TauCeti.expSMulEquiv f t k`: multiplication of smooth `k`-forms by `e^{t f}`.
* `TauCeti.wittenExtDerivₗ f t k`: the Witten deformation `d_t` of the exterior derivative.
* `TauCeti.wittenComplex f t`: the cochain complex of smooth forms with differential `d_t`.

## Main results

* `TauCeti.mextDeriv_exp_mul_smul`: `d (e^{t f} φ) = e^{t f} (dφ + t df ∧ φ)` for rough forms.
* `TauCeti.wittenExtDerivₗ_apply`: `d_t φ = dφ + t df ∧ φ`.
* `TauCeti.wittenExtDerivₗ_comp_wittenExtDerivₗ`: `d_t ∘ d_t = 0`.
* `TauCeti.wittenComplexIso`: multiplication by `e^{t f}` identifies the Witten complex with the
  de Rham complex.
* `TauCeti.wittenCohomologyIso`: the cohomology of `d_t` is de Rham cohomology.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692,
  Section 2 (the deformed differential `d_t = e^{-tf} d e^{tf}` and its cohomology).
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Springer, 1987,
  Chapter 11 (Witten's proof of the Morse inequalities).
-/

public section

noncomputable section

open CategoryTheory Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

section RoughForm

variable [IsManifold I 1 M]

/-- **Conjugating the exterior derivative by `e^{t f}`.** At a point where `f` and the rough
form `φ` are differentiable, `d (e^{t f} φ) = e^{t f} (dφ + t df ∧ φ)`. The degree `0 + 1 + k` of
`df ∧ φ` is identified with `k + 1` by `Fin.cast`. -/
theorem mextDeriv_exp_mul_smul {f : M → ℝ} {φ : RoughForm I M ℝ k} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (φ y)) x)
    (t : ℝ) (v : Fin (k + 1) → TangentSpace I x) :
    mextDeriv (fun y ↦ Real.exp (t * f y) • φ y) x v =
      Real.exp (t * f x) * (mextDeriv φ x v +
        t * (mextDeriv (RoughForm.ofFunction I f)).wedge φ x
          (v ∘ Fin.cast (show 0 + 1 + k = k + 1 by omega))) := by
  have hderiv : HasDerivAt (fun s ↦ Real.exp (t * s)) (Real.exp (t * f x) * t) (f x) := by
    simpa using ((hasDerivAt_id (f x)).const_mul t).exp
  have hexp : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ Real.exp (t * f y)) x :=
    (hderiv.differentiableAt.comp_mdifferentiableAt hf :)
  rw [mextDeriv_fun_smul hexp hφ v]
  simp only [RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    mextDeriv_ofFunction_comp_of_hasDerivAt hf hderiv,
    ContinuousAlternatingMap.pairedWedge_smul_left, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  ring

end RoughForm

section SmoothForm

/-- The smooth function `e^{t f}`. -/
private def expMul (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ Real.exp (t * f x),
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).comp_contMDiff f.contMDiff :)⟩

private theorem expMul_apply (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (x : M) :
    expMul f t x = Real.exp (t * f x) :=
  (rfl)

private theorem expMul_mul_expMul_neg (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (x : M) :
    expMul f t x * expMul f (-t) x = 1 := by
  rw [expMul_apply, expMul_apply, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]

section Gauge

variable [IsManifold I 1 M]

variable (k) in
/-- Multiplication of smooth `k`-forms by the positive function `e^{t f}`, a linear automorphism
whose inverse is multiplication by `e^{-t f}`. -/
def expSMulEquiv (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) : SmoothForm I M ℝ k ≃ₗ[ℝ] SmoothForm I M ℝ k where
  toLinearMap := SmoothForm.funSMulₗ (expMul f t)
  invFun := SmoothForm.funSMulₗ (expMul f (-t))
  left_inv φ := Subtype.ext <| funext fun x ↦ by
    simp only [LinearMap.toFun_eq_coe, SmoothForm.coe_funSMulₗ, smul_smul,
      mul_comm (expMul f (-t) x), expMul_mul_expMul_neg, one_smul]
  right_inv φ := Subtype.ext <| funext fun x ↦ by
    simp only [LinearMap.toFun_eq_coe, SmoothForm.coe_funSMulₗ, smul_smul,
      expMul_mul_expMul_neg, one_smul]

/-- The rough form underlying `e^{t f} φ` is the pointwise product. -/
@[simp]
theorem coe_expSMulEquiv (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (φ : SmoothForm I M ℝ k) :
    (expSMulEquiv k f t φ : RoughForm I M ℝ k) = fun x ↦ Real.exp (t * f x) • φ.1 x := by
  simp [expSMulEquiv, expMul_apply]

/-- The inverse of multiplication by `e^{t f}` is multiplication by `e^{-t f}`. -/
@[simp]
theorem expSMulEquiv_symm (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) :
    (expSMulEquiv k f t).symm = expSMulEquiv k f (-t) :=
  LinearEquiv.ext fun _ ↦ rfl

end Gauge

variable [IsManifold I 2 M]

/-- **The Witten deformation of the exterior derivative**, `d_t = e^{-t f} ∘ d ∘ e^{t f}`, as a
linear map from smooth `k`-forms to smooth `(k + 1)`-forms. It is the local operator
`d_t φ = dφ + t df ∧ φ` (`TauCeti.wittenExtDerivₗ_apply`). -/
def wittenExtDerivₗ (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (k : ℕ) :
    SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ (k + 1) :=
  (expSMulEquiv (k + 1) f (-t)).toLinearMap ∘ₗ mextDerivₗ I k ∘ₗ (expSMulEquiv k f t).toLinearMap

/-- The defining conjugation formula `d_t φ = e^{-t f} d (e^{t f} φ)`. -/
theorem wittenExtDerivₗ_def (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (φ : SmoothForm I M ℝ k) :
    wittenExtDerivₗ f t k φ = expSMulEquiv (k + 1) f (-t) (mextDerivₗ I k (expSMulEquiv k f t φ)) :=
  (rfl)

/-- **Multiplication by `e^{t f}` intertwines `d_t` with `d`:** `e^{t f} d_t φ = d (e^{t f} φ)`. -/
theorem expSMulEquiv_wittenExtDerivₗ (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (φ : SmoothForm I M ℝ k) :
    expSMulEquiv (k + 1) f t (wittenExtDerivₗ f t k φ) =
      mextDerivₗ I k (expSMulEquiv k f t φ) := by
  rw [wittenExtDerivₗ_def, ← expSMulEquiv_symm, LinearEquiv.apply_symm_apply]

/-- **The Witten differential is the local operator `d_t φ = dφ + t df ∧ φ`.** The degree
`0 + 1 + k` of `df ∧ φ` is identified with `k + 1` by `Fin.cast`. -/
theorem wittenExtDerivₗ_apply (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (φ : SmoothForm I M ℝ k) (x : M)
    (v : Fin (k + 1) → TangentSpace I x) :
    (wittenExtDerivₗ f t k φ).1 x v =
      mextDeriv φ.1 x v + t * (mextDeriv (RoughForm.ofFunction I f)).wedge φ.1 x
        (v ∘ Fin.cast (show 0 + 1 + k = k + 1 by omega)) := by
  simp only [wittenExtDerivₗ_def, coe_expSMulEquiv, mextDerivₗ_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [mextDeriv_exp_mul_smul (f.contMDiff.mdifferentiableAt (by simp)) (φ.mdifferentiableAt x),
    ← mul_assoc, ← Real.exp_add]
  simp

/-- **`d_t = d + t df ∧ ·` as an identity of smooth forms.** Here `df` is the exterior derivative
of the smooth `0`-form of `f`, and the degree `0 + 1 + k` of the wedge is transported to `k + 1`. -/
theorem wittenExtDerivₗ_eq_add_smul (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (φ : SmoothForm I M ℝ k) :
    wittenExtDerivₗ f t k φ =
      mextDerivₗ I k φ + t • LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q)
        (show 0 + 1 + k = k + 1 by omega)
          (SmoothForm.wedge (mextDerivₗ I 0 (SmoothForm.ofFunction f)) φ) := by
  apply Subtype.ext
  funext x
  ext v
  simp only [wittenExtDerivₗ_apply, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  rw [SmoothForm.cast_apply]
  simp [mextDerivₗ_apply]

/-- At `t = 0` the Witten differential is the exterior derivative. -/
@[simp]
theorem wittenExtDerivₗ_zero (f : C^∞⟮I, M; ℝ⟯) (k : ℕ) :
    wittenExtDerivₗ f 0 k = mextDerivₗ I k := by
  ext φ : 1
  apply Subtype.ext
  funext x
  ext v
  rw [wittenExtDerivₗ_apply, zero_mul, add_zero, mextDerivₗ_apply]

/-- **The Witten differential squares to zero.** -/
@[simp]
theorem wittenExtDerivₗ_comp_wittenExtDerivₗ (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (k : ℕ) :
    wittenExtDerivₗ f t (k + 1) ∘ₗ wittenExtDerivₗ f t k = 0 := by
  ext φ : 1
  rw [LinearMap.comp_apply, LinearMap.zero_apply, wittenExtDerivₗ_def (k := k + 1),
    expSMulEquiv_wittenExtDerivₗ, ← LinearMap.comp_apply (mextDerivₗ I (k + 1)),
    mextDerivₗ_comp_mextDerivₗ, LinearMap.zero_apply, map_zero]

variable (f : C^∞⟮I, M; ℝ⟯) (t : ℝ)

/-- **The Witten complex**: smooth real forms with the deformed differential `d_t`. -/
def wittenComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (SmoothForm I M ℝ k))
    (fun k ↦ ModuleCat.ofHom (wittenExtDerivₗ f t k))
    (fun k ↦ ModuleCat.hom_ext (wittenExtDerivₗ_comp_wittenExtDerivₗ f t k))

/-- The canonical identification of the degree-`k` object of the Witten complex with smooth
`k`-forms. -/
def wittenComplexXIso (k : ℕ) :
    (wittenComplex f t).X k ≅ ModuleCat.of ℝ (SmoothForm I M ℝ k) := by
  unfold wittenComplex
  exact Iso.refl _

/-- Under the canonical identifications of the objects, the differential of the Witten complex is
the Witten differential. -/
@[reassoc]
theorem wittenComplex_d (k : ℕ) :
    (wittenComplex f t).d k (k + 1) ≫ (wittenComplexXIso f t (k + 1)).hom =
      (wittenComplexXIso f t k).hom ≫ ModuleCat.ofHom (wittenExtDerivₗ f t k) := by
  dsimp +instances [wittenComplexXIso, wittenComplex]
  simp

/-- The differential of the Witten complex, evaluated on an element. -/
theorem wittenComplex_d_apply (k : ℕ) (φ : (wittenComplex f t).X k) :
    (wittenComplex f t).d k (k + 1) φ =
      (wittenComplexXIso f t (k + 1)).inv
        (wittenExtDerivₗ f t k ((wittenComplexXIso f t k).hom φ)) := by
  rw [(Iso.eq_comp_inv _).mpr (wittenComplex_d f t k), ModuleCat.comp_apply,
    ModuleCat.comp_apply, ConcreteCategory.hom_ofHom]

/-- **Multiplication by `e^{t f}` identifies the Witten complex with the de Rham complex.** In
degree `k` the isomorphism is `expSMulEquiv k f t` (`TauCeti.wittenComplexIso_hom_f`). -/
def wittenComplexIso : wittenComplex f t ≅ deRhamComplex I M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ wittenComplexXIso f t k ≪≫ (expSMulEquiv k f t).toModuleIso ≪≫
      (deRhamComplexXIso I k).symm) <| by
    rintro k _ rfl
    have hcomm : (expSMulEquiv k f t).toModuleIso.hom ≫ ModuleCat.ofHom (mextDerivₗ I k) =
        ModuleCat.ofHom (wittenExtDerivₗ f t k) ≫ (expSMulEquiv (k + 1) f t).toModuleIso.hom := by
      ext φ : 2
      exact (expSMulEquiv_wittenExtDerivₗ f t φ).symm
    rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d I (M := M) k),
      (Iso.eq_comp_inv _).mpr (wittenComplex_d f t k)]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      reassoc_of% hcomm]

/-- In each degree, the isomorphism of the Witten complex with the de Rham complex is
multiplication by `e^{t f}`. -/
@[reassoc]
theorem wittenComplexIso_hom_f (k : ℕ) :
    (wittenComplexIso f t).hom.f k ≫ (deRhamComplexXIso I k).hom =
      (wittenComplexXIso f t k).hom ≫ ModuleCat.ofHom (expSMulEquiv k f t).toLinearMap := by
  simp [wittenComplexIso]

/-- **The cohomology of the Witten differential is de Rham cohomology**, for every smooth
function `f` and every parameter `t`. -/
def wittenCohomologyIso (k : ℕ) :
    (wittenComplex f t).homology k ≅ (deRhamComplex I M).homology k :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (wittenComplexIso f t)

variable {f t}

/-- **In degree zero, `d_t g = 0` exactly when `e^{t f} g` is locally constant.** Thus the kernel of
`d_t` on functions consists of the locally constant multiples of `e^{-t f}`. -/
theorem wittenExtDerivₗ_apply_eq_zero_iff_isLocallyConstant (g : SmoothForm I M ℝ 0) :
    wittenExtDerivₗ f t 0 g = 0 ↔ IsLocallyConstant fun x ↦ Real.exp (t * f x) * g.1 x 0 := by
  rw [← (expSMulEquiv 1 f t).map_eq_zero_iff, expSMulEquiv_wittenExtDerivₗ,
    ← mem_closedForms_iff_mextDerivₗ_eq_zero, mem_closedForms_zero_iff, coe_expSMulEquiv]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- **`e^{-t f}` is annihilated by the Witten differential**: `d_t (e^{-t f} · 1) = 0`. For
`f = x²` on the line, with its nondegenerate minimum at `0`, and `t > 0`, this is the Gaussian
`e^{-t x²}`. -/
theorem wittenExtDerivₗ_expSMulEquiv_neg_ofFunction_one :
    wittenExtDerivₗ f t 0 (expSMulEquiv 0 f (-t) (SmoothForm.ofFunction (ContMDiffMap.const 1))) =
      0 := by
  rw [wittenExtDerivₗ_apply_eq_zero_iff_isLocallyConstant, coe_expSMulEquiv]
  have hconst : ∀ x, (ContMDiffMap.const 1 : C^∞⟮I, M; ℝ⟯) x = 1 := fun _ ↦ rfl
  simp only [ContinuousAlternatingMap.smul_apply, SmoothForm.coe_ofFunction,
    RoughForm.ofFunction_apply, hconst, smul_eq_mul, mul_one, ← Real.exp_add, neg_mul,
    add_neg_cancel, Real.exp_zero]
  exact IsLocallyConstant.const 1

end SmoothForm

end TauCeti
