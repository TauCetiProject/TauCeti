/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Complex-valued smooth functions on real manifolds

Complex-valued functions on a real manifold are real smooth maps, not holomorphic maps.
This file equips their native `ContMDiffMap` carrier with the complex algebra structure
induced by constant functions. The native real scalar action agrees with restriction of
scalars. Real and imaginary parts identify this real vector space with a pair of real
function spaces, and conjugation is a real algebra involution. Differentiation commutes with
real and imaginary parts at every nonzero differentiability order. Precomposition with a
smooth map is a complex algebra homomorphism (`ContMDiffMap.compRightComplexAlgHom`), used
to pull back complex-valued differential data.

The constructions use Mathlib's pointwise smooth-function ring, `compLeftRingHom`, and
its continuous real-linear maps `Complex.reCLM`, `Complex.imCLM`, `Complex.ofRealCLM`
and `Complex.conjCLE`. No dimension or boundary assumptions are needed.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

/-- Complex multiplication and addition are smooth over the real numbers. -/
instance realComplexContMDiffRing {n : ℕ∞ω} : ContMDiffRing 𝓘(ℝ, ℂ) n ℂ where
  toContMDiffAdd := instContMDiffAddSelf
  contMDiff_mul := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contDiff_mul.contMDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- Constant complex functions on a real manifold, as a ring homomorphism. -/
def complexSmoothConstants : ℂ →+* C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun := ContMDiffMap.const
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

@[simp]
theorem complexSmoothConstants_apply (z : ℂ) (x : M) :
    (complexSmoothConstants (I := I) (n := n) z) x = z := by
  rfl

/-- The complex algebra of real-smooth complex-valued functions, via constants. -/
instance complexSmoothFunctionsAlgebra : Algebra ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  complexSmoothConstants.toAlgebra

/-- The complex algebra map is the constant-function ring homomorphism. -/
@[simp]
theorem algebraMap_eq_complexSmoothConstants :
    algebraMap ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ = complexSmoothConstants := by
  rfl

end TauCeti

namespace ContMDiffMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

@[simp]
theorem complex_smul_apply (z : ℂ) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    (z • f) x = z * f x := by
  rfl

section Pullback

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Pullback of real-smooth complex-valued functions as a complex algebra homomorphism. -/
def compRightComplexAlgHom (φ : C^n⟮J, N; I, M⟯) :
    C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₐ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun f := f.comp φ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem compRightComplexAlgHom_apply (φ : C^n⟮J, N; I, M⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : compRightComplexAlgHom φ f = f.comp φ :=
  (rfl)

/-- Pullback along the identity is the identity algebra homomorphism. -/
@[simp]
theorem compRightComplexAlgHom_id :
    compRightComplexAlgHom (ContMDiffMap.id : C^n⟮I, M; I, M⟯) = AlgHom.id ℂ _ :=
  (rfl)

/-- Pullback along a composite reverses the order of the algebra homomorphisms. -/
theorem compRightComplexAlgHom_comp {E'' H'' P : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P]
    (φ : C^n⟮J, N; I, M⟯) (ψ : C^n⟮K, P; J, N⟯) :
    compRightComplexAlgHom (φ.comp ψ) =
      (compRightComplexAlgHom ψ).comp (compRightComplexAlgHom φ) :=
  (rfl)

end Pullback

/-- Restricting complex scalars recovers the native real scalar action. -/
instance complexSmoothFunctions_isScalarTower :
    IsScalarTower ℝ ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  smul_assoc r z f := by
    ext x
    simp [mul_assoc]

/-- Real and complex constant scalar actions commute. -/
instance complexSmoothFunctions_smulCommClass :
    SMulCommClass ℝ ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  smul_comm r z f := by
    ext x
    simp [mul_left_comm]

/-- Real part of a complex-valued real-smooth function, as a real-linear map. -/
def re : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℝ] C^n⟮I, M; ℝ⟯ where
  toFun f := ⟨fun x ↦ (f x).re, Complex.reCLM.contMDiff.comp f.contMDiff⟩
  map_add' f g := by ext x; exact Complex.add_re (f x) (g x)
  map_smul' r f := by ext x; exact Complex.smul_re r (f x)

/-- Imaginary part of a complex-valued real-smooth function, as a real-linear map. -/
def im : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℝ] C^n⟮I, M; ℝ⟯ where
  toFun f := ⟨fun x ↦ (f x).im, Complex.imCLM.contMDiff.comp f.contMDiff⟩
  map_add' f g := by ext x; exact Complex.add_im (f x) (g x)
  map_smul' r f := by ext x; exact Complex.smul_im r (f x)

@[simp]
theorem re_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) : f.re x = (f x).re := by
  rfl

@[simp]
theorem im_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) : f.im x = (f x).im := by
  rfl

/-- Inclusion of real-valued smooth functions into complex-valued ones as a real algebra map. -/
def ofReal : C^n⟮I, M; ℝ⟯ →ₐ[ℝ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toRingHom := compLeftRingHom I M Complex.ofRealHom Complex.ofRealCLM.contMDiff
  commutes' _ := by ext; rfl

@[simp]
theorem ofReal_apply (f : C^n⟮I, M; ℝ⟯) (x : M) :
    ofReal f x = (f x : ℂ) := by
  rfl

@[simp]
theorem ofReal_re (f : C^n⟮I, M; ℝ⟯) : (ofReal f).re = f := by
  ext x
  simp

@[simp]
theorem ofReal_im (f : C^n⟮I, M; ℝ⟯) : (ofReal f).im = 0 := by
  ext x
  simp

/-- Inclusion of real-valued functions is injective. -/
theorem ofReal_injective :
    Function.Injective (ofReal (I := I) (M := M) (n := n)) := by
  intro f g h
  simpa using congrArg re h

/-- Real and imaginary parts reconstruct the original smooth function. -/
theorem ofReal_re_add_I_smul_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ofReal f.re + Complex.I • ofReal f.im = f := by
  ext x
  simpa [mul_comm] using Complex.re_add_im (f x)

/-- Complex-valued real-smooth functions are uniquely pairs of real-smooth functions. -/
def equivRealProd :
    C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℝ] C^n⟮I, M; ℝ⟯ × C^n⟮I, M; ℝ⟯ where
  toLinearMap := re.prod im
  invFun p := ofReal p.1 + Complex.I • ofReal p.2
  left_inv := ofReal_re_add_I_smul_im
  right_inv p := by ext x <;> simp

@[simp]
theorem equivRealProd_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    equivRealProd f = (f.re, f.im) := by
  rfl

@[simp]
theorem equivRealProd_symm_apply (p : C^n⟮I, M; ℝ⟯ × C^n⟮I, M; ℝ⟯) :
    equivRealProd.symm p = ofReal p.1 + Complex.I • ofReal p.2 := by
  rfl

/-- Complex smooth functions are determined by their real and imaginary parts. -/
theorem ext_re_im {f g : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hre : f.re = g.re) (him : f.im = g.im) : f = g :=
  equivRealProd.injective (by simp [hre, him])

/-- Equality of complex smooth functions is equality of both real and imaginary parts. -/
theorem ext_re_im_iff {f g : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    f = g ↔ f.re = g.re ∧ f.im = g.im :=
  ⟨fun h ↦ by simp [h], fun h ↦ ext_re_im h.1 h.2⟩

/-- Pointwise complex conjugation is an involutive real algebra equivalence. -/
def conj : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₐ[ℝ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toRingEquiv :=
    { ContMDiffMap.compLeftRingHom I M (starRingEnd ℂ)
        (Complex.conjCLE.toContinuousLinearMap.contMDiff.congr
          fun z ↦ (Complex.conjCLE_apply z).symm) with
      invFun f := ⟨fun x ↦ star (f x),
        (Complex.conjCLE.toContinuousLinearMap.contMDiff.comp f.contMDiff).congr
          fun x ↦ (Complex.conjCLE_apply (f x)).symm⟩
      left_inv f := by ext x; exact star_star (f x)
      right_inv f := by ext x; exact star_star (f x) }
  commutes' r := by
    ext x
    -- Mathlib has no application lemmas for compLeftRingHom or the real algebra map.
    -- Expose their pointwise definitions before simplifying conjugation of a real constant.
    dsimp [compLeftRingHom, algebraMap, C]
    exact Complex.conj_ofReal r

@[simp]
theorem conj_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) : conj f x = star (f x) := by
  rfl

@[simp]
theorem conj_symm : (conj (I := I) (M := M) (n := n)).symm = conj := by
  ext f x
  rfl

@[simp]
theorem conj_ofReal (f : C^n⟮I, M; ℝ⟯) : conj (ofReal f) = ofReal f := by
  ext x
  simp

@[simp]
theorem complexSmoothConstants_re (z : ℂ) :
    (TauCeti.complexSmoothConstants (I := I) (M := M) (n := n) z).re = const z.re := by
  ext x
  rfl

@[simp]
theorem complexSmoothConstants_im (z : ℂ) :
    (TauCeti.complexSmoothConstants (I := I) (M := M) (n := n) z).im = const z.im := by
  ext x
  rfl

@[simp]
theorem conj_complexSmoothConstants (z : ℂ) :
    conj (TauCeti.complexSmoothConstants (I := I) (M := M) (n := n) z) =
      TauCeti.complexSmoothConstants (star z) := by
  ext x
  rfl

@[simp]
theorem conj_complex_smul (z : ℂ) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    conj (z • f) = star z • conj f := by
  ext x
  simp

@[simp]
theorem conj_conj (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : conj (conj f) = f := by
  ext x
  simp

@[simp]
theorem conj_re (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : (conj f).re = f.re := by
  ext x
  simp

@[simp]
theorem conj_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : (conj f).im = -f.im := by
  ext x
  simp

/-- Real part of a product of complex-valued smooth functions. -/
theorem mul_re (f g : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (f * g).re = f.re * g.re - f.im * g.im := by
  ext x
  simp [Complex.mul_re]

/-- Imaginary part of a product of complex-valued smooth functions. -/
theorem mul_im (f g : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (f * g).im = f.re * g.im + f.im * g.re := by
  ext x
  simp [Complex.mul_im]

/-- Real part of a complex scalar multiple of a smooth function. -/
@[simp]
theorem complex_smul_re (z : ℂ) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (z • f).re = z.re • f.re - z.im • f.im := by
  ext x
  simp [Complex.mul_re]

/-- Imaginary part of a complex scalar multiple of a smooth function. -/
@[simp]
theorem complex_smul_im (z : ℂ) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (z • f).im = z.re • f.im + z.im • f.re := by
  ext x
  simp [Complex.mul_im]

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

@[simp]
theorem comp_re (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (g : C^n⟮J, N; I, M⟯) :
    (f.comp g).re = f.re.comp g := by
  ext x
  rfl

@[simp]
theorem comp_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (g : C^n⟮J, N; I, M⟯) :
    (f.comp g).im = f.im.comp g := by
  ext x
  rfl

@[simp]
theorem conj_comp (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (g : C^n⟮J, N; I, M⟯) :
    conj (f.comp g) = (conj f).comp g := by
  ext x
  rfl

@[simp]
theorem ofReal_comp (f : C^n⟮I, M; ℝ⟯) (g : C^n⟮J, N; I, M⟯) :
    ofReal (f.comp g) = (ofReal f).comp g := by
  ext x
  rfl

variable {U V : TopologicalSpace.Opens M}

/-- Real part commutes with restriction to an open subset. -/
@[simp]
theorem restrictRingHom_re (h : U ≤ V) (f : C^n⟮I, V; 𝓘(ℝ, ℂ), ℂ⟯) :
    (restrictRingHom I 𝓘(ℝ, ℂ) ℂ h f).re = restrictRingHom I 𝓘(ℝ) ℝ h f.re := by
  ext x
  rfl

/-- Imaginary part commutes with restriction to an open subset. -/
@[simp]
theorem restrictRingHom_im (h : U ≤ V) (f : C^n⟮I, V; 𝓘(ℝ, ℂ), ℂ⟯) :
    (restrictRingHom I 𝓘(ℝ, ℂ) ℂ h f).im = restrictRingHom I 𝓘(ℝ) ℝ h f.im := by
  ext x
  rfl

/-- Conjugation commutes with restriction to an open subset. -/
@[simp]
theorem conj_restrictRingHom (h : U ≤ V) (f : C^n⟮I, V; 𝓘(ℝ, ℂ), ℂ⟯) :
    conj (restrictRingHom I 𝓘(ℝ, ℂ) ℂ h f) = restrictRingHom I 𝓘(ℝ, ℂ) ℂ h (conj f) := by
  ext x
  rfl

/-- Inclusion of real functions commutes with restriction to an open subset. -/
@[simp]
theorem ofReal_restrictRingHom (h : U ≤ V) (f : C^n⟮I, V; ℝ⟯) :
    ofReal (restrictRingHom I 𝓘(ℝ) ℝ h f) =
      restrictRingHom I 𝓘(ℝ, ℂ) ℂ h (ofReal f) := by
  ext x
  rfl

/-- Differentiation of a complex-valued real-smooth function commutes with taking real parts. -/
@[simp]
theorem mvfderiv_re (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (hn : n ≠ 0) (x : M) :
    mvfderiv I f.re x = Complex.reCLM.comp (mvfderiv I f x) := by
  have hre : ⇑f.re = Complex.reCLM ∘ f := by ext y; simp
  rw [hre]
  ext v
  exact Complex.reCLM.mvfderiv_comp_apply (f.contMDiff.mdifferentiable hn).mdifferentiableAt v

/-- Differentiation of a complex-valued real-smooth function commutes with taking imaginary
parts. -/
@[simp]
theorem mvfderiv_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (hn : n ≠ 0) (x : M) :
    mvfderiv I f.im x = Complex.imCLM.comp (mvfderiv I f x) := by
  have him : ⇑f.im = Complex.imCLM ∘ f := by ext y; simp
  rw [him]
  ext v
  exact Complex.imCLM.mvfderiv_comp_apply (f.contMDiff.mdifferentiable hn).mdifferentiableAt v

/-- The differential of a complex function vanishes exactly when the differentials of both
real components vanish. -/
theorem mvfderiv_eq_zero_iff_re_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (hn : n ≠ 0) (x : M) :
    mvfderiv I f x = 0 ↔ mvfderiv I f.re x = 0 ∧ mvfderiv I f.im x = 0 := by
  constructor
  · intro h
    simp [mvfderiv_re f hn, mvfderiv_im f hn, h]
  · rintro ⟨hr, hi⟩
    ext v
    apply Complex.ext
    · simpa only [mvfderiv_re f hn, ContinuousLinearMap.comp_apply,
        Complex.reCLM_apply, zero_apply, Complex.zero_re] using
        congrArg (fun L ↦ L v) hr
    · simpa only [mvfderiv_im f hn, ContinuousLinearMap.comp_apply,
        Complex.imCLM_apply, zero_apply, Complex.zero_im] using
        congrArg (fun L ↦ L v) hi

end ContMDiffMap
