/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Star.LinearMap
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Complex-valued smooth functions on real manifolds

Complex-valued functions on a real manifold are real smooth maps, not holomorphic maps.
This file equips their native `ContMDiffMap` carrier with the complex algebra structure
induced by constant functions. The native real scalar action agrees with restriction of
scalars. Real and imaginary parts identify this real vector space with a pair of real
function spaces, so complex-linear maps out of it are determined on real-valued functions
(`ContMDiffMap.linearMap_ext_ofReal`), a real-linear map between real-valued functions
complexifies to a complex-linear map between complex-valued ones
(`ContMDiffMap.complexifyLinearMap`), and conjugation is a real algebra involution. Conjugation is
also the star operation of a star ring and complex star module, and the complexified maps are
exactly the complex-linear maps commuting with it
(`ContMDiffMap.exists_complexifyLinearMap_eq_iff`).
Differentiation commutes with real and imaginary parts at every nonzero differentiability
order. Precomposition with a smooth map is a complex algebra homomorphism
(`ContMDiffMap.compRightComplexAlgHom`), used to pull back complex-valued differential data.
For a diffeomorphism it is a complex algebra isomorphism (`Diffeomorph.compRightComplexAlgEquiv`),
and conjugating by it carries the complex-linear operators on the functions on one manifold to
those on the other (`Diffeomorph.pushforwardOperator`), functorially in the diffeomorphism.

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
    C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₐ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯ :=
  AlgHom.mk' (compRightAlgHom ℝ ℂ φ).toRingHom (fun c f ↦ by
    ext x
    simp)

@[simp]
theorem compRightComplexAlgHom_apply (φ : C^n⟮J, N; I, M⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : compRightComplexAlgHom φ f = f.comp φ := by
  simp [compRightComplexAlgHom]

/-- Pullback along the identity is the identity algebra homomorphism. -/
@[simp]
theorem compRightComplexAlgHom_id :
    compRightComplexAlgHom (ContMDiffMap.id : C^n⟮I, M; I, M⟯) = AlgHom.id ℂ _ := by
  ext f x
  simp only [compRightComplexAlgHom_apply, AlgHom.id_apply, comp_apply]
  rfl

/-- Pullback along a composite reverses the order of the algebra homomorphisms. -/
theorem compRightComplexAlgHom_comp {E'' H'' P : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P]
    (φ : C^n⟮J, N; I, M⟯) (ψ : C^n⟮K, P; J, N⟯) :
    compRightComplexAlgHom (φ.comp ψ) =
      (compRightComplexAlgHom ψ).comp (compRightComplexAlgHom φ) := by
  ext f x
  simp

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

/-- **Splitting by a partition of unity.** If real-valued smooth functions `ρ i` add up to `1` on a
set `K` containing the support of a complex-valued smooth function `g`, then `g` is the sum of the
products `ρ i · g`. -/
theorem eq_sum_mulLeft_ofReal {ι : Type*} (s : Finset ι) (ρ : ι → C^n⟮I, M; ℝ⟯) {K : Set M}
    {g : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} (hg : Function.support g ⊆ K)
    (hρ : ∀ x ∈ K, ∑ i ∈ s, ρ i x = 1) :
    g = ∑ i ∈ s, LinearMap.mulLeft ℂ (ofReal (ρ i)) g := by
  ext x
  simp only [coe_sum, Finset.sum_apply, LinearMap.mulLeft_apply, coe_mul, Pi.mul_apply,
    ofReal_apply, ← Finset.sum_mul]
  by_cases hx : x ∈ K
  · rw [← Complex.ofReal_sum, hρ x hx, Complex.ofReal_one, one_mul]
  · rw [Function.notMem_support.1 fun h ↦ hx (hg h), mul_zero]

/-- Real and imaginary parts reconstruct the original smooth function. -/
theorem ofReal_re_add_I_smul_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ofReal f.re + Complex.I • ofReal f.im = f := by
  ext x
  simpa [mul_comm] using Complex.re_add_im (f x)

/-- A complex-linear map out of complex-valued smooth functions is determined by its values on
real-valued functions. -/
theorem linearMap_ext_ofReal {N : Type*} [AddCommMonoid N] [Module ℂ N]
    {φ ψ : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] N} (h : ∀ u : C^n⟮I, M; ℝ⟯, φ (ofReal u) = ψ (ofReal u)) :
    φ = ψ := by
  ext f
  rw [← ofReal_re_add_I_smul_im f, map_add, map_add, map_smul, map_smul, h, h]

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

theorem conj_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) : conj f x = star (f x) := by
  rfl

@[simp]
theorem conj_symm : (conj (I := I) (M := M) (n := n)).symm = conj := by
  ext f x
  rfl

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

/-- Pointwise complex conjugation is the star operation of the complex smooth functions, making them
a star ring and a star module over `ℂ`. -/
instance complexSmoothFunctionsStarRing : StarRing C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  star := conj
  star_involutive f := by
    ext x
    simp [conj_apply]
  star_mul f g := by
    ext x
    simp [conj_apply, mul_comm]
  star_add f g := by
    ext x
    simp [conj_apply]

/-- The star of a complex smooth function is its pointwise complex conjugate. -/
@[simp]
theorem coe_star (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : ⇑(star f) = star ⇑f := by
  rfl

theorem star_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) : (star f) x = star (f x) := by
  rfl

/-- `star` is the simp-normal form of conjugation of complex smooth functions. -/
@[simp]
theorem conj_eq_star (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : conj f = star f := by
  rfl

instance complexSmoothFunctionsStarModule : StarModule ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  star_smul z f := by
    ext x
    simp

@[simp]
theorem star_re (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : (star f).re = f.re := by
  ext x
  simp

@[simp]
theorem star_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : (star f).im = -f.im := by
  ext x
  simp

@[simp]
theorem star_ofReal (f : C^n⟮I, M; ℝ⟯) : star (ofReal f) = ofReal f := by
  ext x
  simp

@[simp]
theorem star_complexSmoothConstants (z : ℂ) :
    star (TauCeti.complexSmoothConstants (I := I) (M := M) (n := n) z) =
      TauCeti.complexSmoothConstants (star z) := by
  ext x
  rfl

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
theorem star_comp (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (g : C^n⟮J, N; I, M⟯) :
    star (f.comp g) = (star f).comp g := by
  ext x
  rfl

@[simp]
theorem ofReal_comp (f : C^n⟮I, M; ℝ⟯) (g : C^n⟮J, N; I, M⟯) :
    ofReal (f.comp g) = (ofReal f).comp g := by
  ext x
  rfl

/-- The complexification of a real-linear map `D` between real-valued smooth functions: the
complex-linear map acting by `D` on real and imaginary parts, `D (u + i v) = D u + i D v`. -/
def complexifyLinearMap :
    (C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮J, N; ℝ⟯) →ₗ[ℝ]
      C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun D :=
    { toFun f := ofReal (D f.re) + Complex.I • ofReal (D f.im)
      map_add' f g := by
        simp only [map_add, smul_add]
        abel
      map_smul' z f := by
        ext x
        apply Complex.ext <;> simp <;> ring }
  map_add' D₁ D₂ := by
    ext f x
    apply Complex.ext <;> simp
  map_smul' r D := by
    ext f x
    apply Complex.ext <;> simp

/-- The complexification of `D` acts on `f` through the real and imaginary parts of `f`. -/
@[simp]
theorem complexifyLinearMap_apply (D : C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮J, N; ℝ⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexifyLinearMap D f = ofReal (D f.re) + Complex.I • ofReal (D f.im) :=
  (rfl)

/-- The complexification of `D` extends `D` from real to complex functions. -/
theorem complexifyLinearMap_ofReal (D : C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮J, N; ℝ⟯) (u : C^n⟮I, M; ℝ⟯) :
    complexifyLinearMap D (ofReal u) = ofReal (D u) := by
  ext x
  simp

/-- **The complexification of a local operator is local.** If `D g` vanishes at `x` whenever the
real-valued function `g` vanishes near `x`, then `complexifyLinearMap D f` vanishes at `x` whenever
the complex-valued function `f` vanishes near `x`. -/
theorem complexifyLinearMap_apply_eq_zero {D : C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮I, M; ℝ⟯} {x : M}
    (hD : ∀ g : C^n⟮I, M; ℝ⟯, (∀ᶠ y in nhds x, g y = 0) → D g x = 0)
    {f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} (hf : ∀ᶠ y in nhds x, f y = 0) :
    complexifyLinearMap D f x = 0 := by
  simp [hD f.re (hf.mono fun y hy ↦ by simp [hy]), hD f.im (hf.mono fun y hy ↦ by simp [hy])]

/-- **Real operators.** A complex-linear map `P` between complex-valued smooth functions is the
complexification of a real-linear map between real-valued smooth functions exactly when it commutes
with complex conjugation, `P (star f) = star (P f)`. The real map is then `u ↦ Re (P u)`. -/
theorem exists_complexifyLinearMap_eq_iff
    {P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯} :
    (∃ D, complexifyLinearMap D = P) ↔ ∀ f, P (star f) = star (P f) := by
  refine ⟨?_, fun h ↦ ⟨re ∘ₗ P.restrictScalars ℝ ∘ₗ ofReal.toLinearMap, ?_⟩⟩
  · rintro ⟨D, rfl⟩ f
    ext x
    apply Complex.ext <;> simp
  -- `P` sends real functions to real functions, since they are their own conjugates.
  refine linearMap_ext_ofReal fun u ↦ ?_
  have him : (P (ofReal u)).im = 0 := by
    have h' := congrArg im (h (ofReal u))
    rw [star_ofReal, star_im] at h'
    exact self_eq_neg.1 h'
  refine ext_re_im ?_ ?_ <;> simp [him]

open WithConv in
/-- The complexification of a real-linear map between real-valued smooth functions commutes with
conjugation: it is self-adjoint for Mathlib's intrinsic star of linear maps. -/
theorem isSelfAdjoint_toConv_complexifyLinearMap (D : C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮J, N; ℝ⟯) :
    IsSelfAdjoint (toConv (complexifyLinearMap D)) :=
  (LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _).2
    (exists_complexifyLinearMap_eq_iff.1 ⟨D, rfl⟩)

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

/-- Star commutes with restriction to an open subset. -/
@[simp]
theorem star_restrictRingHom (h : U ≤ V) (f : C^n⟮I, V; 𝓘(ℝ, ℂ), ℂ⟯) :
    star (restrictRingHom I 𝓘(ℝ, ℂ) ℂ h f) = restrictRingHom I 𝓘(ℝ, ℂ) ℂ h (star f) := by
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

namespace Diffeomorph

open ContMDiffMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Precomposition with a `C^n` diffeomorphism `φ : N → M`, as a complex algebra isomorphism from
the real `C^n` complex-valued functions on `M` to those on `N`, with inverse the precomposition with
`φ⁻¹`. This is the complex-linear version of `Diffeomorph.compRightAlgEquiv ℝ ℂ φ`. -/
def compRightComplexAlgEquiv (φ : N ≃ₘ^n⟮J, I⟯ M) :
    C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₐ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯ :=
  AlgEquiv.ofAlgHom (compRightComplexAlgHom φ.toContMDiffMap)
    (compRightComplexAlgHom φ.symm.toContMDiffMap)
    (AlgHom.ext fun _ ↦ ContMDiffMap.ext fun _ ↦ by simp)
    (AlgHom.ext fun _ ↦ ContMDiffMap.ext fun _ ↦ by simp)

theorem coe_compRightComplexAlgEquiv_apply (φ : N ≃ₘ^n⟮J, I⟯ M) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⇑(compRightComplexAlgEquiv φ f) = f ∘ φ := by
  ext x
  simp [compRightComplexAlgEquiv]

@[simp]
theorem compRightComplexAlgEquiv_apply (φ : N ≃ₘ^n⟮J, I⟯ M) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (x : N) : compRightComplexAlgEquiv φ f x = f (φ x) := by
  simp [compRightComplexAlgEquiv]

theorem compRightComplexAlgEquiv_symm_apply (φ : N ≃ₘ^n⟮J, I⟯ M) (f : C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯)
    (x : M) : (compRightComplexAlgEquiv φ).symm f x = f (φ.symm x) := by
  simp [compRightComplexAlgEquiv]

/-- The inverse of precomposition with `φ` is precomposition with `φ⁻¹`. -/
@[simp]
theorem compRightComplexAlgEquiv_symm (φ : N ≃ₘ^n⟮J, I⟯ M) :
    (compRightComplexAlgEquiv φ).symm = compRightComplexAlgEquiv φ.symm :=
  AlgEquiv.ext fun _ ↦ ContMDiffMap.ext fun _ ↦ by
    rw [compRightComplexAlgEquiv_symm_apply, compRightComplexAlgEquiv_apply]

/-- Precomposition with the identity is the identity. -/
@[simp]
theorem compRightComplexAlgEquiv_refl :
    compRightComplexAlgEquiv (Diffeomorph.refl I M n) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ ↦ ContMDiffMap.ext fun _ ↦ by simp

/-- Precomposition with a composite reverses the order of the precompositions. -/
theorem compRightComplexAlgEquiv_trans {E'' H'' P : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace P] [ChartedSpace H'' P] (φ : N ≃ₘ^n⟮J, I⟯ M) (ψ : M ≃ₘ^n⟮I, K⟯ P) :
    compRightComplexAlgEquiv (φ.trans ψ) =
      (compRightComplexAlgEquiv ψ).trans (compRightComplexAlgEquiv φ) :=
  AlgEquiv.ext fun _ ↦ ContMDiffMap.ext fun _ ↦ by simp

/-- The **pushforward** of complex-linear operators on the real-smooth complex-valued functions
along a `C^n` diffeomorphism `Φ : M → N`: the operator `P` on `M` becomes the operator
`u ↦ P (u ∘ Φ) ∘ Φ⁻¹` on `N`. It is an isomorphism of complex algebras, so it respects the
identity and composition of operators. -/
def pushforwardOperator (Φ : M ≃ₘ^n⟮I, J⟯ N) :
    Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₐ[ℂ] Module.End ℂ C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯ :=
  (compRightComplexAlgEquiv Φ.symm).toLinearEquiv.conjAlgEquiv ℂ

@[simp]
theorem pushforwardOperator_apply_apply (Φ : M ≃ₘ^n⟮I, J⟯ N)
    (P : Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (u : C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) (y : N) :
    pushforwardOperator Φ P u y = P (compRightComplexAlgEquiv Φ u) (Φ.symm y) := by
  simp [pushforwardOperator, LinearEquiv.conjAlgEquiv_apply, ← AlgEquiv.toLinearEquiv_symm]

/-- As a function, the pushforward of `P` applied to `u` is `P (u ∘ Φ) ∘ Φ⁻¹`. -/
theorem coe_pushforwardOperator_apply (Φ : M ≃ₘ^n⟮I, J⟯ N)
    (P : Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (u : C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⇑(pushforwardOperator Φ P u) = P (compRightComplexAlgEquiv Φ u) ∘ Φ.symm :=
  funext <| pushforwardOperator_apply_apply Φ P u

/-- The pushforward along `Φ⁻¹` undoes the pushforward along `Φ`. -/
@[simp]
theorem pushforwardOperator_symm (Φ : M ≃ₘ^n⟮I, J⟯ N) :
    (pushforwardOperator Φ).symm = pushforwardOperator Φ.symm := by
  rw [pushforwardOperator, pushforwardOperator, LinearEquiv.symm_conjAlgEquiv,
    ← AlgEquiv.toLinearEquiv_symm, compRightComplexAlgEquiv_symm, symm_symm]

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem pushforwardOperator_refl :
    pushforwardOperator (Diffeomorph.refl I M n) = AlgEquiv.refl := by
  ext P u x
  simp

/-- The pushforward along a composite of diffeomorphisms is the composite of the pushforwards. -/
theorem pushforwardOperator_trans {E'' H'' P : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P]
    [ChartedSpace H'' P] (Φ : M ≃ₘ^n⟮I, J⟯ N) (Ψ : N ≃ₘ^n⟮J, K⟯ P) :
    pushforwardOperator (Φ.trans Ψ) = (pushforwardOperator Φ).trans (pushforwardOperator Ψ) := by
  ext P u x
  simp [compRightComplexAlgEquiv_trans]

end Diffeomorph
