/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.RingTheory.Derivation.DifferentialOperator
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
(`ContMDiffMap.complexifyLinearMap`), and conjugation is a real algebra involution. Conjugating
the input and output of a complex-linear map, `f ↦ conj (P (conj f))`, gives a complex-linear map
(`ContMDiffMap.intrinsicConj`); it fixes exactly the complexifications of real-linear maps
(`ContMDiffMap.intrinsicConj_eq_self_iff`), so every complex-linear map `P` is `A + i B` with `A`
and `B` complexifications
(`ContMDiffMap.exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq`), namely of
`u ↦ Re (P u)` and `u ↦ Im (P u)` on real-valued functions
(`ContMDiffMap.complexifyLinearMap_re_comp_add_I_smul_complexifyLinearMap_im_comp`). When `P` is
a complex differential operator in Grothendieck's sense, these real and imaginary parts are real
differential operators of the same order
(`TauCeti.re_comp_restrictScalars_comp_ofReal_mem_differentialOperators`,
`TauCeti.im_comp_restrictScalars_comp_ofReal_mem_differentialOperators`).
Differentiation commutes with real and imaginary parts at every nonzero differentiability
order. Precomposition with a smooth map is a complex algebra homomorphism
(`ContMDiffMap.compRightComplexAlgHom`), used to pull back complex-valued differential data.
For a diffeomorphism it is a complex algebra isomorphism (`Diffeomorph.compRightComplexAlgEquiv`),
and conjugating by it carries the complex-linear operators on the functions on one manifold to
those on the other (`Diffeomorph.pushforwardOperator`), functorially in the diffeomorphism. An
operator is invariant under the pushforward along a self-diffeomorphism exactly when it commutes
with precomposition by it (`Diffeomorph.pushforwardOperator_eq_self_iff`).

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

/-- The real part is linear over real-valued functions. -/
@[simp]
theorem re_ofReal_mul (b : C^n⟮I, M; ℝ⟯) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (ofReal b * f).re = b * f.re := by
  ext x
  simp

/-- The imaginary part is linear over real-valued functions. -/
@[simp]
theorem im_ofReal_mul (b : C^n⟮I, M; ℝ⟯) (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (ofReal b * f).im = b * f.im := by
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

/-- Conjugation does not change the support of a function. -/
@[simp]
theorem support_conj (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : Function.support (conj f) = Function.support f :=
  Function.support_comp_eq star star_eq_zero f

/-- Conjugation does not change the topological support of a function. -/
@[simp]
theorem tsupport_conj (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : tsupport (conj f) = tsupport f :=
  tsupport_comp_eq star_eq_zero f

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

/-- The **complex conjugate** `f ↦ conj (P (conj f))` of a complex-linear map `P` between
complex-valued smooth functions, again complex-linear. This is the intrinsic star of linear maps
(`LinearMap.intrinsicStar`) for pointwise conjugation `ContMDiffMap.conj`, written out because the
function spaces carry no `Star` instance. Its fixed points are exactly the complexifications of
real-linear maps between real-valued functions (`ContMDiffMap.intrinsicConj_eq_self_iff`). -/
def intrinsicConj (P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun f := conj (P (conj f))
  map_add' f g := by simp
  map_smul' z f := by simp

@[simp]
theorem intrinsicConj_apply (P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    intrinsicConj P f = conj (P (conj f)) :=
  (rfl)

@[simp]
theorem intrinsicConj_intrinsicConj (P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    intrinsicConj (intrinsicConj P) = P := by
  ext f x
  simp

theorem intrinsicConj_injective :
    Function.Injective
      (intrinsicConj : (C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) → _) :=
  Function.LeftInverse.injective intrinsicConj_intrinsicConj

@[simp]
theorem intrinsicConj_add (P Q : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    intrinsicConj (P + Q) = intrinsicConj P + intrinsicConj Q := by
  ext f x
  simp

@[simp]
theorem intrinsicConj_sub (P Q : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    intrinsicConj (P - Q) = intrinsicConj P - intrinsicConj Q := by
  ext f x
  simp

@[simp]
theorem intrinsicConj_zero :
    intrinsicConj (0 : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) = 0 := by
  ext f x
  simp

@[simp]
theorem intrinsicConj_neg (P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    intrinsicConj (-P) = -intrinsicConj P := by
  ext f x
  simp

@[simp]
theorem intrinsicConj_id : intrinsicConj (LinearMap.id : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] _) =
    LinearMap.id := by
  ext f x
  simp

/-- Conjugation of linear maps is conjugate-linear. -/
@[simp]
theorem intrinsicConj_smul (z : ℂ) (P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    intrinsicConj (z • P) = star z • intrinsicConj P := by
  ext f x
  simp

/-- Conjugation of linear maps respects composition. -/
theorem intrinsicConj_comp {E'' H'' L : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace L]
    [ChartedSpace H'' L] (P : C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮K, L; 𝓘(ℝ, ℂ), ℂ⟯)
    (Q : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    intrinsicConj (P ∘ₗ Q) = intrinsicConj P ∘ₗ intrinsicConj Q := by
  ext f x
  simp

/-- The complexification of a real-linear map commutes with conjugation. -/
@[simp]
theorem intrinsicConj_complexifyLinearMap (D : C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮J, N; ℝ⟯) :
    intrinsicConj (complexifyLinearMap D) = complexifyLinearMap D :=
  linearMap_ext_ofReal fun u ↦ by simp

/-- **Real operators.** A complex-linear map between complex-valued smooth functions commutes with
conjugation exactly when it is the complexification of a real-linear map between real-valued
functions, namely of `u ↦ Re (P u)`. -/
theorem intrinsicConj_eq_self_iff {P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯} :
    intrinsicConj P = P ↔ ∃ D : C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮J, N; ℝ⟯, complexifyLinearMap D = P := by
  refine ⟨fun hP ↦ ⟨re ∘ₗ P.restrictScalars ℝ ∘ₗ ofReal.toLinearMap, ?_⟩, ?_⟩
  · refine linearMap_ext_ofReal fun u ↦ ?_
    -- `P` maps real functions to real functions, since it commutes with conjugation.
    have him : (P (ofReal u)).im = 0 := by
      have h := congrArg im (LinearMap.congr_fun hP (ofReal u))
      rw [intrinsicConj_apply, conj_ofReal, conj_im] at h
      ext x
      simpa using neg_eq_self.1 (congrFun (congrArg DFunLike.coe h) x)
    rw [complexifyLinearMap_ofReal, ← ofReal_re_add_I_smul_im (P (ofReal u)), him]
    simp
  · rintro ⟨D, rfl⟩
    exact intrinsicConj_complexifyLinearMap D

/-- **Real and imaginary parts of an operator.** Every complex-linear map `P` between
complex-valued smooth functions is `A + i B` for the complexifications of real-linear maps `A`
and `B` between real-valued functions, with `A = (P + Pᶜ) / 2` and `B = (P - Pᶜ) / (2 i)` for the
conjugate `Pᶜ = intrinsicConj P`. -/
theorem exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq
    (P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    ∃ A B : C^n⟮I, M; ℝ⟯ →ₗ[ℝ] C^n⟮J, N; ℝ⟯,
      complexifyLinearMap A = (2⁻¹ : ℂ) • (P + intrinsicConj P) ∧
      complexifyLinearMap B = (2 * Complex.I)⁻¹ • (P - intrinsicConj P) ∧
      complexifyLinearMap A + Complex.I • complexifyLinearMap B = P := by
  obtain ⟨A, hA⟩ := (intrinsicConj_eq_self_iff (P := (2⁻¹ : ℂ) • (P + intrinsicConj P))).1 (by
    rw [intrinsicConj_smul, intrinsicConj_add, intrinsicConj_intrinsicConj, add_comm]
    simp)
  have hstar : star (2 * Complex.I)⁻¹ = -(2 * Complex.I)⁻¹ := by
    rw [star_inv₀, star_mul', Complex.star_def, Complex.conj_I, map_ofNat, mul_neg, inv_neg]
  obtain ⟨B, hB⟩ := (intrinsicConj_eq_self_iff
    (P := (2 * Complex.I)⁻¹ • (P - intrinsicConj P))).1 (by
      rw [intrinsicConj_smul, intrinsicConj_sub, intrinsicConj_intrinsicConj, hstar]
      module)
  refine ⟨A, B, hA, hB, ?_⟩
  have hI : Complex.I * (2 * Complex.I)⁻¹ = 2⁻¹ := by
    field_simp
  rw [hA, hB, smul_smul, hI]
  module

/-- **Real and imaginary parts of an operator, explicitly.** Every complex-linear map `P` between
complex-valued smooth functions is `A + i B` for the complexifications of the real-linear maps
`A u = Re (P u)` and `B u = Im (P u)` on real-valued functions `u`. -/
theorem complexifyLinearMap_re_comp_add_I_smul_complexifyLinearMap_im_comp
    (P : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮J, N; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexifyLinearMap (re ∘ₗ P.restrictScalars ℝ ∘ₗ ofReal.toLinearMap) +
      Complex.I • complexifyLinearMap (im ∘ₗ P.restrictScalars ℝ ∘ₗ ofReal.toLinearMap) = P :=
  linearMap_ext_ofReal fun u ↦ by
    simpa [complexifyLinearMap_ofReal] using ofReal_re_add_I_smul_im (P (ofReal u))

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

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

section RealImaginaryParts

variable {m : ℕ} {Q : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- Reading a complex differential operator `Q` on real-valued functions and composing with a
real-linear map `σ` that intertwines multiplication by a real function `b` on complex and on real
functions gives a real differential operator of the same order: the inclusion of real functions
and `σ` intertwine the commutators with `b`. -/
private theorem comp_restrictScalars_comp_ofReal_mem_differentialOperators
    {σ : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hσ : ∀ (b : C^∞⟮I, M; ℝ⟯) y, σ (ContMDiffMap.ofReal b * y) = b * σ y)
    (hQ : Q ∈ differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m) :
    σ ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m :=
  comp_comp_mem_differentialOperators
    (fun b ↦ ⟨ContMDiffMap.ofReal b, fun x ↦ map_mul ContMDiffMap.ofReal b x, hσ b⟩)
    (restrictScalars_mem_differentialOperators hQ)

/-- **The real part of a complex differential operator.** If `Q` is a complex differential
operator of order at most `m` on the complex-valued smooth functions, for commutators with
complex-valued smooth functions, then `u ↦ Re (Q u)`, on real-valued functions `u`, is a real
differential operator of order at most `m`. -/
theorem re_comp_restrictScalars_comp_ofReal_mem_differentialOperators
    (hQ : Q ∈ differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m) :
    ContMDiffMap.re ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m :=
  comp_restrictScalars_comp_ofReal_mem_differentialOperators ContMDiffMap.re_ofReal_mul hQ

/-- **The imaginary part of a complex differential operator.** If `Q` is a complex differential
operator of order at most `m` on the complex-valued smooth functions, for commutators with
complex-valued smooth functions, then `u ↦ Im (Q u)`, on real-valued functions `u`, is a real
differential operator of order at most `m`. -/
theorem im_comp_restrictScalars_comp_ofReal_mem_differentialOperators
    (hQ : Q ∈ differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m) :
    ContMDiffMap.im ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m :=
  comp_restrictScalars_comp_ofReal_mem_differentialOperators ContMDiffMap.im_ofReal_mul hQ

end RealImaginaryParts

end TauCeti

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

/-- An operator is invariant under the pushforward along `Φ` exactly when it commutes with
precomposition by `Φ`: `P (u ∘ Φ) = (P u) ∘ Φ` for every `u`. -/
theorem pushforwardOperator_eq_self_iff (Φ : M ≃ₘ^n⟮I, I⟯ M)
    {P : Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    pushforwardOperator Φ P = P ↔
      ∀ u, P (compRightComplexAlgEquiv Φ u) = compRightComplexAlgEquiv Φ (P u) := by
  refine ⟨fun h u ↦ ContMDiffMap.ext fun x ↦ ?_, fun h ↦ LinearMap.ext fun u ↦
    ContMDiffMap.ext fun y ↦ ?_⟩
  · conv_rhs => rw [compRightComplexAlgEquiv_apply, ← h, pushforwardOperator_apply_apply,
      Φ.symm_apply_apply]
  · rw [pushforwardOperator_apply_apply, h, compRightComplexAlgEquiv_apply, Φ.apply_symm_apply]

end Diffeomorph
