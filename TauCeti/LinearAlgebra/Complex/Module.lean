/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Tactic.FastInstance
import Mathlib.Tactic.Module

/-!
# Real-linear evaluation and scalar multiplication on the complex plane

A real-linear map out of the complex plane is determined by its values at `1` and `I`.
In particular, a complex scalar action decomposes into its real and imaginary parts.
This decomposition applies to any real module structure compatible with the complex action.

For a real-linear map `L` into a complex module, its defect from complex linearity
`e ↦ L e + I • L (I * e)` is conjugate-linear and is therefore determined by its value at `1`.
A real-linear map is unchanged by conjugating its argument exactly when it vanishes at `I`
(`LinearMap.forall_apply_conj_eq_iff`). A real-linear map with `L I = A (L 1)`, for `A`
squaring to `-1`, satisfies `L (b * I) = A (L b)` for every `b`
(`LinearMap.apply_mul_I_eq_of_apply_I_eq`), and a real-linear map intertwines multiplication by
`I` with such an `A` exactly when `L 1 + A (L I) = 0` (`LinearMap.forall_apply_I_mul_eq_iff`).
A real-bilinear map is unchanged by conjugating both arguments exactly when it vanishes at
`(1, I)` and `(I, 1)` (`LinearMap.forall_apply_conj_apply_conj_eq_iff`).
Multiplication by `I` and by `-I` are mutually inverse on any complex multiplication action.
Multiplication by `I` squares to `-1` as a real-linear endomorphism of a complex module
(`Complex.toLinearMap_I_comp_toLinearMap_I`).

A real-linear map between complex modules that commutes with multiplication by `I` is complex
linear (`LinearMap.complexOfMapISmul`), and one that anticommutes with it is conjugate-linear
(`LinearMap.map_smul_eq_conj_smul_of_map_I_smul`). The non-instance
`RestrictScalars.realModule` normalizes the restricted real module at the additive-group parent
for use in constructions on real modules.

Likewise an `ℝ`-algebra map out of the complex plane is determined by its value at `I`, so a
conjugacy `g z = w * f z * w⁻¹` by a unit `w` between two such maps holds everywhere once it holds
at `I` (`Units.conj_complexAlgHom_apply`).

The real part `ℜ a = (a + a*) / 2` of an element of a complex star module is `a` corrected by
half its skew difference `a* - a` (`TauCeti.realPart_eq_add_half_star_sub`).

A vector lies in the real span of a complex basis exactly when its coordinates are real
(`Module.Basis.mem_span_real_range_iff`). In particular, the real span of the standard basis of
`ι → ℂ` is `ℝ^ι`, the vectors with real entries (`TauCeti.mem_span_real_range_basisFun_iff`).
-/

public section

/-- The restricted real module indexed by the inherited additive-group parent.
This normalizes the inherited additive-monoid instance of the scalar-restriction type alias. -/
@[expose, instance_reducible]
noncomputable def RestrictScalars.realModule (M : Type*) [AddCommGroup M] [Module ℂ M] :
    @Module ℝ (RestrictScalars ℝ ℂ M) Real.semiring
      (instAddCommGroupRestrictScalars ℝ ℂ M).toAddCommMonoid :=
  fast_instance% RestrictScalars.module ℝ ℂ M


namespace LinearMap

/-- A real-linear map out of the complex plane is evaluated in the real basis `(1,I)`. -/
theorem apply_eq_re_smul_one_add_im_smul_I {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (L : ℂ →ₗ[ℝ] F) (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I := by
  -- Fold the right side into `L` of the real-basis expansion `z.re • 1 + z.im • I = z`.
  rw [← map_smul, ← map_smul, ← map_add]
  simp

end LinearMap

namespace Complex

/-- Multiplication by `-I` undoes multiplication by `I`. -/
theorem I_smul_neg_I_smul {X : Type*} [MulAction ℂ X] (x : X) : I • (-I • x) = x := by
  rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

/-- Multiplication by `I` undoes multiplication by `-I`. -/
theorem neg_I_smul_I_smul {X : Type*} [MulAction ℂ X] (x : X) : -I • (I • x) = x := by
  rw [smul_smul, neg_mul, I_mul_I, neg_neg, one_smul]

/-- Multiplication by `I` squares to `-1` as a real-linear endomorphism of a complex module. -/
theorem toLinearMap_I_comp_toLinearMap_I {W : Type*} [AddCommGroup W] [Module ℂ W] [Module ℝ W]
    [IsScalarTower ℝ ℂ W] :
    DistribSMul.toLinearMap ℝ W I ∘ₗ DistribSMul.toLinearMap ℝ W I = -LinearMap.id :=
  LinearMap.ext fun v ↦ by simp [smul_smul]

/-- Decompose a complex scalar action into its real and imaginary parts. -/
@[simp]
lemma re_smul_add_im_smul {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
    [IsScalarTower ℝ ℂ V] (z : ℂ) (v : V) :
    z.re • v + z.im • (I • v) = z • v := by
  simpa only [LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, one_smul]
    using (LinearMap.apply_eq_re_smul_one_add_im_smul_I
      ((LinearMap.toSpanSingleton ℂ V v).restrictScalars ℝ) z).symm

end Complex

namespace Module.Basis

/-- A vector lies in the real span of a complex basis exactly when its coordinates are real. -/
theorem mem_span_real_range_iff {ι M : Type*} [AddCommGroup M] [Module ℝ M] [Module ℂ M]
    [IsScalarTower ℝ ℂ M] (b : Basis ι ℂ M) (m : M) :
    m ∈ Submodule.span ℝ (Set.range b) ↔ ∀ i, (b.repr m i).im = 0 := by
  rw [b.mem_span_iff_repr_mem ℝ]
  refine forall_congr' fun i ↦ ⟨?_, fun h ↦ ⟨(b.repr m i).re, Complex.ext (by simp) (by simp [h])⟩⟩
  rintro ⟨r, hr⟩
  simp [← hr]

end Module.Basis

namespace LinearMap

open Complex ComplexConjugate

/-- Rotating `L 1 + I • L I` by the conjugate of `e` gives the derivative of `L` along `e` plus
`I` times its derivative along `I * e`: the map `e ↦ L e + I • L (I * e)` is conjugate-linear. For
`L` the derivative of a map `u` at `w + r e^{iθ}` and `e = e^{iθ}`, these are the radial derivative
and `r⁻¹` times the angular derivative of `(r, θ) ↦ u (w + r e^{iθ})`. -/
theorem conj_smul_apply_one_add_I_smul_apply_I {F : Type*} [AddCommGroup F] [Module ℝ F]
    [Module ℂ F] [IsScalarTower ℝ ℂ F] (L : ℂ →ₗ[ℝ] F) (e : ℂ) :
    conj e • (L 1 + I • L I) = L e + I • L (I * e) := by
  rw [L.apply_eq_re_smul_one_add_im_smul_I e, L.apply_eq_re_smul_one_add_im_smul_I (I * e),
    ← re_smul_add_im_smul (conj e)]
  simp only [mul_re, I_re, I_im, mul_im, conj_re, conj_im, smul_add, smul_smul, I_mul_I]
  module

/-- A real-linear map out of the complex plane is unchanged by conjugating its argument exactly
when it vanishes at `I`. -/
theorem forall_apply_conj_eq_iff {F : Type*} [AddCommGroup F] [Module ℝ F] (L : ℂ →ₗ[ℝ] F) :
    (∀ z, L (conj z) = L z) ↔ L I = 0 := by
  refine ⟨fun h ↦ ?_, fun hL z ↦ ?_⟩
  · -- `L (conj I) = -L I`, so `L I` equals its own negative.
    simpa [neg_eq_iff_add_eq_zero, ← two_smul ℝ] using h I
  · rw [L.apply_eq_re_smul_one_add_im_smul_I (conj z), L.apply_eq_re_smul_one_add_im_smul_I z, hL]
    simp

/-- If a real-linear map out of the complex plane sends `I` to `A (L 1)`, where `A` squares to
`-1`, then so does its precomposition with multiplication by any `b`: `L (b * I) = A (L b)`. -/
theorem apply_mul_I_eq_of_apply_I_eq {F : Type*} [AddCommGroup F] [Module ℝ F]
    (L : ℂ →ₗ[ℝ] F) {A : F →ₗ[ℝ] F} (hL : L I = A (L 1)) (hA : ∀ v, A (A v) = -v) (b : ℂ) :
    L (b * I) = A (L b) := by
  rw [L.apply_eq_re_smul_one_add_im_smul_I, L.apply_eq_re_smul_one_add_im_smul_I b, hL]
  simp [hA]
  module

/-- A real-linear map `L` out of the complex plane intertwines multiplication by `I` with an
endomorphism `A` squaring to `-1` exactly when `L 1 + A (L I) = 0`: the value at `I` is then
determined by the value at `1`. -/
theorem forall_apply_I_mul_eq_iff {F : Type*} [AddCommGroup F] [Module ℝ F]
    (L : ℂ →ₗ[ℝ] F) {A : F →ₗ[ℝ] F} (hA : ∀ v, A (A v) = -v) :
    (∀ w, L (I * w) = A (L w)) ↔ L 1 + A (L I) = 0 := by
  refine ⟨fun h => ?_, fun h w => ?_⟩
  · rw [← mul_one I, h 1, hA, add_neg_cancel]
  · have hI : L I = A (L 1) := by rw [eq_neg_of_add_eq_zero_left h, map_neg, hA, neg_neg]
    rw [mul_comm]
    exact L.apply_mul_I_eq_of_apply_I_eq hI hA w

/-- A real-bilinear map on the complex plane is unchanged by conjugating both arguments exactly
when `B 1 I = B I 1 = 0`. -/
theorem forall_apply_conj_apply_conj_eq_iff {F : Type*} [AddCommGroup F] [Module ℝ F]
    (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] F) :
    (∀ v e, B (conj v) (conj e) = B v e) ↔ B 1 I = 0 ∧ B I 1 = 0 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ v e ↦ ?_⟩
  -- Conjugation negates `I` and fixes `1`, so `B 1 I` and `B I 1` equal their own negatives.
  · simpa [neg_eq_iff_add_eq_zero, ← two_smul ℝ] using h 1 I
  · simpa [neg_eq_iff_add_eq_zero, ← two_smul ℝ] using h I 1
  -- Expand both arguments in the real basis `(1, I)`; the mixed terms are the ones that vanish.
  · simp [B.apply_eq_re_smul_one_add_im_smul_I (conj v), B.apply_eq_re_smul_one_add_im_smul_I v,
      (B 1).apply_eq_re_smul_one_add_im_smul_I (conj e), (B 1).apply_eq_re_smul_one_add_im_smul_I e,
      (B I).apply_eq_re_smul_one_add_im_smul_I (conj e), (B I).apply_eq_re_smul_one_add_im_smul_I e,
      h₁, h₂]

end LinearMap

namespace TauCeti

open scoped ComplexStarModule in
/-- The real part `(a + a*) / 2` is `a` plus half the skew difference `a* - a`. -/
theorem realPart_eq_add_half_star_sub {A : Type*} [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] (a : A) :
    (ℜ a : A) = a + (2 : ℝ)⁻¹ • (star a - a) := by
  rw [realPart_apply_coe]
  module

/-- The real span of the standard basis of `ι → ℂ` is `ℝ^ι`, the vectors with real entries. -/
theorem mem_span_real_range_basisFun_iff {ι : Type*} [Finite ι] (w : ι → ℂ) :
    w ∈ Submodule.span ℝ (Set.range (Pi.basisFun ℂ ι)) ↔ ∀ i, (w i).im = 0 := by
  simp [(Pi.basisFun ℂ ι).mem_span_real_range_iff]

end TauCeti

section ComplexOfMapISmul

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]

namespace LinearMap

/-- A real-linear map between complex modules that commutes with multiplication by `I`, as a
complex-linear map. -/
def complexOfMapISmul (u : V →ₗ[ℝ] W) (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    V →ₗ[ℂ] W where
  toFun := u
  map_add' := u.map_add
  map_smul' c v := by
    -- Split `c • v` into real multiples of `v` and `I • v`.
    rw [← Complex.re_smul_add_im_smul c v, map_add, map_smul, map_smul, h, RingHom.id_apply,
      Complex.re_smul_add_im_smul]

@[simp]
theorem coe_complexOfMapISmul (u : V →ₗ[ℝ] W) (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    ⇑(u.complexOfMapISmul h) = u :=
  funext fun _ ↦ rfl

@[simp]
theorem restrictScalars_complexOfMapISmul (u : V →ₗ[ℝ] W)
    (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    (u.complexOfMapISmul h).restrictScalars ℝ = u :=
  LinearMap.ext fun _ ↦ rfl

/-- A real-linear map between complex modules that anticommutes with multiplication by `I` is
conjugate-linear: `u (z • v) = conj z • u v`. -/
theorem map_smul_eq_conj_smul_of_map_I_smul (u : V →ₗ[ℝ] W)
    (h : ∀ v, u (Complex.I • v) = -(Complex.I • u v)) (z : ℂ) (v : V) :
    u (z • v) = starRingEnd ℂ z • u v := by
  conv_rhs => rw [← Complex.re_smul_add_im_smul]
  rw [← Complex.re_smul_add_im_smul z v, map_add, map_smul, map_smul, h, Complex.conj_re,
    Complex.conj_im, smul_neg, neg_smul]

end LinearMap

end ComplexOfMapISmul

namespace Units

/-- **Conjugation of an `ℝ`-algebra map out of `ℂ` is detected on `Complex.I`.** If `g` agrees with
the `w`-conjugate of `f` at `i` then it agrees with it everywhere: conjugation by `w` is an
`ℝ`-algebra automorphism, and `ℝ`-algebra maps out of `ℂ` are determined by their value at `i`. -/
theorem conj_complexAlgHom_apply {A : Type*} [Semiring A] [Algebra ℝ A] (w : Aˣ)
    (f g : ℂ →ₐ[ℝ] A) (h : g Complex.I = (w : A) * f Complex.I * ((w⁻¹ : Aˣ) : A)) (z : ℂ) :
    g z = (w : A) * f z * ((w⁻¹ : Aˣ) : A) := by
  have hfg : g = (MulSemiringAction.toAlgHom ℝ A (ConjAct.toConjAct w)).comp f :=
    Complex.algHom_ext (by simpa [ConjAct.units_smul_def] using h)
  simpa [ConjAct.units_smul_def] using DFunLike.congr_fun hfg z

end Units
