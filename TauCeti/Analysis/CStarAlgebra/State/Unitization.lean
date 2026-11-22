/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# Extending positive functionals and states to the unitization

A positive functional `τ` on a possibly nonunital C⋆-algebra `A` extends to the minimal unitization
`A⁺¹ = Unitization ℂ A` in two complementary ways:

1. **Norm-preserving extension of positive functionals**
   (`PositiveContinuousLinearMap.unitization`): `τ⁺¹ (λ + a) = λ ‖τ‖ + τ a`. This is the unique
   positive extension with the same norm, so it is additive on positive functionals and preserves
   faithfulness when `A` has no unit. That the extension of a tracial state is again a tracial state
   is `PositiveContinuousLinearMap.isTracialState_unitization_iff`, in
   `TauCeti.Analysis.CStarAlgebra.State.Tracial`.
2. **Affine extension on the weak-* dual** (`WeakDual.unitizationFunctional`): sending `c + a` to
   `c + φ a` for any `φ : WeakDual ℂ A`. Conversely, restricting along the canonical embedding
   `Unitization.inrNonUnitalStarAlgHom ℂ A : A →⋆ₙₐ[ℂ] A⁺¹` via `TauCeti.pullbackFunctional`
   recovers `φ`. These two maps match `TauCeti.stateSpace A⁺¹` bijectively with the positive
   contractive functionals (quasistates)
   `{φ : WeakDual ℂ A | (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1}` of `A`. In particular,
   every state of `A` extends uniquely to a state of `A⁺¹`, and the restriction of a state of `A⁺¹`
   to `A` is a state of `A` whenever its restriction has norm one — for instance whenever it attains
   the norm of some nonzero element of `A`.

## Main declarations

* `PositiveContinuousLinearMap.unitization`: the extension `τ⁺¹ (λ + a) = λ ‖τ‖ + τ a`, a positive
  functional on `A⁺¹` (`PositiveContinuousLinearMap.unitization_apply`) restricting to `τ` on `A`
  (`PositiveContinuousLinearMap.unitization_apply_inr`).
* `PositiveContinuousLinearMap.norm_unitization`: `‖τ⁺¹‖ = ‖τ‖`, so `τ⁺¹` is a state exactly when
  `τ` is.
* `PositiveContinuousLinearMap.eq_unitization_iff`: a positive functional on `A⁺¹` equals `τ⁺¹`
  exactly when it restricts to `τ` on `A` and has the norm of `τ`. In particular every state of
  `A⁺¹` restricting to a state `τ` is `τ⁺¹`
  (`PositiveContinuousLinearMap.eq_unitization_of_mem_stateSpace`).
* `PositiveContinuousLinearMap.unitization_injective` and
  `PositiveContinuousLinearMap.unitization_add`: the extension is injective and additive;
  additivity rests on `PositiveContinuousLinearMap.opNorm_add`, `‖τ + σ‖ = ‖τ‖ + ‖σ‖`.
* `PositiveContinuousLinearMap.unitization_map_mul_comm`: if `τ (a * b) = τ (b * a)` on `A`, then
  the same holds for `τ⁺¹` on `A⁺¹`.
* `PositiveContinuousLinearMap.eq_zero_of_unitization_map_star_mul_self_eq_zero`: if `τ` is
  faithful, `τ (star a * a) = 0 → a = 0`, and `A` has no two-sided unit, then `τ⁺¹` is faithful
  too.
* `WeakDual.unitizationFunctional`: the weak-* continuous affine extension `WeakDual ℂ A →
  WeakDual ℂ A⁺¹` sending `x` to `x.fst + φ x.snd`.
* `TauCeti.unitizationFunctional_mem_stateSpace_iff`: `φ.unitizationFunctional` is a state of
  `A⁺¹` if and only if `φ` is nonnegative on nonnegative elements and has norm at most one.
* `TauCeti.bijOn_unitizationFunctional`: `WeakDual.unitizationFunctional` maps the positive
  contractive functionals of `A` bijectively onto `stateSpace A⁺¹`, with inverse given by
  restriction along `Unitization.inrNonUnitalStarAlgHom ℂ A`
  (`TauCeti.unitizationFunctional_pullbackFunctional_inr_of_map_one`).
* `TauCeti.existsUnique_mem_stateSpace_unitization`: every state of `A` extends uniquely to a
  state of `A⁺¹`.
* `TauCeti.pullbackFunctional_inr_mem_stateSpace_of_mem_stateSpace_of_norm_apply_eq_norm_of_ne_zero`
  restricts a state of `A⁺¹` attaining `‖a‖` on a nonzero `a : A` to a state of `A`.

## Implementation notes

The positivity of `τ⁺¹` is the inequality `0 ≤ |λ|² ‖τ‖ + 2 Re (star λ * τ a) + τ (a⋆a)` for the
value of `τ⁺¹` at `(λ + a)⋆ (λ + a)`, which follows from `|τ a|² ≤ ‖τ‖ τ (a⋆a)`
(`PositiveContinuousLinearMap.norm_map_sq_le_opNorm_mul`); every positive element of the
C⋆-algebra `A⁺¹` has the form `x⋆x`. Faithfulness passes to `τ⁺¹` because, for `x = λ + b` with
`τ⁺¹ (x⋆x) = 0`, the null space of `τ⁺¹` is a left ideal
(`TauCeti.map_star_mul_mul_self_eq_zero`), so `cx = λc + cb ∈ A` lies in the null space of `τ`
for every `c ∈ A` and vanishes. If `λ ≠ 0`, then `e = -λ⁻¹ b` is a right unit of `A`,
and a right unit of a star algebra is a two-sided unit (`TauCeti.exists_right_identity_iff`).
Without the hypothesis on units this fails: for `A = ℂ` and `τ = id`, `τ⁺¹` vanishes at `1 - 1_A`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Proposition 3.5.10.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math.
  185 (2017), Remark 1.5.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.3.9.
* B. Blackadar, *Operator Algebras*, Springer, 2006, II.6.2.5.
-/

public section

open scoped ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ σ : A →P[ℂ] ℂ}

/-- The value of `λ + a ↦ λ ‖τ‖ + τ a` at `x⋆x` is nonnegative. -/
private theorem unitization_aux_nonneg (τ : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    0 ≤ ‖(τ : A →L[ℂ] ℂ)‖ * (star x * x).fst + τ (star x * x).snd := by
  simp only [Unitization.fst_mul, Unitization.snd_mul, Unitization.fst_star, Unitization.snd_star,
    map_add, map_smul, map_star, smul_eq_mul]
  set r := x.fst
  set a := x.snd
  have hs : 0 ≤ τ (star a * a) := τ.map_nonneg (star_mul_self_nonneg a)
  have hts := τ.norm_map_sq_le_opNorm_mul a
  rw [Complex.nonneg_iff] at hs ⊢
  obtain ⟨hs_re, hs_im⟩ := hs
  rw [← Complex.re_eq_norm.mpr ⟨hs_re, hs_im⟩, Complex.sq_norm, Complex.normSq_apply] at hts
  set N := ‖(τ : A →L[ℂ] ℂ)‖
  have hN : 0 ≤ N := norm_nonneg _
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_im, Complex.mul_im]
  refine ⟨?_, by linarith⟩
  -- Cauchy–Schwarz in `ℝ²` for `r` and `τ a`, then `|τ a|² ≤ ‖τ‖ τ (a⋆a)`
  have hcs : (r.re * (τ a).re + r.im * (τ a).im) ^ 2 ≤
      (r.re * r.re + r.im * r.im) * (N * (τ (star a * a)).re) := by
    nlinarith [sq_nonneg (r.re * (τ a).im - r.im * (τ a).re), mul_self_nonneg r.re,
      mul_self_nonneg r.im]
  nlinarith [sq_nonneg (N * (r.re * r.re + r.im * r.im) - (τ (star a * a)).re),
    mul_nonneg hN (add_nonneg (mul_self_nonneg r.re) (mul_self_nonneg r.im))]

/-- The extension `τ⁺¹ (λ + a) = λ ‖τ‖ + τ a` of a positive functional `τ` on `A` to a positive
functional on the unitization `Unitization ℂ A`. It agrees with `τ` on `A` and has the same norm,
and it is the only positive functional on `Unitization ℂ A` with these two properties. -/
noncomputable def unitization (τ : A →P[ℂ] ℂ) : Unitization ℂ A →P[ℂ] ℂ :=
  .mk₀
    { toFun x := ‖(τ : A →L[ℂ] ℂ)‖ * x.fst + τ x.snd
      map_add' x y := by simp only [Unitization.fst_add, Unitization.snd_add, map_add]; ring
      map_smul' c x := by
        simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul, smul_eq_mul,
          RingHom.id_apply]
        ring
      cont := by fun_prop }
    fun x hx => by
      obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
      exact unitization_aux_nonneg τ y

/-- `τ⁺¹ (λ + a) = λ ‖τ‖ + τ a`. -/
theorem unitization_apply (τ : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    τ.unitization x = ‖(τ : A →L[ℂ] ℂ)‖ * x.fst + τ x.snd :=
  (rfl)

/-- The extension `τ⁺¹` agrees with `τ` on `A`. -/
@[simp]
theorem unitization_apply_inr (τ : A →P[ℂ] ℂ) (a : A) :
    τ.unitization (a : Unitization ℂ A) = τ a := by
  simp [unitization_apply]

/-- The extension `τ⁺¹` takes the value `λ ‖τ‖` at the scalar `λ`. -/
@[simp]
theorem unitization_apply_inl (τ : A →P[ℂ] ℂ) (c : ℂ) :
    τ.unitization (Unitization.inl c : Unitization ℂ A) = ‖(τ : A →L[ℂ] ℂ)‖ * c := by
  simp [unitization_apply]

/-- The extension `τ⁺¹` takes the value `‖τ‖` at the unit. -/
@[simp]
theorem unitization_apply_one (τ : A →P[ℂ] ℂ) :
    τ.unitization (1 : Unitization ℂ A) = ‖(τ : A →L[ℂ] ℂ)‖ := by
  simp [unitization_apply]

/-- Restricting `τ⁺¹` along `A → Unitization ℂ A` recovers `τ`. -/
@[simp]
theorem unitization_comp_inrNonUnitalStarAlgHom (τ : A →P[ℂ] ℂ) :
    τ.unitization.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)) = τ :=
  ext fun a => by simp

/-- The extension `τ⁺¹` has the same norm as `τ`. -/
@[simp]
theorem norm_unitization (τ : A →P[ℂ] ℂ) :
    ‖(τ.unitization : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ :=
  Complex.ofReal_injective <| by rw [ofReal_opNorm_eq_map_one, unitization_apply_one]

/-- **Uniqueness of the unitization extension.** A positive functional on `Unitization ℂ A` is
the extension `τ⁺¹` exactly when it agrees with `τ` on `A` and has the same norm as `τ`. -/
theorem eq_unitization_iff {ω : Unitization ℂ A →P[ℂ] ℂ} :
    ω = τ.unitization ↔
      (∀ a : A, ω a = τ a) ∧ ‖(ω : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ := by
  refine ⟨by rintro rfl; simp, fun ⟨h, hn⟩ => ext fun x => ?_⟩
  have h1 : ω 1 = ‖(τ : A →L[ℂ] ℂ)‖ := by rw [← ofReal_opNorm_eq_map_one, hn]
  have hinl : (Unitization.inl x.fst : Unitization ℂ A) = x.fst • 1 := by ext <;> simp
  rw [← Unitization.inl_fst_add_inr_snd_eq x, map_add, hinl, map_smul, h1, h]
  simp

/-- Every state of `Unitization ℂ A` that restricts to a state `τ` of `A` is the extension
`τ⁺¹`. -/
theorem eq_unitization_of_mem_stateSpace {ω : Unitization ℂ A →P[ℂ] ℂ}
    (hω : StrongDual.toWeakDual (ω : Unitization ℂ A →L[ℂ] ℂ) ∈
      TauCeti.stateSpace (Unitization ℂ A))
    (hτ : StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ TauCeti.stateSpace A)
    (h : ∀ a : A, ω a = τ a) : ω = τ.unitization := by
  rw [toWeakDual_mem_stateSpace_iff] at hω hτ
  exact eq_unitization_iff.mpr ⟨h, hω.trans hτ.symm⟩

/-- The extension to the unitization is injective. -/
theorem unitization_injective :
    Function.Injective (unitization : (A →P[ℂ] ℂ) → Unitization ℂ A →P[ℂ] ℂ) :=
  fun τ σ h => by
    rw [← unitization_comp_inrNonUnitalStarAlgHom τ, h, unitization_comp_inrNonUnitalStarAlgHom]

/-- Two positive functionals have the same extension to the unitization exactly when they are
equal. -/
@[simp]
theorem unitization_inj : τ.unitization = σ.unitization ↔ τ = σ :=
  unitization_injective.eq_iff

/-- The extension of the zero functional is zero. -/
@[simp]
theorem unitization_zero : (0 : A →P[ℂ] ℂ).unitization = 0 :=
  ext fun x => by simp [unitization_apply]

/-- The extension to the unitization is additive. -/
@[simp]
theorem unitization_add (τ σ : A →P[ℂ] ℂ) :
    (τ + σ).unitization = τ.unitization + σ.unitization :=
  ext fun x => by
    simp only [add_apply, unitization_apply, opNorm_add]
    push_cast
    ring

/-- If `τ (a * b) = τ (b * a)` for all `a, b ∈ A`, the extension `τ⁺¹` has the same property on
`Unitization ℂ A`. -/
theorem unitization_map_mul_comm (h : ∀ a b : A, τ (a * b) = τ (b * a))
    (x y : Unitization ℂ A) : τ.unitization (x * y) = τ.unitization (y * x) := by
  simp only [unitization_apply, Unitization.fst_mul, Unitization.snd_mul, map_add, map_smul,
    smul_eq_mul, h x.snd y.snd]
  ring

/-- **Faithfulness of the unitization extension.** Let `τ` be a positive functional on a
C⋆-algebra `A` without a two-sided unit, faithful in the sense that `τ (star a * a) = 0` only for
`a = 0`. Then the extension `τ⁺¹` to `Unitization ℂ A` is faithful too. -/
theorem eq_zero_of_unitization_map_star_mul_self_eq_zero
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) (hA : ¬∃ e : A, ∀ a : A, e * a = a ∧ a * e = a)
    {x : Unitization ℂ A} (hx : τ.unitization (star x * x) = 0) : x = 0 := by
  -- for `c ∈ A`, `c x = λ c + c b` lies in `A` and in the null space of `τ⁺¹`, hence vanishes
  have hl : ∀ c : A, x.fst • c + c * x.snd = 0 := fun c => by
    refine hf _ ?_
    have h := TauCeti.map_star_mul_mul_self_eq_zero τ.unitization (c : Unitization ℂ A) hx
    have hcx : (c : Unitization ℂ A) * x = ((x.fst • c + c * x.snd : A) : Unitization ℂ A) :=
      Unitization.ext (by simp) (by simp [add_comm])
    rwa [hcx, ← Unitization.inr_star, ← Unitization.inr_mul, unitization_apply_inr] at h
  obtain h0 | h0 := eq_or_ne x.fst 0
  · have hsnd : x.snd = 0 := hf _ <| by
      simpa [unitization_apply, h0] using hx
    exact Unitization.ext h0 hsnd
  · -- `e = -λ⁻¹ b` is a right unit of `A`, hence a two-sided unit
    refine (hA (TauCeti.exists_right_identity_iff.mp ⟨-(x.fst⁻¹ • x.snd), fun c => ?_⟩)).elim
    have hc : c * x.snd = -(x.fst • c) := eq_neg_of_add_eq_zero_right (hl c)
    simp [mul_smul_comm, hc, h0]

end PositiveContinuousLinearMap

section WeakDualUnitization

open Set WeakDual
open scoped CStarAlgebra

namespace WeakDual

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Extend a functional `φ` in the weak-* dual of `A` to the minimal unitization `A⁺¹` by sending
`x` to `x.fst + φ x.snd`. -/
noncomputable def unitizationFunctional (φ : WeakDual ℂ A) : WeakDual ℂ A⁺¹ :=
  StrongDual.toWeakDual
    { toLinearMap := (Unitization.fstHom ℂ A).toLinearMap +
        (toStrongDual φ : A →ₗ[ℂ] ℂ).comp (Unitization.sndHom ℂ ℂ A)
      cont := Unitization.continuous_fst.add
        ((toStrongDual φ).continuous.comp Unitization.continuous_snd) }

/-- `φ.unitizationFunctional` evaluates at `x : A⁺¹` as `x.fst + φ x.snd`. -/
@[simp]
theorem unitizationFunctional_apply (φ : WeakDual ℂ A) (x : A⁺¹) :
    φ.unitizationFunctional x = x.fst + φ x.snd :=
  (rfl)

/-- `φ.unitizationFunctional` takes the value `1` at the unit of `A⁺¹`. -/
theorem unitizationFunctional_one (φ : WeakDual ℂ A) : φ.unitizationFunctional 1 = 1 := by
  simp

/-- `φ.unitizationFunctional` restricts to `φ` on `A ↪ A⁺¹`. -/
theorem unitizationFunctional_inr (φ : WeakDual ℂ A) (a : A) :
    φ.unitizationFunctional (a : A⁺¹) = φ a := by
  simp

/-- `φ.unitizationFunctional` acts as the identity on scalars `Unitization.inl c`. -/
theorem unitizationFunctional_inl (φ : WeakDual ℂ A) (c : ℂ) :
    φ.unitizationFunctional (Unitization.inl c) = c := by
  simp

/-- `WeakDual.unitizationFunctional` is weak-* continuous. -/
@[fun_prop]
theorem continuous_unitizationFunctional :
    Continuous (unitizationFunctional : WeakDual ℂ A → WeakDual ℂ A⁺¹) :=
  continuous_of_continuous_eval fun x => continuous_const.add (eval_continuous x.snd)

/-- `WeakDual.unitizationFunctional` preserves affine combinations. -/
theorem unitizationFunctional_combo (φ ψ : WeakDual ℂ A) {s t : ℝ} (hst : s + t = 1) :
    (s • φ + t • ψ).unitizationFunctional =
      s • φ.unitizationFunctional + t • ψ.unitizationFunctional :=
  DFunLike.ext _ _ fun x => by
    simp only [unitizationFunctional_apply, add_apply, WeakDual.real_smul_apply]
    have hst' : (s : ℂ) + t = 1 := by exact_mod_cast hst
    linear_combination -x.fst * hst'

/-- `WeakDual.unitizationFunctional` is injective. -/
theorem unitizationFunctional_injective :
    Function.Injective (unitizationFunctional : WeakDual ℂ A → WeakDual ℂ A⁺¹) := fun φ ψ h =>
  DFunLike.ext _ _ fun a => by simpa using congr($h (a : A⁺¹))

/-- Two functionals have the same unitization extension if and only if they are equal. -/
@[simp]
theorem unitizationFunctional_inj {φ ψ : WeakDual ℂ A} :
    φ.unitizationFunctional = ψ.unitizationFunctional ↔ φ = ψ :=
  unitizationFunctional_injective.eq_iff

end WeakDual

namespace TauCeti

section Order

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

/-- Restricting `φ.unitizationFunctional` along `inr` recovers `φ`. -/
@[simp]
theorem pullbackFunctional_inr_unitizationFunctional {φ : WeakDual ℂ A} :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) φ.unitizationFunctional = φ :=
  DFunLike.ext _ _ fun a => by simp

/-- Any functional `ψ` on `A⁺¹` normalized by `ψ 1 = 1` is the unitization extension of its
restriction to `A`. -/
theorem unitizationFunctional_pullbackFunctional_inr_of_map_one {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ 1 = 1) :
    (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ).unitizationFunctional = ψ :=
  DFunLike.ext _ _ fun x => by
    conv_rhs => rw [← Unitization.inl_fst_add_inr_snd_eq x, ← Unitization.algebraMap_eq_inl,
      Algebra.algebraMap_eq_smul_one]
    simp [map_add, map_smul, hψ]

/-- Key square-positivity step: for a positive contractive functional `φ` on `A`, its unitization
extension is nonnegative on every element of the form `star s * s` in `A⁺¹`. -/
private theorem unitizationFunctional_star_mul_self_nonneg
    (hpos : ∀ a, 0 ≤ a → 0 ≤ φ a) (hnorm : ‖toStrongDual φ‖ ≤ 1) (s : A⁺¹) :
    0 ≤ φ.unitizationFunctional (star s * s) := by
  set c : ℂ := s.fst
  set a : A := s.snd
  set r : ℝ := ‖φ (star a * a)‖
  have hw_eq : φ (star a * a) = (r : ℂ) :=
    (Complex.norm_of_nonneg' (hpos _ (star_mul_self_nonneg a))).symm
  have hcs : ‖φ a‖ ^ 2 ≤ r :=
    (WeakDual.norm_apply_sq_le_mul_of_map_nonneg hpos a).trans
      (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have hstar : φ (star a) = star (φ a) := WeakDual.map_star_of_map_nonneg hpos a
  -- Complete the square:
  -- `‖c‖² + star c * φ a + c * star (φ a) + φ (a⋆ * a) = ‖c + φ a‖² + (φ (a⋆ * a) - ‖φ a‖²)`.
  have hid : φ.unitizationFunctional (star s * s) =
      ((‖c + φ a‖ ^ 2 + (r - ‖φ a‖ ^ 2) : ℝ) : ℂ) := by
    simp only [unitizationFunctional_apply, Unitization.fst_mul, Unitization.fst_star,
      Unitization.snd_mul, Unitization.snd_star, map_add, map_smul, smul_eq_mul]
    rw [hstar, hw_eq]
    have hnorm_sq (z : ℂ) : (‖z‖ : ℂ) ^ 2 = star z * z := (Complex.conj_mul' z).symm
    push_cast
    rw [hnorm_sq (c + φ a), hnorm_sq (φ a)]
    simp only [star_add]
    ring
  rw [hid]
  exact Complex.zero_le_real.2 (by linarith [sq_nonneg ‖c + φ a‖])

/-- **Characterization of unitized states.** The unitization extension `φ.unitizationFunctional`
is a state of `A⁺¹` if and only if `φ` is nonnegative on nonnegative elements of `A` and has
operator norm at most `1`. -/
theorem unitizationFunctional_mem_stateSpace_iff :
    φ.unitizationFunctional ∈ stateSpace A⁺¹ ↔
      (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1 := by
  rw [mem_stateSpace_iff_map_one]
  refine ⟨fun ⟨hpos, _⟩ => ⟨fun a ha => ?_, ?_⟩, fun ⟨hpos, hnorm⟩ => ⟨fun x hx => ?_, by simp⟩⟩
  · simpa using hpos (a : A⁺¹) ((Unitization.inr_nonneg_iff ℂ).2 ha)
  · refine (toStrongDual φ).opNorm_le_bound zero_le_one fun a => ?_
    have hψ : φ.unitizationFunctional ∈ stateSpace A⁺¹ :=
      mem_stateSpace_iff_map_one.2 ⟨hpos, by simp⟩
    simpa [Unitization.norm_inr] using norm_apply_le_of_mem_stateSpace hψ (a : A⁺¹)
  · rw [StarOrderedRing.nonneg_iff] at hx
    refine AddSubmonoid.closure_induction ?_ (by simp)
      (fun u v _ _ hu hv => by simpa [map_add] using add_nonneg hu hv) hx
    rintro _ ⟨s, rfl⟩
    exact unitizationFunctional_star_mul_self_nonneg hpos hnorm s

/-- Every state of `A` extends via `WeakDual.unitizationFunctional` to a state of `A⁺¹`. -/
theorem unitizationFunctional_mem_stateSpace_of_mem_stateSpace (hφ : φ ∈ stateSpace A) :
    φ.unitizationFunctional ∈ stateSpace A⁺¹ :=
  unitizationFunctional_mem_stateSpace_iff.2
    ⟨fun _ => map_nonneg_of_mem_stateSpace hφ, (norm_toStrongDual_of_mem_stateSpace hφ).le⟩

/-- Every state `φ : stateSpace A` extends via `WeakDual.unitizationFunctional` to a state of
`A⁺¹`. -/
@[simp]
theorem StateSpace.unitizationFunctional_mem_stateSpace (φ : stateSpace A) :
    φ.val.unitizationFunctional ∈ stateSpace A⁺¹ :=
  unitizationFunctional_mem_stateSpace_of_mem_stateSpace φ.property

/-- The zero functional on `A` extends via `WeakDual.unitizationFunctional` to the character
`x ↦ x.fst`, which is a state of `A⁺¹`. -/
@[simp]
theorem unitizationFunctional_zero_mem_stateSpace :
    (0 : WeakDual ℂ A).unitizationFunctional ∈ stateSpace A⁺¹ :=
  unitizationFunctional_mem_stateSpace_iff.2
    ⟨fun _ _ => by simp [← toStrongDual_apply], by simp⟩

private theorem pullbackFunctional_inr_pos_and_norm_le_one {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) :
    (∀ a, 0 ≤ a → 0 ≤ pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ a) ∧
      ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ ≤ 1 :=
  unitizationFunctional_mem_stateSpace_iff.1 <|
    (unitizationFunctional_pullbackFunctional_inr_of_map_one
      (map_one_of_mem_stateSpace hψ)).symm ▸ hψ

/-- `WeakDual.unitizationFunctional` maps the positive contractive functionals of `A` bijectively
onto the state space of `A⁺¹`. -/
theorem bijOn_unitizationFunctional :
    BijOn (unitizationFunctional (A := A))
      {φ : WeakDual ℂ A | (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1}
      (stateSpace A⁺¹) := by
  refine ⟨fun φ hφ => unitizationFunctional_mem_stateSpace_iff.2 hφ,
    unitizationFunctional_injective.injOn, fun ψ hψ => ?_⟩
  exact ⟨pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ,
    pullbackFunctional_inr_pos_and_norm_le_one hψ,
    unitizationFunctional_pullbackFunctional_inr_of_map_one (map_one_of_mem_stateSpace hψ)⟩

/-- States of `A⁺¹` are determined by their restrictions to `A`. -/
theorem injOn_pullbackFunctional_inr_stateSpace :
    InjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A)) (stateSpace A⁺¹) := by
  intro ψ₁ hψ₁ ψ₂ hψ₂ h
  rw [← unitizationFunctional_pullbackFunctional_inr_of_map_one (map_one_of_mem_stateSpace hψ₁),
    ← unitizationFunctional_pullbackFunctional_inr_of_map_one (map_one_of_mem_stateSpace hψ₂), h]

/-- **Unique extension of states to the unitization.** Every state of `A` extends to a unique state
of `A⁺¹`. -/
theorem existsUnique_mem_stateSpace_unitization (hφ : φ ∈ stateSpace A) :
    ∃! ψ : WeakDual ℂ A⁺¹, ψ ∈ stateSpace A⁺¹ ∧ ∀ a : A, ψ a = φ a := by
  refine ⟨φ.unitizationFunctional,
    ⟨unitizationFunctional_mem_stateSpace_of_mem_stateSpace hφ, fun a => by simp⟩, ?_⟩
  rintro ψ ⟨hψ, hψφ⟩
  rw [← unitizationFunctional_pullbackFunctional_inr_of_map_one (map_one_of_mem_stateSpace hψ)]
  congr 1
  exact DFunLike.ext _ _ fun a => by simpa using hψφ a

/-- Restricting a state of `A⁺¹` along `inr` produces a functional that is nonnegative on
nonnegative elements of `A`. -/
theorem map_nonneg_pullbackFunctional_inr_of_mem_stateSpace {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) {a : A} (ha : 0 ≤ a) :
    0 ≤ pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ a := by
  simpa using map_nonneg_of_mem_stateSpace hψ ((Unitization.inr_nonneg_iff ℂ).2 ha)

/-- Restricting a state of `A⁺¹` along `inr` produces a contractive functional on `A`. -/
theorem norm_toStrongDual_pullbackFunctional_inr_le_one_of_mem_stateSpace {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) :
    ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ ≤ 1 :=
  (pullbackFunctional_inr_pos_and_norm_le_one hψ).2

/-- The restriction of a state of `A⁺¹` to `A` is a state of `A` if and only if its norm on `A` is
one. -/
theorem pullbackFunctional_inr_mem_stateSpace_iff_of_mem_stateSpace {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A ↔
      ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ = 1 :=
  ⟨norm_toStrongDual_of_mem_stateSpace, fun hnorm =>
    mem_stateSpace_iff.2 ⟨fun _ => map_nonneg_pullbackFunctional_inr_of_mem_stateSpace hψ, hnorm⟩⟩

/-- **Restriction of norm-attaining unitized states.** If a state `ψ` of `A⁺¹` attains the norm of
some nonzero element `a : A` (`‖ψ a‖ = ‖a‖`), then its restriction to `A` is a state of `A`. -/
theorem pullbackFunctional_inr_mem_stateSpace_of_mem_stateSpace_of_norm_apply_eq_norm_of_ne_zero
    {ψ : WeakDual ℂ A⁺¹} (hψ : ψ ∈ stateSpace A⁺¹) {a : A} (ha : a ≠ 0)
    (hnorm : ‖ψ (a : A⁺¹)‖ = ‖a‖) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A := by
  rw [pullbackFunctional_inr_mem_stateSpace_iff_of_mem_stateSpace hψ]
  set φ := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  refine le_antisymm (norm_toStrongDual_pullbackFunctional_inr_le_one_of_mem_stateSpace hψ) ?_
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hle : ‖a‖ ≤ ‖toStrongDual φ‖ * ‖a‖ := by
    simpa [φ, hnorm] using (toStrongDual φ).le_opNorm a
  exact (le_mul_iff_one_le_left ha_pos).1 hle

end Order

end TauCeti

end WeakDualUnitization
