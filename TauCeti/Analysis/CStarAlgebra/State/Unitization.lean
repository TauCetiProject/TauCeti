/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import Mathlib.Analysis.CStarAlgebra.Unitization
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.Analysis.Real.Sqrt
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Extending positive functionals to the unitization

A positive functional `τ` on a possibly nonunital C⋆-algebra `A` extends to the unitization
`A⁺¹ = Unitization ℂ A` by `τ⁺¹ (λ + a) = λ ‖τ‖ + τ a`. This is the unique positive extension with
the same norm, so statements about states of unital C⋆-algebras pass to nonunital ones along
it. The extension of a faithful positive functional is faithful when `A` has no unit. That the
extension of a tracial state is again a tracial state is
`PositiveContinuousLinearMap.isTracialState_unitization_iff`, in
`TauCeti.Analysis.CStarAlgebra.State.Tracial`.

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
* `PositiveContinuousLinearMap.norm_apply_sub_apply_mul_sq_le`: **the approximate unit
  estimate**: for a positive functional `γ` and a positive contraction `e`,
  `‖γ y - γ (y e)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²`, from the Cauchy–Schwarz inequality for `γ⁺¹`,
  with the left variant `norm_apply_sub_apply_mul_left_sq_le`, the unsquared forms
  `norm_apply_sub_apply_mul_le` and `norm_apply_sub_apply_mul_left_le`, and the two-sided
  variant `norm_apply_sub_apply_mul_mul_le`.
* `TauCeti.surjOn_pullbackFunctional_inr_stateSpace`: every state of `A` is the restriction of a
  state of `A⁺¹`.

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

The approximate unit estimate is the Cauchy–Schwarz inequality for `γ⁺¹` applied to `y` and
`1 - e`, with `(1 - e)² ≤ 1 - e` for a positive contraction `e`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Proposition 3.5.10.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math.
  185 (2017), Remark 1.5.
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
    rwa [Unitization.inr_mul_eq_inr c x, ← Unitization.inr_star, ← Unitization.inr_mul,
      unitization_apply_inr] at h
  obtain h0 | h0 := eq_or_ne x.fst 0
  · have hsnd : x.snd = 0 := hf _ <| by
      simpa [unitization_apply, h0] using hx
    exact Unitization.ext h0 hsnd
  · -- `e = -λ⁻¹ b` is a right unit of `A`, hence a two-sided unit
    refine (hA (TauCeti.exists_right_identity_iff.mp ⟨-(x.fst⁻¹ • x.snd), fun c => ?_⟩)).elim
    have hc : c * x.snd = -(x.fst • c) := eq_neg_of_add_eq_zero_right (hl c)
    simp [mul_smul_comm, hc, h0]

/-- **The approximate unit estimate.** For a positive functional `γ` and a positive contraction
`e`, `‖γ y - γ (y e)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²`. -/
theorem norm_apply_sub_apply_mul_sq_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (y * e)‖ ^ 2 ≤
      ‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re) * ‖y‖ ^ 2 := by
  set N := ‖(γ : A →L[ℂ] ℂ)‖
  set u : Unitization ℂ A := star (y : Unitization ℂ A)
  set v : Unitization ℂ A := 1 - (e : Unitization ℂ A)
  have hkey : γ y - γ (y * e) = γ.unitization (star u * v) := by
    simp only [u, v, star_star, mul_sub, mul_one, ← Unitization.inr_mul, map_sub,
      unitization_apply_inr]
  have hcs := PositiveLinearMap.norm_map_star_mul_sq_le γ.unitization u v
  have h1 : ‖γ.unitization (star u * u)‖ ≤ N * ‖y‖ ^ 2 := by
    simp only [u, star_star, ← Unitization.inr_star, ← Unitization.inr_mul, unitization_apply_inr]
    calc ‖γ (y * star y)‖ ≤ N * ‖y * star y‖ := (γ : A →L[ℂ] ℂ).le_opNorm _
      _ = N * ‖y‖ ^ 2 := by rw [CStarRing.norm_self_mul_star, sq]
  have hval : γ.unitization (star v * v) = N - γ e - γ e + γ (e * e) := by
    have hv : star v * v =
        1 - (e : Unitization ℂ A) - e + ((e * e : A) : Unitization ℂ A) := by
      simp only [v, star_sub, star_one, ← Unitization.inr_star, he.star_eq, Unitization.inr_mul]
      noncomm_ring
    rw [hv, map_add, map_sub, map_sub, unitization_apply_one, unitization_apply_inr,
      unitization_apply_inr]
  have hnn : 0 ≤ γ.unitization (star v * v) := γ.unitization.map_nonneg (star_mul_self_nonneg v)
  have hee : (γ (e * e)).re ≤ (γ e).re :=
    (Complex.le_def.mp (γ.mono (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he he1))).1
  have h2 : ‖γ.unitization (star v * v)‖ ≤ N - (γ e).re := by
    rw [← Complex.re_eq_norm.mpr hnn, hval]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    linarith
  rw [hkey]
  calc ‖γ.unitization (star u * v)‖ ^ 2
      ≤ ‖γ.unitization (star u * u)‖ * ‖γ.unitization (star v * v)‖ := hcs
    _ ≤ (N * ‖y‖ ^ 2) * (N - (γ e).re) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = N * (N - (γ e).re) * ‖y‖ ^ 2 := by ring

/-- The left-hand version of `norm_apply_sub_apply_mul_sq_le`:
`‖γ y - γ (e y)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²` for a positive contraction `e`. -/
theorem norm_apply_sub_apply_mul_left_sq_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (e * y)‖ ^ 2 ≤
      ‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re) * ‖y‖ ^ 2 := by
  have h := norm_apply_sub_apply_mul_sq_le γ he he1 (star y)
  have hs : star y * e = star (e * y) := by rw [star_mul, he.star_eq]
  rwa [hs, map_star, map_star, ← star_sub, norm_star, norm_star] at h

/-- The unsquared form of `norm_apply_sub_apply_mul_sq_le`:
`‖γ y - γ (y e)‖ ≤ √(‖γ‖ (‖γ‖ - Re γ e)) ‖y‖` for a positive contraction `e`. -/
theorem norm_apply_sub_apply_mul_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (y * e)‖ ≤
      Real.sqrt (‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re)) * ‖y‖ :=
  (Real.le_sqrt_of_sq_le (norm_apply_sub_apply_mul_sq_le γ he he1 y)).trans_eq
    (by rw [Real.sqrt_mul_sq, abs_norm])

/-- The unsquared form of `norm_apply_sub_apply_mul_left_sq_le`:
`‖γ y - γ (e y)‖ ≤ √(‖γ‖ (‖γ‖ - Re γ e)) ‖y‖` for a positive contraction `e`. -/
theorem norm_apply_sub_apply_mul_left_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (e * y)‖ ≤
      Real.sqrt (‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re)) * ‖y‖ :=
  (Real.le_sqrt_of_sq_le (norm_apply_sub_apply_mul_left_sq_le γ he he1 y)).trans_eq
    (by rw [Real.sqrt_mul_sq, abs_norm])

/-- The two-sided version of `norm_apply_sub_apply_mul_sq_le`:
`‖γ y - γ (e y e)‖ ≤ 2 √(‖γ‖ (‖γ‖ - Re γ e)) ‖y‖` for a positive contraction `e`. -/
theorem norm_apply_sub_apply_mul_mul_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (e * y * e)‖ ≤
      2 * Real.sqrt (‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re)) * ‖y‖ := by
  set c := ‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re)
  have h1 := norm_apply_sub_apply_mul_left_le γ he he1 y
  have h2 := norm_apply_sub_apply_mul_le γ he he1 (e * y)
  have hey : ‖e * y‖ ≤ ‖y‖ := (norm_mul_le e y).trans (mul_le_of_le_one_left (norm_nonneg y) he1)
  calc ‖γ y - γ (e * y * e)‖ ≤ ‖γ y - γ (e * y)‖ + ‖γ (e * y) - γ (e * y * e)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt c * ‖y‖ + Real.sqrt c * ‖y‖ :=
        add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hey (Real.sqrt_nonneg c)))
    _ = 2 * Real.sqrt c * ‖y‖ := by ring

end PositiveContinuousLinearMap

namespace TauCeti

open Set WeakDual

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every state `φ` of `A` is the restriction of a state of `Unitization ℂ A`, namely
`λ + a ↦ λ + φ a`. -/
theorem surjOn_pullbackFunctional_inr_stateSpace :
    SurjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A))
      (stateSpace (Unitization ℂ A)) (stateSpace A) := by
  intro φ hφ
  let τ : A →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun _ => map_nonneg_of_mem_stateSpace hφ
  refine ⟨StrongDual.toWeakDual (τ.unitization : Unitization ℂ A →L[ℂ] ℂ), ?_,
    DFunLike.ext _ _ fun a => ?_⟩
  · rw [PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff,
      PositiveContinuousLinearMap.norm_unitization]
    exact norm_toStrongDual_of_mem_stateSpace hφ
  · simp only [pullbackFunctional_apply, Unitization.inrNonUnitalStarAlgHom_apply,
      StrongDual.toWeakDual_apply]
    exact (τ.unitization_apply_inr a).trans
      (PositiveContinuousLinearMap.mk₀_apply (R := ℂ) _ _ a)

end Unitization

end TauCeti
