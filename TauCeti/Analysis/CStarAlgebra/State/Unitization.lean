/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Tracial
public import Mathlib.Analysis.CStarAlgebra.Unitization
import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# Extending positive functionals and tracial states to the unitization

A positive functional `τ` on a possibly nonunital C⋆-algebra `A` extends to the unitization
`A⁺¹ = Unitization ℂ A` by `τ⁺¹ (λ + a) = λ ‖τ‖ + τ a`. This is the unique positive extension with
the same norm, so statements about states of unital C⋆-algebras pass to nonunital ones along
it. For a tracial state `τ`, the extension `τ⁺¹` is again a tracial state. The extension of a
faithful positive functional is faithful when `A` has no unit.

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
* `PositiveContinuousLinearMap.isTracialState_unitization_iff`: `τ⁺¹` is a tracial state exactly
  when `τ` is.
* `PositiveContinuousLinearMap.eq_zero_of_unitization_map_star_mul_self_eq_zero`: if `τ` is
  faithful, `τ (star a * a) = 0 → a = 0`, and `A` has no two-sided unit, then `τ⁺¹` is faithful
  too.

## Implementation notes

The positivity of `τ⁺¹` is the inequality `0 ≤ |λ|² ‖τ‖ + 2 Re (star λ * τ a) + τ (a⋆a)` for the
value of `τ⁺¹` at `(λ + a)⋆ (λ + a)`, which follows from `|τ a|² ≤ ‖τ‖ τ (a⋆a)`
(`PositiveContinuousLinearMap.norm_map_sq_le_opNorm_mul`); every positive element of the
C⋆-algebra `A⁺¹` has the form `x⋆x`. Faithfulness passes to `τ⁺¹` because, for `x = λ + b` with
`τ⁺¹ (x⋆x) = 0`, the null space of `τ⁺¹` is a left ideal, so `cx = λc + cb ∈ A` lies in the null
space of `τ` for every `c ∈ A` and vanishes. If `λ ≠ 0`, then `e = -λ⁻¹ b` is a right unit of `A`,
and a right unit of a C⋆-algebra is self-adjoint (`e⋆ = e⋆e`), hence a two-sided unit. Without
the hypothesis on units this fails: for `A = ℂ` and `τ = id`, `τ⁺¹` vanishes at `1 - 1_A`.

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

/-- The value of `λ + a ↦ λ ‖τ‖ + τ a` at `(λ + a)⋆ (λ + a)` is nonnegative. -/
private theorem unitization_aux_nonneg (τ : A →P[ℂ] ℂ) (r : ℂ) (a : A) :
    0 ≤ ‖(τ : A →L[ℂ] ℂ)‖ * (star r * r) + (star r * τ a + r * star (τ a) + τ (star a * a)) := by
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
      simpa [map_star τ] using unitization_aux_nonneg τ y.fst y.snd

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
    rw [add_apply, unitization_apply, unitization_apply, unitization_apply, opNorm_add, add_apply]
    push_cast
    ring

/-- If `τ (a * b) = τ (b * a)` for all `a, b ∈ A`, the extension `τ⁺¹` has the same property on
`Unitization ℂ A`. -/
theorem unitization_map_mul_comm (h : ∀ a b : A, τ (a * b) = τ (b * a))
    (x y : Unitization ℂ A) : τ.unitization (x * y) = τ.unitization (y * x) := by
  simp only [unitization_apply, Unitization.fst_mul, Unitization.snd_mul, map_add, map_smul,
    smul_eq_mul, h x.snd y.snd]
  ring

/-- The extension `τ⁺¹` is a tracial state of `Unitization ℂ A` exactly when `τ` is a tracial
state of `A`. -/
@[simp]
theorem isTracialState_unitization_iff : τ.unitization.IsTracialState ↔ τ.IsTracialState := by
  simp only [isTracialState_iff, norm_unitization, and_congr_right_iff]
  refine fun _ => ⟨fun h a b => ?_, unitization_map_mul_comm⟩
  simpa only [← Unitization.inr_mul, unitization_apply_inr] using h a b

/-- The extension of a tracial state to the unitization is a tracial state. -/
theorem IsTracialState.unitization (hτ : τ.IsTracialState) : τ.unitization.IsTracialState :=
  isTracialState_unitization_iff.mpr hτ

/-- **Faithfulness of the unitization extension.** Let `τ` be a positive functional on a
C⋆-algebra `A` without a two-sided unit, faithful in the sense that `τ (star a * a) = 0` only for
`a = 0`. Then the extension `τ⁺¹` to `Unitization ℂ A` is faithful too. -/
theorem eq_zero_of_unitization_map_star_mul_self_eq_zero
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) (hA : ¬∃ e : A, ∀ a : A, e * a = a ∧ a * e = a)
    {x : Unitization ℂ A} (hx : τ.unitization (star x * x) = 0) : x = 0 := by
  -- for `c ∈ A`, `c x = λ c + c b` lies in `A` and in the null space of `τ⁺¹`, hence vanishes
  have hl : ∀ c : A, x.fst • c + c * x.snd = 0 := fun c => by
    refine hf _ ?_
    -- the null space of a positive functional is a left ideal
    let φ := TauCeti.StarPositiveFunctional.ofPositiveLinearMap
      (τ.unitization : Unitization ℂ A →ₚ[ℂ] ℂ)
    have h := (φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero _).mp <|
      φ.mul_mem_nullSubmodule (c : Unitization ℂ A)
        ((φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero x).mpr (by simpa [φ] using hx))
    simp only [φ, TauCeti.StarPositiveFunctional.ofPositiveLinearMap_apply,
      coe_toPositiveLinearMap] at h
    have hcx : (c : Unitization ℂ A) * x = ((x.fst • c + c * x.snd : A) : Unitization ℂ A) :=
      Unitization.ext (by simp) (by simp [add_comm])
    rwa [hcx, ← Unitization.inr_star, ← Unitization.inr_mul, unitization_apply_inr] at h
  obtain h0 | h0 := eq_or_ne x.fst 0
  · have hsnd : x.snd = 0 := hf _ <| by
      simpa [unitization_apply, h0] using hx
    exact Unitization.ext h0 hsnd
  · -- `e = -λ⁻¹ b` is a right unit of `A`, hence self-adjoint and a two-sided unit
    set e := -(x.fst⁻¹ • x.snd)
    have hr : ∀ c : A, c * e = c := fun c => by
      rw [mul_neg, mul_smul_comm, eq_neg_of_add_eq_zero_right (hl c), smul_neg, neg_neg,
        inv_smul_smul₀ h0]
    have he : star e = e := by
      have h1 : star e * e = star e := hr (star e)
      calc star e = star (star e * e) := by rw [star_mul, star_star, h1]
        _ = e := by rw [h1, star_star]
    refine (hA ⟨e, fun c => ⟨?_, hr c⟩⟩).elim
    rw [← star_star (e * c), star_mul, he, hr, star_star]

end PositiveContinuousLinearMap
