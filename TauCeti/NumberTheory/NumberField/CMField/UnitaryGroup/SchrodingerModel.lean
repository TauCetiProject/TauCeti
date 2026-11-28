/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.WeilData
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.SchwartzBruhat
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.NumberTheory.NumberField.CMField.AddChar

/-!
# The Schrödinger model above a set of places disjoint from its conjugate

Let `E` be a CM field with Weil data `W`, `𝔸_f` its finite adeles with complex conjugation
`a ↦ conj a`, `Ô` the integral finite adeles, and `ψ₀` the self-dual character of `𝔸_f`
(`TauCeti.WeilData.selfDualAddChar`). Let `e` be an idempotent of `𝔸_f`: the indicator `e_S` of
a set `S` of finite places, so that `conj e` is the indicator of the conjugate set `conj S`. The
set `S` is disjoint from `conj S` exactly when `e · conj e = 0`, and then `e + conj e` is the
indicator of `S ∪ conj S`.

For `y ∈ 𝔸_f^n`, the **Schrödinger operator** of `y` above `e`
(`TauCeti.WeilData.schrodingerAct`) acts on functions on `𝔸_f^n` by

`(ρ(y) Ψ)(x) = ψ₀(½ e · y* (2x + y)) · Ψ(x + y)`,

where `y* z = Σ_i conj y_i · z_i`. When `e · conj e = 0` these operators form the Schrödinger model
of the Heisenberg group of `𝔸_f^n` in the polarisation given by the components at `S` and at
`conj S`:

* they compose up to the finite Heisenberg datum `β_f(a, b) = ψ₀(½ b* a)` of the parts at
  `S ∪ conj S`: `ρ(y) ρ(y') = β_f(e' y, e' y') ρ(y + y')` with `e' = e + conj e`
  (`TauCeti.WeilData.schrodingerAct_mul_schrodingerAct`);
* corrected by the semicharacter `semi` of `e' y`, the operator of `y` is
  `Ψ ↦ (x ↦ ψ₀(y* e (x + c₀ y)) · Ψ(x + y))`, with `c₀ = (1 − j⁻¹)/2`
  (`TauCeti.WeilData.semichar_smul_schrodingerAct`), so the corrected operators of the vectors
  integral at `S ∪ conj S` fix the indicator of the box `B_e = {x : e x ∈ Ô^n}`
  (`TauCeti.WeilData.semichar_smul_schrodingerAct_indicator_integralBox`);
* on a function `Ψ` that is Schwartz–Bruhat above `e`, a vector `e y` at `S` acts by translation,
  `ρ(e y) Ψ = Ψ(· + y)`, and a vector `conj e · y` at `conj S` by the character
  `x ↦ ψ₀(y* e x)` (`TauCeti.WeilData.schrodingerAct_smul`,
  `TauCeti.WeilData.schrodingerAct_star_smul`);
* the operators keep the functions that are Schwartz–Bruhat above `e`
  (`TauCeti.WeilData.isSchwartzBruhatAbove_schrodingerAct`).

The box indicator is the vacuum of this model; these laws are the computations behind the vectors
of the space of data named by Schwartz–Bruhat functions. The phases are compared through the
triviality of `ψ₀` on the elements `z + conj z` (`TauCeti.WeilData.selfDualAddChar_add_star`).

## Main definitions

* `TauCeti.WeilData.schrodingerAct W e y`: the Schrödinger operator `ρ(y)` above `e`.

## Provenance

The operators and their laws correspond to `New.schrodingerAct`,
`New.schrodingerAct_schrodingerAct`, `New.semichar_smul_schrodingerAct`,
`New.schrodingerAct_boxIndicator`, `New.IsSchwartzBruhat.schrodingerAct_idem` and
`New.IsSchwartzBruhat.schrodingerAct_star_idem_smul` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Weil/MixedModel/SchwartzBruhat.lean`, which works with the indicator of a set of places
disjoint from its conjugate. Here the set of places is replaced by an idempotent `e` with
`e · conj e = 0`; the proofs follow grh-lean's, reducing each law to a scalar identity in `e`,
`conj e`, `½` and `c₀` and to the triviality of `ψ₀` on `Ô` and on the elements `z + conj z`.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211 (the
  Heisenberg group of a symplectic space over a local field and its Schrödinger model).
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField Matrix

namespace TauCeti.WeilData

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {Φ : CMType E} (W : WeilData Φ)
  {n : Type*} [Fintype n]

/-- `ψ₀` is trivial on the elements `z + conj z`: `t = j α (conj α)` is purely imaginary, so
`t (z + conj z)` is purely imaginary, and `ψ_f` is trivial on purely imaginary finite adeles. -/
theorem selfDualAddChar_add_star (z : FiniteAdeleRing (𝓞 E) E) :
    W.selfDualAddChar (z + star z) = 1 := by
  have ht : star (W.scaleIdele : FiniteAdeleRing (𝓞 E) E) = -W.scaleIdele := by
    rw [coe_scaleIdele, star_mul, star_mul, star_star, ← algebraMap_star_comm, W.star_j, map_neg]
    ring
  rw [selfDualAddChar_apply]
  refine GlobalNumberFields.finiteAdeleAddChar_eq_one_of_mem_skewAdjoint ?_
  rw [skewAdjoint.mem_iff, star_mul, star_add, star_star, ht]
  ring

/-- The **Schrödinger operator** of `y ∈ 𝔸_f^n` above `e ∈ 𝔸_f`: the linear operator
`(ρ(y) Ψ)(x) = ψ₀(½ e · y* (2x + y)) · Ψ(x + y)` on functions on `𝔸_f^n`, where `ψ₀` is the
self-dual character of the Weil data and `y* z = Σ_i conj y_i · z_i`. -/
def schrodingerAct (e : FiniteAdeleRing (𝓞 E) E) (y : n → FiniteAdeleRing (𝓞 E) E) :
    Module.End ℂ ((n → FiniteAdeleRing (𝓞 E) E) → ℂ) where
  toFun Ψ x := W.selfDualAddChar
    (algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹ * e * (star y ⬝ᵥ (2 • x + y))) * Ψ (x + y)
  map_add' Ψ Ψ' := funext fun x ↦ by simp only [Pi.add_apply, mul_add]
  map_smul' c Ψ := funext fun x ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm]

/-- The value of a Schrödinger operator. -/
@[simp]
theorem schrodingerAct_apply (e : FiniteAdeleRing (𝓞 E) E) (y : n → FiniteAdeleRing (𝓞 E) E)
    (Ψ : (n → FiniteAdeleRing (𝓞 E) E) → ℂ) (x : n → FiniteAdeleRing (𝓞 E) E) :
    W.schrodingerAct e y Ψ x = W.selfDualAddChar
      (algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹ * e * (star y ⬝ᵥ (2 • x + y))) * Ψ (x + y) :=
  (rfl)

/-- The Schrödinger operator of `0` is the identity. -/
@[simp]
theorem schrodingerAct_zero (e : FiniteAdeleRing (𝓞 E) E) :
    W.schrodingerAct e (0 : n → FiniteAdeleRing (𝓞 E) E) = 1 := by
  refine LinearMap.ext fun Ψ ↦ funext fun x ↦ ?_
  simp

variable {e : FiniteAdeleRing (𝓞 E) E}

/-- **The Heisenberg law** of the Schrödinger model. For an idempotent `e` with `e · conj e = 0`,
the operators compose up to the finite Heisenberg datum `β_f(a, b) = ψ₀(½ b* a)` of the parts of
`y` and `y'` at `e' = e + conj e`: `ρ(y) ρ(y') = β_f(e' y, e' y') ρ(y + y')`. -/
theorem schrodingerAct_mul_schrodingerAct (he : IsIdempotentElem e) (hc : e * star e = 0)
    (y y' : n → FiniteAdeleRing (𝓞 E) E) :
    W.schrodingerAct e y * W.schrodingerAct e y' =
      (W.selfDualAddChar (algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹ *
        (star ((e + star e) • y') ⬝ᵥ ((e + star e) • y))) : ℂ) •
        W.schrodingerAct e (y + y') := by
  refine LinearMap.ext fun Ψ ↦ funext fun x ↦ ?_
  set h := algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹ with hh
  have hstar_h : star h = h := by rw [hh, ← algebraMap_star_comm, star_inv₀, star_ofNat]
  -- The two phases on the left are the phases on the right times `ψ₀(s + conj s)`, for
  -- `s = -½ e · y* y'`.
  have key : h * e * (star y ⬝ᵥ (2 • x + y)) + h * e * (star y' ⬝ᵥ (2 • (x + y) + y')) =
      (h * (star ((e + star e) • y') ⬝ᵥ ((e + star e) • y)) +
        h * e * (star (y + y') ⬝ᵥ (2 • x + (y + y')))) +
        (-(h * e * (star y ⬝ᵥ y')) + star (-(h * e * (star y ⬝ᵥ y')))) := by
    rw [star_neg, star_mul, star_mul, hstar_h, ← Matrix.star_dotProduct]
    simp only [star_add, star_smul, star_star, smul_dotProduct, dotProduct_smul, add_dotProduct,
      dotProduct_add, smul_add, two_nsmul, smul_eq_mul]
    linear_combination (-(h * (star y' ⬝ᵥ y))) * he.eq - (2 * h * (star y' ⬝ᵥ y)) * hc -
      (h * (star y' ⬝ᵥ y)) * he.star.eq
  simp only [mul_apply_eq_comp, LinearMap.smul_apply, schrodingerAct_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [add_assoc x y y', ← mul_assoc, ← mul_assoc, ← Circle.coe_mul, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, AddChar.map_add_eq_mul (x := _ + _),
    W.selfDualAddChar_add_star, mul_one]

/-- **The Schrödinger operators in the normalisation of the lattice.** For an idempotent `e` with
`e · conj e = 0`, the operator of `y` corrected by the semicharacter of `e' y`, `e' = e + conj e`,
is `Ψ ↦ (x ↦ ψ₀(y* e (x + c₀ y)) · Ψ(x + y))`, where `c₀ = (1 − j⁻¹)/2`. -/
theorem semichar_smul_schrodingerAct (he : IsIdempotentElem e) (hc : e * star e = 0)
    (y : n → FiniteAdeleRing (𝓞 E) E) (Ψ : (n → FiniteAdeleRing (𝓞 E) E) → ℂ) :
    (W.semichar ((e + star e) • y) : ℂ) • W.schrodingerAct e y Ψ = fun x ↦
      W.selfDualAddChar (star y ⬝ᵥ
        (e • (x + algebraMap E (FiniteAdeleRing (𝓞 E) E) W.traceOne • y))) * Ψ (x + y) := by
  refine funext fun x ↦ ?_
  set h := algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹ with hh
  set c := algebraMap E (FiniteAdeleRing (𝓞 E) E) W.traceOne
  have hstar_h : star h = h := by rw [hh, ← algebraMap_star_comm, star_inv₀, star_ofNat]
  have h2 : 2 * h = 1 := ofNat_mul_algebraMap_inv two_ne_zero
  have hcc : c + star c = 1 := by
    rw [← algebraMap_star_comm, ← map_add, W.traceOne_add_star, map_one]
  have hk : algebraMap E (FiniteAdeleRing (𝓞 E) E) (W.traceOne / 2) = c * h := by
    rw [div_eq_mul_inv, map_mul]
  -- The semicharacter is written with the sum `Σ_i conj z_i · z_i`, which is `z* z`.
  have hsum : ∑ i, star (((e + star e) • y) i) * ((e + star e) • y) i =
      star ((e + star e) • y) ⬝ᵥ ((e + star e) • y) := by
    simp only [dotProduct, Pi.star_apply]
  -- The two phases add up to the phase on the right plus `s + conj s`, for
  -- `s = c₀ ½ conj e · y* y`, on which `ψ₀` is trivial.
  have key : c * h * (star ((e + star e) • y) ⬝ᵥ ((e + star e) • y)) +
        h * e * (star y ⬝ᵥ (2 • x + y)) =
      star y ⬝ᵥ (e • (x + c • y)) +
        (c * h * star e * (star y ⬝ᵥ y) + star (c * h * star e * (star y ⬝ᵥ y))) := by
    have hY : star (star y ⬝ᵥ y) = star y ⬝ᵥ y := (Matrix.star_dotProduct y y).symm
    rw [star_mul, star_mul, star_mul, hstar_h, star_star, hY]
    simp only [star_add, star_smul, star_star, smul_dotProduct, dotProduct_smul, dotProduct_add,
      smul_add, two_nsmul, smul_eq_mul]
    linear_combination (c * h * (star y ⬝ᵥ y)) * he.eq + (c * h * (star y ⬝ᵥ y)) * he.star.eq +
      (2 * c * h * (star y ⬝ᵥ y)) * hc + (e * (star y ⬝ᵥ x) + e * (star y ⬝ᵥ y) * c) * h2 -
      (h * (star y ⬝ᵥ y) * e) * hcc
  rw [Pi.smul_apply, schrodingerAct_apply, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
    semichar_apply, ← AddChar.map_add_eq_mul, hk, hsum, key, AddChar.map_add_eq_mul,
    W.selfDualAddChar_add_star, mul_one]

/-- **The box indicator is the vacuum.** For an idempotent `e` with `e · conj e = 0` and a vector
`y` integral at `e' = e + conj e`, the Schrödinger operator of `y`, corrected by the
semicharacter of `e' y`, fixes the indicator of the box `B_e`. -/
theorem semichar_smul_schrodingerAct_indicator_integralBox (he : IsIdempotentElem e)
    (hc : e * star e = 0) {y : n → FiniteAdeleRing (𝓞 E) E}
    (hy : y ∈ integralBox n (e + star e)) :
    (W.semichar ((e + star e) • y) : ℂ) • W.schrodingerAct e y
        ((integralBox n e : Set (n → FiniteAdeleRing (𝓞 E) E)).indicator 1) =
      (integralBox n e : Set (n → FiniteAdeleRing (𝓞 E) E)).indicator 1 := by
  classical
  -- `y` is integral at `e`, as `e = e (e + conj e)`.
  have hyS : y ∈ integralBox n e := by
    have h := integralBox_le_integralBox_mul (n := n) he.mem_integralAdeles hy
    rwa [mul_add, he.eq, hc, add_zero] at h
  rw [W.semichar_smul_schrodingerAct he hc]
  refine funext fun x ↦ ?_
  simp only [Set.indicator_apply, SetLike.mem_coe, add_mem_cancel_right hyS, Pi.one_apply]
  split_ifs with hx
  swap
  · rw [mul_zero]
  set c := algebraMap E (FiniteAdeleRing (𝓞 E) E) W.traceOne
  have hcint : c ∈ integralAdeles (𝓞 E) E :=
    (algebraMap_mem_integralAdeles_iff _).2
      ⟨⟨W.traceOne, W.isIntegral_traceOne⟩, RingOfIntegers.map_mk _ _⟩
  -- On the box, the phase is `ψ₀` of the pairing `(e' y)* e (x + c₀ y)` of two integral vectors.
  have hpair : star y ⬝ᵥ (e • (x + c • y)) = star ((e + star e) • y) ⬝ᵥ (e • (x + c • y)) := by
    simp only [star_smul, star_add, star_star, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    linear_combination (-(star y ⬝ᵥ (x + c • y))) * hc - (star y ⬝ᵥ (x + c • y)) * he.eq
  have hint : star y ⬝ᵥ (e • (x + c • y)) ∈ integralAdeles (𝓞 E) E := by
    rw [hpair]
    refine Subalgebra.sum_mem _ fun i _ ↦ mul_mem ?_ ?_
    · rw [Pi.star_apply, NumberField.IsCMField.star_mem_integralAdeles_iff]
      exact mem_integralBox.1 hy i
    · rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Pi.smul_apply, smul_eq_mul,
        mul_left_comm]
      exact add_mem (mem_integralBox.1 hx i) (mul_mem hcint (mem_integralBox.1 hyS i))
  -- `ψ₀` is trivial on `Ô`, which is self-dual for it.
  rw [(by simpa using (W.forall_selfDualAddChar_mul_eq_one_iff _).2 hint 1 (one_mem _) :
    W.selfDualAddChar _ = 1), Circle.coe_one, mul_one]

/-- On a function that is Schwartz–Bruhat above an idempotent `e` with `e · conj e = 0`, a vector
`e y` at the places of `e` acts by **translation**: `ρ(e y) Ψ = Ψ(· + y)`. -/
theorem schrodingerAct_smul (he : IsIdempotentElem e) (hc : e * star e = 0)
    {Ψ : (n → FiniteAdeleRing (𝓞 E) E) → ℂ} (hΨ : IsSchwartzBruhatAbove e Ψ)
    (y : n → FiniteAdeleRing (𝓞 E) E) :
    W.schrodingerAct e (e • y) Ψ = fun x ↦ Ψ (x + y) := by
  refine funext fun x ↦ ?_
  have hphase : algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹ * e *
      (star (e • y) ⬝ᵥ (2 • x + e • y)) = 0 := by
    rw [star_smul, smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_assoc _ e, hc, mul_zero,
      zero_mul]
  rw [schrodingerAct_apply, hphase, AddChar.map_zero_eq_one, Circle.coe_one, one_mul,
    ← hΨ.apply_smul, smul_add, smul_smul, he.eq, ← smul_add, hΨ.apply_smul]

/-- On a function that is Schwartz–Bruhat above an idempotent `e` with `e · conj e = 0`, a vector
`conj e · y` at the conjugate places acts by **multiplication by a character**:
`(ρ(conj e · y) Ψ)(x) = ψ₀(y* e x) · Ψ(x)`. -/
theorem schrodingerAct_star_smul (he : IsIdempotentElem e) (hc : e * star e = 0)
    {Ψ : (n → FiniteAdeleRing (𝓞 E) E) → ℂ} (hΨ : IsSchwartzBruhatAbove e Ψ)
    (y : n → FiniteAdeleRing (𝓞 E) E) :
    W.schrodingerAct e (star e • y) Ψ = fun x ↦ W.selfDualAddChar (star y ⬝ᵥ (e • x)) * Ψ x := by
  refine funext fun x ↦ ?_
  set h := algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹
  have h2 : 2 * h = 1 := ofNat_mul_algebraMap_inv two_ne_zero
  have hphase : h * e * (star (star e • y) ⬝ᵥ (2 • x + star e • y)) = star y ⬝ᵥ (e • x) := by
    simp only [star_smul, star_star, smul_dotProduct, dotProduct_smul, dotProduct_add,
      two_nsmul, smul_eq_mul]
    linear_combination (2 * h * (star y ⬝ᵥ x)) * he.eq + (e * (star y ⬝ᵥ x)) * h2 +
      (h * e * (star y ⬝ᵥ y)) * hc
  have hpart : Ψ (x + star e • y) = Ψ x := by
    rw [← hΨ.apply_smul, smul_add, smul_smul, hc, zero_smul, add_zero, hΨ.apply_smul]
  rw [schrodingerAct_apply, hphase, hpart]

/-- The Schrödinger operators above an idempotent `e` keep the functions that are Schwartz–Bruhat
above `e`. -/
theorem isSchwartzBruhatAbove_schrodingerAct (he : IsIdempotentElem e)
    {Ψ : (n → FiniteAdeleRing (𝓞 E) E) → ℂ} (hΨ : IsSchwartzBruhatAbove e Ψ)
    (y : n → FiniteAdeleRing (𝓞 E) E) :
    IsSchwartzBruhatAbove e (W.schrodingerAct e y Ψ) := by
  set h := algebraMap E (FiniteAdeleRing (𝓞 E) E) 2⁻¹
  -- `ρ(y) Ψ` is a translate of `Ψ` times a locally constant phase that only sees `e x`.
  have hφ : IsLocallyConstant fun x : n → FiniteAdeleRing (𝓞 E) E ↦
      (W.selfDualAddChar (h * e * (star y ⬝ᵥ (2 • x + y))) : ℂ) := by
    simp only [selfDualAddChar_apply]
    exact (GlobalNumberFields.isLocallyConstant_finiteAdeleAddChar.comp_continuous
      (f := fun x ↦ (W.scaleIdele : FiniteAdeleRing (𝓞 E) E) * (h * e * (star y ⬝ᵥ (2 • x + y))))
      (by fun_prop)).comp _
  have hφe (x : n → FiniteAdeleRing (𝓞 E) E) :
      (W.selfDualAddChar (h * e * (star y ⬝ᵥ (2 • (e • x) + y))) : ℂ) =
        W.selfDualAddChar (h * e * (star y ⬝ᵥ (2 • x + y))) := by
    congr 2
    simp only [dotProduct_add, dotProduct_smul, two_nsmul, smul_eq_mul]
    linear_combination (2 * h * (star y ⬝ᵥ x)) * he.eq
  have hfun : W.schrodingerAct e y Ψ = fun x ↦
      (W.selfDualAddChar (h * e * (star y ⬝ᵥ (2 • x + y))) : ℂ) * Ψ (x + y) :=
    funext (W.schrodingerAct_apply e y Ψ)
  rw [hfun]
  exact (hΨ.comp_add he y).mul_left hφ hφe

end TauCeti.WeilData
