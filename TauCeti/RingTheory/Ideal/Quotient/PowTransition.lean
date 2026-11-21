/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Quotient transition maps, transport, and multiplication between ideal quotients

This file collects reusable infrastructure for transition maps between module and ideal quotients:

* **Ideal-power filtration**: `Ideal.pow_succ_smul_top_antitone` records that `n ↦ I ^ (n + 1) • ⊤`
  is decreasing.
* **Quotient-constructor transport and transition compatibility**:
  `Submodule.quotEquivOfEq_ideal_mk` evaluates `Submodule.quotEquivOfEq` directly on
  `Ideal.Quotient.mk`, and `Submodule.factor_quotEquivOfEq`, `Submodule.factor_comp_quotEquivOfEq`,
  and `Ideal.Quotient.factor_quotEquivOfEq` record that `factor` commutes with `quotEquivOfEq`.
* **Multiplication maps between ideal quotients**: for a commutative ring `R`, multiplication by
  `a : R` induces an `R`-linear map `Ideal.Quotient.mulLeft a h : (R ⧸ I) →ₗ[R] (R ⧸ J)` whenever
  `Ideal.span {a} * I ≤ J`, specializing to `Ideal.Quotient.mulSpanPowSucc a n`, mapping
  `R ⧸ Ideal.span {a ^ n}` to `R ⧸ Ideal.span {a ^ (n + 1)}`. Both maps satisfy exact
  compatibility with `Ideal.Quotient.factor` (`mulLeft_factor`, `mulSpanPowSucc_factor`) and
  injectivity criteria for left-regular scalars (`mulLeft_injective`, `mulSpanPowSucc_injective`).
-/

public section

namespace Ideal

variable {A : Type*} [Ring A] (I : Ideal A)
variable (M : Type*) [AddCommGroup M] [Module A M]

/-- The `I`-adic filtration `n ↦ I^{n+1} M` of `M` is decreasing. -/
theorem pow_succ_smul_top_antitone :
    Antitone fun n : ℕ ↦ (I ^ (n + 1) • ⊤ : Submodule A M) :=
  fun _ _ h ↦ Submodule.pow_smul_top_le I M (Nat.add_le_add_right h 1)

end Ideal

namespace Submodule

section QuotEquivOfEq

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- `Submodule.quotEquivOfEq` transports `Ideal.Quotient.mk I x` to `Ideal.Quotient.mk J x`. -/
@[simp, grind =]
theorem quotEquivOfEq_ideal_mk {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
    (h : I = J) (x : R) :
    Submodule.quotEquivOfEq I J h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x := by
  rw [← Ideal.Quotient.mk_eq_mk, Submodule.quotEquivOfEq_mk, Ideal.Quotient.mk_eq_mk]

/-- `Submodule.factor` commutes with `Submodule.quotEquivOfEq`. -/
theorem factor_quotEquivOfEq {p₁ p₂ q₁ q₂ : Submodule R M}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (h₁ : p₁ ≤ q₁) (h₂ : p₂ ≤ q₂) (x : M ⧸ p₁) :
    Submodule.factor h₂ (Submodule.quotEquivOfEq p₁ p₂ hp x) =
      Submodule.quotEquivOfEq q₁ q₂ hq (Submodule.factor h₁ x) := by
  obtain ⟨m, rfl⟩ := p₁.mkQ_surjective x
  rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    ← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk]

/-- `Submodule.factor` commutes with `Submodule.quotEquivOfEq` as linear maps. -/
theorem factor_comp_quotEquivOfEq {p₁ p₂ q₁ q₂ : Submodule R M}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (h₁ : p₁ ≤ q₁) (h₂ : p₂ ≤ q₂) :
    Submodule.factor h₂ ∘ₗ (Submodule.quotEquivOfEq p₁ p₂ hp).toLinearMap =
      (Submodule.quotEquivOfEq q₁ q₂ hq).toLinearMap ∘ₗ Submodule.factor h₁ :=
  LinearMap.ext (factor_quotEquivOfEq hp hq h₁ h₂)

end QuotEquivOfEq

end Submodule

namespace Ideal.Quotient

section Factor

variable {R : Type*} [Ring R]

/-- `Ideal.Quotient.factor` commutes with `Ideal.quotEquivOfEq`. -/
theorem factor_quotEquivOfEq {I₁ I₂ J₁ J₂ : Ideal R}
    [I₁.IsTwoSided] [I₂.IsTwoSided] [J₁.IsTwoSided] [J₂.IsTwoSided]
    (hI : I₁ = I₂) (hJ : J₁ = J₂) (h₁ : I₁ ≤ J₁) (h₂ : I₂ ≤ J₂) (x : R ⧸ I₁) :
    Ideal.Quotient.factor h₂ (Ideal.quotEquivOfEq hI x) =
      Ideal.quotEquivOfEq hJ (Ideal.Quotient.factor h₁ x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    Ideal.quotEquivOfEq_mk]

end Factor

section MulLeft

variable {R : Type*} [CommRing R]

/-- Multiplication by `a` induces an `R`-linear map `(R ⧸ I) →ₗ[R] (R ⧸ J)` whenever
`Ideal.span {a} * I ≤ J`. -/
def mulLeft {I J : Ideal R} (a : R) (h : Ideal.span {a} * I ≤ J) :
    (R ⧸ I) →ₗ[R] (R ⧸ J) :=
  Submodule.mapQ I J (LinearMap.lsmul R R a) fun r hr ↦ by
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul]
    exact h (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self a) hr)

/-- Evaluating `Ideal.Quotient.mulLeft a h` on the residue class of `r` gives the class of
`a * r`. -/
@[simp, grind =]
theorem mulLeft_mk {I J : Ideal R} (a : R) (h : Ideal.span {a} * I ≤ J) (r : R) :
    mulLeft a h (mk I r) = mk J (a * r) := by
  rw [mulLeft, ← mk_eq_mk, Submodule.mapQ_apply, LinearMap.lsmul_apply, smul_eq_mul, mk_eq_mk]

/-- Composing `Ideal.Quotient.mulLeft a h` with the quotient transition map `factor hJI` is
scalar multiplication by `a`. -/
@[simp, grind =]
theorem mulLeft_factor {I J : Ideal R} (a : R) (h : Ideal.span {a} * I ≤ J) (hJI : J ≤ I)
    (q : R ⧸ J) :
    mulLeft a h (factor hJI q) = a • q := by
  obtain ⟨r, rfl⟩ := mk_surjective q
  rw [factor_mk, mulLeft_mk, ← mk_eq_mk, ← mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul]

/-- `Ideal.Quotient.mulLeft a h` is injective if and only if `a * r ∈ J` implies `r ∈ I`. -/
theorem mulLeft_injective_iff {I J : Ideal R} (a : R) (h : Ideal.span {a} * I ≤ J) :
    Function.Injective (mulLeft a h) ↔ ∀ r : R, a * r ∈ J → r ∈ I := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  constructor
  · intro hker r hr
    have h0 : mk I r = 0 := hker (mk I r) <| by
      rw [LinearMap.mem_ker, mulLeft_mk, eq_zero_iff_mem]
      exact hr
    exact eq_zero_iff_mem.mp h0
  · intro hdiv q hq
    obtain ⟨r, rfl⟩ := mk_surjective q
    rw [LinearMap.mem_ker, mulLeft_mk, eq_zero_iff_mem] at hq
    exact eq_zero_iff_mem.mpr (hdiv r hq)

/-- If `a` is left-regular and `J ≤ Ideal.span {a} * I` (so `J = Ideal.span {a} * I`), then
`Ideal.Quotient.mulLeft a h` is injective. -/
theorem mulLeft_injective {I J : Ideal R} {a : R} (h : Ideal.span {a} * I ≤ J)
    (hJI : J ≤ Ideal.span {a} * I) (ha : IsLeftRegular a) :
    Function.Injective (mulLeft a h) := by
  rw [mulLeft_injective_iff]
  intro r hr
  obtain ⟨s, hs, hsr⟩ := Ideal.mem_span_singleton_mul.mp (hJI hr)
  exact ha hsr ▸ hs

/-- Multiplication by `a` induces an `R`-linear map
`(R ⧸ Ideal.span {a ^ n}) →ₗ[R] (R ⧸ Ideal.span {a ^ (n + 1)})`. -/
def mulSpanPowSucc (a : R) (n : ℕ) :
    (R ⧸ Ideal.span {a ^ n}) →ₗ[R] (R ⧸ Ideal.span {a ^ (n + 1)}) :=
  mulLeft a (by rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ'])

/-- Evaluating `Ideal.Quotient.mulSpanPowSucc a n` on the residue class of `r` gives the class of
`a * r`. -/
@[simp, grind =]
theorem mulSpanPowSucc_mk (a : R) (n : ℕ) (r : R) :
    mulSpanPowSucc a n (mk (Ideal.span {a ^ n}) r) = mk (Ideal.span {a ^ (n + 1)}) (a * r) :=
  mulLeft_mk a _ r

/-- Composing `Ideal.Quotient.mulSpanPowSucc a n` with the transition map from `R ⧸ (a ^ (n + 1))`
to `R ⧸ (a ^ n)` is scalar multiplication by `a`. -/
@[simp, grind =]
theorem mulSpanPowSucc_factor (a : R) (n : ℕ)
    (h : Ideal.span {a ^ (n + 1)} ≤ Ideal.span {a ^ n}) (q : R ⧸ Ideal.span {a ^ (n + 1)}) :
    mulSpanPowSucc a n (factor h q) = a • q :=
  mulLeft_factor a _ h q

/-- For any left-regular element `a` of a commutative ring `R`,
`Ideal.Quotient.mulSpanPowSucc a n` is injective. -/
theorem mulSpanPowSucc_injective {a : R} (ha : IsLeftRegular a) (n : ℕ) :
    Function.Injective (mulSpanPowSucc a n) :=
  mulLeft_injective _ (by rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ']) ha

end MulLeft

end Ideal.Quotient
