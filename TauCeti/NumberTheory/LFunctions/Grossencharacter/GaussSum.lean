/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.FiniteCharacter
public import TauCeti.NumberTheory.NumberField.AddChar
import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# Gauss sums of Grossencharacters

Let `χ` be a presentation at the modulus `𝔪` of an algebraic Hecke character of a number field `K`,
with finite part `𝔪₀` and residue character `χ_f` on `𝓞 K ⧸ 𝔪₀`
(`TauCeti.LFunctions.Grossencharacter.residueCharacter`). For `y` in the trace dual `𝔪₀⁻¹ 𝔡⁻¹` of
`𝔪₀`, `𝔡` the different of `K`, the trace `Tr(x y)` is an integer for every `x ∈ 𝔪₀`, so
`x ↦ e^{2πi Tr(x y)}` is an additive character of `𝓞 K ⧸ 𝔪₀`
(`Ideal.traceAddChar`). The **Gauss sum** of Neukirch VII (6.3) is

`τ(χ, y) = ∑_{x mod 𝔪₀} χ_f(x) e^{2πi Tr(x y)}`,

Mathlib's `gaussSum` of the residue character against this additive character. The residue
character is evaluated on the residue class itself, so only the trace needs representatives and
any may be used (`TauCeti.LFunctions.Grossencharacter.gaussSum_eq_sum`). When `𝔪₀ = 𝓞 K` the
residue ring has a single element, a unit at which `χ_f` is `1`, and the Gauss sum is `1`; a sum
that read the coefficient `finiteCharacter` at the representative `0` would give `0` instead.

Neukirch VII (6.4) computes the Gauss sums of a presentation at its finite conductor, that is,
when `𝔪₀` is the finite conductor of the Hecke character:

* `τ(χ, a y) = conj(χ_f(a)) τ(χ, y)` for every `a ∈ 𝓞 K`. For `a` a unit modulo `𝔪₀` this is the
  substitution `x ↦ x a⁻¹`, valid for every presentation. For `a` not a unit modulo `𝔪₀` both sides
  vanish: `a` lies in a prime `𝔭 ∣ 𝔪₀`, and, `𝔪₀` being the finite conductor, the residue character
  is nontrivial on the residue units congruent to `1` modulo `𝔪₀ 𝔭⁻¹`
  (`TauCeti.LFunctions.Grossencharacter.finiteConductor_dvd_iff_residueCharacter_eq_one`), while
  the additive character `x ↦ e^{2πi Tr(x a y)}` is invariant under them;
* `|τ(χ, y)| = √N(𝔪₀)` when moreover the integral ideal `y 𝔪₀ 𝔡` is prime to `𝔪₀`, which makes the
  additive character primitive.

The hypothesis `y ∈ 𝔪₀⁻¹ 𝔡⁻¹` cannot be dropped: over `ℚ`, with the even character modulo `5`,
the element `y = 1/25` does not give an additive character modulo `5` at all.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.gaussSum`: the Gauss sum `τ(χ, y)`, built from the trace
  character `Ideal.traceAddChar` of `TauCeti.NumberTheory.NumberField.AddChar`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.gaussSum_eq_sum`: the Gauss sum as a sum over the residue
  units, with arbitrary representatives in the trace.
* `TauCeti.LFunctions.Grossencharacter.gaussSum_of_finitePart_eq_top`: when `𝔪₀ = 𝓞 K` the Gauss
  sum is `1`.
* `TauCeti.LFunctions.Grossencharacter.gaussSum_smul_of_isUnit` and
  `TauCeti.LFunctions.Grossencharacter.gaussSum_smul`: `τ(χ, a y) = conj(χ_f(a)) τ(χ, y)`, for `a`
  a unit modulo `𝔪₀`, and for every `a` when `𝔪₀` is the finite conductor.
* `TauCeti.LFunctions.Grossencharacter.norm_gaussSum`: `|τ(χ, y)| = √N(𝔪₀)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.3) and (6.4).
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors FourierTransform ComplexConjugate

attribute [local instance] Fintype.ofFinite

variable {K : Type*} [Field K] [NumberField K]

/-! ### The Gauss sum of a presentation -/

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {𝔪 : Modulus K}

/-- **The Gauss sum** `τ(χ, y) = ∑_{x mod 𝔪₀} χ_f(x) e^{2πi Tr(x y)}` of a presentation `χ` at the
modulus `𝔪`, for `y` in the trace dual `𝔪₀⁻¹ 𝔡⁻¹` of the finite part `𝔪₀` of `𝔪` (Neukirch VII
(6.3)): Mathlib's `gaussSum` of the residue character of `χ` against the trace character of `y`.
-/
def gaussSum (χ : Grossencharacter K 𝔪)
    (y : (FractionalIdeal.dual ℤ ℚ (𝔪.finitePart : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) : ℂ :=
  _root_.gaussSum χ.residueCharacter (Ideal.traceAddChar 𝔪.finitePart y)

/-- The Gauss sum of a presentation is Mathlib's `gaussSum` of its residue character against the
trace character. -/
theorem gaussSum_def (χ : Grossencharacter K 𝔪)
    (y : (FractionalIdeal.dual ℤ ℚ (𝔪.finitePart : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    χ.gaussSum y = _root_.gaussSum χ.residueCharacter (Ideal.traceAddChar 𝔪.finitePart y) :=
  (rfl)

/-- **The Gauss sum as a sum over the residue units**: for any choice `r` of representatives of
the residue units modulo `𝔪₀`, `τ(χ, y) = ∑_x χ_f(x) e^{2πi Tr(r(x) y)}`. -/
theorem gaussSum_eq_sum (χ : Grossencharacter K 𝔪)
    (y : (FractionalIdeal.dual ℤ ℚ (𝔪.finitePart : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K))
    (r : (𝓞 K ⧸ 𝔪.finitePart)ˣ → 𝓞 K) (hr : ∀ x, Ideal.Quotient.mk 𝔪.finitePart (r x) = x) :
    χ.gaussSum y = ∑ x : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
      χ.residueCharacter x * 𝐞 (Algebra.trace ℚ K (r x * y) : ℝ) := by
  rw [gaussSum_def, _root_.gaussSum]
  symm
  refine Fintype.sum_of_injective _ Units.val_injective _ _ (fun x hx ↦ ?_) fun x ↦ ?_
  · rw [MulChar.map_nonunit _ fun hu ↦ hx ⟨hu.unit, hu.unit_spec⟩, zero_mul]
  · rw [← hr x, Ideal.traceAddChar_mk, numberFieldTraceChar_apply, hr, mul_comm (y : K)]

/-- **When the modulus has trivial finite part (`𝔪₀ = 𝓞 K`), the Gauss sum is `1`**: the residue
ring has a single element, a unit at which the residue character is `1`. -/
theorem gaussSum_of_finitePart_eq_top (χ : Grossencharacter K 𝔪) (h : 𝔪.finitePart = ⊤)
    (y : (FractionalIdeal.dual ℤ ℚ (𝔪.finitePart : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    χ.gaussSum y = 1 := by
  have : Subsingleton (𝓞 K ⧸ 𝔪.finitePart) := Ideal.Quotient.subsingleton_iff.mpr h
  rw [gaussSum_def, _root_.gaussSum, Fintype.sum_subsingleton _ 0, AddChar.map_zero_eq_one,
    mul_one, Subsingleton.elim (0 : 𝓞 K ⧸ 𝔪.finitePart) 1, map_one]

/-- **The Gauss sum at a multiple by a residue unit**: if `a` is a unit modulo `𝔪₀`, then
`τ(χ, a y) = conj(χ_f(a)) τ(χ, y)`. -/
theorem gaussSum_smul_of_isUnit (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePart a))
    (y : (FractionalIdeal.dual ℤ ℚ (𝔪.finitePart : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    χ.gaussSum (a • y) =
      conj (χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart a)) * χ.gaussSum y := by
  rw [gaussSum_def, gaussSum_def, Ideal.traceAddChar_smul, ← ha.unit_spec, gaussSum_mulShift_eq,
    starRingEnd_apply, MulChar.star_apply']

/-- **Neukirch VII (6.4)**: for a presentation at the finite conductor of its Hecke character,
`τ(χ, a y) = conj(χ_f(a)) τ(χ, y)` for every `a ∈ 𝓞 K`. When `a` is not a unit modulo `𝔪₀` both
sides vanish. -/
theorem gaussSum_smul (χ : Grossencharacter K 𝔪)
    (hχ : χ.toHeckeCharacter.finiteConductor = 𝔪.finitePart) (a : 𝓞 K)
    (y : (FractionalIdeal.dual ℤ ℚ (𝔪.finitePart : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    χ.gaussSum (a • y) =
      conj (χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart a)) * χ.gaussSum y := by
  by_cases ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePart a)
  · exact χ.gaussSum_smul_of_isUnit ha y
  rw [MulChar.map_nonunit _ ha, map_zero, zero_mul, gaussSum_def, Ideal.traceAddChar_smul]
  -- `a` lies in a prime `𝔭 ∣ 𝔪₀`; write `𝔪₀ = 𝔭 𝔫`.
  obtain ⟨𝔭, h𝔭, h𝔭a⟩ := Ideal.exists_le_maximal _
    (by rwa [Ne, ← Ideal.Quotient.isUnit_mk_iff] : Ideal.span {a} ⊔ 𝔪.finitePart ≠ ⊤)
  obtain ⟨𝔫, h𝔫⟩ := Ideal.dvd_iff_le.mpr (le_sup_right.trans h𝔭a)
  -- `𝔫` is not contained in `𝔪₀`, as `𝔭 ≠ 𝓞 K`.
  have h𝔫le : ¬ 𝔫 ≤ 𝔪.finitePart := fun hle ↦ by
    have h𝔫0 : 𝔫 ≠ 0 := fun h0 ↦ 𝔪.finitePart_ne_zero (by rw [h𝔫, h0, mul_zero])
    have h1 : 𝔭 * 𝔫 = 1 * 𝔫 := by
      rw [one_mul]
      exact le_antisymm Ideal.mul_le_right (h𝔫 ▸ hle)
    exact h𝔭.ne_top (by rw [← Ideal.one_eq_top]; exact mul_right_cancel₀ h𝔫0 h1)
  -- Hence the residue character is nontrivial on some residue unit `u ≡ 1 mod 𝔫`.
  obtain ⟨u, hu, hu1, hχu⟩ : ∃ u : 𝓞 K, IsUnit (Ideal.Quotient.mk 𝔪.finitePart u) ∧
      u - 1 ∈ 𝔫 ∧ χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart u) ≠ 1 := by
    by_contra! hall
    exact h𝔫le (hχ ▸ Ideal.dvd_iff_le.mp
      ((χ.finiteConductor_dvd_iff_residueCharacter_eq_one 𝔫).mpr hall))
  refine MulChar.gaussSum_mulShift_eq_zero_of_mul_sub_one_eq_zero _ _ (u := hu.unit) ?_
    (by rwa [hu.unit_spec])
  rw [hu.unit_spec, ← map_one (Ideal.Quotient.mk 𝔪.finitePart), ← map_sub, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, h𝔫]
  exact Ideal.mul_mem_mul (h𝔭a (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))) hu1

/-- **The absolute value of the Gauss sum**: for a presentation at the finite conductor of its
Hecke character, and `y` such that the integral ideal `y 𝔪₀ 𝔡` is prime to `𝔪₀`, `𝔡` the
different of `K`, `|τ(χ, y)| = √N(𝔪₀)`. -/
theorem norm_gaussSum (χ : Grossencharacter K 𝔪)
    (hχ : χ.toHeckeCharacter.finiteConductor = 𝔪.finitePart)
    {y : (FractionalIdeal.dual ℤ ℚ (𝔪.finitePart : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)}
    (hy : FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) * 𝔪.finitePart *
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) + 𝔪.finitePart = 1) :
    ‖χ.gaussSum y‖ = √(Ideal.absNorm 𝔪.finitePart) := by
  rw [gaussSum_def, TauCeti.norm_gaussSum_of_forall_mulShift (fun b ↦ ?_)
    (Ideal.isPrimitive_traceAddChar hy), Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_eq_fintype_card]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.traceAddChar_smul, ← gaussSum_def, ← gaussSum_def, gaussSum_smul χ hχ,
    starRingEnd_apply, MulChar.star_apply']

end TauCeti.LFunctions.Grossencharacter
