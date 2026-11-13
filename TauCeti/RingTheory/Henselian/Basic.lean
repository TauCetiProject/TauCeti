/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ComputeDegree

/-!
# Henselian rings

This file gathers the basic consequences of Henselianity that Mathlib does not provide.

Mathlib has both halves of the comparison between `HenselianRing R I`, which lifts a simple root
over `R ⧸ I`, and `HenselianLocalRing R`, which lifts a simple root over the residue field, except
for the step that produces the local class from the ideal-theoretic one at `I = 𝔪`. So
`IsAdicComplete.henselianRing` never reaches `HenselianLocalRing`, and the Henselian API is
unavailable for a complete local ring such as the integers of a complete discretely valued field.

The step is short: the two differ only in their simplicity hypothesis, `IsUnit (f' a₀)` against
`IsUnit (Ideal.Quotient.mk 𝔪 (f' a₀))`, and over a local ring a unit maps to a unit.

`HenselianRing R J` lifts simple roots of monic polynomials only, but the monicity is not needed.
If `f(a₀) ∈ J` and `f'(a₀)` is a unit, write `f(a₀ + X) = c + u X + ⋯` with `c ∈ J` and `u` a unit,
of degree `n`. The substitution `X = c / U` turns it into `U⁻ⁿ c m(U)` for the monic polynomial
`m(U) = Uⁿ + ∑ fᵢ₊₁ cⁱ Uⁿ⁻¹⁻ⁱ`, whose reduction `Uⁿ⁻¹ (U + u)` has the simple root `-u`. A lift `U`
of that root is a unit because `J` lies in the Jacobson radical, and `a₀ + c / U` is the root
of `f`, with `a₀ + c / U ≡ a₀ mod J`.

The second half of the file extracts roots. Let `R` be a ring that is Henselian at an ideal `J`,
and let `n` be a natural number that is invertible in `R`. Then every element `w` congruent to `1`
modulo an ideal `I ≤ J` has an `n`-th root that is itself congruent to `1` modulo `I`.

This is the standard source of `n`-th roots of principal units away from the residue
characteristic: over the integer ring of a local field it shows that each positive-depth step of
the unit filtration is carried onto itself by the `n`-th power map.

Without assuming `2` invertible, every element of `1 + 4J` is a square. This supplies deep
square roots in residue characteristic two, by solving `t² + t = c` for `c ∈ J`.

Finally, for a monic quadratic whose discriminant is a unit, any root modulo `J` is
simple and lifts to a root in the ring; when it has a root modulo `J`, all its roots in a domain
algebra already lie in the ring.

## Main results

* `TauCeti.HenselianRing.henselianLocalRing`: a local ring that is Henselian at its maximal ideal
  is a Henselian local ring.
* `TauCeti.IsAdicComplete.henselianLocalRing`: a local ring that is complete for the adic topology
  of its maximal ideal is a Henselian local ring.
* `TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq`: a simple power root in the
  residue field lifts to a root with the same residue.
* `Polynomial.exists_isRoot_sub_mem`: Hensel's lemma for a polynomial
  that need not be monic, over any Henselian pair.
* `TauCeti.HenselianLocalRing.exists_conic_eq`: a smooth conic perturbed by a cubic in the
  maximal ideal lifts each solution of its residue equation to a solution over the ring.
* `TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem`: if `n` is invertible,
  `I ≤ J` and `w ≡ 1 mod I`, then `w = a ^ n` for some `a ≡ 1 mod I`.
* `TauCeti.HenselianRing.exists_quadratic_root_of_isUnit_discrim`: a root modulo `I` of a monic
  quadratic `X ^ 2 + b X + c` with unit discriminant lifts to a root in `R` with unit derivative.
* `TauCeti.HenselianRing.mem_range_algebraMap_of_isUnit_discrim`: when such a quadratic has a root
  modulo `I`, all its roots in domain `R`-algebras already lie in `R`.
* `TauCeti.HenselianRing.mem_range_algebraMap_of_sq_add_mul_add_eq_zero_of_isUnit`: its case `b` a
  unit and `c ∈ I`, where the root modulo `I` is `0`.

## Implementation notes

Hensel's lemma applied to `X ^ n - w` at the approximate root `1` produces a root `a` with
`a ≡ 1` modulo `J` only. The congruence is then sharpened to `I` through the factorization
`a ^ n - 1 = (1 + a + ⋯ + a ^ (n - 1)) * (a - 1)`, whose first factor reduces to `n` modulo `J`
and is therefore a unit, `J` lying in the Jacobson radical.
-/

public section

open Polynomial

namespace TauCeti

open IsLocalRing

/-- A local ring that is Henselian at its maximal ideal is a Henselian local ring. The two
hypotheses differ only in their simplicity condition, which asks the derivative to be a unit in the
residue field rather than in the ring, and over a local ring the image of a unit is a unit.

This is not an instance: Mathlib already registers the converse implication as one, so the pair
would form an instance cycle. -/
theorem HenselianRing.henselianLocalRing (R : Type*) [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] : HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _)

/-- A local ring that is complete for the adic topology of its maximal ideal is a Henselian local
ring. This is Mathlib's `IsAdicComplete.henselianRing` at `I = 𝔪`, read through
`TauCeti.HenselianRing.henselianLocalRing`. -/
instance IsAdicComplete.henselianLocalRing (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R :=
  HenselianRing.henselianLocalRing R

namespace HenselianLocalRing

/-- If `n` is a unit, a unit residue root of `X ^ n - u` lifts to a root with the same residue. -/
theorem exists_pow_eq_of_residue_pow_eq {R : Type*} [CommRing R] [HenselianLocalRing R]
    {n : ℕ} (hn : IsUnit (n : R)) {x₀ u : R} (hx₀ : IsUnit x₀)
    (h : residue R x₀ ^ n = residue R u) :
    ∃ x : R, x ^ n = u ∧ residue R x = residue R x₀ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have heval : (X ^ n - C u).eval x₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp [map_sub, map_pow, h]
  have hder : IsUnit ((X ^ n - C u).derivative.eval x₀) := by
    have hd : (X ^ n - C u).derivative.eval x₀ = (n : R) * x₀ ^ (n - 1) := by
      simp [derivative_X_pow]
    exact hd ▸ hn.mul (hx₀.pow _)
  obtain ⟨x, hx, hres⟩ := HenselianLocalRing.is_henselian _
    (monic_X_pow_sub_C u hn0) x₀ heval hder
  refine ⟨x, by simpa [sub_eq_zero] using hx, ?_⟩
  exact (Ideal.Quotient.eq).mpr hres

end HenselianLocalRing

end TauCeti

namespace Polynomial

/-- The substitution `X = c / U` behind Hensel's lemma without monicity: if `g` has degree `k + 1`
and constant coefficient `c`, and `V * U = 1`, then
`g(c V) U^(k+1) = c (U^(k+1) + ∑ᵢ gᵢ₊₁ cⁱ U^(k−i))`. -/
private theorem eval_mul_mul_pow_eq {R : Type*} [CommRing R] (g : R[X]) {k : ℕ}
    (hk : g.natDegree = k + 1) {U V : R} (hVU : V * U = 1) :
    g.eval (g.coeff 0 * V) * U ^ (k + 1) = g.coeff 0 * (X ^ (k + 1) +
      ∑ i ∈ Finset.range (k + 1), C (g.coeff (i + 1) * g.coeff 0 ^ i) * X ^ (k - i)).eval U := by
  rw [eval_eq_sum_range, hk, Finset.sum_range_succ']
  simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, pow_zero, mul_one,
    add_mul, Finset.sum_mul, mul_add, Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hik : U ^ (k + 1) = U ^ (k - i) * U ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hi
    omega
  rw [hik]
  calc g.coeff (i + 1) * (g.coeff 0 * V) ^ (i + 1) * (U ^ (k - i) * U ^ (i + 1))
      = g.coeff 0 * (g.coeff (i + 1) * g.coeff 0 ^ i * U ^ (k - i)) * (V * U) ^ (i + 1) := by ring
    _ = g.coeff 0 * (g.coeff (i + 1) * g.coeff 0 ^ i * U ^ (k - i)) := by
      rw [hVU, one_pow, mul_one]

/-- Hensel's lemma without monicity at the approximate root `0`: if the constant coefficient of
`g` lies in the Henselian ideal `J` and its linear coefficient is a unit, then `g` has a root
in `J`. -/
private theorem exists_mem_eval_eq_zero {R : Type*} [CommRing R] {J : Ideal R}
    [HenselianRing R J] (g : R[X]) (hcJ : g.coeff 0 ∈ J)
    (hu₁ : IsUnit (g.coeff 1)) : ∃ b ∈ J, g.eval b = 0 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨0, J.zero_mem, Subsingleton.elim _ _⟩
  have := _root_.isLocalHom_of_le_jacobson (HenselianRing.jac (R := R) (I := J))
  set c := g.coeff 0
  set u := g.coeff 1 with hu
  -- `g` is not constant, so its degree is `k + 1` for some `k`.
  obtain ⟨k, hk⟩ : ∃ k, g.natDegree = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 ↦ not_isUnit_zero (M₀ := R) ?_
    rwa [hu, coeff_eq_zero_of_natDegree_lt (by omega)] at hu₁
  -- Substituting `X = c / U` gives `U ^ (k + 1) * g (c / U) = c * m U` for the monic `m` below.
  set m : R[X] :=
    X ^ (k + 1) + ∑ i ∈ Finset.range (k + 1), C (g.coeff (i + 1) * c ^ i) * X ^ (k - i) with hm
  have hmonic : m.Monic := by
    refine monic_X_pow_add ((degree_sum_le _ _).trans_lt ?_)
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i _ ↦ ?_
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast (by omega : k - i < k + 1))
  -- The reduction of `m` is `X ^ k * (X + u)`, with the simple root `-u`.
  have hmap : m.map (Ideal.Quotient.mk J) = X ^ k * (X + C (Ideal.Quotient.mk J u)) := by
    have hc0 : Ideal.Quotient.mk J c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcJ
    simp [hm, Polynomial.map_sum, Finset.sum_range_succ', pow_succ, hc0, ← hu]
    ring
  obtain ⟨U, hU, hUu⟩ := HenselianRing.is_henselian (I := J) m hmonic (-u)
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← eval_map_apply, hmap]
      simp)
    (by
      rw [← eval_map_apply, ← derivative_map, hmap]
      simpa [derivative_mul, derivative_X_pow] using (hu₁.neg.map (Ideal.Quotient.mk J)).pow k)
  have hUunit : IsUnit U := by
    apply isUnit_of_map_unit (Ideal.Quotient.mk J)
    rw [Ideal.Quotient.eq.mpr hUu]
    exact hu₁.neg.map _
  set V := hUunit.unit⁻¹
  have hVU : (V : R) * U = 1 := hUunit.val_inv_mul
  have hkey : g.eval (c * V) * U ^ (k + 1) = c * m.eval U := eval_mul_mul_pow_eq g hk hVU
  refine ⟨c * V, J.mul_mem_right _ hcJ, ?_⟩
  rw [hU.eq_zero, mul_zero] at hkey
  exact ((hUunit.pow (k + 1)).mul_left_eq_zero).1 hkey

/-- **Hensel's lemma without monicity.** Over a Henselian pair `(R, J)`, a simple root of a
polynomial modulo `J` lifts to a root with the same image in `R ⧸ J`, whether or not the polynomial
is monic. -/
theorem exists_isRoot_sub_mem {R : Type*} [CommRing R] {J : Ideal R} [HenselianRing R J]
    (f : R[X]) {a₀ : R} (h₁ : f.eval a₀ ∈ J)
    (h₂ : IsUnit (Ideal.Quotient.mk J (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ J := by
  have := _root_.isLocalHom_of_le_jacobson (HenselianRing.jac (R := R) (I := J))
  -- Translate the approximate root to `0`.
  set g := f.comp (X + C a₀) with hg
  have hc : g.coeff 0 ∈ J := by simpa [hg, coeff_zero_eq_eval_zero] using h₁
  have hu : IsUnit (g.coeff 1) := by
    simpa only [hg, ← taylor_apply, taylor_coeff_one] using
      isUnit_of_map_unit (Ideal.Quotient.mk J) _ h₂
  obtain ⟨b, hb, hgb⟩ := exists_mem_eval_eq_zero g hc hu
  refine ⟨b + a₀, by simpa [IsRoot, hg, eval_comp] using hgb, by rwa [add_sub_cancel_right]⟩

end Polynomial

namespace TauCeti.HenselianLocalRing

open IsLocalRing

/-- Over a Henselian local ring, suppose `a₁² + 4 a₂` and `A` are units and `z ∈ 𝔪`.
Every solution of `Y² + a₁ X Y − a₂ X² − z X³ = A` modulo `𝔪` lifts to a solution in the ring
with the same residues in both coordinates. -/
theorem exists_conic_eq {R : Type*} [CommRing R] [HenselianLocalRing R]
    {a₁ a₂ z A X₀ Y₀ : R} (hb₂ : IsUnit (a₁ ^ 2 + 4 * a₂)) (hz : z ∈ maximalIdeal R)
    (hA : IsUnit A) (h₀ : Y₀ ^ 2 + a₁ * X₀ * Y₀ - a₂ * X₀ ^ 2 - z * X₀ ^ 3 - A ∈ maximalIdeal R) :
    ∃ X Y : R, Y ^ 2 + a₁ * X * Y - a₂ * X ^ 2 - z * X ^ 3 - A = 0 ∧
      X - X₀ ∈ maximalIdeal R ∧ Y - Y₀ ∈ maximalIdeal R := by
  by_cases hY : IsUnit (2 * Y₀ + a₁ * X₀)
  · -- Hensel's lemma in `Y`
    obtain ⟨Y, hY', hYY₀⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R)
      (X ^ 2 + C (a₁ * X₀) * X - C (a₂ * X₀ ^ 2 + z * X₀ ^ 3 + A)) (a₀ := Y₀)
      (by convert h₀ using 1; simp; ring) (by
        convert hY.map (Ideal.Quotient.mk (maximalIdeal R)) using 1
        simp [derivative_pow])
    refine ⟨X₀, Y, ?_, by simp, hYY₀⟩
    linear_combination (by simpa using hY'.eq_zero :
      Y ^ 2 + a₁ * X₀ * Y - (a₂ * X₀ ^ 2 + z * X₀ ^ 3 + A) = 0)
  · -- otherwise `∂/∂X` is a unit, since both partials in `𝔪` would force `X₀, Y₀, A ∈ 𝔪`
    have hX : IsUnit (-3 * z * X₀ ^ 2 - 2 * a₂ * X₀ + a₁ * Y₀) := by
      by_contra hX
      rw [← residue_ne_zero_iff_isUnit] at hb₂ hA
      rw [← residue_ne_zero_iff_isUnit, not_not] at hY hX
      have hz0 := (residue_eq_zero_iff _).2 hz
      have h00 := (residue_eq_zero_iff _).2 h₀
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat] at hb₂ hY hX h00
      have hX₀ : residue R X₀ = 0 := by
        refine (mul_eq_zero.1 ?_).resolve_left hb₂
        linear_combination residue R a₁ * hY - 2 * hX - 6 * residue R X₀ ^ 2 * hz0
      have hY₀ : residue R Y₀ = 0 := by
        refine (mul_eq_zero.1 ?_).resolve_left hb₂
        linear_combination 2 * residue R a₂ * hY + residue R a₁ * hX +
          3 * residue R a₁ * residue R X₀ ^ 2 * hz0
      exact hA (by rw [hX₀, hY₀, hz0] at h00; linear_combination -h00)
    obtain ⟨X', hX', hXX₀⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R)
      (-C z * X ^ 3 - C a₂ * X ^ 2 + C (a₁ * Y₀) * X + C (Y₀ ^ 2 - A)) (a₀ := X₀)
      (by convert h₀ using 1; simp; ring) (by
        convert hX.map (Ideal.Quotient.mk (maximalIdeal R)) using 1
        congr 1
        simp [derivative_pow]
        ring)
    refine ⟨X', Y₀, ?_, hXX₀, by simp⟩
    linear_combination (by simpa using hX'.eq_zero :
      -(z * X' ^ 3) - a₂ * X' ^ 2 + a₁ * Y₀ * X' + (Y₀ ^ 2 - A) = 0)

end TauCeti.HenselianLocalRing

namespace TauCeti

namespace HenselianRing

variable {R : Type*} [CommRing R]

/-- In a ring Henselian at an ideal `J`, if `n` is invertible then every element congruent to `1`
modulo an ideal `I ≤ J` is the `n`-th power of an element congruent to `1` modulo `I`. -/
theorem exists_pow_eq_and_sub_one_mem_of_sub_one_mem {I J : Ideal R} [HenselianRing R J]
    (hI : I ≤ J) {n : ℕ} (hn : IsUnit (n : R)) {w : R} (hw : w - 1 ∈ I) :
    ∃ a : R, a ^ n = w ∧ a - 1 ∈ I := by
  -- Over the zero ring `IsUnit (n : R)` says nothing, so `n = 0` is not excluded there.
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨1, Subsingleton.elim _ _, by simp⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have heval : (X ^ n - C w).eval (1 : R) ∈ J := by
    simpa using J.neg_mem_iff.mpr (hI hw)
  obtain ⟨a, ha, ha1⟩ := HenselianRing.is_henselian (X ^ n - C w)
    (monic_X_pow_sub_C w hn0) 1 heval
    (by simpa [derivative_X_pow] using hn.map (Ideal.Quotient.mk J))
  have hpow : a ^ n = w := by simpa [sub_eq_zero] using ha
  refine ⟨a, hpow, ?_⟩
  -- The geometric sum `1 + a + ⋯ + a ^ (n - 1)` reduces to `n` modulo `J`, hence is a unit.
  have ha_quot : Ideal.Quotient.mk J a = 1 := by
    rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    exact ha1
  have := _root_.isLocalHom_of_le_jacobson (HenselianRing.jac (R := R) (I := J))
  have hunit : IsUnit (∑ j ∈ Finset.range n, a ^ j) :=
    isUnit_of_map_unit (Ideal.Quotient.mk J) _
      (by simpa [ha_quot] using hn.map (Ideal.Quotient.mk J))
  obtain ⟨u, hu⟩ := hunit
  have hsub : a - 1 = ↑u⁻¹ * (w - 1) := by
    rw [← hpow, ← geom_sum_mul, ← hu, Units.inv_mul_cancel_left]
  rw [hsub]
  exact I.mul_mem_left _ hw

/-- In a ring Henselian at `J`, an element `c ∈ J` has the form `t² + t` for some `t ∈ J`.
This is the simple-root form of Hensel's lemma that also works in residue characteristic two. -/
theorem exists_sq_add_eq_of_mem {J : Ideal R} [HenselianRing R J] {c : R} (hc : c ∈ J) :
    ∃ t ∈ J, t ^ 2 + t = c := by
  obtain ⟨t, ht, htJ⟩ := HenselianRing.is_henselian (X ^ 2 + X - C c)
    (by
      rw [add_sub_assoc]
      exact monic_X_pow_add (lt_of_le_of_lt (degree_X_sub_C_le c) (by decide)))
    0 (by simpa using J.neg_mem hc) (by simp)
  exact ⟨t, by simpa using htJ, by simpa [sub_eq_zero] using ht⟩

/-- In a ring Henselian at `J`, every element of `1 + 4J` is a square. No invertibility
assumption on `2` in the ring or its residue rings is needed. -/
theorem isSquare_one_add_four_mul_of_mem {J : Ideal R} [HenselianRing R J]
    {c : R} (hc : c ∈ J) : IsSquare (1 + 4 * c) := by
  obtain ⟨t, -, ht⟩ := exists_sq_add_eq_of_mem hc
  refine ⟨1 + 2 * t, ?_⟩
  rw [← ht]
  ring

end HenselianRing

end TauCeti

namespace TauCeti.HenselianRing

/-- A root modulo `I` of a monic quadratic `X ^ 2 + b X + c` over a ring Henselian along `I`
lifts to a root in `R` when the discriminant `b ^ 2 - 4 c` is a unit: the root is simple, since
`(2 t + b) ^ 2` is the discriminant modulo `I`. The lift has unit derivative `2 s + b`. -/
theorem exists_quadratic_root_of_isUnit_discrim {R : Type*} [CommRing R] {I : Ideal R}
    [HenselianRing R I] {b c t : R} (hd : IsUnit (b ^ 2 - 4 * c))
    (ht : t ^ 2 + b * t + c ∈ I) :
    ∃ s : R, s ^ 2 + b * s + c = 0 ∧ s - t ∈ I ∧ IsUnit (2 * s + b) := by
  have hu : IsUnit (Ideal.Quotient.mk I (2 * t + b)) := by
    have h0 : Ideal.Quotient.mk I (t ^ 2 + b * t + c) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ht
    simp only [map_add, map_mul, map_pow] at h0
    have key := discrim_eq_sq_of_quadratic_eq_zero (a := (1 : R ⧸ I)) (b := Ideal.Quotient.mk I b)
      (c := Ideal.Quotient.mk I c) (x := Ideal.Quotient.mk I t) (by linear_combination h0)
    refine (isUnit_pow_iff two_ne_zero).1 ?_
    rw [map_add, map_mul, map_ofNat, ← mul_one (2 : R ⧸ I), ← key]
    have := hd.map (Ideal.Quotient.mk I)
    simp only [map_sub, map_mul, map_pow, map_ofNat] at this
    simpa [discrim] using this
  let f : R[X] := X ^ 2 + C b * X + C c
  have hmon : f.Monic := by
    dsimp [f]
    monicity!
  have hf₀ : f.eval t ∈ I := by simpa [f] using ht
  have hder : f.derivative.eval t = 2 * t + b := by
    simp [f, one_add_one_eq_two]
  obtain ⟨s, hs, hst⟩ := HenselianRing.is_henselian f hmon t hf₀ (by rwa [hder])
  refine ⟨s, by simpa [f] using hs.eq_zero, hst, ?_⟩
  have := _root_.isLocalHom_of_le_jacobson (HenselianRing.jac (R := R) (I := I))
  refine IsUnit.of_map (Ideal.Quotient.mk I) _ ?_
  have hmk : Ideal.Quotient.mk I s = Ideal.Quotient.mk I t := (Ideal.Quotient.eq.2 hst).symm ▸ rfl
  simpa [hmk] using hu

/-- A root, in an `R`-algebra without zero divisors, of `X ^ 2 + b X + c` already lies in `R`
when the Henselian ring `R` has a root `t` of the quadratic modulo `I` and the discriminant
`b ^ 2 - 4 c` is a unit: Hensel's lemma lifts `t` to a root `s ∈ R`, and then
`(x - s) (x + s + b) = 0`. -/
theorem mem_range_algebraMap_of_isUnit_discrim {R S : Type*} [CommRing R] {I : Ideal R}
    [HenselianRing R I] [CommRing S] [NoZeroDivisors S] [Algebra R S] {b c t : R}
    (hd : IsUnit (b ^ 2 - 4 * c)) (ht : t ^ 2 + b * t + c ∈ I) {x : S}
    (hx : x ^ 2 + algebraMap R S b * x + algebraMap R S c = 0) :
    x ∈ Set.range (algebraMap R S) := by
  obtain ⟨s, hs, -⟩ := exists_quadratic_root_of_isUnit_discrim hd ht
  have hs' : algebraMap R S s ^ 2 + algebraMap R S b * algebraMap R S s +
      algebraMap R S c = 0 := by
    simpa using congrArg (algebraMap R S) hs
  have hfac : (x - algebraMap R S s) * (x + algebraMap R S s + algebraMap R S b) = 0 := by
    linear_combination hx - hs'
  rcases mul_eq_zero.mp hfac with h | h
  · exact ⟨s, (sub_eq_zero.mp h).symm⟩
  · exact ⟨-s - b, by simp only [map_sub, map_neg]; linear_combination -h⟩

/-- A root, in an `R`-algebra without zero divisors, of `X ^ 2 + b X + c` with `b` a unit and
`c ∈ I` already lies in the Henselian ring `R`: the reduction `X (X + b)` has the simple
root `0`. -/
theorem mem_range_algebraMap_of_sq_add_mul_add_eq_zero_of_isUnit {R S : Type*} [CommRing R]
    {I : Ideal R} [HenselianRing R I] [CommRing S] [NoZeroDivisors S] [Algebra R S] {b c : R}
    (hb : IsUnit b) (hc : c ∈ I) {x : S}
    (hx : x ^ 2 + algebraMap R S b * x + algebraMap R S c = 0) :
    x ∈ Set.range (algebraMap R S) := by
  have := _root_.isLocalHom_of_le_jacobson (HenselianRing.jac (R := R) (I := I))
  refine mem_range_algebraMap_of_isUnit_discrim (t := 0) ?_ (by simpa using hc) hx
  refine IsUnit.of_map (Ideal.Quotient.mk I) _ ?_
  simpa [Ideal.Quotient.eq_zero_iff_mem.2 hc] using (hb.map (Ideal.Quotient.mk I)).pow 2

end TauCeti.HenselianRing
