/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
public import TauCeti.KnotTheory.Markov
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Jones representation of the braid group

For a unit `a : Rˣ`, set the Temperley-Lieb loop value to
`δ = -(a ^ 2 + a⁻¹ ^ 2)`. The Kauffman-bracket assignment

`σ i ↦ a • 1 + a⁻¹ • e i`

satisfies the braid relations and defines `TauCeti.TemperleyLieb.jones`, a representation of
`TauCeti.BraidGroup n` in the units of `TemperleyLieb R δ n`. At this loop value the
coefficient-swapped element `a⁻¹ • 1 + a • e i` is the inverse of the assigned crossing.
Composing this representation with the Markov trace `TauCeti.TemperleyLieb.markovTrace` of the
Temperley-Lieb algebra, at `q = a ^ 2`, is the braid route to the Jones polynomial. For a braid `b`
on `n + 1` strands with exponent sum `w`, `TauCeti.MarkovBraid.jonesTrace` is the writhe-normalized
trace `(-a ^ 3) ^ (-w) * tr (jones b)`. The trace property makes it invariant under conjugation.
Under stabilization the new crossing `a • 1 + a⁻¹ • e` contributes `a * δ + a⁻¹ = -a ^ 3` to the
trace, by the two compatibilities of the Markov trace with adding a strand, and the writhe
normalization absorbs this factor; the negative crossing contributes `-a⁻¹ ^ 3` in the same way.
So `jonesTrace` is constant along Markov equivalence (`TauCeti.MarkovEquiv.jonesTrace_eq`); by
Markov's theorem, which is not formalized, it is an invariant of the closed braid as an oriented
link. With the normalization `tr 1 = δ ^ (n + 1)` of the Markov trace, the closure of the trivial
one-strand braid, the unknot, has value `δ`, and the closure of `σ₀ ^ 3`, the right-handed trefoil,
has value `δ * (A⁻⁴ + A⁻¹² - A⁻¹⁶)` at `a = A`. This is `δ` times the writhe-normalized Kauffman
bracket `TauCeti.normalizedKauffmanBracket_rightHandedTrefoilPDCode` of a PD-code of the trefoil, so
the braid route and the diagram route agree on it.

## Main definitions

* `TauCeti.TemperleyLieb.jonesDelta`: the loop value `-(a ^ 2 + a⁻¹ ^ 2)`.
* `TauCeti.TemperleyLieb.jonesUnit`: the Kauffman-bracket expansion of one crossing as a unit.
* `TauCeti.TemperleyLieb.jones`: the Jones representation
  `BraidGroup n →* (TemperleyLieb R (jonesDelta a) n)ˣ`.
* `TauCeti.MarkovBraid.jonesTrace`: the writhe-normalized Markov trace of the Jones
  representation of a braid.

## Main results

* `TauCeti.TemperleyLieb.jonesDelta_inv`: the loop value is unchanged by inverting the unit.
* `TauCeti.TemperleyLieb.mul_jonesDelta_add_inv` and `TauCeti.TemperleyLieb.inv_mul_jonesDelta_add`:
  closing up the two smoothings of a positive or negative crossing on a new strand multiplies by
  `-a ^ 3` or by its inverse, the identities behind invariance under stabilization.
* `TauCeti.TemperleyLieb.jones_sigma`: the representation sends `sigma i` to `jonesUnit a i`.
* `TauCeti.TemperleyLieb.jonesUnit_mul_jonesUnit_comm`: units for disjoint crossings satisfy the
  distant-generator braid relation.
* `TauCeti.TemperleyLieb.jonesUnit_braid`: units for adjacent crossings satisfy the braid relation
  corresponding to the third Reidemeister move.
* `TauCeti.TemperleyLieb.jones_sigma_ne_one_two`: the representation is nontrivial on two
  strands over a nontrivial base ring.
* `TauCeti.TemperleyLieb.jones_strandIncl`: the representation commutes with adding a strand.
* `TauCeti.MarkovEquiv.jonesTrace_eq`: the writhe-normalized trace is a Markov invariant.
* `TauCeti.MarkovBraid.jonesTrace_one_strand` and `TauCeti.MarkovBraid.jonesTrace_sigma_pow_three`:
  its values on the unknot and the trefoil braids.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103-111.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the Kauffman bracket and Jones polynomial).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335-388 (the link invariant from the Markov trace).
-/

public section

namespace TauCeti.TemperleyLieb

variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}

/-- The loop value `-(a ^ 2 + a⁻¹ ^ 2)` at which the Jones representation is defined. -/
def jonesDelta (a : Rˣ) : R := -((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)

/-- The defining equation of the Jones loop value. -/
@[simp]
theorem jonesDelta_def (a : Rˣ) :
    jonesDelta a = -((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) := (rfl)

/-- The Jones loop value is symmetric in `a` and `a⁻¹`, which is what lets the two coefficients
of a crossing be swapped. -/
theorem jonesDelta_eq_neg_inv_sq_add_sq (a : Rˣ) :
    jonesDelta a = -((((a⁻¹ : Rˣ) : R)) ^ 2 + (a : R) ^ 2) := by
  rw [jonesDelta_def]
  ring

/-- The Jones loop value is unchanged by inverting the unit. -/
theorem jonesDelta_inv (a : Rˣ) : jonesDelta a⁻¹ = jonesDelta a := by
  rw [jonesDelta_def, inv_inv, ← jonesDelta_eq_neg_inv_sq_add_sq]

/-- The Kauffman-bracket expansion of an elementary braid, as a unit of the Temperley-Lieb
algebra: `a • 1 + a⁻¹ • e i`, with inverse `a⁻¹ • 1 + a • e i`. -/
def jonesUnit (a : Rˣ) (i : Fin (n - 1)) : (TemperleyLieb R (jonesDelta a) n)ˣ where
  val := crossing (jonesDelta a) (a : R) ((a⁻¹ : Rˣ) : R) i
  inv := crossing (jonesDelta a) ((a⁻¹ : Rˣ) : R) (a : R) i
  val_inv := crossing_mul_crossing_swap_eq_one a.mul_inv (jonesDelta_def a) i
  inv_val := crossing_mul_crossing_swap_eq_one a.inv_mul (jonesDelta_eq_neg_inv_sq_add_sq a) i

/-- The value of the Kauffman-bracket unit. -/
@[simp]
theorem jonesUnit_val (a : Rˣ) (i : Fin (n - 1)) :
    ((jonesUnit a i : (TemperleyLieb R (jonesDelta a) n)ˣ) : TemperleyLieb R (jonesDelta a) n)
      = crossing (jonesDelta a) (a : R) ((a⁻¹ : Rˣ) : R) i := (rfl)

/-- The value of the inverse of the Kauffman-bracket unit. -/
@[simp]
theorem jonesUnit_inv_val (a : Rˣ) (i : Fin (n - 1)) :
    (((jonesUnit a i : (TemperleyLieb R (jonesDelta a) n)ˣ)⁻¹ :
        (TemperleyLieb R (jonesDelta a) n)ˣ) : TemperleyLieb R (jonesDelta a) n)
      = crossing (jonesDelta a) ((a⁻¹ : Rˣ) : R) (a : R) i := (rfl)

private theorem jones_braid_coeff (a : Rˣ) :
    ((a⁻¹ : Rˣ) : R) * ((a : R) ^ 2 + (a : R) * ((a⁻¹ : Rˣ) : R) * jonesDelta a
      + ((a⁻¹ : Rˣ) : R) ^ 2) = 0 := by
  rw [jonesDelta_def]
  linear_combination
    (-((a⁻¹ : Rˣ) : R) * ((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) * a.mul_inv

variable (n) in
/-- The Jones representation of the braid group in the units of the Temperley-Lieb algebra: the
elementary braid `σ i` goes to the Kauffman-bracket expansion `a • 1 + a⁻¹ • e i` of a crossing.
Composing it with the Markov trace is the braid route to the Jones polynomial. -/
def jones (a : Rˣ) : BraidGroup n →* (TemperleyLieb R (jonesDelta a) n)ˣ :=
  BraidGroup.lift (fun i => jonesUnit a i)
    (fun h => Units.ext <| by
      simp only [Units.val_mul, jonesUnit_val]
      exact crossing_mul_crossing_comm _ _ _ _ h)
    (fun h => Units.ext <| by
      simp only [Units.val_mul, jonesUnit_val]
      exact crossing_braid (jones_braid_coeff a) h)

/-- The Jones representation takes an elementary braid to the Kauffman-bracket unit. -/
@[simp]
theorem jones_sigma (a : Rˣ) (i : Fin (n - 1)) :
    jones n a (BraidGroup.sigma i) = jonesUnit a i :=
  BraidGroup.lift_sigma _ _ _ i

/-- Jones units on disjoint pairs of strands commute, the distant-generator braid relation. -/
theorem jonesUnit_mul_jonesUnit_comm (a : Rˣ) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    jonesUnit a i * jonesUnit a j = jonesUnit a j * jonesUnit a i := by
  simpa only [map_mul, jones_sigma] using
    congrArg (jones n a) (BraidGroup.sigma_mul_sigma_comm h)

/-- Jones units on adjacent pairs of strands satisfy the braid relation corresponding to the third
Reidemeister move. -/
theorem jonesUnit_braid (a : Rˣ) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    jonesUnit a i * jonesUnit a j * jonesUnit a i =
      jonesUnit a j * jonesUnit a i * jonesUnit a j := by
  simpa only [map_mul, jones_sigma] using congrArg (jones n a) (BraidGroup.sigma_braid h)

/-- The Jones representation of the two-strand braid group is nontrivial: the elementary braid
does not go to the identity. -/
theorem jones_sigma_ne_one_two [Nontrivial R] (a : Rˣ) (i : Fin (2 - 1)) :
    jones 2 a (BraidGroup.sigma i) ≠ 1 := by
  intro h
  have hval : (a : R) • (1 : TemperleyLieb R (jonesDelta a) 2)
      + ((a⁻¹ : Rˣ) : R) • e (jonesDelta a) i = 1 := by
    rw [← crossing_def, ← jonesUnit_val, ← jones_sigma, h, Units.val_one]
  have hone : (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  have hmat := congrArg (fun x => twoStrandRep (jonesDelta a) x 1 0) hval
  simp [hone] at hmat

/-- The Jones loop value is `-(q + q⁻¹)` for the unit `q = a ^ 2`, the form in which the Markov
trace `TauCeti.TemperleyLieb.markovTrace` is built. -/
theorem jonesDelta_eq_neg_sq_add_inv_sq (a : Rˣ) :
    jonesDelta a = -((↑(a ^ 2) : R) + ((a ^ 2)⁻¹ : Rˣ)) := by
  simp

/-- The two smoothings of a positive crossing on a new strand, closed up by the Markov trace,
contribute `a * δ + a⁻¹ = -a ^ 3`. -/
theorem mul_jonesDelta_add_inv (a : Rˣ) :
    (a : R) * jonesDelta a + ((a⁻¹ : Rˣ) : R) = ((-a ^ 3 : Rˣ) : R) := by
  simp only [jonesDelta_def, Units.val_neg, Units.val_pow_eq_pow_val]
  linear_combination (-((a⁻¹ : Rˣ) : R)) * a.mul_inv

/-- The two smoothings of a negative crossing on a new strand, closed up by the Markov trace,
contribute `a⁻¹ * δ + a = -a⁻¹ ^ 3`. -/
theorem inv_mul_jonesDelta_add (a : Rˣ) :
    ((a⁻¹ : Rˣ) : R) * jonesDelta a + (a : R) = ((-a ^ 3 : Rˣ)⁻¹ : Rˣ) := by
  have h := mul_jonesDelta_add_inv a⁻¹
  rw [jonesDelta_inv, inv_inv] at h
  rw [h, inv_neg, inv_pow]

/-- Adding a straight last strand commutes with the Jones representation: the braid with an added
uncrossed strand goes to the image of its Jones representative under
`TauCeti.TemperleyLieb.strandIncl`. -/
@[simp]
theorem jones_strandIncl (a : Rˣ) (b : BraidGroup (n + 1)) :
    (jones (n + 2) a (BraidGroup.strandIncl b) : TemperleyLieb R (jonesDelta a) (n + 2)) =
      strandIncl (jones (n + 1) a b : TemperleyLieb R (jonesDelta a) (n + 1)) := by
  have h : (jones (n + 2) a).comp BraidGroup.strandIncl =
      (Units.map (strandIncl : TemperleyLieb R (jonesDelta a) (n + 1) →ₐ[R] _).toMonoidHom).comp
        (jones (n + 1) a) :=
    BraidGroup.hom_ext fun i ↦ Units.ext <| by simp
  exact congrArg Units.val (DFunLike.congr_fun h b)

end TauCeti.TemperleyLieb

namespace TauCeti.MarkovBraid

open TemperleyLieb

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The writhe-normalized Markov trace of the Jones representation of a braid: for a braid `b` on
`n + 1` strands with exponent sum `w` it is `(-a ^ 3) ^ (-w) * tr (jones b)`, where `tr` is the
Markov trace `TauCeti.TemperleyLieb.markovTrace` at `q = a ^ 2`, normalized by `tr 1 = δ ^ (n + 1)`.
It is a Markov invariant (`TauCeti.MarkovEquiv.jonesTrace_eq`), and the unknot braid has value `δ`
(`TauCeti.MarkovBraid.jonesTrace_one_strand`). -/
def jonesTrace (β : MarkovBraid) (a : Rˣ) : R :=
  (((-a ^ 3) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) : Rˣ) : R) *
    markovTrace (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
      (jones (β.predStrands + 1) a β.braid : TemperleyLieb R (jonesDelta a) (β.predStrands + 1))

/-- The writhe-normalized trace is the Markov trace of the Jones representative times the writhe
correction. -/
theorem jonesTrace_def (β : MarkovBraid) (a : Rˣ) :
    jonesTrace β a =
      (((-a ^ 3) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) : Rˣ) : R) *
        markovTrace (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
          (jones (β.predStrands + 1) a β.braid :
            TemperleyLieb R (jonesDelta a) (β.predStrands + 1)) := (rfl)

/-- **Markov move I leaves the writhe-normalized trace unchanged**, by the trace property. -/
theorem jonesTrace_conj (a : Rˣ) (b c : BraidGroup (n + 1)) :
    jonesTrace ⟨n, c * b * c⁻¹⟩ a = jonesTrace (R := R) ⟨n, b⟩ a := by
  simp only [jonesTrace_def, map_mul, map_inv, Units.val_mul]
  rw [markovTrace_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mul, mul_comm (ArtinGroup.exponentSum _ c), mul_assoc, mul_inv_cancel, mul_one]

/-- The Markov trace of the Jones representation after adding a strand and crossing it once with
the previous one: the two smoothings of the new crossing contribute `a * δ` and `a⁻¹`. -/
private theorem markovTrace_jones_strandIncl_mul (a : Rˣ) (b : BraidGroup (n + 1))
    (c : BraidGroup (n + 2)) (x y : R)
    (hc : (jones (n + 2) a c : TemperleyLieb R (jonesDelta a) (n + 2)) =
      crossing (jonesDelta a) x y (Fin.last n)) :
    markovTrace (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
        (jones (n + 2) a (BraidGroup.strandIncl b * c) :
          TemperleyLieb R (jonesDelta a) (n + 2)) =
      (x * jonesDelta a + y) * markovTrace (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
        (jones (n + 1) a b : TemperleyLieb R (jonesDelta a) (n + 1)) := by
  rw [map_mul, Units.val_mul, jones_strandIncl, hc, crossing_def, mul_add, mul_smul_comm,
    mul_smul_comm, mul_one, map_add, map_smul, map_smul, markovTrace_strandIncl,
    markovTrace_strandIncl_mul_e_last, smul_eq_mul, smul_eq_mul]
  ring

/-- **Positive stabilization leaves the writhe-normalized trace unchanged.** The new crossing
multiplies the trace by `-a ^ 3` and raises the exponent sum by one. -/
theorem jonesTrace_stabilize (a : Rˣ) (b : BraidGroup (n + 1)) :
    jonesTrace ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ a =
      jonesTrace (R := R) ⟨n, b⟩ a := by
  rw [jonesTrace_def, jonesTrace_def, markovTrace_jones_strandIncl_mul a b _ _ _
    (by rw [jones_sigma, jonesUnit_val])]
  simp only [map_mul, BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_ofAdd, neg_add, zpow_add, zpow_neg_one, Units.val_mul]
  rw [mul_jonesDelta_add_inv, mul_assoc _ _ (_ * _), ← mul_assoc _ (((-a ^ 3 : Rˣ) : R)),
    Units.inv_mul, one_mul]

/-- **Negative stabilization leaves the writhe-normalized trace unchanged.** The new crossing
multiplies the trace by `-a⁻¹ ^ 3` and lowers the exponent sum by one. -/
theorem jonesTrace_stabilizeInv (a : Rˣ) (b : BraidGroup (n + 1)) :
    jonesTrace ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ a =
      jonesTrace (R := R) ⟨n, b⟩ a := by
  rw [jonesTrace_def, jonesTrace_def, markovTrace_jones_strandIncl_mul a b _ _ _
    (by rw [map_inv, jones_sigma, jonesUnit_inv_val])]
  simp only [map_mul, map_inv, BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, neg_add, neg_neg, zpow_add, zpow_one, Units.val_mul]
  rw [inv_mul_jonesDelta_add, mul_assoc _ _ (_ * _), ← mul_assoc (((-a ^ 3 : Rˣ) : R)),
    Units.mul_inv, one_mul]

/-- On one strand the only braid is trivial, and its closure, the unknot, has writhe-normalized
trace `δ`. -/
@[simp]
theorem jonesTrace_one_strand (a : Rˣ) (b : BraidGroup 1) :
    jonesTrace (R := R) ⟨0, b⟩ a = jonesDelta a := by
  have hb : b = 1 := by
    have h : MonoidHom.id (BraidGroup 1) = 1 := BraidGroup.hom_ext fun i ↦ i.elim0
    exact DFunLike.congr_fun h b
  subst hb
  rw [jonesTrace_def]
  simp [markovTrace_one]

/-- **The trefoil.** The closure of `σ₀ ^ 3` on two strands is the right-handed trefoil, and its
writhe-normalized trace is `δ * (a⁻⁴ + a⁻¹² - a⁻¹⁶)`: `δ` times the writhe-normalized Kauffman
bracket of the trefoil computed from a PD-code in
`TauCeti.normalizedKauffmanBracket_rightHandedTrefoilPDCode`. -/
theorem jonesTrace_sigma_pow_three (a : Rˣ) :
    jonesTrace (R := R) ⟨1, BraidGroup.sigma 0 ^ 3⟩ a =
      jonesDelta a * (((a⁻¹ : Rˣ) : R) ^ 4 + ((a⁻¹ : Rˣ) : R) ^ 12 - ((a⁻¹ : Rˣ) : R) ^ 16) := by
  have he : markovTrace (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a)
      (e (jonesDelta a) 0 : TemperleyLieb R (jonesDelta a) 2) = jonesDelta a := by
    simpa [markovTrace_one] using
      markovTrace_strandIncl_mul_e_last (a ^ 2) (jonesDelta_eq_neg_sq_add_inv_sq a) (n := 0) 1
  have hx : (jones (1 + 1) a (BraidGroup.sigma 0 ^ 3) : TemperleyLieb R (jonesDelta a) 2) =
      ((a : R) ^ 3) • 1 + (3 * (a : R) ^ 2 * ((a⁻¹ : Rˣ) : R) +
        3 * (a : R) * ((a⁻¹ : Rˣ) : R) ^ 2 * jonesDelta a +
          ((a⁻¹ : Rˣ) : R) ^ 3 * jonesDelta a ^ 2) • e (jonesDelta a) 0 := by
    rw [map_pow, Units.val_pow_eq_pow_val, jones_sigma, jonesUnit_val, crossing_def]
    simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      mul_one, e_mul_self, smul_smul]
    module
  rw [jonesTrace_def, hx]
  simp only [map_add, map_smul, markovTrace_one, he, map_pow, BraidGroup.exponentSum_sigma,
    smul_eq_mul, toAdd_pow, toAdd_ofAdd]
  have hu : (((-a ^ 3) ^ (-(3 • 1 : ℤ)) : Rˣ) : R) = -((a⁻¹ : Rˣ) : R) ^ 9 := by
    have h3 : (-(3 • 1 : ℤ)) = -((3 : ℕ) : ℤ) := by norm_num
    rw [h3, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, inv_neg,
      Units.val_neg, ← inv_pow, Units.val_pow_eq_pow_val]
    ring
  rw [hu, jonesDelta_def]
  set b : R := ((a⁻¹ : Rˣ) : R)
  -- The two sides are polynomials in `a` and `b = a⁻¹` that agree modulo `a * b = 1`; the
  -- coefficient below is the quotient of their difference by `a * b - 1`.
  linear_combination (-b ^ 6 - b ^ 14 - (a : R) * b ^ 7 + 2 * (a : R) * b ^ 15 -
    (a : R) ^ 2 * b ^ 4 - (a : R) ^ 2 * b ^ 8 - 4 * (a : R) ^ 2 * b ^ 12 -
    (a : R) ^ 3 * b ^ 5 - (a : R) ^ 3 * b ^ 9 + 3 * (a : R) ^ 3 * b ^ 13 -
    (a : R) ^ 4 * b ^ 6 - 4 * (a : R) ^ 4 * b ^ 10 - (a : R) ^ 5 * b ^ 7 +
    (a : R) ^ 5 * b ^ 11 - (a : R) ^ 6 * b ^ 8) * a.mul_inv

end TauCeti.MarkovBraid

namespace TauCeti

open TemperleyLieb

variable {R : Type*} [CommRing R]

/-- A single Markov move does not change the writhe-normalized trace. -/
theorem IsMarkovMove.jonesTrace_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ) (a : Rˣ) :
    β.jonesTrace a = γ.jonesTrace (R := R) a := by
  induction h with
  | conj b c => exact MarkovBraid.jonesTrace_conj a b c
  | stabilize b => exact MarkovBraid.jonesTrace_stabilize a b
  | stabilizeInv b => exact MarkovBraid.jonesTrace_stabilizeInv a b

/-- **The writhe-normalized Markov trace of the Jones representation is a Markov invariant.** By
Markov's theorem this makes it an invariant of the oriented link obtained by closing the braid. -/
theorem MarkovEquiv.jonesTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) (a : Rˣ) :
    β.jonesTrace a = γ.jonesTrace (R := R) a :=
  h.induction (fun hmove ↦ hmove.jonesTrace_eq a) (fun _ ↦ rfl) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih')

end TauCeti
