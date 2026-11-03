/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.CrossingInsertion
public import TauCeti.KnotTheory.BraidWord.StrandIncl
public import TauCeti.KnotTheory.Markov.Closure
public import TauCeti.KnotTheory.Markov.Skein
public import TauCeti.KnotTheory.TemperleyLieb
import Mathlib.Tactic.LinearCombination
import TauCeti.KnotTheory.BraidWord.FreeCancellation.Closure

/-!
# The two routes to the Jones polynomial of a closed braid agree

The Jones polynomial of a closed braid can be computed in two ways. The diagram route closes a
braid word to an oriented PD-code (`TauCeti.BraidWord.closure`) and takes the writhe-normalized
Kauffman bracket of the diagram, a state sum over its smoothings. The braid route sends the braid to
the Temperley–Lieb algebra by the Jones representation and takes the writhe-normalized Markov trace
`TauCeti.MarkovBraid.jonesTrace`. This file proves that they agree: for every braid word `w`, the
trace of the braid `w` represents is `δ` times the normalized bracket of the closure of `w`, where
`δ = -(A² + A⁻²)` is the loop value (`TauCeti.BraidWord.jonesTrace_toBraid`). The factor `δ` is
the difference of normalizations: the bracket gives the unknot the value `1`, the Markov trace the
value `δ`. In terms of the Jones polynomial, the trace is `δ` times the Jones polynomial of the
closure evaluated at `t ^ (1/2) = A⁻²`
(`TauCeti.BraidWord.jonesTrace_toBraid_eq_eval₂_jonesPolynomial`); only when `δ` is invertible
does this say that the evaluated Jones polynomial is the trace divided by `δ`.

The proof is the uniqueness of skein invariants, `TauCeti.MarkovBraid.eq_of_skein`. Both sides are
Markov invariants. The trace is one by `TauCeti.MarkovEquiv.jonesTrace_eq`; the bracket of the
closure is one since closures of Markov-equivalent braids are Reidemeister equivalent
(`TauCeti.MarkovEquiv.reidemeisterEquiv_closure`). Both satisfy the skein relation
`A⁴ V(σᵢ c) - A⁻⁴ V(σᵢ⁻¹ c) = (A⁻² - A²) V(c)`: the trace by `TauCeti.MarkovBraid.jonesTrace_skein`,
and the bracket by `TauCeti.BraidWord.normalizedKauffmanBracket_closure_cons_skein`, applied to a
word for `c` beginning with `σᵢ σᵢ⁻¹`, so that both positions of the crossing already meet the
diagram. Both are multiplied by `δ` when an uncrossed strand is added, and both take the value `δ`
on the unknot. The comparison holds over every commutative ring, without dividing by `δ`.

## Main results

* `TauCeti.BraidWord.jonesTrace_toBraid`: the Markov trace of the Jones representation is `δ`
  times the normalized Kauffman bracket of the closure.
* `TauCeti.BraidWord.jonesTrace_toBraid_eq_eval₂_jonesPolynomial`: the same in terms of the Jones
  polynomial of the closure.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1 and 3.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup TemperleyLieb LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- The diagram route on a braid: `δ` times the normalized bracket of the closure of a chosen word
representing it. -/
private noncomputable def closureBracket (a : Rˣ) (β : MarkovBraid) : R :=
  jonesDelta a * (toBraid_surjective β.braid).choose.closure.normalizedKauffmanBracket a

/-- The diagram route can be computed from any word representing the braid. -/
private theorem closureBracket_mk (a : Rˣ) {n : ℕ} (w : BraidWord (n + 1)) :
    closureBracket a ⟨n, w.toBraid⟩ = jonesDelta a * w.closure.normalizedKauffmanBracket a := by
  have h : OrientedPDCode.ReidemeisterEquiv
      (toBraid_surjective (MarkovBraid.mk n w.toBraid).braid).choose.closure w.closure :=
    reidemeisterEquiv_closure_of_toBraid_eq
      (toBraid_surjective (MarkovBraid.mk n w.toBraid).braid).choose_spec
  rw [closureBracket, h.normalizedKauffmanBracket_eq]

private theorem closureBracket_markovEquiv (a : Rˣ) (β γ : MarkovBraid) (h : MarkovEquiv β γ) :
    closureBracket a β = closureBracket a γ := by
  rw [closureBracket, closureBracket, (h.reidemeisterEquiv_closure
    (toBraid_surjective β.braid).choose_spec
      (toBraid_surjective γ.braid).choose_spec).normalizedKauffmanBracket_eq]

private theorem closureBracket_skein (a : Rˣ) (n : ℕ) (c : BraidGroup (n + 1)) (i : Fin n) :
    (a : R) ^ 4 * closureBracket a ⟨n, sigma (n := n + 1) i * c⟩ -
        ((a⁻¹ : Rˣ) : R) ^ 4 * closureBracket a ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
      (((a⁻¹ : Rˣ) : R) ^ 2 - (a : R) ^ 2) * closureBracket a ⟨n, c⟩ := by
  -- A word for `c` starting with `σᵢ σᵢ⁻¹` meets both positions of the crossing.
  obtain ⟨v, rfl⟩ := toBraid_surjective c
  let v' : BraidWord (n + 1) := (i, 1) :: (i, -1) :: v
  have hv' : v'.toBraid = v.toBraid := by
    rw [toBraid_cons, toBraid_cons]
    simp
  have hp : v'.crossingsAt (strand i) ≠ [] := by
    rw [Ne, crossingsAt_cons_eq_nil_iff]
    simp
  have hq : v'.crossingsAt (strandSucc i) ≠ [] := by
    rw [Ne, crossingsAt_cons_eq_nil_iff]
    simp
  have hpos : toBraid ((i, 1) :: v' : BraidWord (n + 1)) = sigma (n := n + 1) i * v.toBraid := by
    rw [toBraid_cons, hv']
    simp
  have hneg : toBraid ((i, -1) :: v' : BraidWord (n + 1)) =
      (sigma (n := n + 1) i)⁻¹ * v.toBraid := by
    rw [toBraid_cons, hv']
    simp
  rw [← hpos, ← hneg, ← hv', closureBracket_mk, closureBracket_mk, closureBracket_mk]
  linear_combination jonesDelta a * normalizedKauffmanBracket_closure_cons_skein v' i hp hq a

private theorem closureBracket_strandIncl (a : Rˣ) (n : ℕ) (b : BraidGroup (n + 1)) :
    closureBracket a ⟨n + 1, BraidGroup.strandIncl b⟩ = jonesDelta a * closureBracket a ⟨n, b⟩ := by
  obtain ⟨w, rfl⟩ := toBraid_surjective b
  rw [← toBraid_strandIncl, closureBracket_mk, closureBracket_mk,
    normalizedKauffmanBracket_closure_strandIncl]

/-- **The braid and diagram routes to the Jones polynomial agree.** For a braid word `w` on
`n + 1` strands, the writhe-normalized Markov trace of the Jones representation of the braid
represented by `w` is `δ = -(A² + A⁻²)` times the writhe-normalized Kauffman bracket of the closure
of `w`, over every commutative ring. -/
theorem jonesTrace_toBraid (a : Rˣ) {n : ℕ} (w : BraidWord (n + 1)) :
    MarkovBraid.jonesTrace ⟨n, w.toBraid⟩ a =
      jonesDelta a * w.closure.normalizedKauffmanBracket a := by
  have h := MarkovBraid.eq_of_skein (a ^ 4) (((a⁻¹ : Rˣ) : R) ^ 2 - (a : R) ^ 2) (jonesDelta a)
    (F := fun β ↦ β.jonesTrace a) (G := closureBracket a)
    (fun β γ h ↦ h.jonesTrace_eq a) (closureBracket_markovEquiv a)
    (fun n c i ↦ by simpa using MarkovBraid.jonesTrace_skein a 1 c i)
    (fun n c i ↦ by simpa using closureBracket_skein a n c i)
    (fun n b ↦ MarkovBraid.jonesTrace_strandIncl a b)
    (fun n b ↦ closureBracket_strandIncl a n b)
    (by
      rw [MarkovBraid.jonesTrace_one_strand, ← toBraid_nil (n := 1), closureBracket_mk,
        closure_nil, OrientedPDCode.normalizedKauffmanBracket_def,
        PDCode.kauffmanBracket_eq_jonesDelta_pow, ← OrientedPDCode.card_crossinglessComponents,
        OrientedPDCode.crossinglessComponents_unlink]
      simp [OrientedPDCode.writhe_def])
  rw [congrFun h, closureBracket_mk]

/-- The braid and diagram routes agree, in terms of the Jones polynomial: the Markov trace of the
Jones representation is `δ` times the Jones polynomial of the closure at `t ^ (1/2) = A⁻²`. -/
theorem jonesTrace_toBraid_eq_eval₂_jonesPolynomial (a : Rˣ) {n : ℕ} (w : BraidWord (n + 1)) :
    MarkovBraid.jonesTrace ⟨n, w.toBraid⟩ a =
      jonesDelta a * eval₂ (Int.castRingHom R) (a⁻¹ ^ 2) w.closure.jonesPolynomial := by
  rw [jonesTrace_toBraid, OrientedPDCode.eval₂_jonesPolynomial]

end TauCeti.BraidWord
