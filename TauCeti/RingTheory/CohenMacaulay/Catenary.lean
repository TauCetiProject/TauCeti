/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.Catenary
import TauCeti.RingTheory.CohenMacaulay.Height

/-!
# Cohen–Macaulay rings are catenary

Let `R` be a Noetherian ring all of whose localizations `R_q` at primes are Cohen–Macaulay, that
is, a Cohen–Macaulay ring in the sense of Stacks, Definition 10.103.12 (0AAH). Then heights of
primes add along chains: for primes `p ⊆ q`, `ht p + ht (q / p) = ht q`. This is the dimension
formula `ht P + dim (R_q ⧸ P) = dim R_q` of the Cohen–Macaulay local ring `R_q`
(`Module.IsCohenMacaulay.height_add_ringKrullDim_quotient`), applied to the prime `P = p R_q`.

Additivity of heights makes `R` catenary, through the characterisation of catenary Noetherian rings
by additivity of heights of quotient primes
(`TauCeti.Excellence.isCatenary_iff_height_add_of_isNoetherianRing`). This is the first step of
the proof that Cohen–Macaulay rings are universally catenary (Stacks, Lemma 10.105.9 (00NM)); the
remaining step is that polynomial rings over Cohen–Macaulay rings are Cohen–Macaulay.

In a catenary ring every saturated chain of primes from `p` to `q` has length `ht (q / p)`, so in a
Cohen–Macaulay ring every saturated chain of primes from a minimal prime to `q` has length `ht q`.
For a Noetherian local ring all of whose localizations at primes are Cohen–Macaulay, taking `q` to
be the maximal ideal, this says that every maximal chain of primes has length `dim R`. Stacks,
Lemma 10.103.9 (0AAE) proves this assuming only that `R` itself is Cohen–Macaulay; deducing that
form from this one needs localization of Cohen–Macaulay modules (Stacks, Tag 0AAG).

## Main results

* `Module.IsCohenMacaulay.height_add_height_map_quotientMk`: if `R_q` is Cohen–Macaulay, then
  `ht p + ht (q / p) = ht q` for every prime `p ⊆ q`.
* `TauCeti.Excellence.isCatenary_of_forall_isCohenMacaulay`: a Noetherian ring whose localizations
  at all primes are Cohen–Macaulay is catenary.
* `TauCeti.Excellence.length_eq_height_of_forall_isCohenMacaulay`: in such a ring, a saturated chain
  of primes from a minimal prime to `q` has length `ht q`.

## References

* [Stacks Project, Lemma 10.105.9](https://stacks.math.columbia.edu/tag/00NM)
* [Stacks Project, Lemma 10.103.9](https://stacks.math.columbia.edu/tag/0AAE)
-/

public section

universe u

open Ideal

namespace Module.IsCohenMacaulay

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **Additivity of heights.** For primes `p ⊆ q` of a Noetherian ring `R` such that `R_q` is
Cohen–Macaulay, `ht p + ht (q / p) = ht q`, where `q / p` is the image of `q` in `R ⧸ p`. -/
theorem height_add_height_map_quotientMk {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : IsCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q)) (hpq : p ≤ q) :
    p.height + (q.map (Ideal.Quotient.mk p)).height = q.height := by
  let A := Localization.AtPrime q
  let Q : PrimeSpectrum R := ⟨q, ‹_›⟩
  let P : Set.Iic Q := ⟨⟨p, ‹_›⟩, hpq⟩
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso A q
  -- The prime `x = p R_q` of `R_q`, which lies over `p`.
  let x := e.symm P
  have hx : x.asIdeal.under R = p :=
    congrArg (fun y : Set.Iic Q ↦ y.1.asIdeal) (e.apply_symm_apply P)
  -- The primes of `R_q` containing `x` are the primes of `R` between `p` and `q`.
  let f : Set.Ici P ≃o Set.Icc P.1 Q :=
    { toFun y := ⟨y.1.1, y.2, y.1.2⟩
      invFun y := ⟨⟨y.1, y.2.2⟩, y.2.1⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_rel_iff' := Iff.rfl }
  have hcoheight : ringKrullDim (A ⧸ x.asIdeal) = (q.map (Ideal.Quotient.mk p)).height := by
    rw [← x.coheight_eq_ringKrullDim_quotient, ← Order.coheight_orderIso e, e.apply_symm_apply,
      Order.coheight_eq_krullDim_Ici, Order.krullDim_eq_of_orderIso f,
      PrimeSpectrum.krullDim_Icc P.2]
  have key := h.height_add_ringKrullDim_quotient x.asIdeal
  rw [hcoheight, ← IsLocalization.height_under q.primeCompl, hx,
    IsLocalization.AtPrime.ringKrullDim_eq_height q] at key
  exact_mod_cast key

end Module.IsCohenMacaulay

namespace TauCeti.Excellence

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **Cohen–Macaulay rings are catenary.** A Noetherian ring whose localizations at all primes are
Cohen–Macaulay is catenary. This is the first step of the proof of Stacks, Lemma 10.105.9 (00NM),
that such a ring is universally catenary. -/
theorem isCatenary_of_forall_isCohenMacaulay
    (h : ∀ (q : Ideal R) [q.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q)) :
    IsCatenary R := by
  refine isCatenary_iff_height_add_of_isNoetherianRing.2 fun p q r hpq hqr ↦ ?_
  have hpr := (h r.asIdeal).height_add_height_map_quotientMk (hpq.trans hqr)
  have hqr' := (h r.asIdeal).height_add_height_map_quotientMk hqr
  have hpq' := (h q.asIdeal).height_add_height_map_quotientMk hpq
  -- `ht p + ht (r / p) = ht r = ht q + ht (r / q) = ht p + ht (q / p) + ht (r / q)`, and `ht p`
  -- is finite.
  rw [← hqr', ← hpq', add_assoc] at hpr
  exact (WithTop.add_left_inj Ideal.height_ne_top_of_isPrime).1 hpr

/-- **Saturated chains of primes in a Cohen–Macaulay ring.** In a Noetherian ring whose
localizations at all primes are Cohen–Macaulay, every saturated chain of primes
`p₀ ⋖ p₁ ⋖ ⋯ ⋖ pₙ` starting at a minimal prime has length `n = ht pₙ`. For a local ring and
`pₙ` the maximal ideal, `ht pₙ = dim R`: every maximal chain of primes has length `dim R`. This is
Stacks, Lemma 10.103.9 (0AAE) under the stronger hypothesis that every localization of `R` is
Cohen–Macaulay, not only `R` itself. -/
theorem length_eq_height_of_forall_isCohenMacaulay
    (h : ∀ (q : Ideal R) [q.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q))
    (s : RelSeries {(x, y) : PrimeSpectrum R × PrimeSpectrum R | x ⋖ y})
    (hs : s.head.asIdeal ∈ minimalPrimes R) : (s.length : ℕ∞) = s.last.asIdeal.height := by
  have := isCatenary_of_forall_isCohenMacaulay h
  have hle : s.head ≤ s.last :=
    LTSeries.head_le_last (s.map ⟨id, fun h ↦ CovBy.lt h⟩)
  have hlen := TauCeti.Order.IsCatenary.krullDim_Icc_eq_length s
  rw [PrimeSpectrum.krullDim_Icc hle] at hlen
  rw [← (h s.last.asIdeal).height_add_height_map_quotientMk hle, ← WithBot.coe_inj.1 hlen,
    Ideal.height_eq_zero_iff.2 hs, zero_add]

end TauCeti.Excellence
