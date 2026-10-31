/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import TauCeti.Algebra.CharP.Frobenius.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.Flat.LocalCriterion
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Kunz's theorem: regular rings have flat Frobenius

Let `R` be a regular ring of characteristic `p`. Then the absolute Frobenius `R → R`,
`a ↦ a ^ p`, is flat (`TauCeti.IsRegularRing.flat_frobenius`). This is the implication from
regularity to flatness in Kunz's characterization of regular rings in characteristic `p`.

For a regular local ring `(R, 𝔪)` of dimension `d`, Frobenius is a local homomorphism carrying a
regular system of parameters `x₁, …, x_d` to `x₁ ^ p, …, x_d ^ p`. These generate an ideal with
radical `𝔪`, so they form a system of parameters, which is a regular sequence because `R` is
Cohen–Macaulay. A local homomorphism of Noetherian local rings carrying generators of the maximal
ideal of the source to a regular sequence is flat (`RingHom.Flat.of_isWeaklyRegular_map`), which
gives the local case `TauCeti.IsRegularLocalRing.flat_frobenius`. This replaces the appeal to
miracle flatness in the Stacks proof: the dimension count is only needed to see that the powers
form a regular sequence. Flatness is local on the target, and Frobenius commutes with
localization, so the local case gives the global one.

The theorems are stated for an exponential characteristic `p`, so that in characteristic zero,
where `p = 1` and Frobenius is the identity, they hold trivially.

## Main results

* `TauCeti.IsRegularLocalRing.flat_frobenius`: Frobenius of a regular local ring is flat.
* `TauCeti.IsRegularRing.flat_frobenius`: **Kunz's theorem**, Frobenius of a regular ring is
  flat.

Frobenius is a local homomorphism by `TauCeti.isLocalHom_frobenius`, and regularity cannot be
dropped: a ring of exponential characteristic `p > 1` with flat Frobenius is reduced
(`TauCeti.isReduced_of_flat_frobenius`).

## References

* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
* [Stacks Project, Lemma 51.17.6](https://stacks.math.columbia.edu/tag/0EC0), the implication
  from regularity to flatness.
-/

public section

open IsLocalRing Ideal RingTheory.Sequence

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]

namespace TauCeti

/-- **Frobenius of a regular local ring is flat.** In a regular local ring of exponential
characteristic `p`, the `p`-th powers of a regular system of parameters form a regular sequence,
so the Frobenius endomorphism is flat. -/
theorem IsRegularLocalRing.flat_frobenius [IsRegularLocalRing R] : (frobenius R p).Flat := by
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  have hofList : ofList s.toList = maximalIdeal R := by simpa [ofList] using hspan
  refine RingHom.Flat.of_isWeaklyRegular_map (frobenius R p) hofList ?_
  refine (isCohenMacaulay.isRegular_of_le_radical (fun r hr ↦ ?_)
    (le_trans ?_ (radical_mono le_sup_left)) ?_).toIsWeaklyRegular
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hr
    exact map_nonunit (frobenius R p) r (hofList ▸ subset_span hr')
  · -- Every `r` in the system of parameters has `r ^ p` among the new generators.
    rw [← hofList, ofList, span_le]
    exact fun r hr ↦ ⟨p, subset_span (List.mem_map_of_mem (f := frobenius R p) hr)⟩
  · rw [List.length_map, Finset.length_toList, hcard, Module.supportDim_self_eq_ringKrullDim,
      ← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal]

/-- **Kunz's theorem.** The Frobenius endomorphism of a regular ring of exponential characteristic
`p` is flat. Stacks, Lemma 51.17.6 (0EC0), the implication from regularity to flatness. -/
@[stacks 0EC0 "regularity implies flatness of Frobenius"]
theorem IsRegularRing.flat_frobenius [IsRegularRing R] : (frobenius R p).Flat := by
  obtain _ | ⟨hp⟩ := ‹ExpChar R p›
  · exact RingHom.Flat.of_bijective (f := frobenius R 1)
      ⟨fun a b h ↦ by simpa [frobenius_def] using h, fun a ↦ ⟨a, by simp [frobenius_def]⟩⟩
  refine RingHom.Flat.ofLocalizationPrime _ fun J hJ ↦ ?_
  -- Frobenius of `R` induces Frobenius of `R_J`, since `a ^ p ∈ J` exactly when `a ∈ J`.
  have hQ : J.comap (frobenius R p) = J.comap (RingHom.id R) := by
    ext a
    exact hJ.pow_mem_iff_mem p hp.pos
  have : CharP (Localization.AtPrime J) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  have : ExpChar (Localization.AtPrime J) p := .prime hp
  have hcomp : Localization.localRingHom _ J (frobenius R p) rfl =
      (frobenius (Localization.AtPrime J) p).comp
        (Localization.localRingHom _ J (RingHom.id R) hQ) :=
    IsLocalization.ringHom_ext (J.comap (frobenius R p)).primeCompl <| RingHom.ext fun a ↦ by
      simp [Localization.localRingHom_to_map, frobenius_def]
  rw [hcomp]
  exact (RingHom.Flat.localRingHom (RingHom.Flat.id R) J _ hQ).comp
    (IsRegularLocalRing.flat_frobenius p)

end TauCeti
