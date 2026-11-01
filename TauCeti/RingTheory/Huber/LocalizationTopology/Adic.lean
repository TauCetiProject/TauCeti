/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Basic

/-!
# Rational localisations of adic rings away from one element

Let `A` be a ring whose topology is the `I`-adic topology for a finitely generated ideal `I`,
with the pair of definition `(A, I)` (`TauCeti.Huber.PairOfDefinition.adic`). For `f ∈ A`,
consider Wedhorn's localisation topology on `A_f` with the single numerator `1` and
denominator `f`, the topology of the rational subset `R(1/f) = D(f)`. Its candidate ring of
definition `D = A[1/f]` is all of `A_f`, so the topology is simply the adic topology of the
extended ideal `I A_f`. This identifies the coordinate ring `A⟨1/f⟩` of Huber's theory with the
completed localisation of the theory of formal schemes, which is the `I A_f`-adic completion of
`A_f` (EGA I, Ch. 0, 7.6.1–7.6.2).

## Main results

* `TauCeti.Huber.PairOfDefinition.locSubring_adic_one_eq_top`: the ring `D = A[1/f]` is all of
  `A_f`.
* `TauCeti.Huber.PairOfDefinition.isAdic_locTopology_adic_one`: the localisation topology is the
  adic topology of `I A_f`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.51.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.6.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] {I : Ideal A} (hI : IsAdic I)
  (hfg : I.FG) (f : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away f S]

/-- For the pair of definition `(A, I)` of an adic ring, the candidate ring of definition
`A[1/f]` of the localisation away from `f` with numerator `1` is all of `A_f`. -/
theorem locSubring_adic_one_eq_top : locSubring (adic I hI hfg) {1} f S = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f x
  have hx : x = algebraMap A S a * IsLocalization.Away.invSelf f ^ n := by
    rw [← ha, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  rw [hx]
  refine mul_mem (algebraMap_mem_locSubring _ _ _ _ (by simp)) (pow_mem ?_ n)
  rw [← TauCeti.Localization.divBy_one]
  exact divBy_mem_locSubring _ _ _ _ rfl

/-- The basic neighbourhoods of zero of the localisation topology with numerator `1` and
denominator `f`, for the pair of definition `(A, I)`, are the powers of `I A_f`. -/
private theorem coe_locIdealImage_adic_one (n : ℕ) :
    (locIdealImage (adic I hI hfg) {1} f S n : Set S) =
      ((I.map (algebraMap A S) ^ n : Ideal S) : Set S) := by
  set P := adic I hI hfg
  have hsurj : Function.Surjective (locSubring P {1} f S).subtype := fun x ↦
    ⟨⟨x, (locSubring_adic_one_eq_top hI hfg f S).symm ▸ Subring.mem_top x⟩, rfl⟩
  have hcomp : (locSubring P {1} f S).subtype.comp (toLocSubring P {1} f S) =
      (algebraMap A S).comp P.ringOfDefinition.subtype :=
    RingHom.ext fun _ ↦ toLocSubring_apply P {1} f S _
  ext x
  rw [SetLike.mem_coe, mem_locIdealImage_iff, SetLike.mem_coe, ← Ideal.map_pow,
    ← adic_extendedIdealOfDefinition I hI hfg, extendedIdealOfDefinition_def, ← Ideal.map_pow,
    Ideal.map_map, ← hcomp, ← Ideal.map_map, ← locIdeal_pow,
    Ideal.mem_map_iff_of_surjective _ hsurj]
  simp only [Subring.coe_subtype]

/-- **The localisation topology of `A_f` for an adic ring.** For the pair of definition `(A, I)`
of a ring with the `I`-adic topology, the localisation topology on `A_f` with numerator `1` and
denominator `f` is the adic topology of the extended ideal `I A_f`. -/
theorem isAdic_locTopology_adic_one [SeparatelyContinuousMul A]
    (hden : HasDenominatorPower (adic I hI hfg) {1} f S) :
    letI := locTopology (adic I hI hfg) {1} f S hden
    IsAdic (I.map (algebraMap A S)) := by
  let _ := locTopology (adic I hI hfg) {1} f S hden
  have _ := isTopologicalRing_locTopology (adic I hI hfg) {1} f S hden
  have hbasis := hasBasis_nhds_zero_locTopology (adic I hI hfg) {1} f S hden
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun U hU ↦ ?_⟩
  · refine (I.map (algebraMap A S) ^ n).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
    have h := hbasis.mem_of_mem (i := n) trivial
    rwa [coe_locIdealImage_adic_one] at h
  · obtain ⟨n, -, hn⟩ := hbasis.mem_iff.mp hU
    exact ⟨n, coe_locIdealImage_adic_one hI hfg f S n ▸ hn⟩

end TauCeti.Huber.PairOfDefinition
