/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Quotient
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Checks for quotients of henselian pairs

The pair `(ℤ⟦t⟧, (t))` is henselian by completeness. Quotienting by `(2)` exercises
permanence for an ideal not contained in `(t)`, and the image of `(t)` is still nonzero.
A simple root with derivative `3` lifts in this quotient although `3` was not a unit
in `ℤ⟦t⟧`. The other checks cover the zero and unit quotient ideals and composition
of surjections.
-/

public section

open Polynomial

section General

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) [HenselianRing R I]

-- Successive quotient maps retain henselianity, using ideal-map composition.
example (φ : R →+* S) (hφ : Function.Surjective φ)
    (ψ : S →+* T) (hψ : Function.Surjective ψ) :
    HenselianRing T (I.map (ψ.comp φ)) := by
  let := φ.henselianRing_of_surjective hφ I
  simpa only [Ideal.map_map] using ψ.henselianRing_of_surjective hψ (I.map φ)

-- No change to the ring, up to the canonical zero-ideal quotient.
example : HenselianRing (R ⧸ (⊥ : Ideal R)) (I.map (Ideal.Quotient.mk ⊥)) :=
  inferInstance

-- The zero ring is allowed as a target.
example : HenselianRing (R ⧸ (⊤ : Ideal R)) (I.map (Ideal.Quotient.mk ⊤)) :=
  inferInstance

end General

noncomputable section PowerSeries

private abbrev R := PowerSeries ℤ
private abbrev I : Ideal R := Ideal.span {PowerSeries.X}
private abbrev J : Ideal R := Ideal.span {PowerSeries.C 2}
private abbrev S := R ⧸ J
private abbrev q : R →+* S := Ideal.Quotient.mk J
private abbrev t : S := q PowerSeries.X

-- This quotient is not covered by permanence restricted to J ≤ I.
example : ¬J ≤ I := by
  intro h
  have hmem := h (Ideal.subset_span (Set.mem_singleton (PowerSeries.C 2)))
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmem
  have := congrArg PowerSeries.constantCoeff hr
  simp only [PowerSeries.constantCoeff_C, map_mul, PowerSeries.constantCoeff_X,
    zero_mul] at this
  contradiction

-- Completeness supplies the source henselian pair, with a nonzero proper ideal.
example : HenselianRing R I := inferInstance

example : HenselianRing S (I.map q) := inferInstance

-- Reduction of coefficients modulo 2 detects that the image of t is nonzero.
private theorem t_ne_zero : t ≠ 0 := by
  let φ : R →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp only [φ, map_ofNat]
    have h2 : (2 : ZMod 2) = 0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg PowerSeries.C h2
  let ψ : S →+* PowerSeries (ZMod 2) := Ideal.Quotient.lift J φ hJ
  intro ht
  have hψ : ψ (q PowerSeries.X) = PowerSeries.X :=
    (Ideal.Quotient.lift_mk J φ hJ).trans (PowerSeries.map_X _)
  have heq : ψ (q PowerSeries.X) = ψ 0 := congrArg ψ ht
  rw [hψ, map_zero] at heq
  exact PowerSeries.X_ne_zero heq

example : I.map q ≠ ⊥ := by
  intro h
  have ht : t ∈ I.map q := Ideal.mem_map_of_mem q (Ideal.subset_span (by simp))
  exact t_ne_zero (by simpa [h] using ht)

-- A chosen lift of a quotient unit need not itself be a unit.
example : ¬IsUnit (3 : R) := by
  intro h
  have h' : IsUnit (3 : ℤ) := by
    simpa only [map_ofNat] using h.map PowerSeries.constantCoeff
  rcases Int.isUnit_iff.mp h' with h3 | h3 <;> omega

/-- In `ℤ⟦t⟧/(2)`, the polynomial `Y² + 3Y - t` has a nonzero root in the image
of `(t)`. Its derivative at zero is a unit only after passing to the quotient. -/
theorem TauCeti.Examples.HenselianQuotient.exists_nonzero_root :
    ∃ x : PowerSeries ℤ ⧸ Ideal.span {PowerSeries.C 2},
      x ≠ 0 ∧ x ^ 2 + 3 * x = Ideal.Quotient.mk _ PowerSeries.X ∧
        x ∈ (Ideal.span {PowerSeries.X}).map (Ideal.Quotient.mk _) := by
  have h3 : (3 : S) = 1 := by
    rw [← map_ofNat q 3, ← map_one q, Ideal.Quotient.eq]
    norm_num
    exact Ideal.subset_span (by simp)
  obtain ⟨x, hx, hxI⟩ := Polynomial.exists_isRoot_sub_mem (J := I.map q)
    (X ^ 2 + C 3 * X - C t : S[X]) (a₀ := 0)
    (by
      simpa using (I.map q).neg_mem
        (Ideal.mem_map_of_mem q (Ideal.subset_span (by simp))))
    (by simp [h3])
  have heq : x ^ 2 + 3 * x = t := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using hx
  refine ⟨x, ?_, heq, by simpa using hxI⟩
  intro hx0
  exact t_ne_zero (by simpa [hx0] using heq.symm)

end PowerSeries
