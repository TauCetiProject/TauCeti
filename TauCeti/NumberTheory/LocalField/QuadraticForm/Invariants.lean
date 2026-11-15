/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Classification
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Realization

import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo

/-!
# The local invariants of a quadratic form, and the classification as an equivalence

A regular quadratic form over a nonarchimedean local field `K` in which `2` is invertible has
three invariants: its rank `n`, its plain discriminant `d ∈ Kˣ/(Kˣ)²` and its local Hasse
invariant `s ∈ {±1}`. This file bundles them as `TauCeti.LocalFormInvariants K`, the local
counterpart of the global systems `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants`, and
cuts out the **admissible** triples: those with

* `d = [1]` and `s = 1` in rank zero;
* `s = 1` in rank one;
* `s = 1` in rank two whenever `d = [-1]`.

The classification of forms over `K` by `(n, d, s)` (O'Meara 63:20, Serre IV Thm 7) and the
realization of invariants (O'Meara 63:23, Serre IV Prop 6) together say that taking invariants is
a bijection from isometry classes onto admissible triples. This is
`TauCeti.RegularFormClass.localInvariantsEquiv`; its inverse is the realization map, sending an
admissible triple to the unique class with those invariants.

Over `ℚ_2` the binary form `⟨-1, -1⟩` has discriminant `[1]` and Hasse invariant
`(-1, -1)_{ℚ_2} = -1`, so it realizes `(2, [1], -1)`, while `(2, [-1], -1)` is excluded. The two
discriminants in the rank-two exception therefore cannot be confused with each other.

## Main definitions

* `TauCeti.LocalFormInvariants`: rank, discriminant and Hasse sign.
* `TauCeti.LocalFormInvariants.IsAdmissible`: the admissibility conditions above.
* `TauCeti.RegularFormClass.localInvariants`: the invariants of a regular-form class.
* `TauCeti.RegularFormClass.localInvariantsEquiv`: regular-form classes are in bijection with
  admissible triples.

## Main results

* `TauCeti.RegularFormClass.localInvariants_injective`: the classification.
* `TauCeti.RegularFormClass.range_localInvariants`: the realized triples are exactly the
  admissible ones.
* `TauCeti.RegularFormClass.localInvariants_mk_binary`: the invariants of `⟨a, b⟩`.
* `TauCeti.RegularFormClass.localInvariants_neg_one_neg_one_padicTwo`: `⟨-1, -1⟩` over `ℚ_2`
  realizes `(2, [1], -1)`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20 and §63:23.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.3, Theorem 7 and Proposition 6.
-/

public section

namespace TauCeti

/-- The **local invariants** of a regular quadratic form over a field `K`: a rank `n`, a
discriminant in `Kˣ/(Kˣ)²`, and a Hasse sign in `{±1}`. The triples that occur over a
nonarchimedean local field are cut out by `LocalFormInvariants.IsAdmissible`. -/
@[ext]
structure LocalFormInvariants (K : Type*) [Field K] where
  /-- The rank. -/
  rank : ℕ
  /-- The plain discriminant, a square class. -/
  discr : SquareClassGroup K
  /-- The Hasse sign. -/
  hasse : ℤˣ

namespace LocalFormInvariants

variable {K : Type*} [Field K]

/-- **Admissibility of a triple of local invariants.** A triple `(n, d, s)` is admissible when
`d = [1]` and `s = 1` in rank zero, `s = 1` in rank one, and `s = 1` in rank two whenever
`d = [-1]`. Over a nonarchimedean local field these are exactly the triples realized by regular
forms (`TauCeti.RegularFormClass.range_localInvariants`). -/
structure IsAdmissible (I : LocalFormInvariants K) : Prop where
  /-- In rank zero the discriminant is trivial. -/
  discr_eq_zero_of_rank_eq_zero : I.rank = 0 → I.discr = 0
  /-- In rank at most one the Hasse sign is trivial. -/
  hasse_eq_one_of_rank_le_one : I.rank ≤ 1 → I.hasse = 1
  /-- In rank two the Hasse sign is trivial when the discriminant is the class of `-1`. -/
  hasse_eq_one_of_rank_eq_two : I.rank = 2 → I.discr = squareClass (-1 : Kˣ) → I.hasse = 1

end LocalFormInvariants

namespace RegularFormClass

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- The local invariants `(n, d, s)` of a regular-form class: its rank, its plain discriminant
and its local Hasse invariant. -/
noncomputable def localInvariants (x : RegularFormClass K) : LocalFormInvariants K :=
  ⟨x.rank, discr x, localHasse x⟩

/-- The rank of `localInvariants x` is the rank of `x`. -/
@[simp]
theorem rank_localInvariants (x : RegularFormClass K) : x.localInvariants.rank = x.rank :=
  (rfl)

/-- The discriminant of `localInvariants x` is the discriminant of `x`. -/
@[simp]
theorem discr_localInvariants (x : RegularFormClass K) : x.localInvariants.discr = discr x :=
  (rfl)

/-- The Hasse sign of `localInvariants x` is the local Hasse invariant of `x`. -/
@[simp]
theorem hasse_localInvariants (x : RegularFormClass K) :
    x.localInvariants.hasse = localHasse x :=
  (rfl)

/-- The zero class has invariants `(0, [1], 1)`. -/
@[simp]
theorem localInvariants_zero : (0 : RegularFormClass K).localInvariants = ⟨0, 0, 1⟩ := by
  ext <;> simp

/-- The invariants of the binary diagonal class `⟨a, b⟩` are `(2, [ab], (a, b)_K)`. -/
@[simp]
theorem localInvariants_mk_binary (a b : Kˣ) :
    localInvariants (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      ⟨2, squareClass (a * b), hilbertSymbol a b⟩ := by
  ext <;> simp [rank_mk, Fin.prod_univ_two]

/-- The invariants of every regular-form class are admissible. -/
theorem isAdmissible_localInvariants (x : RegularFormClass K) :
    x.localInvariants.IsAdmissible where
  discr_eq_zero_of_rank_eq_zero h := by
    rw [discr_localInvariants, rank_eq_zero_iff.mp h, discr_zero]
  hasse_eq_one_of_rank_le_one h := localHasse_eq_one_of_rank_le_one h
  hasse_eq_one_of_rank_eq_two h hd := localHasse_eq_one_of_rank_eq_two_of_discr_eq_neg_one h hd

/-- **Local classification** (O'Meara 63:20, Serre IV Thm 7). A regular-form class over a
nonarchimedean local field is determined by its rank, discriminant and local Hasse invariant. -/
theorem localInvariants_injective : Function.Injective (localInvariants (K := K)) :=
  fun _ _ h => eq_of_discr_eq_of_localHasse_eq (congrArg LocalFormInvariants.rank h)
    (congrArg LocalFormInvariants.discr h) (congrArg LocalFormInvariants.hasse h)

/-- Two regular-form classes are equal exactly when their local invariants are. -/
@[simp]
theorem localInvariants_inj {x y : RegularFormClass K} :
    x.localInvariants = y.localInvariants ↔ x = y :=
  localInvariants_injective.eq_iff

/-- **Realization of local invariants** (O'Meara 63:23, Serre IV Prop 6). The triples
`(n, d, s)` of rank, discriminant and local Hasse invariant of regular-form classes over a
nonarchimedean local field are exactly the admissible ones. -/
theorem range_localInvariants :
    Set.range (localInvariants (K := K)) = {I | I.IsAdmissible} := by
  ext I
  refine ⟨fun ⟨x, hx⟩ => hx ▸ isAdmissible_localInvariants x, fun hI => ?_⟩
  obtain hn | hn := Nat.eq_zero_or_pos I.rank
  · refine ⟨0, ?_⟩
    ext
    · simp [hn]
    · simp [hI.discr_eq_zero_of_rank_eq_zero hn]
    · simp [hI.hasse_eq_one_of_rank_le_one (by omega)]
  · obtain ⟨x, hr, hd, hs⟩ := exists_of_realization hn I.discr I.hasse
      (fun h => hI.hasse_eq_one_of_rank_le_one h.le) hI.hasse_eq_one_of_rank_eq_two
    exact ⟨x, LocalFormInvariants.ext hr hd hs⟩

/-- **The classification of regular forms over a local field, as an equivalence.** Taking rank,
discriminant and local Hasse invariant is a bijection from regular-form classes over a
nonarchimedean local field onto admissible triples. Its inverse is the realization map. -/
noncomputable def localInvariantsEquiv :
    RegularFormClass K ≃ {I : LocalFormInvariants K // I.IsAdmissible} :=
  Equiv.ofBijective (fun x => ⟨x.localInvariants, isAdmissible_localInvariants x⟩)
    ⟨fun _ _ h => localInvariants_injective (congrArg Subtype.val h), fun I => by
      obtain ⟨x, hx⟩ : I.1 ∈ Set.range (localInvariants (K := K)) := by
        rw [range_localInvariants]
        exact I.2
      exact ⟨x, Subtype.ext hx⟩⟩

/-- `localInvariantsEquiv` sends a class to its local invariants. -/
@[simp]
theorem coe_localInvariantsEquiv_apply (x : RegularFormClass K) :
    (localInvariantsEquiv x : LocalFormInvariants K) = x.localInvariants :=
  (rfl)

/-- The realization map: the class `localInvariantsEquiv.symm I` has invariants `I`. -/
@[simp]
theorem localInvariants_localInvariantsEquiv_symm_apply
    (I : {I : LocalFormInvariants K // I.IsAdmissible}) :
    (localInvariantsEquiv.symm I).localInvariants = I := by
  rw [← coe_localInvariantsEquiv_apply, Equiv.apply_symm_apply]

/-- **Worked example over `ℚ_2`.** The binary form `⟨-1, -1⟩` has discriminant `[1]` and Hasse
invariant `(-1, -1)_{ℚ_2} = -1`, so it realizes the admissible triple `(2, [1], -1)`. -/
theorem localInvariants_neg_one_neg_one_padicTwo :
    localInvariants (Quotient.mk (regularFormSetoid ℚ_[2]) ⟨2, ![-1, -1]⟩) = ⟨2, 0, -1⟩ := by
  rw [localInvariants_mk_binary, hilbertSymbol_neg_one_neg_one_padicTwo, neg_one_mul, neg_neg,
    squareClass_one]

/-- **Worked example over `ℚ_2`.** No regular form realizes either excluded triple
`(1, [1], -1)` or `(2, [-1], -1)`, while `⟨-1, -1⟩` realizes `(2, [1], -1)`
(`localInvariants_neg_one_neg_one_padicTwo`). In particular `[-1] ≠ [1]` in `ℚ_2ˣ/(ℚ_2ˣ)²`. -/
example :
    (∀ x : RegularFormClass ℚ_[2], x.localInvariants ≠ ⟨1, 0, -1⟩) ∧
      (∀ x : RegularFormClass ℚ_[2], x.localInvariants ≠ ⟨2, squareClass (-1), -1⟩) ∧
      squareClass (-1 : ℚ_[2]ˣ) ≠ 0 := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun h => ?_⟩
  · have hI := isAdmissible_localInvariants x
    rw [hx] at hI
    exact absurd (hI.hasse_eq_one_of_rank_le_one le_rfl) (by decide)
  · have hI := isAdmissible_localInvariants x
    rw [hx] at hI
    exact absurd (hI.hasse_eq_one_of_rank_eq_two rfl rfl) (by decide)
  · have hI := isAdmissible_localInvariants
      (Quotient.mk (regularFormSetoid ℚ_[2]) ⟨2, ![-1, -1]⟩)
    rw [localInvariants_neg_one_neg_one_padicTwo] at hI
    exact absurd (hI.hasse_eq_one_of_rank_eq_two rfl h.symm) (by decide)

end RegularFormClass

end TauCeti
