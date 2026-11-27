/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Centres of valuations on subrings

A valuation of a ring `K` that is bounded by `1` on the image of a commutative `R`-algebra map
`R → K` determines a prime ideal of `R`: the elements whose images have value strictly below `1`.
When `K` is the fraction field of `R` and the valuation is nontrivial, this centre is nonzero. The
value group may be any linearly ordered commutative group with zero.

For a valuation subring `A` of a field `L` containing the image of `B`, the centre is the ideal of
the elements of `B` that are nonunits of `A`; write `A.IsCenteredAt P` when `A` contains `B` with
centre `P`. For a group acting compatibly on `B` and `L`, the centre of `g • A` is `g • P`.

## Main definitions and results

* `Valuation.centerIdeal`: the prime centre of a valuation bounded by `1` on `R`.
* `Valuation.mem_centerIdeal`: membership is equivalent to valuation strictly below `1`.
* `Valuation.notMem_centerIdeal_iff`: off the centre, the valuation takes the value `1`.
* `Valuation.centerIdeal_ne_bot`: a nontrivial valuation of the fraction field has nonzero centre.
* `Valuation.heightOneSpectrum`: the nonzero prime centre bundled as `HeightOneSpectrum R`.
  This structure records a nonzero prime ideal; it is a height one prime when `R` is Dedekind.
* `Valuation.asIdeal_heightOneSpectrum`: the underlying ideal is the centre ideal.
* `ValuationSubring.IsCenteredAt A P`: `A` contains `B` and `P` is its centre on `B`; it is
  `Valuation.centerIdeal` of the valuation of `A` (`ValuationSubring.IsCenteredAt.eq_centerIdeal`).
* `ValuationSubring.IsCenteredAt.ne_top_of_ne_bot`: a valuation subring with nonzero centre on a
  subring is proper.
* `ValuationSubring.IsCenteredAt.smul`: the centre of `g • A` is `g • P`.

The comparison of a valuation subring with the localization at its centre is in
`TauCeti/RingTheory/Valuation/LocalizationAtCenter.lean`.

## Provenance

`ValuationSubring.IsCenteredAt.smul_sub_pow_mem_of_forall`, which restricts a `q`-power
congruence from a valuation subring to its centre, is adapted from the restriction argument of
the `riemann-hypothesis` formalisation (https://github.com/leanprover-community/riemann-hypothesis,
branch `tc-galois-5-frobenius`, commit `c62bdab14fd`,
`src/Lib/ClassField/Places/FrobeniusComparison.lean`, declaration `New.IsFrob.isArithFrobAt`).
**Adapted, not copied**: it is stated here for any ring `B`, any group acting compatibly on `B`
and `L`, and any exponent `q`, in terms of `ValuationSubring.IsCenteredAt`.
-/

public section

open scoped Pointwise

open IsDedekindDomain

namespace Valuation

variable {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section CenterIdeal

variable {K : Type*} [Ring K] [Algebra R K] {w : _root_.Valuation K Γ₀}

variable (R) in
/-- The **centre** on `R` of a valuation `w` of `K` that is bounded by `1` on the image of `R`:
the ideal of elements of `R` whose images have valuation strictly below `1`. It is prime
(`Valuation.isPrime_centerIdeal`), and it is nonzero as soon as `w` is nontrivial and `K` is the
fraction field of `R` (`Valuation.centerIdeal_ne_bot`). -/
def centerIdeal (w : _root_.Valuation K Γ₀) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    Ideal R where
  carrier := {r | w (algebraMap R K r) < 1}
  add_mem' {a b} ha hb := by
    simpa only [Set.mem_ofPred_eq, map_add] using (w.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c r hr := by
    simpa only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] using
      (mul_le_of_le_one_left' (hR c)).trans_lt hr

/-- An element belongs to the centre ideal exactly when its valuation is strictly below `1`. -/
@[simp]
theorem mem_centerIdeal {r : R} {hR : ∀ r : R, w (algebraMap R K r) ≤ 1} :
    r ∈ centerIdeal R w hR ↔ w (algebraMap R K r) < 1 :=
  Iff.rfl

/-- Off its centre, and only there, a valuation bounded by `1` on `R` takes the value `1`. -/
theorem notMem_centerIdeal_iff {r : R} {hR : ∀ r : R, w (algebraMap R K r) ≤ 1} :
    r ∉ centerIdeal R w hR ↔ w (algebraMap R K r) = 1 := by
  rw [mem_centerIdeal, not_lt, le_antisymm_iff, and_iff_right (hR r)]

/-- The centre of a valuation bounded by `1` on `R` is a prime ideal of `R`. -/
theorem isPrime_centerIdeal (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (centerIdeal R w hR).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun h ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · simpa using (Ideal.eq_top_iff_one _).mp h
  · by_contra! h
    rw [mem_centerIdeal, map_mul, map_mul, notMem_centerIdeal_iff.mp h.1,
      notMem_centerIdeal_iff.mp h.2, mul_one] at hxy
    exact hxy.false

end CenterIdeal

variable {K : Type*} [Field K] [Algebra R K] {w : _root_.Valuation K Γ₀}

/-- The centre of a nontrivial valuation of the fraction field `K` of `R` is a nonzero ideal of
`R`: an element of `K` of value below `1` is a fraction `a / b` whose numerator `a` is a nonzero
element of the centre. -/
theorem centerIdeal_ne_bot [IsFractionRing R K] [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : centerIdeal R w hR ≠ ⊥ := by
  obtain ⟨y, hy0, hy1⟩ := IsNontrivial.exists_lt_one (v := w)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) y
  refine (Submodule.ne_bot_iff _).mpr ⟨a, ?_, ?_⟩
  · rw [mem_centerIdeal, ← hab, map_mul]
    exact (mul_le_of_le_one_right' (hR b)).trans_lt hy1
  · rintro rfl
    exact hy0 ((IsLocalization.map_units K b).mul_left_eq_zero.mp (hab.trans (map_zero _)))

variable [IsFractionRing R K]

variable (R) in
/-- The nonzero prime centre of a nontrivial valuation of `K` bounded by `1` on `R`, bundled
as a `HeightOneSpectrum R`. This is a height one prime when `R` is a Dedekind domain. -/
def heightOneSpectrum (w : _root_.Valuation K Γ₀) [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : HeightOneSpectrum R where
  asIdeal := centerIdeal R w hR
  isPrime := isPrime_centerIdeal hR
  ne_bot := centerIdeal_ne_bot hR

-- Parenthesize `rfl` to avoid inferred `@[defeq]`, which would require exposing the definition.
/-- The underlying ideal of `heightOneSpectrum` is the centre ideal. -/
@[simp]
theorem asIdeal_heightOneSpectrum [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (heightOneSpectrum R w hR).asIdeal = centerIdeal R w hR := (rfl)

end Valuation

/-! ### Valuation subrings centred at an ideal -/

namespace ValuationSubring

variable {B L : Type*} [CommRing B] [Field L] [Algebra B L]

/-- **A valuation subring centred at a prime.** The valuation subring `A` of `L` contains the
image of `B`, and the elements of `B` that are nonunits of `A` form the ideal `P`. Then `P` is
prime (`ValuationSubring.IsCenteredAt.isPrime`); it is Tau Ceti's `Valuation.centerIdeal` of the
valuation of `A` (`ValuationSubring.IsCenteredAt.eq_centerIdeal`). -/
structure IsCenteredAt (A : ValuationSubring L) (P : Ideal B) : Prop where
  /-- The valuation subring contains the image of `B`. -/
  algebraMap_mem (b : B) : algebraMap B L b ∈ A
  /-- An element of `B` lies in `P` exactly when its image is a nonunit of `A`. -/
  algebraMap_mem_nonunits_iff (b : B) : algebraMap B L b ∈ A.nonunits ↔ b ∈ P

/-- A valuation subring containing the image of `B` is centred at the centre ideal of its
valuation. -/
theorem isCenteredAt_centerIdeal (A : ValuationSubring L)
    (hA : ∀ b : B, A.valuation (algebraMap B L b) ≤ 1) :
    A.IsCenteredAt (A.valuation.centerIdeal B hA) where
  algebraMap_mem b := (A.valuation_le_one_iff _).mp (hA b)
  algebraMap_mem_nonunits_iff b := by rw [mem_nonunits_iff, Valuation.mem_centerIdeal]

namespace IsCenteredAt

variable {A : ValuationSubring L} {P Q : Ideal B}

/-- The valuation of `A` is at most `1` on the image of `B`. -/
theorem valuation_algebraMap_le_one (h : A.IsCenteredAt P) (b : B) :
    A.valuation (algebraMap B L b) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (h.algebraMap_mem b)

/-- The valuation of `A` is below `1` exactly on the image of `P`. -/
theorem valuation_algebraMap_lt_one_iff (h : A.IsCenteredAt P) (b : B) :
    A.valuation (algebraMap B L b) < 1 ↔ b ∈ P := by
  rw [← mem_nonunits_iff, h.algebraMap_mem_nonunits_iff]

/-- The valuation of `A` is `1` exactly on the image of the complement of `P`. -/
theorem valuation_algebraMap_eq_one_iff (h : A.IsCenteredAt P) (b : B) :
    A.valuation (algebraMap B L b) = 1 ↔ b ∉ P := by
  rw [← h.valuation_algebraMap_lt_one_iff, not_lt, le_antisymm_iff,
    and_iff_right (h.valuation_algebraMap_le_one b)]

/-- The centre is Tau Ceti's `Valuation.centerIdeal` of the valuation of `A`. -/
theorem eq_centerIdeal (h : A.IsCenteredAt P) :
    P = A.valuation.centerIdeal B h.valuation_algebraMap_le_one := by
  ext b
  rw [Valuation.mem_centerIdeal, h.valuation_algebraMap_lt_one_iff]

/-- The centre of a valuation subring is a prime ideal. -/
theorem isPrime (h : A.IsCenteredAt P) : P.IsPrime :=
  h.eq_centerIdeal ▸ Valuation.isPrime_centerIdeal _

/-- A valuation subring has only one centre. -/
theorem unique (h : A.IsCenteredAt P) (h' : A.IsCenteredAt Q) : P = Q := by
  ext b
  rw [← h.algebraMap_mem_nonunits_iff, h'.algebraMap_mem_nonunits_iff]

/-- A valuation subring centred at a nonzero ideal of a ring embedded in `L` is not `L`: a nonzero
element of the centre is a nonzero nonunit. -/
theorem ne_top_of_ne_bot (h : A.IsCenteredAt P) (hB : Function.Injective (algebraMap B L))
    (hP : P ≠ ⊥) : A ≠ ⊤ := by
  rintro rfl
  obtain ⟨b, hbP, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hb := (h.algebraMap_mem_nonunits_iff b).mpr hbP
  rw [mem_nonunits_iff_or, or_iff_left (not_not.mpr (mem_top _)), map_eq_zero_iff _ hB] at hb
  exact hb0 hb

section Action

variable {G : Type*} [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
  [SMulDistribClass G B L]

/-- **Equivariance of the centre**: if `A` is centred at `P`, then `g • A` is centred at
`g • P`. -/
theorem smul (h : A.IsCenteredAt P) (g : G) : (g • A).IsCenteredAt (g • P) where
  algebraMap_mem b := by
    rw [mem_pointwise_smul_iff_inv_smul_mem, ← algebraMap.smul']
    exact h.algebraMap_mem _
  algebraMap_mem_nonunits_iff b := by
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h.algebraMap_mem_nonunits_iff,
      algebraMap.smul', ← smul_mem_nonunits_pointwise_smul_iff (g := g) (x := g⁻¹ • _),
      smul_inv_smul]

/-- The stabilizer of a valuation subring stabilizes its centre. -/
theorem stabilizer_le (h : A.IsCenteredAt P) :
    MulAction.stabilizer G A ≤ MulAction.stabilizer G P := fun g hg ↦
  ((MulAction.mem_stabilizer_iff.mp hg ▸ h.smul g).unique h)

/-- If `g` raises every element of `A` to the `q`-th power modulo the nonunits of `A`, it raises
every element of `B` to the `q`-th power modulo the centre. -/
theorem smul_sub_pow_mem_of_forall (h : A.IsCenteredAt P) {g : G} {q : ℕ}
    (hg : ∀ x ∈ A, g • x - x ^ q ∈ A.nonunits) (b : B) : g • b - b ^ q ∈ P := by
  rw [← h.algebraMap_mem_nonunits_iff, map_sub, map_pow, algebraMap.smul']
  exact hg _ (h.algebraMap_mem b)

end Action

end IsCenteredAt

end ValuationSubring
