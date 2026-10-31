/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Real
public import Mathlib.ModelTheory.Algebra.Ring.Definability
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.QuantifierElimination
public import TauCeti.ModelTheory.Order

/-!
# Semialgebraic sets are the sets definable in the field language

Over a real closed field the order is definable from the ring operations: `x` is positive exactly
when `x * z ^ 2 = 1` for some `z`. Consequently every semialgebraic subset of `σ → R` is already
definable with parameters in the first-order language of rings `Language.ring`, without the order
symbol. When semialgebraic sets are closed under projection, as they are over `ℝ` by the
Tarski–Seidenberg theorem, the converse holds as well. Then the semialgebraic sets, the sets
definable in the language of rings and the sets definable in the language of ordered rings all
coincide.

Following Mathlib, statements about first-order structures on a concrete ring take the structures
as instance hypotheses, since `FirstOrder.Ring.compatibleRingOfRing` and
`FirstOrder.Language.orderStructure` are not global instances. With these two structures
installed on `R`, the instances of `TauCeti.ModelTheory.Order` make the sum-language structure an
ordered structure, so the results of
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.QuantifierElimination` apply. The theorems
`TauCeti.isSemialgebraic_iff_definable_ring_real` and `TauCeti.isSemialgebraic_iff_definable_real`
install them on `ℝ` and state the identification there with no hypothesis.

## Main results

* `TauCeti.IsSemialgebraic.definable_ring`: over a real closed field, a semialgebraic set is
  definable with parameters in the language of rings.
* `TauCeti.isSemialgebraic_iff_definable_ring`: given projection closure, a subset of `σ → R` is
  semialgebraic if and only if it is definable with parameters in the language of rings.
* `TauCeti.definable_ring_iff_definable`: given projection closure, the order symbol adds no
  definable sets.
* `TauCeti.isSemialgebraic_iff_definable_ring_real`, `TauCeti.isSemialgebraic_iff_definable_real`:
  the semialgebraic subsets of `σ → ℝ` are the sets definable with parameters in the field `ℝ`,
  and in the ordered field `ℝ`.

## References

* S. Basu, R. Pollack, and M.-F. Roy,
  [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
  second edition, Sections 2.3 and 2.4.
* D. Marker, *Model Theory: An Introduction*, Graduate Texts in Mathematics 217, Springer (2002),
  Section 3.3.
-/

public section

open FirstOrder FirstOrder.Language MvPolynomial Set

namespace TauCeti

section Converse

variable {R : Type*} [CommRing R] [Ring.CompatibleRing R] [LinearOrder R] [IsOrderedAddMonoid R]
  [HasSemialgebraicProjections R] {σ : Type*}

/-- Given projection closure, a subset of `σ → R` definable with parameters in the language of
rings is semialgebraic. -/
theorem _root_.Set.Definable.isSemialgebraic_of_ring {A : Set R} {s : Set (σ → R)}
    (hs : A.Definable Language.ring s) : IsSemialgebraic s := by
  -- Expand by the order of `R` and eliminate quantifiers in the language of ordered rings.
  let _ := orderStructure R
  exact (hs.map_expansion (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order))
    |>.isSemialgebraic

end Converse

variable {R : Type*} [Field R] [Ring.CompatibleRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R] {σ : Type*}

/-- **The order of a real closed field is definable from its ring operations.** A semialgebraic
subset of `σ → R` is definable with parameters from `R` in the language of rings. Zero sets are
definable by equations, and the positivity set of `p` is the projection of the zero set of
`p * z ^ 2 - 1`, since the positive elements of `R` are its nonzero squares. -/
theorem IsSemialgebraic.definable_ring {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    (univ : Set R).Definable Language.ring s := by
  have hzero {τ : Type _} (q : MvPolynomial τ R) :
      (univ : Set R).Definable Language.ring {v | eval v q = 0} := by
    simpa [zeroLocus_span] using
      (Ring.mvPolynomial_zeroLocus_definable {q}).mono (subset_univ _)
  refine IsSemialgebraic.induction hzero (fun p ↦ ?_) definable_empty
    (fun _ _ h ↦ h.compl) (fun _ _ _ _ h₁ h₂ ↦ h₁.union h₂) hs
  -- `0 < a` exactly when `a * z ^ 2 = 1` for some `z`.
  convert (hzero (rename Sum.inl p * X (Sum.inr ()) ^ 2 - 1 :
    MvPolynomial (σ ⊕ Unit) R)).exists_of_finite (β := Unit) using 1
  ext v
  simp only [mem_ofPred_eq, map_sub, map_mul, map_pow, eval_rename, eval_X, map_one,
    Sum.elim_comp_inl, Sum.elim_inr, sub_eq_zero]
  constructor
  · intro hp
    obtain ⟨r, hr⟩ := IsRealClosed.nonneg_iff_isSquare.1 hp.le
    have hr0 : r ≠ 0 := by rintro rfl; simp [hr] at hp
    exact ⟨fun _ ↦ r⁻¹, by rw [hr]; field_simp⟩
  · rintro ⟨u, hu⟩
    exact pos_of_mul_pos_left (hu ▸ one_pos) (sq_nonneg (u ()))

variable [HasSemialgebraicProjections R]

/-- **Tarski's theorem in the field language.** Given projection closure, a subset of `σ → R` is
semialgebraic if and only if it is definable in the language of rings with parameters from `R`. -/
theorem isSemialgebraic_iff_definable_ring {s : Set (σ → R)} :
    IsSemialgebraic s ↔ (univ : Set R).Definable Language.ring s :=
  ⟨IsSemialgebraic.definable_ring, Set.Definable.isSemialgebraic_of_ring⟩

/-- Given projection closure, a subset of `σ → R` is definable with parameters in the language of
rings if and only if it is definable with parameters in the language of ordered rings, for any
structure on `R` interpreting `≤` as the order of `R`. -/
theorem definable_ring_iff_definable [Language.order.Structure R]
    [(Language.ring.sum Language.order).OrderedStructure R] {s : Set (σ → R)} :
    (univ : Set R).Definable Language.ring s ↔
      (univ : Set R).Definable (Language.ring.sum Language.order) s := by
  rw [← isSemialgebraic_iff_definable_ring, isSemialgebraic_iff_definable]

/-- **Tarski's theorem for the real field.** A subset of `σ → ℝ` is semialgebraic if and only if
it is definable with parameters in the field `ℝ`, that is, in the language of rings with its usual
interpretation. -/
theorem isSemialgebraic_iff_definable_ring_real {s : Set (σ → ℝ)} :
    IsSemialgebraic s ↔
      letI := Ring.compatibleRingOfRing ℝ
      (univ : Set ℝ).Definable Language.ring s :=
  letI := Ring.compatibleRingOfRing ℝ
  isSemialgebraic_iff_definable_ring

/-- A subset of `σ → ℝ` is semialgebraic if and only if it is definable with parameters in the
ordered field `ℝ`, that is, in the language of ordered rings with its usual interpretation. -/
theorem isSemialgebraic_iff_definable_real {s : Set (σ → ℝ)} :
    IsSemialgebraic s ↔
      letI := Ring.compatibleRingOfRing ℝ
      letI := orderStructure ℝ
      (univ : Set ℝ).Definable (Language.ring.sum Language.order) s :=
  letI := Ring.compatibleRingOfRing ℝ
  letI := orderStructure ℝ
  isSemialgebraic_iff_definable

end TauCeti
