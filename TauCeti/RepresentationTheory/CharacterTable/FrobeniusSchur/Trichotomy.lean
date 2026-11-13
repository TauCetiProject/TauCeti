/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.InvariantForm.Squares
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# The Frobenius-Schur trichotomy

`TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants` computes the indicator
`ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)` as the signed count `dim (Sym²V)ᴳ - dim (Λ²V)ᴳ` of invariants in the two
squares.  This file turns those two invariant counts into counts of **bilinear forms** on `V`, by
the identification of `TauCeti/RepresentationTheory/InvariantForm/Squares.lean`, and reads the
trichotomy off it.

The dictionary is elementary.  A functional on `Sym²V` becomes a bilinear form on `V` by composing
with the universal multilinear map, and the form it produces is symmetric because the symmetric
square does not see the order of its two arguments; a functional on `Λ²V` becomes a form in the
same way, and the form it produces is alternating because a repeated argument wedges to zero.
Both assignments are injective, and the universal property of each square makes them surjective
onto the symmetric, respectively alternating, forms.  The assignments carry invariant functionals
to invariant forms, and every invariant symmetric, respectively alternating, form arises this way.
So over a field in which `|G|` is invertible the two `finrank` equalities
`dim {invariant symmetric forms} = dim (Sym²V)ᴳ` and
`dim {invariant alternating forms} = dim (Λ²V)ᴳ` hold
(`Representation.finrank_symmetricInvariantForms` and
`Representation.finrank_alternatingInvariantForms`); when the invariant spaces are
infinite-dimensional both sides are `0`, by the convention that `finrank` of an infinite-dimensional
space is `0`. For a finite-dimensional representation
over a field in which `|G|` is invertible,
`TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariantForms` gives the signed
count of invariant forms:

`ν₂(ρ) = dim {invariant symmetric forms} - dim {invariant alternating forms}`.

On an **irreducible** representation over an algebraically closed field the invariant forms are at
most a line, and `TauCeti.Representation.IsInvariantForm.isSymm_or_isAlt` says a nonzero one is
symmetric or alternating.  Away from characteristic two no nonzero form is both, so the two counts
are `1, 0` or `0, 1` or `0, 0`, which is the **trichotomy**: `ν₂(ρ)` is `1` when `ρ` carries a
nonzero invariant symmetric form (the orthogonal case), `-1` when it carries a nonzero invariant
alternating form (the symplectic, or quaternionic, case), and `0` when it carries no nonzero
invariant form at all (the complex case).  The nonzero invariant form of the first two cases is
automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`.  That the indicator takes only these three
values needs no hypothesis on the characteristic: each of the two counts is at most the count `0`
or `1` of all invariant forms, and when `(|G| : k) = 0` the indicator is `0` by the convention
`0⁻¹ = 0`.

Currying identifies the invariant forms with the invariant functionals on the tensor square
`V ⊗ V` (`Representation.map_lcurry_eq_invariantForms`), so over a field in which `|G|` is
invertible `Representation.finrank_invariantForms_eq_finrank_invariants_tprod_self` says that the
invariant forms and the invariants of `V ⊗ V` have the same `finrank`: the same dimension when
finite-dimensional, and `0` on both sides, by convention, otherwise.  Both lemmas are in
`TauCeti/RepresentationTheory/InvariantForm.lean`.

Characteristic zero does three jobs, and nothing else: it moves the splitting of that count over
the two squares from an equation in `k` to an equation of natural numbers, it keeps a form from
being symmetric and alternating at once, and it supplies `Invertible (Nat.card G : k)` in the
statements that do not assume it.  Averaging characters produces identities in `k` and nothing
more, so for a finite-dimensional `V` over a field `k` in which `|G|` is invertible the splitting is
stated first in that form (`TauCeti.Representation.finrank_invariantForms_cast`); in characteristic
`p` it is an identity of residues, and it is the injectivity of `ℕ → k` that turns it into an
equality of dimensions, for a finite group.

Three ingredients come from earlier modules and are only applied here.  The invariant forms
themselves and the symmetric and the alternating ones among them are in
`TauCeti/RepresentationTheory/InvariantForm.lean`; the dictionary turning a functional on either
square into a form is `TauCeti.BilinForm.ofSymmetricSquareDual` and
`TauCeti.BilinForm.ofExteriorSquareDual`, in `TauCeti/LinearAlgebra/BilinearForm/Squares.lean`; and
the fact that the dictionary carries the invariant functionals onto the invariant forms, with the
two counts that follow, is in `TauCeti/RepresentationTheory/InvariantForm/Squares.lean`.  What this
file adds is the count of all invariant forms, the indicator as a signed count, and the
trichotomy.

## Main results

* `TauCeti.Representation.finrank_invariantForms`: **the invariant forms are as many as the
  invariants of the two squares together**, for a finite-dimensional representation of a finite
  group over a field of characteristic zero, as natural numbers; for a finite-dimensional `V` over a
  field in which `|G|` is invertible it holds as an identity in `k`
  (`TauCeti.Representation.finrank_invariantForms_cast`).
* `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariantForms`: **the indicator is
  the signed count of invariant forms**, `ν₂(ρ) = dim {symmetric} - dim {alternating}`.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff`,
  `TauCeti.Representation.frobeniusSchurIndicator_eq_neg_one_iff` and
  `TauCeti.Representation.frobeniusSchurIndicator_eq_zero_iff`: **the trichotomy**, each value of
  the indicator characterized by the invariant forms, for an irreducible representation over an
  algebraically closed field of characteristic zero.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one`: the indicator
  of an irreducible representation over an algebraically closed field takes only the values `1`,
  `0` and `-1`, in every characteristic.

## Implementation notes

The identifications of the invariant symmetric and alternating forms with the invariant
functionals on the two squares (`TauCeti/RepresentationTheory/InvariantForm/Squares.lean`), and the
one for the tensor square (`TauCeti/RepresentationTheory/InvariantForm.lean`), hold over any
commutative ring, with no finiteness assumption.  The dimension counts read off them need `k` to be
a field in which `|G|` is invertible; they equate `finrank`s, so on an infinite-dimensional
invariant space both sides are `0` by convention.  The results of this file take the field in
`Type`, as `TauCeti.Representation.frobeniusSchurIndicator` does.

What connects the submodule of invariant forms to the character machinery is currying:
`Representation.map_lcurry_eq_invariantForms` identifies it with the invariant functionals on
`V ⊗ V`, `TauCeti.Representation.finrank_invariants_dual` counts those as the invariants of
`V ⊗ V`, and Mathlib's `Representation.card_inv_mul_sum_char_eq_finrank` counts the invariants of
`V ⊗ V` by characters.

The dimension lemmas used below are stated for an abstract module and applied with that module
supplied explicitly.  The reason is mechanical: the `AddCommMonoid` structure on a space of
bilinear forms is the one on linear maps, and asking the elaborator to solve for an `AddCommGroup`
structure inducing it does not terminate quickly.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
-/

public section

open scoped TensorProduct

open Module (finrank)

universe v w

variable {k : Type} {G : Type v} {V : Type w}

namespace TauCeti

namespace Representation

open _root_.LinearMap (BilinForm)

/-! ### Counting the invariant forms -/

section Counting

variable [Field k] [Group G] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Finite G]

section Invertible

variable [Invertible (Nat.card G : k)]

omit [Finite G] in
/-- **The invariant forms are as many as the invariants of the two squares together**, as an
identity in `k`, for a finite-dimensional `V` over a field in which `|G|` is invertible: the
invariant forms have the `finrank` of the invariants of the tensor square
(`Representation.finrank_invariantForms_eq_finrank_invariants_tprod_self`), and
`TauCeti.Representation.finrank_invariants_tprod_self_cast` splits that count in two.

In characteristic `p` this is an identity of residues only; see
`TauCeti.Representation.finrank_invariantForms` for the characteristic-zero form. -/
theorem finrank_invariantForms_cast (ρ : Representation k G V) :
    (finrank k (invariantForms ρ) : k) =
      (finrank k (ρ.symmetricPower 2).invariants : k) +
        (finrank k (ρ.exteriorPower 2).invariants : k) := by
  rw [ρ.finrank_invariantForms_eq_finrank_invariants_tprod_self,
    finrank_invariants_tprod_self_cast]

end Invertible

variable [CharZero k]

/-- **The invariant forms are as many as the invariants of the two squares together**, as natural
numbers, for a finite-dimensional representation of a finite group over a field of characteristic
zero.  Characteristic zero is what lifts `TauCeti.Representation.finrank_invariantForms_cast` from
an identity in `k`. -/
theorem finrank_invariantForms (ρ : Representation k G V) :
    finrank k (invariantForms ρ) =
      finrank k (ρ.symmetricPower 2).invariants + finrank k (ρ.exteriorPower 2).invariants := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact_mod_cast finrank_invariantForms_cast ρ

end Counting

/-! ### The indicator as a signed count of invariant forms -/

section Indicator

variable [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Invertible (Nat.card G : k)]

/-- **The Frobenius-Schur indicator is the signed count of invariant bilinear forms**,
`ν₂(ρ) = dim {invariant symmetric forms} - dim {invariant alternating forms}`, for a
finite-dimensional representation over a field in which `|G|` is invertible. -/
theorem frobeniusSchurIndicator_eq_sub_finrank_invariantForms (ρ : Representation k G V) :
    frobeniusSchurIndicator ρ = (finrank k (symmetricInvariantForms ρ) : k) -
      (finrank k (alternatingInvariantForms ρ) : k) := by
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants, ρ.finrank_symmetricInvariantForms,
    ρ.finrank_alternatingInvariantForms]

end Indicator

/-! ### The trichotomy -/

section Trichotomy

variable [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) [ρ.IsIrreducible] {B : BilinForm k V}

omit [CharZero k] [IsAlgClosed k] [ρ.IsIrreducible] in
/-- **The complex case.** A representation with no nonzero invariant form has Frobenius-Schur
indicator `0`.  For a finite-dimensional representation over a field in which `|G|` is invertible
this is the count `ν₂(ρ) = 0 - 0`; when `(|G| : k) = 0` or `V` is infinite-dimensional,
`frobeniusSchurIndicator ρ` vanishes by the junk-value conventions `0⁻¹ = 0` and
`LinearMap.trace = 0`. -/
theorem frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot (h : invariantForms ρ = ⊥) :
    frobeniusSchurIndicator ρ = 0 := by
  by_cases hcard : (Nat.card G : k) = 0
  · rw [frobeniusSchurIndicator_def, hcard, inv_zero, zero_mul]
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  by_cases hV : FiniteDimensional k V
  swap
  · simp [frobeniusSchurIndicator_def, Representation.character,
      TauCeti.LinearMap.trace_eq_zero_of_not_finite hV]
  have hs : symmetricInvariantForms ρ = ⊥ :=
    le_bot_iff.mp (le_of_le_of_eq (symmetricInvariantForms_le ρ) h)
  have ha : alternatingInvariantForms ρ = ⊥ :=
    le_bot_iff.mp (le_of_le_of_eq (alternatingInvariantForms_le ρ) h)
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

/-- **The orthogonal case.** An irreducible representation carrying a nonzero invariant symmetric
form has Frobenius-Schur indicator `1`.  Such a form is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`. -/
theorem frobeniusSchurIndicator_eq_one_of_isSymm (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (hsymm : B.IsSymm) : frobeniusSchurIndicator ρ = 1 := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  have hone : finrank k (invariantForms ρ) = 1 := by
    rw [hB.invariantForms_eq_span hB0]
    exact finrank_span_singleton (K := k) (V := BilinForm k V) hB0
  have hle : 1 ≤ finrank k (symmetricInvariantForms ρ) :=
    Submodule.one_le_finrank_iff (R := k) (M := BilinForm k V) |>.mpr
      ((Submodule.ne_bot_iff _).mpr ⟨B, mem_symmetricInvariantForms.mpr ⟨hB, hsymm⟩, hB0⟩)
  have hadd := ρ.finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms
  have hs : finrank k (symmetricInvariantForms ρ) = 1 := by omega
  have ha : finrank k (alternatingInvariantForms ρ) = 0 := by omega
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

/-- **The symplectic case.** An irreducible representation carrying a nonzero invariant alternating
form has Frobenius-Schur indicator `-1`.  Such a form is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`. -/
theorem frobeniusSchurIndicator_eq_neg_one_of_isAlt (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (halt : B.IsAlt) : frobeniusSchurIndicator ρ = -1 := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  have hone : finrank k (invariantForms ρ) = 1 := by
    rw [hB.invariantForms_eq_span hB0]
    exact finrank_span_singleton (K := k) (V := BilinForm k V) hB0
  have hle : 1 ≤ finrank k (alternatingInvariantForms ρ) :=
    Submodule.one_le_finrank_iff (R := k) (M := BilinForm k V) |>.mpr
      ((Submodule.ne_bot_iff _).mpr ⟨B, mem_alternatingInvariantForms.mpr ⟨hB, halt⟩, hB0⟩)
  have hadd := ρ.finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms
  have hs : finrank k (symmetricInvariantForms ρ) = 0 := by omega
  have ha : finrank k (alternatingInvariantForms ρ) = 1 := by omega
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

omit [CharZero k] in
/-- **The Frobenius-Schur trichotomy.** The indicator of an irreducible representation over an
algebraically closed field takes only the values `1`, `0` and `-1`, in every characteristic.  The
invariant forms span at most a line, so when `|G|` is invertible in `k` the indicator, the signed
count `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariantForms`, is a
difference of two numbers in `{0, 1}`; when `(|G| : k) = 0` it is `0` by the convention
`0⁻¹ = 0`. -/
theorem frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one :
    frobeniusSchurIndicator ρ = 1 ∨ frobeniusSchurIndicator ρ = 0 ∨
      frobeniusSchurIndicator ρ = -1 := by
  by_cases hbot : invariantForms ρ = ⊥
  · exact Or.inr (Or.inl (frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot))
  by_cases hcard : (Nat.card G : k) = 0
  · exact Or.inr (Or.inl (by rw [frobeniusSchurIndicator_def, hcard, inv_zero, zero_mul]))
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  obtain ⟨B, hB, hB0⟩ := (Submodule.ne_bot_iff _).mp hbot
  have hspan := (mem_invariantForms.mp hB).invariantForms_eq_span hB0
  have hs := Submodule.finrank_mono ((symmetricInvariantForms_le ρ).trans hspan.le)
  have ha := Submodule.finrank_mono ((alternatingInvariantForms_le ρ).trans hspan.le)
  rw [finrank_span_singleton (K := k) (V := BilinForm k V) hB0] at hs ha
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms]
  interval_cases finrank k (symmetricInvariantForms ρ) <;>
    interval_cases finrank k (alternatingInvariantForms ρ) <;> simp

/-- **The indicator is `1` exactly in the orthogonal case**, that is, exactly when the
representation carries a nondegenerate invariant symmetric form.  Nondegeneracy is nonvanishing
here, by `TauCeti.Representation.IsInvariantForm.nondegenerate_iff_ne_zero`. -/
theorem frobeniusSchurIndicator_eq_one_iff :
    frobeniusSchurIndicator ρ = 1 ↔
      ∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B.IsSymm ∧ B.Nondegenerate := by
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  refine ⟨fun h => ?_, fun ⟨_, hB, hsymm, hnd⟩ =>
    frobeniusSchurIndicator_eq_one_of_isSymm ρ hB (hB.nondegenerate_iff_ne_zero.mp hnd) hsymm⟩
  rcases exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot ρ with
    ⟨C, hC, hC0, hsymm⟩ | ⟨_, hB, hB0, halt⟩ | hbot
  · exact ⟨C, hC, hsymm, hC.nondegenerate hC0⟩
  · rw [frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB hB0 halt] at h
    exact absurd h (by norm_num)
  · rw [frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot] at h
    exact absurd h.symm one_ne_zero

/-- **The indicator is `-1` exactly in the symplectic case**, that is, exactly when the
representation carries a nondegenerate invariant alternating form.  Nondegeneracy is nonvanishing
here, by `TauCeti.Representation.IsInvariantForm.nondegenerate_iff_ne_zero`. -/
theorem frobeniusSchurIndicator_eq_neg_one_iff :
    frobeniusSchurIndicator ρ = -1 ↔
      ∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B.IsAlt ∧ B.Nondegenerate := by
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  refine ⟨fun h => ?_, fun ⟨_, hB, halt, hnd⟩ =>
    frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB (hB.nondegenerate_iff_ne_zero.mp hnd) halt⟩
  rcases exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot ρ with
    ⟨_, hB, hB0, hsymm⟩ | ⟨C, hC, hC0, halt⟩ | hbot
  · rw [frobeniusSchurIndicator_eq_one_of_isSymm ρ hB hB0 hsymm] at h
    exact absurd h (by norm_num)
  · exact ⟨C, hC, halt, hC.nondegenerate hC0⟩
  · rw [frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot] at h
    exact absurd h (by norm_num)

/-- **The indicator is `0` exactly in the complex case**, that is, exactly when the representation
carries no nonzero invariant bilinear form at all. -/
theorem frobeniusSchurIndicator_eq_zero_iff :
    frobeniusSchurIndicator ρ = 0 ↔ invariantForms ρ = ⊥ := by
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  refine ⟨fun h => ?_, frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ⟩
  rcases exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot ρ with
    ⟨_, hB, hB0, hsymm⟩ | ⟨_, hB, hB0, halt⟩ | hbot
  · rw [frobeniusSchurIndicator_eq_one_of_isSymm ρ hB hB0 hsymm] at h
    exact absurd h one_ne_zero
  · rw [frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB hB0 halt] at h
    exact absurd h (by norm_num)
  · exact hbot

end Trichotomy

end Representation

end TauCeti
