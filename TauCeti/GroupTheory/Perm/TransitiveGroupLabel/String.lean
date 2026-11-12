/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Basic
import Std.Data.String.ToNat
-- Exhaustive recognition checks compute with the table sizes and decimal rendering.
import all TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Basic
import all Init.Data.ToString.Basic
import all Init.Data.Repr

/-!
# Literal transitive-group labels

The reference transitive groups have zero-based indices, whereas the external label `nTj`
uses a one-based group number. `transitiveGroupLabelString` renders an index in this notation,
and `parseTransitiveGroupLabel` recognizes exactly these strings, with no whitespace, leading
zeroes, or suffixes. Recognition searches the finite reference table (currently degrees one
through five), so unsupported degrees are rejected rather than assigned a spurious reference
group. `parseTransitiveGroupLabel_eq_some_iff` is both soundness and completeness of recognition;
the returned index can be used directly with `TransitiveGroupLabel` and `referenceSubgroup`.

## References

* LMFDB, *Transitive groups*, entries of degrees at most five.
* G. Butler and J. McKay, *The transitive groups of degree up to eleven*.
-/

public section

namespace TauCeti

/-- The external `nTj` string of a zero-based reference-group index. -/
def transitiveGroupLabelString (n : ℕ) (j : TransitiveGroupIndex n) : String :=
  toString n ++ "T" ++ toString (j.val + 1)

/-- A literal reference-group label uses the degree, an uppercase `T`, and the one-based index. -/
theorem transitiveGroupLabelString_def (n : ℕ) (j : TransitiveGroupIndex n) :
    transitiveGroupLabelString n j = toString n ++ "T" ++ toString (j.val + 1) := (rfl)

/-- Distinct reference-group indices in a fixed degree have distinct literal labels. -/
theorem transitiveGroupLabelString_injective (n : ℕ) :
    Function.Injective (transitiveGroupLabelString n) := by
  intro j k h
  apply Fin.val_injective
  simpa only [transitiveGroupLabelString_def, String.append_right_inj,
    Nat.toString_eq_repr, Nat.repr_inj, Nat.add_right_cancel_iff] using h

/-- Recognize a literal `nTj` label in degree `n`, returning its zero-based reference-group index.
Only the degrees supported by `numTransitiveGroups` are recognized. -/
def parseTransitiveGroupLabel (n : ℕ) (s : String) : Option (TransitiveGroupIndex n) :=
  (List.finRange (numTransitiveGroups n)).find? fun j => transitiveGroupLabelString n j == s

/-- Recognition succeeds exactly for the literal label of the returned reference-group index.
In particular, a successful parse checks the degree, the separator and the one-based number. -/
@[simp] theorem parseTransitiveGroupLabel_eq_some_iff {n : ℕ} {s : String}
    {j : TransitiveGroupIndex n} :
    parseTransitiveGroupLabel n s = some j ↔ s = transitiveGroupLabelString n j := by
  constructor
  · intro h
    have hh := List.find?_some (p := fun k => transitiveGroupLabelString n k == s) h
    exact (beq_iff_eq.mp hh).symm
  · intro h
    have hex : (parseTransitiveGroupLabel n s).isSome :=
      List.find?_isSome.mpr ⟨j, by simp, by simp [h]⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hex
    have hh := List.find?_some (p := fun k => transitiveGroupLabelString n k == s) hk
    have hkj := transitiveGroupLabelString_injective n ((beq_iff_eq.mp hh).trans h)
    exact hkj ▸ hk

/-- Rendering and then recognizing a reference-group index recovers that index. -/
@[simp] theorem parseTransitiveGroupLabel_labelString (n : ℕ) (j : TransitiveGroupIndex n) :
    parseTransitiveGroupLabel n (transitiveGroupLabelString n j) = some j :=
  parseTransitiveGroupLabel_eq_some_iff.mpr rfl

/-- Recognition fails exactly when no supported reference-group index has the input label. -/
@[simp] theorem parseTransitiveGroupLabel_eq_none_iff (n : ℕ) (s : String) :
    parseTransitiveGroupLabel n s = none ↔ ∀ j, s ≠ transitiveGroupLabelString n j := by
  simp [Option.eq_none_iff_forall_not_mem]

/-- No literal label is recognized in a degree for which there are no reference groups. -/
theorem parseTransitiveGroupLabel_eq_none_of_numTransitiveGroups_eq_zero {n : ℕ}
    (hn : numTransitiveGroups n = 0) (s : String) :
    parseTransitiveGroupLabel n s = none := by
  rw [parseTransitiveGroupLabel_eq_none_iff]
  intro j
  have := j.isLt
  omega

/-- The five labels in degree four are recognized with zero-based indices. -/
example :
    (["4T1", "4T2", "4T3", "4T4", "4T5"].map
      (fun s => (parseTransitiveGroupLabel 4 s).map Fin.val)) =
      [some 0, some 1, some 2, some 3, some 4] := by
  decide +kernel

/-- Noncanonical decimal spellings, zero or out-of-range group numbers, wrong degrees,
whitespace and suffixes are not accepted as degree-four group labels. -/
example :
    (["04T1", "4T01", "4T0", "4T6", "3T1", "4t1", " 4T1", "4T1 ", "4T1-a"].map
      (parseTransitiveGroupLabel 4)) = List.replicate 9 none := by
  decide +kernel

end TauCeti
