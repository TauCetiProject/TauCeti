/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Canonical.AmbientGroup
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius

/-!
# Frobenius on the canonical Lie-type ambient group

For a valid Lie-type index `d` of characteristic `p`, `d.canonicalFrobenius k` is the
`p ^ k`-power Frobenius on the entire canonical ambient group. In particular,
`d.canonicalFrobenius 1` is the prime-field map in the half-Frobenius square law
`τ ^ 2 = Frob_p`. The map `d.canonicalFrobenius d.fieldExponent` is the `q`-power field
factor of ordinary and graph-twisted Steinberg maps; when `d.fieldExponent = 2 * m + 1`,
it also occurs in `(τ ^ (2 * m + 1)) ^ 2 = Frob_q`. Keeping the exponent as an argument
covers both the prime-field square law and Steinberg iterates.

This specializes `DynkinType.ChevalleyDatum.frobenius` at the full-weight datum and the
index's algebraic closure. It is induced by the field map, not reconstructed from root
values or transported from one of the represented models. Its equations hold on every
root subgroup, including negative and nonsimple roots, and on the canonical torus in
fundamental-weight coordinates. No generation theorem for the ambient group is assumed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 10–11.
* R. W. Carter, *Finite Groups of Lie Type*, §1.17.
-/

public section

namespace TauCeti.ValidLieTypeIndex

noncomputable section

variable (d : ValidLieTypeIndex)

/-- The `p ^ k`-power Frobenius on all canonical ambient points, where `p` is the indexed
characteristic. At `k = d.fieldExponent` this is the indexed `q`-power Frobenius. -/
def canonicalFrobenius (k : ℕ) : _root_.Monoid.End d.CanonicalAmbientGroup :=
  (d.dynkinType.scChevalleyDatum d.dynkinType_valid).frobenius d.characteristic k d.Closure

/-- Canonical Frobenius is the Frobenius of the full-weight Chevalley datum. -/
theorem canonicalFrobenius_def (k : ℕ) :
    d.canonicalFrobenius k =
      (d.dynkinType.scChevalleyDatum d.dynkinType_valid).frobenius
        d.characteristic k d.Closure :=
  (rfl)

/-- On underlying matrices, canonical Frobenius applies field Frobenius entrywise. -/
@[simp]
theorem coe_canonicalFrobenius (k : ℕ) (g : d.CanonicalAmbientGroup) :
    (d.canonicalFrobenius k g : Matrix.GeneralLinearGroup
        (Fin (d.dynkinType.scWeightBasisCard d.dynkinType_valid)) d.Closure) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius d.Closure d.characteristic k) g := by
  rw [canonicalFrobenius_def]
  exact (d.dynkinType.scChevalleyDatum d.dynkinType_valid).coe_frobenius
    d.characteristic k d.Closure g

/-- Canonical Frobenius raises every root parameter to its `p ^ k`-th power. -/
@[simp]
theorem canonicalFrobenius_canonicalRootSubgroup (k : ℕ)
    (γ : Fin d.dynkinType.numRoots) (u : Multiplicative d.Closure) :
    d.canonicalFrobenius k (d.canonicalRootSubgroup γ u) =
      d.canonicalRootSubgroup γ
        (Multiplicative.ofAdd (u.toAdd ^ d.characteristic ^ k)) := by
  rw [canonicalFrobenius_def, canonicalRootSubgroup_def]
  have h := (d.dynkinType.scChevalleyDatum d.dynkinType_valid).frobenius_rootSubgroupPoints
    d.characteristic k d.Closure γ u.toAdd
  rw [ofAdd_toAdd] at h
  exact h

/-- On the canonical torus, Frobenius raises every fundamental-weight coordinate to its
`p ^ k`-th power. -/
@[simp]
theorem canonicalFrobenius_canonicalTorus (k : ℕ)
    (s : Fin d.dynkinType.rank → d.Closureˣ) :
    d.canonicalFrobenius k (d.canonicalTorus s) =
      d.canonicalTorus (s ^ d.characteristic ^ k) := by
  rw [canonicalFrobenius_def, canonicalTorus_def]
  exact (d.dynkinType.scChevalleyDatum d.dynkinType_valid).frobenius_torusPoints
    d.characteristic k d.Closure s

/-- The character pullback of canonical Frobenius is multiplication by `p ^ k` on the
full weight lattice. -/
theorem isCharacterMap_canonicalFrobenius (k : ℕ) :
    IsCharacterMap d.canonicalTorus (d.canonicalFrobenius k)
      ((d.characteristic ^ k : ℕ) • 1) := by
  rw [canonicalFrobenius_def, canonicalTorus_def]
  exact (d.dynkinType.scChevalleyDatum d.dynkinType_valid).isCharacterMap_frobenius
    d.characteristic k d.Closure

/-- The zeroth canonical Frobenius is the identity on the whole ambient group. -/
@[simp]
theorem canonicalFrobenius_zero : d.canonicalFrobenius 0 = 1 := by
  rw [canonicalFrobenius_def]
  exact (d.dynkinType.scChevalleyDatum d.dynkinType_valid).frobenius_zero
    d.characteristic d.Closure

/-- Adding Frobenius exponents composes the corresponding canonical point maps. -/
theorem canonicalFrobenius_add (k m : ℕ) :
    d.canonicalFrobenius (k + m) = d.canonicalFrobenius k * d.canonicalFrobenius m := by
  simp only [canonicalFrobenius_def]
  exact (d.dynkinType.scChevalleyDatum d.dynkinType_valid).frobenius_add
    d.characteristic k d.Closure m

/-- The `m`-th iterate of canonical `p ^ k`-Frobenius is canonical `p ^ (k * m)`-Frobenius.
Powers here use composition of endomorphisms. -/
theorem canonicalFrobenius_pow (k m : ℕ) :
    d.canonicalFrobenius k ^ m = d.canonicalFrobenius (k * m) := by
  simp only [canonicalFrobenius_def]
  exact (d.dynkinType.scChevalleyDatum d.dynkinType_valid).frobenius_pow
    d.characteristic k d.Closure m

end

end TauCeti.ValidLieTypeIndex
