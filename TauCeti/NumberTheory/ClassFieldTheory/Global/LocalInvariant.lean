/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.BaseChange
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.InfinitePlace
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The local invariants of a global Brauer class

Let `K` be a number field. For every place of `K` this file defines the local invariant of a
cohomological Brauer class `x ∈ Br K = H²(G_K, (Kˢ)ˣ)`, the first ingredients of the global
Brauer sequence

```text
0 → Br K → ⨁_v Br K_v → ℚ/ℤ → 0.
```

The localization map at a place is base change `TauCeti.ClassFieldTheory.brBaseChange` to the
completion, that is, restriction to the decomposition group, and the local invariant is the
invariant of the local Brauer class:

* at a finite place `v`, `finiteInvAt K v x = inv_{K_v} (x ⊗ K_v)`, with the invariant
  `TauCeti.ClassFieldTheory.invMap` of the nonarchimedean local field `v.adicCompletion K`,
  normalized by arithmetic Frobenius;
* at an infinite place `w`, `infiniteInvAt K w x` is the archimedean invariant
  `TauCeti.ClassFieldTheory.infiniteInvMap w` of `x ⊗ K_w`, which is `0` at a complex place and
  `0` or `1/2` at a real place.

Both are additive in `x`, and each vanishes exactly when the localization of `x` does, since the
local invariant maps are injective. The invariants at the infinite places make sense, and are
defined, for every field with its infinite places.

## Main definitions

* `TauCeti.ClassFieldTheory.finiteInvAt K v`: the local invariant `Br K → ℚ/ℤ` at a finite place.
* `TauCeti.ClassFieldTheory.infiniteInvAt K w`: the local invariant `Br K → ℚ/ℤ` at an infinite
  place.

## Main results

* `TauCeti.ClassFieldTheory.finiteInvAt_eq_zero_iff`,
  `TauCeti.ClassFieldTheory.infiniteInvAt_eq_zero_iff`: a local invariant vanishes exactly when the
  localization does.
* `TauCeti.ClassFieldTheory.infiniteInvAt_eq_zero_of_isComplex`: the invariants at complex places
  vanish.
* `TauCeti.ClassFieldTheory.infiniteInvAt_mem_torsionBy_two`: the archimedean invariants are
  killed by `2`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (8.1.17).
* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField

variable (K : Type) [Field K]

/-! ### Infinite places -/

/-- **The local invariant at an infinite place** `w` of a field `K`: the archimedean invariant of
the localization `Br K → Br K_w`. -/
def infiniteInvAt (w : InfinitePlace K) : Br K →+ AddCircle (1 : ℚ) :=
  (infiniteInvMap w).comp (brBaseChange K w.Completion)

/-- The local invariant at an infinite place is the archimedean invariant of the localization. -/
theorem infiniteInvAt_apply (w : InfinitePlace K) (x : Br K) :
    infiniteInvAt K w x = infiniteInvMap w (brBaseChange K w.Completion x) :=
  (rfl)

/-- The local invariant at an infinite place vanishes exactly when the localization of the class
vanishes. -/
@[simp]
theorem infiniteInvAt_eq_zero_iff (w : InfinitePlace K) (x : Br K) :
    infiniteInvAt K w x = 0 ↔ brBaseChange K w.Completion x = 0 := by
  rw [infiniteInvAt_apply, infiniteInvMap_eq_zero_iff]

/-- The local invariant at a complex place vanishes. -/
theorem infiniteInvAt_eq_zero_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) (x : Br K) :
    infiniteInvAt K w x = 0 :=
  infiniteInvMap_eq_zero_of_isComplex w hw _

/-- The local invariants at the infinite places are killed by `2`: they lie in `{0, 1/2}`. -/
theorem infiniteInvAt_mem_torsionBy_two (w : InfinitePlace K) (x : Br K) :
    infiniteInvAt K w x ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ) := by
  rcases w.isReal_or_isComplex with hw | hw
  · have h : infiniteInvAt K w x ∈ Set.range (infiniteInvMap w) := ⟨_, rfl⟩
    rwa [range_infiniteInvMap_of_isReal w hw] at h
  · rw [infiniteInvAt_eq_zero_of_isComplex K w hw]
    exact zero_mem _

/-! ### Finite places -/

section Finite

variable [NumberField K]

/-- **The local invariant at a finite place** `v` of a number field `K`: the invariant of the
nonarchimedean local field `K_v` of the localization `Br K → Br K_v`,
`x ↦ inv_{K_v} (x ⊗ K_v)`. -/
def finiteInvAt (v : HeightOneSpectrum (𝓞 K)) : Br K →+ AddCircle (1 : ℚ) :=
  (invMap (v.adicCompletion K)).toAddMonoidHom.comp (brBaseChange K (v.adicCompletion K))

/-- The local invariant at a finite place is the invariant of the localization. -/
theorem finiteInvAt_apply (v : HeightOneSpectrum (𝓞 K)) (x : Br K) :
    finiteInvAt K v x = invMap (v.adicCompletion K) (brBaseChange K (v.adicCompletion K) x) :=
  (rfl)

/-- The local invariant at a finite place vanishes exactly when the localization of the class
vanishes. -/
@[simp]
theorem finiteInvAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : Br K) :
    finiteInvAt K v x = 0 ↔ brBaseChange K (v.adicCompletion K) x = 0 := by
  rw [finiteInvAt_apply, map_eq_zero_iff _ (invMap _).injective]

end Finite

end TauCeti.ClassFieldTheory
