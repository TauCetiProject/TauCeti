/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum
import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# Surjectivity of the sum of local Brauer invariants

The sum of local invariants in the global Brauer sequence

```text
0 → Br K → ⨁_v Br K_v → ℚ/ℤ → 0
```

has an additive section supported at any chosen finite place. The local invariant is an
additive equivalence at that place, so every element of `ℚ/ℤ` is the invariant of a family
supported there. In particular, `sumLocalInv` is surjective.

The same calculation shows that a family of local Brauer classes can be adjusted at one finite
place to have any prescribed total invariant, and that the adjustment is unique. This is a
statement about local families; it does not assert that a family of total invariant zero is the
localization of a global Brauer class.

The section uses `DFinsupp.singleAddHom` and the inverse of
`TauCeti.ClassFieldTheory.invMap`, the local invariant normalized by arithmetic Frobenius.
The single-place API takes an explicit decidable-equality instance, as `DFinsupp.single` does,
so its equations rewrite families constructed with any such instance. Consumers may supply it
with `classical`; the surjectivity theorem itself needs no decidable-equality instance.

## Main definitions

* `TauCeti.ClassFieldTheory.sumLocalInvSection`: an additive section supported at a chosen
  finite place.

## Main statements

* `TauCeti.ClassFieldTheory.sumLocalInvSection_apply`: the section's single-supported family.
* `TauCeti.ClassFieldTheory.sumLocalInv_sumLocalInvSection`: the section is a right inverse.
* `TauCeti.ClassFieldTheory.sumLocalInv_surjective`: the sum of local invariants is surjective.
* `TauCeti.ClassFieldTheory.sumLocalInv_add_single_eq_iff`: the unique adjustment at a finite
  place giving a prescribed total invariant.

## References

* J. S. Milne, *Class Field Theory*, Chapter VIII, §4, Theorem 4.2.
-/

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField

variable (K : Type) [Field K] [NumberField K]
variable [DecidableEq (HeightOneSpectrum (𝓞 K))]

/-- An additive section of the sum of local invariants, supported at the chosen finite place
`v`. Its class at `v` has invariant the given element of `ℚ/ℤ`. -/
def sumLocalInvSection (v : HeightOneSpectrum (𝓞 K)) :
    AddCircle (1 : ℚ) →+
      (Π₀ w : HeightOneSpectrum (𝓞 K), Br (w.adicCompletion K)) ×
        ((w : InfinitePlace K) → Br w.Completion) :=
  ((DFinsupp.singleAddHom _ v).comp (invMap (v.adicCompletion K)).symm.toAddMonoidHom).prod 0

/-- The section is the family supported at `v` with the prescribed local invariant. -/
@[simp]
theorem sumLocalInvSection_apply (v : HeightOneSpectrum (𝓞 K)) (r : AddCircle (1 : ℚ)) :
    sumLocalInvSection K v r = (DFinsupp.single v ((invMap (v.adicCompletion K)).symm r), 0) :=
  (rfl)

/-- Taking the sum of local invariants after the section recovers the prescribed invariant. -/
theorem sumLocalInv_sumLocalInvSection (v : HeightOneSpectrum (𝓞 K))
    (r : AddCircle (1 : ℚ)) : sumLocalInv K (sumLocalInvSection K v r) = r := by
  simp [sumLocalInvSection_apply]

omit [DecidableEq (HeightOneSpectrum (𝓞 K))] in
/-- The sum of local Brauer invariants is surjective for every number field. -/
theorem sumLocalInv_surjective : Function.Surjective (sumLocalInv K) := by
  classical
  let v : HeightOneSpectrum (𝓞 K) := Classical.arbitrary _
  exact Function.RightInverse.surjective (sumLocalInv_sumLocalInvSection K v)

/-- A prescribed total invariant determines the unique adjustment of a local family at a
chosen finite place. -/
theorem sumLocalInv_add_single_eq_iff (v : HeightOneSpectrum (𝓞 K))
    (y : (Π₀ w : HeightOneSpectrum (𝓞 K), Br (w.adicCompletion K)) ×
      ((w : InfinitePlace K) → Br w.Completion))
    (x : Br (v.adicCompletion K)) (r : AddCircle (1 : ℚ)) :
    sumLocalInv K (y + (DFinsupp.single v x, 0)) = r ↔
      x = (invMap (v.adicCompletion K)).symm (r - sumLocalInv K y) := by
  rw [map_add, sumLocalInv_single, AddEquiv.eq_symm_apply, eq_sub_iff_add_eq, add_comm]

end TauCeti.ClassFieldTheory
