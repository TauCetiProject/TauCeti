/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Cyclic
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.PowerMap
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Quaternion

/-!
# Regression examples: inverse, power, and fusion maps on class data

These downstream kernel checks exercise the `@[expose]`d definitions in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.PowerMap` across module boundaries on
`cyclicClassData 4` and `quaternionClassData 2`:

* `cyclicClassData 4` has non-real classes (`invIndex` swaps `1` and `3`), and a proper square map
  (`powIndex 2` sends both `1` and `3` to `2`);
* `zpowIndex (-1)` agrees with `invIndex` on `cyclicClassData 4`;
* fusing `cyclicClassData 4` into `quaternionClassData 2` along the cyclic rotation subgroup `⟨a⟩`
  collapses the inverse pair `1, 3` into a single real quaternion class of order `4`.
-/

namespace TauCeti.Examples

/-- The inverse-class map on `C₄` swaps the two generator classes `1` and `3`. -/
example :
    ((List.finRange (cyclicClassData 4).numClasses).map fun i =>
      ((cyclicClassData 4).invIndex i).val) = [0, 3, 2, 1] := by
  decide

/-- The square map on `C₄` sends both generator classes `1` and `3` to the order-2 class `2`. -/
example :
    ((List.finRange (cyclicClassData 4).numClasses).map fun i =>
      ((cyclicClassData 4).powIndex 2 i).val) = [0, 2, 0, 2] := by
  decide

/-- The `-1`-st integer power map on `C₄` agrees with the inverse-class map in the kernel. -/
example :
    ((List.finRange (cyclicClassData 4).numClasses).map fun i =>
      ((cyclicClassData 4).zpowIndex (-1) i).val) = [0, 3, 2, 1] := by
  decide

/-- Fusing `C₄` into `Q₈` as the rotation subgroup `⟨a⟩` identifies the inverse classes `1` and
`3`. -/
example :
    let φ : Multiplicative (ZMod 4) →* QuaternionGroup 2 :=
      { toFun := fun x => QuaternionGroup.a x.toAdd
        map_one' := rfl
        map_mul' := fun x y => by simp [QuaternionGroup.a_mul_a] }
    ((List.finRange (cyclicClassData 4).numClasses).map fun i =>
      ((cyclicClassData 4).fusion (quaternionClassData 2) φ i).val) = [0, 3, 1, 3] := by
  decide

end TauCeti.Examples
