/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Cyclic
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Fusion
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Quaternion

/-!
# Regression examples: class-fusion maps on class data

This downstream kernel check exercises the `@[expose]`d definition `TauCeti.ClassData.fusion` in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Fusion` across module boundaries:
fusing `cyclicClassData 4` into `quaternionClassData 2` along the cyclic rotation subgroup `⟨a⟩`
collapses the inverse pair `1, 3` into a single real quaternion class of order `4`.
-/

namespace TauCeti.Examples

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
