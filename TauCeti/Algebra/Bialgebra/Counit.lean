/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Rational scalars pulled back along the counit of a bialgebra

When a bialgebra `H` over `R` is a `ℚ`-algebra, pulling back its `ℚ`-algebra structure along the
counit `ε : H →ₐ[R] R` equips the base ring `R` with a `ℚ`-algebra structure. This is a reducible
non-instance (`TauCeti.Bialgebra.counitRatAlgebra`), together with `algebraMap_counitRatAlgebra`
identifying its structure map with the counit composite `ε ∘ algebraMap ℚ H`.

## Main declarations

* `TauCeti.Bialgebra.counitRatAlgebra`: the `ℚ`-algebra structure on the base ring `R` pulled
  back along the counit of a `ℚ`-bialgebra `H`.
* `TauCeti.Bialgebra.algebraMap_counitRatAlgebra`: its structure map is the counit composed with
  `algebraMap ℚ H`.
-/

public section

namespace TauCeti.Bialgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.Bialgebra R H] [Algebra ℚ H]

variable (R H) in
/-- Pull back the `ℚ`-algebra structure of a bialgebra `H` along its counit to equip the base
ring `R` with a `ℚ`-algebra structure. -/
@[instance_reducible]
noncomputable def counitRatAlgebra : Algebra ℚ R :=
  ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra

/-- The structure map of `counitRatAlgebra R H` is the composite of `algebraMap ℚ H` with the
counit. -/
@[simp]
theorem algebraMap_counitRatAlgebra :
    @algebraMap ℚ R _ _ (counitRatAlgebra R H) =
      (_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H) :=
  RingHom.algebraMap_toAlgebra _

end TauCeti.Bialgebra
