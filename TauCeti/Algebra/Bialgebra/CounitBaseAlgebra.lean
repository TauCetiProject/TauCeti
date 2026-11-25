/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Induced base-ring algebra structure from a bialgebra counit

If an `R`-bialgebra `H` also carries an `S`-algebra structure (for example `S = ℚ` when `H` is a
rational coordinate bialgebra), composing `algebraMap S H` with the counit `ε : H →ₐ[R] R` equips
the base semiring `R` with an `S`-algebra structure. Because `H` cannot be inferred from the target
type `Algebra S R`, this is packaged as an explicit definition rather than a global instance.

## Main declarations

* `TauCeti.Bialgebra.counitBaseAlgebra`: the `S`-algebra structure on `R` induced by composing
  `algebraMap S H` with `Bialgebra.counitAlgHom R H`.
* `TauCeti.Bialgebra.counitBaseAlgebra_algebraMap_eq`,
  `TauCeti.Bialgebra.counitBaseAlgebra_algebraMap_apply`, and
  `TauCeti.Bialgebra.counitBaseAlgebra_smul_def`: the induced structure map and scalar action.
-/

public section

namespace TauCeti.Bialgebra

variable (S R H : Type*) [CommSemiring S] [CommSemiring R] [Semiring H]
  [_root_.Bialgebra R H] [Algebra S H]

/-- The `S`-algebra structure on the base semiring `R` of an `R`-bialgebra `H` that is also an
`S`-algebra, obtained by composing `algebraMap S H` with the counit `ε : H →ₐ[R] R`.

This is a `def` rather than an `instance` because `H` cannot be inferred from `Algebra S R`. -/
@[instance_reducible]
def counitBaseAlgebra : Algebra S R :=
  Algebra.compHom R ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap S H))

/-- The structure map of `counitBaseAlgebra S R H` is `ε ∘ algebraMap S H`. -/
theorem counitBaseAlgebra_algebraMap_eq :
    letI := counitBaseAlgebra S R H
    algebraMap S R = (_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap S H) :=
  (rfl)

/-- Evaluating `algebraMap S R` under `counitBaseAlgebra S R H` applies the counit to
`algebraMap S H s`. -/
theorem counitBaseAlgebra_algebraMap_apply (s : S) :
    letI := counitBaseAlgebra S R H
    algebraMap S R s = Coalgebra.counit (R := R) (algebraMap S H s) :=
  (rfl)

/-- Scalar multiplication under `counitBaseAlgebra S R H` multiplies by `ε (algebraMap S H s)`. -/
theorem counitBaseAlgebra_smul_def (s : S) (r : R) :
    letI := counitBaseAlgebra S R H
    s • r = Coalgebra.counit (R := R) (algebraMap S H s) * r :=
  (rfl)

end TauCeti.Bialgebra
