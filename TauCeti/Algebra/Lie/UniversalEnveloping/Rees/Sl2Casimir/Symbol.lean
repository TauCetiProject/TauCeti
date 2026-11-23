/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# The `sl₂` quadratic Casimir symbol in the symmetric algebra

Defines the quadratic Casimir symbol `sl2CasimirSymbol R L h e f = ι(h)² + 4 * ι(e) * ι(f)` in
`SymmetricAlgebra R L`, together with its specialization `slFinTwoCasimirSymbol R` to the standard
triple of `LieAlgebra.SpecialLinear.sl (Fin 2) R`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol`: `ι(h)² + 4 * ι(e) * ι(f)` in
  `SymmetricAlgebra R L`.
* `TauCeti.UniversalEnvelopingAlgebra.slFinTwoCasimirSymbol`: specialization to `sl (Fin 2) R`.
-/

public section

open LieAlgebra

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

section Symbol

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The classical quadratic Casimir symbol `ι(h)² + 4 * ι(e) * ι(f)` in `SymmetricAlgebra R L`. -/
noncomputable def sl2CasimirSymbol (h e f : L) : SymmetricAlgebra R L :=
  SymmetricAlgebra.ι R L h ^ 2 + 4 * SymmetricAlgebra.ι R L e * SymmetricAlgebra.ι R L f

/-- Defining polynomial expression for `sl2CasimirSymbol`. -/
theorem sl2CasimirSymbol_def (h e f : L) :
    sl2CasimirSymbol R L h e f =
      SymmetricAlgebra.ι R L h ^ 2 + 4 * SymmetricAlgebra.ι R L e * SymmetricAlgebra.ι R L f :=
  (rfl)

end Symbol

section SlFinTwo

variable (R : Type u) [CommRing R]

/-- The quadratic Casimir symbol `h² + 4ef` in `SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`. -/
noncomputable abbrev slFinTwoCasimirSymbol :
    SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R) :=
  sl2CasimirSymbol R (SpecialLinear.sl (Fin 2) R)
    (TauCeti.slFinTwoBasis R 2) (TauCeti.slFinTwoBasis R 0) (TauCeti.slFinTwoBasis R 1)

end SlFinTwo

end TauCeti.UniversalEnvelopingAlgebra
