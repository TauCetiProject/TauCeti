/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.PoissonBracket.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Sl2Casimir.Basic

/-!
# Zero-fibre Casimir symbol and Poisson-centrality for `sl₂`

Under `reesSpecializationZero`, the subleading `2 * t * j(h)` term of `reesSl2Casimir R L h e f`
vanishes while `j(f) * j(e)` specializes to `ι(e) * ι(f)`, yielding the classical quadratic
Casimir symbol

`sl2CasimirSymbol R L h e f = ι(h)² + 4 * ι(e) * ι(f)`

in `SymmetricAlgebra R L`. For `L = SpecialLinear.sl (Fin 2) R`, centrality of `reesSlFinTwoCasimir`
implies that `slFinTwoCasimirSymbol R` belongs to `lieInvariants` and Poisson-commutes with every
element under `reesZeroFiberBracket`. By contrast, when `(2 : R) ≠ 0`,
`{ι(h), ι(e)} = (2 : R) • ι(e) ≠ 0`, so `ι(e)` is not Poisson-central.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol`: `ι(h)² + 4 * ι(e) * ι(f)` in
  `SymmetricAlgebra R L`.
* `TauCeti.UniversalEnvelopingAlgebra.slFinTwoCasimirSymbol`: specialization to `sl (Fin 2) R`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.reesSpecializationZero_reesSl2Casimir`,
  `TauCeti.UniversalEnvelopingAlgebra.slFinTwoCasimirSymbol_mem_lieInvariants`,
  `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_slFinTwoCasimirSymbol_left`,
  `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_slFinTwoCasimirSymbol_right`:
  zero-fibre specialization and Poisson-centrality of `h² + 4ef`.
* `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_slFinTwo_h_e_ne_zero`: non-centrality
  of `ι(e)` when `(2 : R) ≠ 0`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.2 and §23.1.
* J. Dixmier, *Enveloping Algebras*, Graduate Studies in Mathematics 11, AMS (1996), §2.4.
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

@[simp]
theorem reesSpecializationZero_reesSl2Casimir [Module.Free R L] (h e f : L) :
    reesSpecializationZero R L (reesSl2Casimir R L h e f) = sl2CasimirSymbol R L h e f := by
  rw [reesSl2Casimir_def, sl2CasimirSymbol_def]
  simp only [map_add, map_pow, map_mul, map_ofNat,
    reesSpecializationZero_reesGenerator, reesSpecializationZero_reesParameter]
  ring

end Symbol

section SlFinTwo

variable (R : Type u) [CommRing R]

/-- The quadratic Casimir symbol `h² + 4ef` in `SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`. -/
noncomputable abbrev slFinTwoCasimirSymbol :
    SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R) :=
  sl2CasimirSymbol R (SpecialLinear.sl (Fin 2) R)
    (TauCeti.slFinTwoBasis R 2) (TauCeti.slFinTwoBasis R 0) (TauCeti.slFinTwoBasis R 1)

/-- **Poisson-centrality of `h² + 4ef`** in `SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`: its
zero-fibre symbol belongs to the Lie invariants. -/
theorem slFinTwoCasimirSymbol_mem_lieInvariants :
    slFinTwoCasimirSymbol R ∈
      TauCeti.SymmetricAlgebra.lieInvariants R
        (SpecialLinear.sl (Fin 2) R) (SpecialLinear.sl (Fin 2) R) := by
  rw [slFinTwoCasimirSymbol, ← reesSpecializationZero_reesSl2Casimir]
  exact reesSpecializationZero_mem_lieInvariants_of_mem_center _ _
    (reesSlFinTwoCasimir_mem_center R)

/-- `slFinTwoCasimirSymbol R` has vanishing zero-fibre Poisson bracket with every element of
`SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`. -/
@[simp]
theorem reesZeroFiberBracket_slFinTwoCasimirSymbol_left
    (q : SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)) :
    reesZeroFiberBracket R (SpecialLinear.sl (Fin 2) R) (slFinTwoCasimirSymbol R) q = 0 :=
  (forall_reesZeroFiberBracket_eq_zero_iff_mem_lieInvariants _ _).mpr
    (slFinTwoCasimirSymbol_mem_lieInvariants R) q

@[simp]
theorem reesZeroFiberBracket_slFinTwoCasimirSymbol_right
    (p : SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)) :
    reesZeroFiberBracket R (SpecialLinear.sl (Fin 2) R) p (slFinTwoCasimirSymbol R) = 0 := by
  rw [reesZeroFiberBracket_swap, reesZeroFiberBracket_slFinTwoCasimirSymbol_left, neg_zero]

/-- When `(2 : R) ≠ 0`, `{ι(h), ι(e)} = (2 : R) • ι(e) ≠ 0` in
`SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`, so `ι(e)` is not Poisson-central. -/
theorem reesZeroFiberBracket_slFinTwo_h_e_ne_zero {R : Type u} [CommRing R] (h2 : (2 : R) ≠ 0) :
    reesZeroFiberBracket R (SpecialLinear.sl (Fin 2) R)
      (SymmetricAlgebra.ι R _ (TauCeti.slFinTwoBasis R 2))
      (SymmetricAlgebra.ι R _ (TauCeti.slFinTwoBasis R 0)) ≠ 0 := by
  rw [reesZeroFiberBracket_ι_ι, TauCeti.lie_slFinTwoBasis_two_zero, map_smul]
  intro hzero
  have heval := congrArg (SymmetricAlgebra.lift ((TauCeti.slFinTwoBasis R).coord 0)) hzero
  rw [map_smul, SymmetricAlgebra.lift_ι_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero] at heval
  exact h2 heval

end SlFinTwo

end TauCeti.UniversalEnvelopingAlgebra
