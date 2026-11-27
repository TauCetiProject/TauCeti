/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import TauCeti.RingTheory.Derivation.Frobenius
import TauCeti.Algebra.Field.Subfield.Basic

/-!
# Kähler differentials in prime characteristic and the Frobenius subfield

Every derivation out of a field `k` of prime characteristic `p` vanishes on the Frobenius subfield
`k ^ p = (frobenius k p).fieldRange`, so for any base ring `R` whose image in `k` lies in
`k ^ p`, the module of Kähler differentials `Ω[k⁄R]` is canonically `k`-linearly isomorphic to
`Ω[k⁄(frobenius k p).fieldRange]`.

## Main definitions

* `TauCeti.kaehlerEquivFieldRangeFrobenius`: the canonical `k`-linear equivalence
  `Ω[k⁄R] ≃ₗ[k] Ω[k⁄(frobenius k p).fieldRange]`.
-/

public section

noncomputable section

namespace TauCeti

open KaehlerDifferential

variable (p : ℕ) [Fact p.Prime] (R k : Type*) [CommRing R] [Field k] [ExpChar k p] [Algebra R k]

/-- The canonical `k`-linear equivalence `Ω[k⁄R] ≃ₗ[k] Ω[k⁄k ^ p]` when the image of `R` in `k`
lies in the Frobenius subfield `k ^ p`. -/
def kaehlerEquivFieldRangeFrobenius
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    Ω[k⁄R] ≃ₗ[k] Ω[k⁄(frobenius k p).fieldRange] :=
  letI := (frobenius k p).fieldRange.restrictAlgebra hR
  haveI := (frobenius k p).fieldRange.isScalarTower_restrictAlgebra hR
  let fwd : Ω[k⁄R] →ₗ[k] Ω[k⁄(frobenius k p).fieldRange] :=
    KaehlerDifferential.map R (frobenius k p).fieldRange k k
  let bwd : Ω[k⁄(frobenius k p).fieldRange] →ₗ[k] Ω[k⁄R] :=
    ((D R k).ofMapAlgebraMap fun c ↦
      (D R k).map_eq_zero_of_mem_fieldRange_frobenius c.property).liftKaehlerDifferential
  LinearEquiv.ofLinearMap fwd bwd
    (Derivation.liftKaehlerDifferential_unique _ _ (by
      ext x
      simp [fwd, bwd]))
    (Derivation.liftKaehlerDifferential_unique _ _ (by
      ext x
      simp [fwd, bwd]))

/-- `kaehlerEquivFieldRangeFrobenius` sends `D R k x` to `D (frobenius k p).fieldRange k x`. -/
@[simp]
theorem kaehlerEquivFieldRangeFrobenius_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    kaehlerEquivFieldRangeFrobenius p R k hR (D R k x) = D (frobenius k p).fieldRange k x := by
  let := (frobenius k p).fieldRange.restrictAlgebra hR
  have := (frobenius k p).fieldRange.isScalarTower_restrictAlgebra hR
  rw [kaehlerEquivFieldRangeFrobenius, LinearEquiv.coe_ofLinearMap, KaehlerDifferential.map_D,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- The inverse of `kaehlerEquivFieldRangeFrobenius` sends `D (frobenius k p).fieldRange k x` to
`D R k x`. -/
@[simp]
theorem kaehlerEquivFieldRangeFrobenius_symm_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    (kaehlerEquivFieldRangeFrobenius p R k hR).symm (D (frobenius k p).fieldRange k x) =
      D R k x := by
  let := (frobenius k p).fieldRange.restrictAlgebra hR
  have := (frobenius k p).fieldRange.isScalarTower_restrictAlgebra hR
  rw [kaehlerEquivFieldRangeFrobenius, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    Derivation.liftKaehlerDifferential_comp_D, Derivation.coe_ofMapAlgebraMap]

end TauCeti

end
