/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
import TauCeti.NumberTheory.LocalField.Different.Tower

/-!
# Discriminant exponents in towers of local fields

For a finite separable tower `M/L/K`, the discriminant exponent of `M/K` is the
degree of `M/L` times the exponent of `L/K`, plus the residue degree of `L/K`
times the exponent of `M/L`. This is the valuation of the transitivity formula
for relative discriminant ideals. The residue-degree factor is essential: the
discriminant of `M/L` is an ideal of `𝒪[L]`, while that of `M/K` is an ideal of
`𝒪[K]`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §4.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [Algebra.IsSeparable K M]

/-- In a finite separable tower `M/L/K`, the discriminant exponents satisfy
`δ(M/K) = [M:L] δ(L/K) + f(L/K) δ(M/L)`. -/
theorem discriminantExponent_tower :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable K L :=
      Algebra.isSeparable_tower_bot_of_isSeparable K L M
    letI : Algebra.IsSeparable L M :=
      Algebra.isSeparable_tower_top_of_isSeparable K L M
    discriminantExponent K M =
      Module.finrank L M * discriminantExponent K L +
        inertiaDegree K L * discriminantExponent L M := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  let _ : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : Algebra.IsSeparable L M :=
    Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    inertiaDegree_tower (K := K) (L := L) M,
    differentExponent_tower (K := K) (L := L) (M := M),
    ← ramificationIndex_mul_inertiaDegree (K := L) (L := M)]
  ring

end TauCeti
