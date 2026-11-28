/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
public import TauCeti.LinearAlgebra.End.Exp

/-!
# Action of exponential one-parameter subgroups and locally nilpotent exponentials

Let `H` be a commutative Hopf `ℚ`-algebra over `R` and `d` a tangent vector at the identity whose
left-invariant derivation `D = TauCeti.Bialgebra.leftInvariantDerivation d` is locally nilpotent.
Building on `TauCeti.Comodule.basePointsRepresentation_expPoint_apply_eq_sum`, this file identifies:

* `TauCeti.Comodule.basePointsRepresentation_expPoint_eq_locallyNilpotentExp`: without assuming
  global nilpotence of `ρ'(d) = TauCeti.Comodule.differential d`, `exp d` acts on any `ℚ`-module
  `H`-comodule as `Module.End.locallyNilpotentExp (ρ'(d))`.
* `TauCeti.Comodule.basePointsRepresentation_expPointAt` and
  `TauCeti.Comodule.basePointsRepresentation_expPointAt_of_isNilpotent`: at parameter `t : R`, the
  exponential one-parameter subgroup `TauCeti.Bialgebra.expPointAt d hd t` acts as the exponential
  of `t • ρ'(d)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 11 and 12.
-/

public section

namespace TauCeti.Comodule

attribute [local instance 100] LieRing.ofAssociativeRing

section HopfAlgebra

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M] [Algebra ℚ H] [Module ℚ M]

/-- **The exponential point acts on any comodule as `locallyNilpotentExp` of its differentiated
action.** -/
theorem basePointsRepresentation_expPoint_eq_locallyNilpotentExp
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (m : M) :
    basePointsRepresentation (H := H) M (WithConv.toConv (Bialgebra.expPoint d hd)) m =
      Module.End.locallyNilpotentExp (differential (R := R) (H := H) (M := M) d) (
    exists_pow_differential_apply_eq_zero_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
          hd) m := by
  obtain ⟨N, hN⟩ :=
    exists_pow_differential_apply_eq_zero_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
      hd m
  rw [basePointsRepresentation_expPoint_apply_eq_sum hd hN,
    Module.End.locallyNilpotentExp_apply_eq_sum _ _ hN]

/-- **The exponential one-parameter subgroup acts as `locallyNilpotentExp (t • differential d)`.**
-/
theorem basePointsRepresentation_expPointAt
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : R) (m : M) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) m =
      Module.End.locallyNilpotentExp (t • differential (R := R) (H := H) (M := M) d)
        (Module.End.exists_pow_smul_apply_eq_zero (
    exists_pow_differential_apply_eq_zero_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
            hd) t) m := by
  rw [Bialgebra.expPointAt_eq_toConv_expPoint,
    basePointsRepresentation_expPoint_eq_locallyNilpotentExp]
  have hd_smul : differential (R := R) (H := H) (M := M) (t • d) =
      t • differential (R := R) (H := H) (M := M) d :=
    (differential (R := R) (H := H) (M := M)).toLinearMap.map_smul t d
  simp_rw [hd_smul]

/-- **When the differentiated action is nilpotent, `expPointAt d hd t` acts as
`IsNilpotent.exp (t • differential d)`.** -/
theorem basePointsRepresentation_expPointAt_of_isNilpotent
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hnil : IsNilpotent (differential (R := R) (H := H) (M := M) d)) (t : R) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  rw [Bialgebra.expPointAt_eq_toConv_expPoint,
    basePointsRepresentation_expPoint (M := M)
      (Bialgebra.exists_iterate_leftInvariantDerivation_smul_eq_zero hd t)
      (by
        rw [map_smul (differential (R := R) (H := H) (M := M)) t d]
        exact hnil.smul t),
    map_smul (differential (R := R) (H := H) (M := M)) t d]

end HopfAlgebra

end TauCeti.Comodule
