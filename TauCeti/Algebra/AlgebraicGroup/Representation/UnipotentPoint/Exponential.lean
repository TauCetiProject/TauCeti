/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# Unipotence of exponential points and exponential curves

Let `H` be a commutative Hopf algebra over a commutative ring `R` which is also a `ℚ`-algebra, and
let `d` be a tangent vector at the identity whose left-invariant derivation
`D = TauCeti.Bialgebra.leftInvariantDerivation d` is locally nilpotent on `H`.

By `TauCeti.Comodule.endOfPoint_expPointAt`, the one-parameter exponential curve
`t ↦ Bialgebra.expPointAt d hd t` acts on every finitely generated `H`-comodule `M` over any
commutative `R`-algebra `B` as `IsNilpotent.exp (t • (Comodule.differential d).baseChange B)`,
where `t • (Comodule.differential d).baseChange B` is nilpotent
(`TauCeti.Comodule.isNilpotent_smul_baseChange_differential`). Consequently, every point
`Bialgebra.expPointAt d hd t` on an exponential curve — and hence `Bialgebra.expPoint d hd` — is
unipotent (`TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt`,
`TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`).

## Main declarations

* `TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt` and
  `TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`: exponential points and exponential curves are
  unipotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
-/

public section

namespace TauCeti.HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {B : Type w}
variable [CommRing R] [CommRing H] [_root_.HopfAlgebra R H] [Algebra ℚ H]

/-- Every point on the exponential curve of a tangent vector with locally nilpotent invariant
derivation is unipotent, over any commutative value algebra `B`. -/
theorem isUnipotentPoint_expPointAt [CommRing B] [Algebra R B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : B) :
    IsUnipotentPoint (Bialgebra.expPointAt d hd t) := by
  -- The counit pulls the `ℚ`-algebra structure of `H` to `R` and then to `B`.
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  let : Algebra ℚ B :=
    ((algebraMap R B).comp (algebraMap ℚ R)).toAlgebra
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  rw [Comodule.endOfPoint_expPointAt d hd t]
  obtain ⟨K, hK⟩ :=
    Comodule.isNilpotent_smul_baseChange_differential (R := R) (H := H) (M := M) hd t
  exact ⟨K, IsNilpotent.pow_exp_sub_one_eq_zero hK⟩

/-- The exponential point of a tangent vector with locally nilpotent invariant derivation is
unipotent. -/
theorem isUnipotentPoint_expPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsUnipotentPoint (WithConv.toConv (Bialgebra.expPoint d hd)) := by
  rw [← Bialgebra.expPointAt_one]
  exact isUnipotentPoint_expPointAt d hd (1 : R)

end TauCeti.HopfAlgebra
