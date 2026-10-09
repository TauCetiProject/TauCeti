/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.GrothendieckGroup
public import TauCeti.RepresentationTheory.Induction.Artin.Spanning

/-!
# Modular induction for the local Euler characteristic

Let `F` be a finite extension of `ℚ_p` and `ℓ` a prime. Tate's local Euler characteristic formula
`χ_F(A) = φ_F(A)` for finite smooth discrete `ZMod ℓ`-representations `A` of `G_F` reduces to
representations inflated from a finite Galois quotient `G_F ⧸ V` and induced there from a cyclic
subgroup of order prime to `ℓ`.

Both sides descend to homomorphisms on the Grothendieck group of `(ZMod ℓ)[G_F ⧸ V]`
(`localEulerCharacteristicK0`, `localCardNormK0`) with torsion-free target, and by the modular
Artin induction theorem a positive multiple of every class is a sum of classes induced from such
cyclic subgroups (`TauCeti.eq_of_comp_indK0_eq_of_cyclic_coprime`). The induced classes are those
of the finite-dimensional induced representations `TauCeti.indFDRep`, so the formula for these
inflated induced representations gives it in general. By Shapiro's lemma these are in turn
computed over the fixed field of the cyclic subgroup, where the order of the acting group is prime
to `ℓ`.

## Main results

* `TauCeti.ClassFieldTheory.forall_localEulerCharacteristic_eq_localCardNorm_of_indFDRep`: the
  local Euler characteristic formula for every finite smooth discrete `ZMod ℓ`-representation
  follows from the formula for the inflations of representations induced from cyclic subgroups of
  order prime to `ℓ`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.3.4) and
  the proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Lemma 2.10 and Theorem 2.8.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti.ClassFieldTheory

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharZero F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- **Modular-Artin reduction of the local Euler characteristic formula.** If `χ_F = φ_F` holds
for the inflation to `G_F` of every representation of a finite Galois quotient `G_F ⧸ V` induced
from a cyclic subgroup of order prime to `ℓ`, then it holds for every finite smooth discrete
`ZMod ℓ`-representation of `G_F`. -/
theorem forall_localEulerCharacteristic_eq_localCardNorm_of_indFDRep
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ∀ (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
      (C : Subgroup (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)),
      IsCyclic C ∧ ¬ ℓ ∣ Nat.card C → ∀ B : FDRep (ZMod ℓ) C,
        localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ))
            ((fdGalRepOfQuotient ℓ F V).obj (indFDRep B)) =
          localCardNorm p ((fdGalRepOfQuotient ℓ F V).obj (indFDRep B)))
    (A : GalRep ℓ F) [Finite A.V] [DiscreteTopology A.V]
    [Fact (IsSmoothDiscrete (ZMod ℓ) A)] :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ)) A = localCardNorm p A := by
  -- Check `χ_F = φ_F` on `G₀` of every finite quotient, after induction from every cyclic
  -- subgroup of order prime to `ℓ`, on the class of each finite-dimensional representation.
  refine (forall_localEulerCharacteristic_eq_localCardNorm_iff p
    (Nat.cast_ne_zero.2 (NeZero.ne ℓ)).isUnit).2 (fun V ↦
      eq_of_comp_indK0_eq_of_cyclic_coprime ℓ fun C hC ↦ hom_ext_fdRep fun B ↦ ?_) A
  simp only [AddMonoidHom.comp_apply, indK0_of_indFDRep, localEulerCharacteristicK0_of,
    localCardNormK0_of]
  exact congrArg Additive.ofMul (h V C hC B)

end TauCeti.ClassFieldTheory
