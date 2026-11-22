/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.Frobenius
public import TauCeti.RingTheory.Ideal.WildInertia

/-!
# Decomposition and inertia groups in the absolute Galois group of a field

Let `F` be a field, `F^alg = AlgebraicClosure F`, `G_F = Field.absoluteGaloisGroup F`, and let
`O = integralClosure (𝓞 F) F^alg` be the integral closure of the ring of integers of `F` in `F^alg`.
For a number field `F` this is the ring of all algebraic integers in `F^alg`, and its maximal ideals
are the primes of `F^alg` above the finite places of `F`. Each `σ ∈ G_F` restricts to an
`𝓞 F`-algebra automorphism `toIntegralClosure F σ` of `O`; this is Mathlib's action of a group on
an integral closure, which makes `O` a `G_F`-ring. For an ideal `Q` of `O` this file names

* the **decomposition group** `D_Q = {σ | σ • Q = Q}`, Mathlib's `MulAction.stabilizer`;
* the **inertia group** `I_Q = {σ | ∀ x ∈ O, σ x - x ∈ Q}`, Mathlib's `Ideal.inertia`;
* the **wild inertia group** `P_Q`, `Ideal.wildInertia`: the `σ` such that for every nonzero
  `x ∈ O` the ratio `σ(x)/x` lies in the localization `O_Q` and is `≡ 1` modulo its maximal ideal;
* the predicate `IsArithFrobAtIntegralPrime σ Q`, that `σ x ≡ x ^ q mod Q` for all `x ∈ O`, where
  `q` is the cardinality of the residue field of `𝓞 F` below `Q`; it is Mathlib's `IsArithFrobAt`
  for the action of `σ`, that is `AlgHom.IsArithFrobAt` for `toIntegralClosure F σ`.

All four are reducible, so Mathlib's and Tau Ceti's API for stabilizers, inertia subgroups and
Frobenius elements applies to them directly: `MulAction.stabilizer_smul_eq_stabilizer_map_conj`,
`Ideal.inertia_smul` and `Ideal.wildInertia_smul` give `D_{τQ} = τ D_Q τ⁻¹` and its analogues,
`Ideal.wildInertia_le_inertia` and `Ideal.inertia_le_stabilizer` give `P_Q ≤ I_Q ≤ D_Q`,
`I_Q` and `P_Q` are normal in `D_Q` by instances, `IsArithFrobAt.mem_stabilizer_of_isIntegral`
puts the Frobenius elements at `Q` in `D_Q`, `IsArithFrobAt.iff_mul_inv_mem_inertia` says that
they form one coset of `I_Q`, and `IsArithFrobAt.conj` moves them to `τ • Q`.

At a maximal ideal `Q` above a finite place of a number field, `P_Q` is the inverse limit of the
first lower ramification groups of the finite Galois subextensions at the primes below `Q`
(Serre, *Corps locaux*, IV §2, Proposition 6 and its corollaries, which characterise `G_1` by
`σ(x)/x ≡ 1` modulo the maximal ideal); it is the largest closed normal pro-`p` subgroup of `I_Q`.

## Main definitions

* `TauCeti.GaloisRep.toIntegralClosure F σ`: the action of `σ ∈ G_F` on `O`.
* `TauCeti.GaloisRep.instMulSemiringActionIntegralClosure`: the resulting action of `G_F` on `O`.
* `TauCeti.GaloisRep.decompositionGroup F Q`, `TauCeti.GaloisRep.inertiaGroup F Q` and
  `TauCeti.GaloisRep.wildInertiaGroup F Q`: `D_Q`, `I_Q` and `P_Q` as subgroups of `G_F`.
* `TauCeti.GaloisRep.IsArithFrobAtIntegralPrime σ Q`: `σ` is an arithmetic Frobenius at `Q`.

## Main results

* `TauCeti.GaloisRep.toAlgHom_toIntegralClosure`: `toIntegralClosure F σ` is the action of `σ`.
* `TauCeti.GaloisRep.inertiaGroup_def`: `I_Q` is `AddSubgroup.inertia Q.toAddSubgroup G_F`.
* `TauCeti.GaloisRep.isArithFrobAtIntegralPrime_iff`: the Frobenius predicate is
  `AlgHom.IsArithFrobAt` for `toIntegralClosure F σ`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, 1973, 3.12.
* J.-P. Serre, *Corps locaux*, Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
-/

public section

noncomputable section

open NumberField Pointwise

namespace TauCeti.GaloisRep

variable (F : Type*) [Field F]

/-- The automorphism of the integral closure `O` of `𝓞 F` in `F^alg` induced by `σ ∈ G_F`: Mathlib's
`AlgEquiv.mapIntegralClosure` of `σ`, viewed as an `𝓞 F`-algebra automorphism of `F^alg`. -/
def toIntegralClosure (σ : Field.absoluteGaloisGroup F) :
    integralClosure (𝓞 F) (AlgebraicClosure F) ≃ₐ[𝓞 F]
      integralClosure (𝓞 F) (AlgebraicClosure F) :=
  ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).restrictScalars (𝓞 F)).mapIntegralClosure

variable {F}

/-- `toIntegralClosure F σ` acts on `O` as `σ` acts on `F^alg`. -/
@[simp]
theorem coe_toIntegralClosure_apply (σ : Field.absoluteGaloisGroup F)
    (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    (toIntegralClosure F σ x : AlgebraicClosure F) =
      DFunLike.coe (F := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ
        (x : AlgebraicClosure F) := by
  rw [toIntegralClosure, AlgEquiv.coe_mapIntegralClosure]
  exact AlgEquiv.restrictScalars_apply _ _ _

/-- The action of `G_F` on the integral closure `O` of `𝓞 F` in `F^alg`, by
`σ • x = toIntegralClosure F σ x`: Mathlib's action of a group on an integral closure, for the
action of `G_F` on `F^alg` by evaluation. -/
instance instMulSemiringActionIntegralClosure :
    MulSemiringAction (Field.absoluteGaloisGroup F)
      (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
  instMulSemiringActionSubtypeMemSubalgebraIntegralClosure
    (G := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)

/-- The action of `G_F` on `O` is through `toIntegralClosure`. -/
theorem integralClosure_smul_def (σ : Field.absoluteGaloisGroup F)
    (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    σ • x = toIntegralClosure F σ x :=
  Subtype.ext <| (integralClosure.coe_smul (G := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    σ x).trans (coe_toIntegralClosure_apply σ x).symm

/-- `G_F` acts on `O` by `𝓞 F`-algebra automorphisms. -/
instance instSMulCommClassIntegralClosure :
    SMulCommClass (Field.absoluteGaloisGroup F) (𝓞 F)
      (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
  inferInstanceAs (SMulCommClass (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (𝓞 F)
    (integralClosure (𝓞 F) (AlgebraicClosure F)))

/-- The action of `G_F` on `O` is the restriction of its action on `F^alg`. -/
@[simp]
theorem coe_smul_integralClosure (σ : Field.absoluteGaloisGroup F)
    (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    ((σ • x : integralClosure (𝓞 F) (AlgebraicClosure F)) : AlgebraicClosure F) =
      DFunLike.coe (F := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ
        (x : AlgebraicClosure F) := by
  rw [integralClosure_smul_def, coe_toIntegralClosure_apply]

/-- `toIntegralClosure F σ` is the `𝓞 F`-algebra automorphism by which `σ` acts on `O`. -/
theorem toIntegralClosure_eq_toAlgEquiv (σ : Field.absoluteGaloisGroup F) :
    toIntegralClosure F σ = MulSemiringAction.toAlgEquiv (𝓞 F)
      (integralClosure (𝓞 F) (AlgebraicClosure F)) σ :=
  AlgEquiv.ext fun x ↦ by rw [MulSemiringAction.toAlgEquiv_apply, integralClosure_smul_def]

/-- The `𝓞 F`-algebra map underlying `toIntegralClosure F σ` is the action of `σ` on `O`. -/
theorem toAlgHom_toIntegralClosure (σ : Field.absoluteGaloisGroup F) :
    (toIntegralClosure F σ).toAlgHom =
      MulSemiringAction.toAlgHom (𝓞 F) (integralClosure (𝓞 F) (AlgebraicClosure F)) σ :=
  AlgHom.ext fun x ↦ by
    rw [AlgEquiv.toAlgHom_apply, MulSemiringAction.toAlgHom_apply, integralClosure_smul_def]

/-! ### Decomposition, inertia and wild inertia groups -/

variable (F) (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)))

/-- The **decomposition group** `D_Q` of an ideal `Q` of the integral closure `O` of `𝓞 F` in
`F^alg`: the `σ ∈ G_F` with `σ • Q = Q`, Mathlib's `MulAction.stabilizer`. -/
abbrev decompositionGroup : Subgroup (Field.absoluteGaloisGroup F) :=
  MulAction.stabilizer (Field.absoluteGaloisGroup F) Q

/-- The **inertia group** `I_Q` of an ideal `Q` of `O`: the `σ ∈ G_F` with `σ x - x ∈ Q` for every
`x ∈ O`, Mathlib's `Ideal.inertia`. -/
abbrev inertiaGroup : Subgroup (Field.absoluteGaloisGroup F) :=
  Q.inertia (Field.absoluteGaloisGroup F)

/-- `I_Q` is Mathlib's inertia subgroup of `Q` viewed as an additive subgroup; the carriers agree
definitionally. -/
theorem inertiaGroup_def :
    inertiaGroup F Q = Q.toAddSubgroup.inertia (Field.absoluteGaloisGroup F) :=
  rfl

/-- The **wild inertia group** `P_Q` of an ideal `Q` of `O`, `Ideal.wildInertia`: the `σ ∈ G_F` such
that every `x ∈ O` has `s ∈ 1 + Q` and `q ∈ Q` with `s (σ x - x) = q x`. For a maximal ideal `Q`,
these are the `σ` such that for every nonzero `x ∈ O` the ratio `σ(x)/x` lies in `O_Q` and is `≡ 1`
modulo its maximal ideal; above a finite place of a number field this is the largest closed normal
pro-`p` subgroup of `I_Q`. -/
abbrev wildInertiaGroup : Subgroup (Field.absoluteGaloisGroup F) :=
  Q.wildInertia (Field.absoluteGaloisGroup F)

/-! ### Arithmetic Frobenius elements -/

variable {F} in
/-- `σ ∈ G_F` is an **arithmetic Frobenius** at an ideal `Q` of `O` if `σ x ≡ x ^ q mod Q` for all
`x ∈ O`, where `q` is the cardinality of the residue ring of `𝓞 F` below `Q`: Mathlib's
`IsArithFrobAt` for the action of `σ` on `O`, that is `AlgHom.IsArithFrobAt` for
`toIntegralClosure F σ` (`TauCeti.GaloisRep.isArithFrobAtIntegralPrime_iff`). -/
abbrev IsArithFrobAtIntegralPrime (σ : Field.absoluteGaloisGroup F)
    (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) : Prop :=
  IsArithFrobAt (𝓞 F) σ Q

variable {F Q}

/-- `IsArithFrobAtIntegralPrime σ Q` is Mathlib's `AlgHom.IsArithFrobAt` for
`toIntegralClosure F σ`. -/
theorem isArithFrobAtIntegralPrime_iff {σ : Field.absoluteGaloisGroup F} :
    IsArithFrobAtIntegralPrime σ Q ↔ (toIntegralClosure F σ).toAlgHom.IsArithFrobAt Q := by
  rw [toAlgHom_toIntegralClosure]

end TauCeti.GaloisRep
