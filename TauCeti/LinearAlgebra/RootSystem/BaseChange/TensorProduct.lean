/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.LinearAlgebra.PerfectPairing.BaseChange
-- `Function.Injective.isDomain`, pulling `IsDomain` back along an injective algebra map.
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Scalar extension of a root pairing

A root pairing `P` over `R` on modules `M` and `N`, for instance an integral root datum on its
character and cocharacter lattices, extends along an injective algebra map `R → S`, expressed by
`[FaithfulSMul R S]`, to a root pairing on `S ⊗[R] M` and `S ⊗[R] N`: each root and coroot `x`
becomes `1 ⊗ x`, the perfect pairing of `P` extends by `LinearMap.toPerfPairBaseChange`, and the
reflection permutations are unchanged. This needs the coroot module `N` to be finite projective,
so that duals commute with the scalar extension; `M`, being the dual of `N`, is then finite
projective too. For `R = ℤ` and `S = ℚ` this is the rational root pairing of a root datum, the
rational root system an integral root datum determines.

The construction transports the pairings themselves, hence being valued in a common coefficient
ring (in particular being crystallographic) and the integral pairings, together with spanning,
and, for finitely many roots and a domain `S` of characteristic zero, linear independence of two
roots and being reduced. Irreducibility is not transported. Spanning transports, but an integral
root datum is in general not spanned by its roots, so for it rational spanning, like
irreducibility, has to be proved over `ℚ`.

Unlike `TauCeti.rootPairingBaseChange`, which moves a pairing on the standard lattices `κ → R`
entrywise to `κ → S`, this construction needs no coordinates.

## Main definitions

* `RootPairing.baseChange`: the scalar extension of a root pairing whose coroot module is finite
  projective.

## Main results

* `RootPairing.baseChange_toLinearMap_tmul_tmul`: the extended pairing on pure tensors.
* `RootPairing.baseChange_pairing` and `RootPairing.baseChange_pairingIn`: the root-coroot
  pairings, and the pairings valued in a common coefficient ring, are unchanged.
* `RootPairing.isValuedIn_baseChange` and `RootPairing.isRootSystem_baseChange`: scalar extension
  preserves being valued in a common coefficient ring, and spanning.
* `RootPairing.linearIndependent_pair_root_baseChange_iff` and
  `RootPairing.isReduced_baseChange`: for finitely many roots and a domain of characteristic zero,
  scalar extension preserves and reflects linear independence of two roots, and preserves being
  reduced.

## References

N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1, for the passage from a
root datum over `ℤ` to the root system over `ℚ` that it determines.
-/

public section

namespace RootPairing

open FaithfulSMul (algebraMap_injective)
open TensorProduct

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  (P : RootPairing ι R M N) [Module.Finite R N] [Module.Projective R N]

/-- **The scalar extension of a root pairing.** The roots and coroots of `P` are carried to
`S ⊗[R] M` and `S ⊗[R] N` by `x ↦ 1 ⊗ x`, paired by the scalar extension
`LinearMap.toPerfPairBaseChange` of the perfect pairing of `P`, and permuted by the same
reflection permutations. The coroot module `N` is asked to be finite projective, so that duals
commute with the scalar extension; then so is `M`, its dual. The map `R → S` is asked to be
injective, so that distinct roots stay distinct. -/
noncomputable def baseChange : RootPairing ι S (S ⊗[R] M) (S ⊗[R] N) where
  toLinearMap := P.toLinearMap.toPerfPairBaseChange S
  root := P.root.trans ⟨TensorProduct.mk R S M 1, by
    have : Module.Projective R M := .of_equiv' P.toLinearMap.toPerfPair.symm
    exact Module.Flat.tensorProduct_mk_injective R M S⟩
  coroot := P.coroot.trans ⟨TensorProduct.mk R S N 1, Module.Flat.tensorProduct_mk_injective R N S⟩
  root_coroot_two i := by
    simp [P.root_coroot_two, map_ofNat]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    simp [← P.reflectionPerm_root, tmul_sub, algebraMap_smul]
  reflectionPerm_coroot i j := by
    simp [← P.reflectionPerm_coroot, tmul_sub, algebraMap_smul]

/-- The roots of the scalar extension are the roots of `P` with coefficient one. -/
@[simp] theorem baseChange_root (i : ι) : (P.baseChange S).root i = 1 ⊗ₜ P.root i :=
  (rfl)

/-- The coroots of the scalar extension are the coroots of `P` with coefficient one. -/
@[simp] theorem baseChange_coroot (i : ι) : (P.baseChange S).coroot i = 1 ⊗ₜ P.coroot i :=
  (rfl)

/-- The scalar extension keeps the reflection permutations of `P`. -/
@[simp] theorem baseChange_reflectionPerm :
    (P.baseChange S).reflectionPerm = P.reflectionPerm :=
  (rfl)

/-- The pairing of the scalar extension on pure tensors:
`⟨a ⊗ x, b ⊗ y⟩ = a * b * algebraMap R S ⟨x, y⟩`. -/
@[simp] theorem baseChange_toLinearMap_tmul_tmul (a b : S) (x : M) (y : N) :
    (P.baseChange S).toLinearMap (a ⊗ₜ x) (b ⊗ₜ y) = a * b * algebraMap R S (P.toLinearMap x y) :=
  P.toLinearMap.toPerfPairBaseChange_tmul_tmul S a b x y

/-- The root-coroot pairings of the scalar extension are those of `P`, mapped to `S`. -/
@[simp] theorem baseChange_pairing (i j : ι) :
    (P.baseChange S).pairing i j = algebraMap R S (P.pairing i j) := by
  rw [← root_coroot_eq_pairing, ← root_coroot_eq_pairing, baseChange_root, baseChange_coroot,
    baseChange_toLinearMap_tmul_tmul, one_mul, one_mul]

/-- The Coxeter weights of the scalar extension are those of `P`, mapped to `S`. -/
@[simp] theorem baseChange_coxeterWeight (i j : ι) :
    (P.baseChange S).coxeterWeight i j = algebraMap R S (P.coxeterWeight i j) := by
  simp [coxeterWeight]

/-- Scalar extension preserves being valued in a common coefficient ring `T`; with `T = ℤ`, it
preserves being crystallographic. -/
instance isValuedIn_baseChange (T : Type*) [CommRing T] [Algebra T R] [Algebra T S]
    [IsScalarTower T R S] [P.IsValuedIn T] : (P.baseChange S).IsValuedIn T where
  exists_value i j := by
    obtain ⟨t, ht⟩ := P.exists_value (S := T) i j
    exact ⟨t, by rw [baseChange_pairing, ← ht, IsScalarTower.algebraMap_apply T R S]⟩

/-- The `T`-valued pairings, hence the Cartan matrix of any base, are unchanged by scalar
extension. -/
@[simp] theorem baseChange_pairingIn (T : Type*) [CommRing T] [Algebra T R] [Algebra T S]
    [IsScalarTower T R S] [FaithfulSMul T S] [P.IsValuedIn T] (i j : ι) :
    (P.baseChange S).pairingIn T i j = P.pairingIn T i j := by
  refine algebraMap_injective T S ?_
  rw [algebraMap_pairingIn, baseChange_pairing, IsScalarTower.algebraMap_apply T R S,
    algebraMap_pairingIn]

/-- Scalar extension preserves spanning by the roots and by the coroots. -/
instance isRootSystem_baseChange [P.IsRootSystem] : (P.baseChange S).IsRootSystem where
  span_root_eq_top := by
    have h := congrArg (Submodule.baseChange S) (IsRootSystem.span_root_eq_top (P := P))
    rwa [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at h
  span_coroot_eq_top := by
    have h := congrArg (Submodule.baseChange S) (IsRootSystem.span_coroot_eq_top (P := P))
    rwa [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at h

/-- For finitely many roots and a domain `S` of characteristic zero, two roots of the scalar
extension are linearly independent exactly when the corresponding roots of `P` are: both
conditions say that their Coxeter weight is not `4`. -/
theorem linearIndependent_pair_root_baseChange_iff [Finite ι] [IsDomain S] [CharZero S]
    (i j : ι) :
    LinearIndependent S ![(P.baseChange S).root i, (P.baseChange S).root j] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  have : CharZero R := (algebraMap R S).charZero
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive S (S ⊗[R] M) := .of_isPerfPair (P.baseChange S).toLinearMap
  rw [linearIndependent_iff_coxeterWeight_ne_four, linearIndependent_iff_coxeterWeight_ne_four,
    baseChange_coxeterWeight, ← map_ofNat (algebraMap R S) 4, (algebraMap_injective R S).ne_iff]

/-- For finitely many roots and a domain `S` of characteristic zero, scalar extension preserves
being reduced. -/
instance isReduced_baseChange [Finite ι] [IsDomain S] [CharZero S] [P.IsReduced] :
    (P.baseChange S).IsReduced where
  eq_or_eq_neg i j h := by
    rw [linearIndependent_pair_root_baseChange_iff] at h
    rcases IsReduced.eq_or_eq_neg (P := P) i j h with h | h <;> simp [h, tmul_neg]

end RootPairing
