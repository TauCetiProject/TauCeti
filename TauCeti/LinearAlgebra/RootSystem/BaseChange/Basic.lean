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
# Extension of scalars of a root pairing

Let `P` be a root pairing over a commutative ring `R`, with weight space `M` and coweight space
`N`, and let `S` be an `R`-algebra. This file constructs its extension of scalars
`P.baseChange S`, a root pairing over `S` on `S ⊗[R] M` and `S ⊗[R] N`. The roots and coroots are
`1 ⊗ α` and `1 ⊗ α∨`, the reflection permutations are unchanged, and the pairing is the
`S`-bilinear extension `LinearMap.baseChangePairing` of the pairing of `P`.

Two hypotheses make this a root pairing. The coweight space `N` is finite and free, so that the
extended pairing is again perfect; and `algebraMap R S` is injective (`[FaithfulSMul R S]`), so that
distinct roots stay distinct. The main instance is a root datum, a root pairing over `ℤ` on
finitely generated lattices `X` and `Y`, whose rational scalar extension
`P.baseChange ℚ` on `ℚ ⊗[ℤ] X` and `ℚ ⊗[ℤ] Y` is the root pairing over `ℚ` that the datum
determines. Unlike the integral root datum, this rational pairing can be a root system even when
the roots do not span `X` over `ℤ`.

The properties that pass to the extension are recorded here: the pairing values (hence being
crystallographic and the integral Cartan integers), linear independence of two roots and
reducedness (for flat `S`, or for finitely many roots and a domain `S` of characteristic zero), and
spanning, via
the identification of the root span of the extension with the base change of the root span.
Irreducibility is not transported. `RootPairing.IsIrreducible` asks every nonzero
reflection-invariant submodule to be the whole module, which fails over `ℤ` for any nonzero lattice
`X`, since `2 • X` is invariant; so irreducibility of the rational extension has to be established
over `ℚ` itself.

For the special case of the standard lattices `κ → R` paired by the dot product, where the extension
can be written on `κ → S` without tensor products, see
`TauCeti/LinearAlgebra/RootSystem/BaseChange/Pi.lean`.

## Main definitions

* `RootPairing.baseChange`: the extension of scalars of a root pairing along an `R`-algebra `S`.

## Main results

* `RootPairing.baseChange_pairing`: the pairings of the extension are the images of those of `P`.
* `RootPairing.baseChange_reflection_tmul` and `RootPairing.baseChange_coreflection_tmul`: the
  reflections of the extension are the extensions of the reflections of `P`.
* `RootPairing.isValuedIn_baseChange` and `RootPairing.baseChange_pairingIn`: the extension of a
  pairing valued in `T` is valued in `T`, with the same values; in particular extension of scalars
  preserves being crystallographic.
* `RootPairing.baseChange_coxeterWeight`: the Coxeter weights of the extension are the images of
  those of `P`.
* `RootPairing.isReduced_baseChange`: extension along a flat algebra preserves reducedness.
* `RootPairing.linearIndependent_pair_root_baseChange_iff` and
  `RootPairing.isReduced_baseChange_of_charZero`: for finitely many roots and a domain `S` of
  characteristic zero, extension of scalars preserves and reflects linear independence of two
  roots, and preserves reducedness, with no flatness hypothesis.
* `RootPairing.rootSpan_baseChange` and `RootPairing.corootSpan_baseChange`: the root and coroot
  spans of the extension are the extensions of the root and coroot spans.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

open Module TensorProduct Function Set
open Submodule (span)

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]

variable [Free R N] [Module.Finite R N]

/-- **Extension of scalars of a root pairing.** For an `R`-algebra `S` with `algebraMap R S`
injective, and a finite free coweight space, the root pairing `P` extends to a root pairing over `S`
on `S ⊗[R] M` and `S ⊗[R] N`, with roots `1 ⊗ α`, coroots `1 ⊗ α∨`, the same reflection
permutations, and the `S`-bilinear extension of the pairing of `P`. -/
noncomputable def baseChange : RootPairing ι S (S ⊗[R] M) (S ⊗[R] N) where
  toLinearMap := P.toLinearMap.baseChangePairing S
  root := ⟨TensorProduct.mk R S M 1 ∘ P.root,
    (P.toLinearMap.tensorProduct_mk_injective_of_injective S
      (LinearMap.IsPerfPair.bijective_left _).injective).comp P.root.injective⟩
  coroot := ⟨TensorProduct.mk R S N 1 ∘ P.coroot,
    (P.toLinearMap.flip.tensorProduct_mk_injective_of_injective S
      (LinearMap.IsPerfPair.bijective_right _).injective).comp P.coroot.injective⟩
  root_coroot_two i := by simp [P.root_coroot_two, map_ofNat]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    simp [← P.reflectionPerm_root, tmul_sub, algebraMap_smul]
  reflectionPerm_coroot i j := by
    simp [← P.reflectionPerm_coroot, tmul_sub, algebraMap_smul]

@[simp]
theorem baseChange_toLinearMap :
    (P.baseChange S).toLinearMap = P.toLinearMap.baseChangePairing S :=
  (rfl)

@[simp]
theorem baseChange_root (i : ι) : (P.baseChange S).root i = 1 ⊗ₜ P.root i :=
  (rfl)

@[simp]
theorem baseChange_coroot (i : ι) : (P.baseChange S).coroot i = 1 ⊗ₜ P.coroot i :=
  (rfl)

@[simp]
theorem baseChange_reflectionPerm : (P.baseChange S).reflectionPerm = P.reflectionPerm :=
  (rfl)

@[simp]
theorem baseChange_pairing (i j : ι) :
    (P.baseChange S).pairing i j = algebraMap R S (P.pairing i j) := by
  rw [← root_coroot_eq_pairing, ← root_coroot_eq_pairing]
  simp only [baseChange_toLinearMap, baseChange_root, baseChange_coroot,
    LinearMap.baseChangePairing_tmul_tmul, one_mul]

/-- The Coxeter weights of the extension are those of `P`, mapped to `S`. -/
@[simp]
theorem baseChange_coxeterWeight (i j : ι) :
    (P.baseChange S).coxeterWeight i j = algebraMap R S (P.coxeterWeight i j) := by
  simp [coxeterWeight]

/-- The reflections of the extension are the extensions of the reflections of `P`. -/
@[simp]
theorem baseChange_reflection_tmul (i : ι) (a : S) (x : M) :
    (P.baseChange S).reflection i (a ⊗ₜ x) = a ⊗ₜ P.reflection i x := by
  simp [reflection_apply, tmul_sub, smul_tmul', Algebra.smul_def, mul_comm]

/-- The coreflections of the extension are the extensions of the coreflections of `P`. -/
@[simp]
theorem baseChange_coreflection_tmul (i : ι) (a : S) (y : N) :
    (P.baseChange S).coreflection i (a ⊗ₜ y) = a ⊗ₜ P.coreflection i y := by
  simp [coreflection_apply, root', tmul_sub, smul_tmul', Algebra.smul_def, mul_comm]

section IsValuedIn

variable (T : Type*) [CommRing T] [Algebra T R] [Algebra T S] [IsScalarTower T R S]

/-- The extension of a root pairing valued in `T` is valued in `T`. In particular, extension of
scalars preserves being crystallographic. -/
instance isValuedIn_baseChange [P.IsValuedIn T] : (P.baseChange S).IsValuedIn T where
  exists_value i j := by
    obtain ⟨t, ht⟩ := P.exists_value (S := T) i j
    exact ⟨t, by simp [IsScalarTower.algebraMap_apply T R S, ht]⟩

/-- The `T`-valued pairings of the extension are those of `P`; for `T = ℤ` these are the
Cartan integers. -/
@[simp]
theorem baseChange_pairingIn [FaithfulSMul T S] [P.IsValuedIn T] (i j : ι) :
    (P.baseChange S).pairingIn T i j = P.pairingIn T i j := by
  apply FaithfulSMul.algebraMap_injective T S
  simp [IsScalarTower.algebraMap_apply T R S]

end IsValuedIn

/-- Extension of scalars along a flat algebra preserves reducedness: a pair of roots that becomes
linearly dependent over `S` was already linearly dependent over `R`. -/
instance isReduced_baseChange [Flat R S] [P.IsReduced] : (P.baseChange S).IsReduced := by
  refine ⟨fun i j h ↦ ?_⟩
  have hR : ¬ LinearIndependent R ![P.root i, P.root j] := by
    refine fun hR ↦ h ?_
    convert Flat.linearIndependent_one_tmul (S := S) hR using 1
    ext k
    fin_cases k <;> rfl
  rcases IsReduced.eq_or_eq_neg i j hR with hij | hij <;> simp [hij, tmul_neg]

/-- For finitely many roots and a domain `S` of characteristic zero, two roots of the extension are
linearly independent exactly when the corresponding roots of `P` are: both conditions say that
their Coxeter weight is not `4`. -/
theorem linearIndependent_pair_root_baseChange_iff [Finite ι] [IsDomain S] [CharZero S]
    (i j : ι) :
    LinearIndependent S ![(P.baseChange S).root i, (P.baseChange S).root j] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  have : CharZero R := (algebraMap R S).charZero
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive S (S ⊗[R] M) := .of_isPerfPair (P.baseChange S).toLinearMap
  rw [linearIndependent_iff_coxeterWeight_ne_four, linearIndependent_iff_coxeterWeight_ne_four,
    baseChange_coxeterWeight, ← map_ofNat (algebraMap R S) 4,
    (FaithfulSMul.algebraMap_injective R S).ne_iff]

/-- For finitely many roots and a domain `S` of characteristic zero, extension of scalars preserves
reducedness, whether or not `S` is flat over `R`. -/
theorem isReduced_baseChange_of_charZero [Finite ι] [IsDomain S] [CharZero S] [P.IsReduced] :
    (P.baseChange S).IsReduced := by
  refine ⟨fun i j h ↦ ?_⟩
  rw [linearIndependent_pair_root_baseChange_iff] at h
  rcases IsReduced.eq_or_eq_neg i j h with hij | hij <;> simp [hij, tmul_neg]

/-- The root span of the extension is the extension of the root span. -/
theorem rootSpan_baseChange : (P.baseChange S).rootSpan S = (P.rootSpan R).baseChange S := by
  rw [Submodule.baseChange_span, ← range_comp]
  exact congrArg (fun f ↦ span S (range f)) (funext (P.baseChange_root S)).symm

/-- The coroot span of the extension is the extension of the coroot span. -/
theorem corootSpan_baseChange :
    (P.baseChange S).corootSpan S = (P.corootSpan R).baseChange S := by
  rw [Submodule.baseChange_span, ← range_comp]
  exact congrArg (fun f ↦ span S (range f)) (funext (P.baseChange_coroot S)).symm

/-- The extension of a root system is a root system. -/
instance isRootSystem_baseChange [P.IsRootSystem] : (P.baseChange S).IsRootSystem where
  span_root_eq_top := by
    rw [← rootSpan, rootSpan_baseChange, rootSpan, IsRootSystem.span_root_eq_top,
      Submodule.baseChange_top]
  span_coroot_eq_top := by
    rw [← corootSpan, corootSpan_baseChange, corootSpan, IsRootSystem.span_coroot_eq_top,
      Submodule.baseChange_top]

end RootPairing
