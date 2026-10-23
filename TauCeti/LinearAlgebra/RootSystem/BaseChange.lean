/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Base change of a root pairing carried by the standard lattices

An integral root datum carries its roots and coroots on the standard lattices `κ → ℤ`, paired by
the dot product. The constructions which build a Lie algebra out of a root system — Serre's
presentation, and Geck's construction — instead want a root system over a field of characteristic
zero. This file moves such a pairing along an injective algebra map, expressed by
`[FaithfulSMul R S]`, applying the structure map entrywise to every root and coroot and keeping the
same reflection permutation.

Only the target pairing is chosen here: it is again the dot product, which is perfect on `κ → S` for
every commutative ring `S` by `TauCeti.dotProductBilin_isPerfPair`. So the construction asks the
source pairing to be the dot product too, and every axiom of `RootPairing` then transports along
`Pi.algebraMap`, entrywise application of `algebraMap R S`.

The properties a downstream Lie-theoretic consumer needs are transported separately, each under its
own hypotheses: being crystallographic, being reduced, spanning, carrying a base with a prescribed
Cartan matrix, and the root-string coefficients. Irreducibility is deliberately absent, because it
is *false* over `ℤ`: the sublattice `2 • (κ → ℤ)` is invariant under every reflection. It has to be
proved over the new base ring rather than transported.

## Main definitions

* `TauCeti.rootPairingBaseChange`: the base change of a dot-product root pairing along an injective
  algebra map `R → S`, expressed by `[FaithfulSMul R S]`.
* `TauCeti.rootPairingBaseChangeBase`: the base of the base change attached to a base of the
  original pairing, supported on the same indices.

## Main results

* `TauCeti.isCrystallographic_rootPairingBaseChange`: base change preserves being crystallographic.
* `TauCeti.isReduced_rootPairingBaseChange`: base change preserves being reduced.
* `TauCeti.span_range_root_rootPairingBaseChange_eq_top` and
  `TauCeti.span_range_coroot_rootPairingBaseChange_eq_top`: a spanning family of roots or coroots
  stays spanning.
* `TauCeti.pairingIn_rootPairingBaseChange`: the integral pairings, hence the Cartan matrix of a
  base, are unchanged.
* `TauCeti.chainTopCoeff_rootPairingBaseChange` and `TauCeti.chainBotCoeff_rootPairingBaseChange`:
  the root-string coefficients are unchanged.

## References

The construction is the standard passage from a root datum over `ℤ` to the root system over `ℚ`
that it determines; see N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace TauCeti

open Function Matrix Set
open FaithfulSMul (algebraMap_injective)
open Submodule (span)

/-! ## Entrywise base change of the standard lattice -/

section Entrywise

variable {κ R : Type*} (S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]

/-- Entrywise base change of the standard lattice reads off entrywise. -/
theorem piAlgebraMap_apply (x : κ → R) (j : κ) :
    Pi.algebraMap κ R S x j = algebraMap R S (x j) :=
  rfl

/-- Entrywise base change along an injective algebra map is injective. -/
theorem piAlgebraMap_injective [FaithfulSMul R S] : Injective (Pi.algebraMap κ R S) :=
  fun _ _ h => funext fun j => algebraMap_injective R S (congrFun h j)

/-- Entrywise base change carries the additive closure of a family into the additive closure of the
base-changed family. -/
theorem mem_closure_image_piAlgebraMap {ι : Type*} {g : ι → (κ → R)} {s : Set ι} {x : κ → R}
    (hx : x ∈ AddSubmonoid.closure (g '' s)) :
    Pi.algebraMap κ R S x ∈
      AddSubmonoid.closure ((fun i => Pi.algebraMap κ R S (g i)) '' s) := by
  have h := AddSubmonoid.mem_map_of_mem (Pi.algebraMap κ R S).toAddMonoidHom hx
  rwa [AddMonoidHom.map_mclosure, ← image_comp] at h

/-- A family of vectors spanning the standard lattice still spans after entrywise base change. -/
theorem span_range_piAlgebraMap_eq_top [Finite κ] {ι : Type*} {v : ι → (κ → R)}
    (hv : span R (range v) = ⊤) :
    span S (range fun i => Pi.algebraMap κ R S (v i)) = ⊤ := by
  classical
  have hmem (x : κ → R) :
      Pi.algebraMap κ R S x ∈ span S (range fun i => Pi.algebraMap κ R S (v i)) := by
    have h := Submodule.mem_map_of_mem (f := Pi.algebraMap κ R S) (hv ▸ Submodule.mem_top (x := x))
    rw [Submodule.map_span, ← range_comp] at h
    exact Submodule.span_le_restrictScalars R S _ h
  rw [eq_top_iff, ← (Pi.basisFun S κ).span_eq, Submodule.span_le]
  rintro - ⟨j, rfl⟩
  have hj : Pi.algebraMap κ R S (Pi.single j 1) = Pi.basisFun S κ j := by
    ext k
    rcases eq_or_ne k j with rfl | hk <;> simp [piAlgebraMap_apply, *]
  exact hj ▸ hmem _

end Entrywise

/-! ## The base-changed pairing -/

section Defs

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)

variable [FaithfulSMul R S]

/-- **Base change of a root pairing on the standard lattices.** The roots and coroots of
`P : RootPairing ι R (κ → R) (κ → R)`, whose pairing is the dot product, are pushed entrywise
along the injective map `algebraMap R S`, with injectivity supplied by `[FaithfulSMul R S]`, and
paired again by the dot product on `κ → S`. -/
def rootPairingBaseChange : RootPairing ι S (κ → S) (κ → S) where
  toLinearMap := dotProductBilin S S
  root := ⟨fun i => Pi.algebraMap κ R S (P.root i),
    (piAlgebraMap_injective S).comp P.root.injective⟩
  coroot := ⟨fun i => Pi.algebraMap κ R S (P.coroot i),
    (piAlgebraMap_injective S).comp P.coroot.injective⟩
  root_coroot_two i := by
    simp [Pi.algebraMap, ← RingHom.map_dotProduct, ← hP, map_ofNat]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    have h := congrArg (Pi.algebraMap κ R S) (P.reflectionPerm_root i j)
    simp only [map_sub, map_smul] at h
    simpa [Pi.algebraMap, ← RingHom.map_dotProduct, hP] using h
  reflectionPerm_coroot i j := by
    have h := congrArg (Pi.algebraMap κ R S) (P.reflectionPerm_coroot i j)
    simp only [map_sub, map_smul] at h
    simpa [Pi.algebraMap, ← RingHom.map_dotProduct, hP] using h

@[simp] theorem root_rootPairingBaseChange (i : ι) :
    (rootPairingBaseChange S P hP).root i = Pi.algebraMap κ R S (P.root i) :=
  (rfl)

@[simp] theorem coroot_rootPairingBaseChange (i : ι) :
    (rootPairingBaseChange S P hP).coroot i = Pi.algebraMap κ R S (P.coroot i) :=
  (rfl)

@[simp] theorem reflectionPerm_rootPairingBaseChange :
    (rootPairingBaseChange S P hP).reflectionPerm = P.reflectionPerm :=
  (rfl)

@[simp] theorem toLinearMap_rootPairingBaseChange (x y : κ → S) :
    (rootPairingBaseChange S P hP).toLinearMap x y = x ⬝ᵥ y :=
  (rfl)

@[simp] theorem pairing_rootPairingBaseChange (i j : ι) :
    (rootPairingBaseChange S P hP).pairing i j = algebraMap R S (P.pairing i j) := by
  simp [← RootPairing.root_coroot_eq_pairing, Pi.algebraMap, ← RingHom.map_dotProduct, hP]

/-- An entrywise base-changed vector is a root of the base change exactly when the vector is a
root of the original pairing. -/
theorem piAlgebraMap_mem_range_root_rootPairingBaseChange_iff (x : κ → R) :
    Pi.algebraMap κ R S x ∈ range (rootPairingBaseChange S P hP).root ↔ x ∈ range P.root := by
  simp only [mem_range, root_rootPairingBaseChange, (piAlgebraMap_injective S).eq_iff]

/-- Two roots of the base change into a domain are linearly independent exactly when the
corresponding roots of the original pairing are. -/
theorem linearIndependent_pair_root_rootPairingBaseChange_iff [IsDomain S] (i j : ι) :
    LinearIndependent S
        ![(rootPairingBaseChange S P hP).root i, (rootPairingBaseChange S P hP).root j] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  refine Iff.trans ?_ (linearIndependent_algebraMap_comp_iff (R := R) (S := S))
  congr! 1
  ext k : 1
  fin_cases k <;> rfl

end Defs

/-! ## Transport of the axioms a Lie-theoretic consumer needs -/

section Transport

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y) [FaithfulSMul R S]

/-- Base change preserves being crystallographic: a pairing which was an integer stays that same
integer in the new base ring. -/
instance isCrystallographic_rootPairingBaseChange [P.IsCrystallographic] :
    (rootPairingBaseChange S P hP).IsCrystallographic where
  exists_value i j := by
    refine ⟨P.pairingIn ℤ i j, ?_⟩
    rw [pairing_rootPairingBaseChange, ← P.algebraMap_pairingIn ℤ i j]
    simp [algebraMap_int_eq]

/-- The integral pairing of a crystallographic root pairing is unchanged by base change into a
ring of characteristic zero. Hence so is the Cartan matrix of any base. -/
@[simp] theorem pairingIn_rootPairingBaseChange [CharZero S] [P.IsCrystallographic] (i j : ι) :
    (rootPairingBaseChange S P hP).pairingIn ℤ i j = P.pairingIn ℤ i j := by
  refine algebraMap_injective ℤ S ?_
  rw [RootPairing.algebraMap_pairingIn, pairing_rootPairingBaseChange,
    ← P.algebraMap_pairingIn ℤ i j]
  simp [algebraMap_int_eq]

/-- Base change along an injective map into a domain preserves being reduced. -/
theorem isReduced_rootPairingBaseChange [IsDomain S] [P.IsReduced] :
    (rootPairingBaseChange S P hP).IsReduced where
  eq_or_eq_neg i j h := by
    rw [linearIndependent_pair_root_rootPairingBaseChange_iff] at h
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j h with h | h <;> simp [h]

/-- Base change preserves spanning by the roots. -/
theorem span_range_root_rootPairingBaseChange_eq_top (h : span R (range P.root) = ⊤) :
    span S (range (rootPairingBaseChange S P hP).root) = ⊤ :=
  span_range_piAlgebraMap_eq_top S h

/-- Base change preserves spanning by the coroots. -/
theorem span_range_coroot_rootPairingBaseChange_eq_top (h : span R (range P.coroot) = ⊤) :
    span S (range (rootPairingBaseChange S P hP).coroot) = ⊤ :=
  span_range_piAlgebraMap_eq_top S h

end Transport

/-! ## Bases -/

section Base

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)
  [FaithfulSMul R S] [IsDomain S] (b : P.Base)

/-- **The base change of a base.** A base of `P` is a base of the base-changed pairing, supported
on the same indices. -/
def rootPairingBaseChangeBase : (rootPairingBaseChange S P hP).Base where
  support := b.support
  linearIndepOn_root :=
    linearIndependent_algebraMap_comp_iff (S := S) |>.mpr b.linearIndepOn_root
  linearIndepOn_coroot :=
    linearIndependent_algebraMap_comp_iff (S := S) |>.mpr b.linearIndepOn_coroot
  root_mem_or_neg_mem i := (b.root_mem_or_neg_mem i).imp (mem_closure_image_piAlgebraMap S)
    fun h => by simpa using mem_closure_image_piAlgebraMap S h
  coroot_mem_or_neg_mem i := (b.coroot_mem_or_neg_mem i).imp (mem_closure_image_piAlgebraMap S)
    fun h => by simpa using mem_closure_image_piAlgebraMap S h

@[simp] theorem support_rootPairingBaseChangeBase :
    (rootPairingBaseChangeBase S P hP b).support = b.support :=
  (rfl)

/-- The supports of a base and of its base change name the same indices. -/
def supportEquivRootPairingBaseChangeBase :
    (rootPairingBaseChangeBase S P hP b).support ≃ b.support :=
  Equiv.subtypeEquivRight fun i => by rw [support_rootPairingBaseChangeBase]

@[simp] theorem coe_supportEquivRootPairingBaseChangeBase
    (i : (rootPairingBaseChangeBase S P hP b).support) :
    (supportEquivRootPairingBaseChangeBase S P hP b i : ι) = i :=
  (rfl)

/-- Base change does not change the Cartan matrix of a base. -/
@[simp] theorem cartanMatrix_rootPairingBaseChangeBase [CharZero S] [P.IsCrystallographic]
    (i j : (rootPairingBaseChangeBase S P hP b).support) :
    (rootPairingBaseChangeBase S P hP b).cartanMatrix i j =
      b.cartanMatrix (supportEquivRootPairingBaseChangeBase S P hP b i)
        (supportEquivRootPairingBaseChangeBase S P hP b j) :=
  pairingIn_rootPairingBaseChange S P hP i j

end Base

/-! ## Root strings -/

section Chain

variable {ι κ R : Type*} (S : Type*) [Finite ι] [Fintype κ] [CommRing R] [CommRing S]
  [Algebra R S] [IsDomain R] [CharZero R] [IsDomain S] [CharZero S] [FaithfulSMul R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)
  [P.IsCrystallographic]

/-- Base change preserves the upper root-string coefficient. -/
@[simp] theorem chainTopCoeff_rootPairingBaseChange (i j : ι) :
    (rootPairingBaseChange S P hP).chainTopCoeff i j = P.chainTopCoeff i j := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' := (linearIndependent_pair_root_rootPairingBaseChange_iff S P hP i j).mpr h
    refine eq_of_forall_le_iff fun n => ?_
    rw [← RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff h',
      ← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h,
      ← piAlgebraMap_mem_range_root_rootPairingBaseChange_iff S P hP, map_add, map_nsmul,
      root_rootPairingBaseChange, root_rootPairingBaseChange]
  · rw [P.chainTopCoeff_of_not_linearIndependent h,
      RootPairing.chainTopCoeff_of_not_linearIndependent]
    rwa [linearIndependent_pair_root_rootPairingBaseChange_iff]

/-- Base change preserves the lower root-string coefficient. -/
@[simp] theorem chainBotCoeff_rootPairingBaseChange (i j : ι) :
    (rootPairingBaseChange S P hP).chainBotCoeff i j = P.chainBotCoeff i j := by
  rw [← RootPairing.chainTopCoeff_reflectionPerm_left, chainTopCoeff_rootPairingBaseChange,
    reflectionPerm_rootPairingBaseChange, RootPairing.chainTopCoeff_reflectionPerm_left]

end Chain

end TauCeti
