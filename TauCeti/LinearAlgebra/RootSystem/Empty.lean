/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# Root-free root pairings

When the root index type `ι` is empty, a root pairing `P : RootPairing ι R M N` carries only the
perfect pairing between `M` and `N`, as in the root data of algebraic tori.

## Main definitions

* `RootPairing.empty`: the canonical root-free pairing on a reflexive module `M` and `Dual R M`.
* `RootPairing.Base.ofIsEmpty`: the unique base of a root-free pairing, with empty support.

## Main results

* `RootPairing.empty_toLinearMap`: the pairing of `RootPairing.empty R M` is `Module.Dual.eval`.
* `RootPairing.weylGroup_eq_bot_of_isEmpty` and `RootPairing.Base.instUniqueOfIsEmpty`: a
  root-free pairing has trivial Weyl group and unique base `Base.ofIsEmpty`.
* `RootPairing.instIsReducedOfIsEmpty`, `RootPairing.instIsValuedInOfIsEmpty`, and
  `RootPairing.instIsBalancedOfIsEmpty`: vacuous instances for `[IsEmpty ι]`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §1.1.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C, C.43.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- **The canonical root-free pairing** on a reflexive `R`-module `M` and its dual
`Module.Dual R M`. -/
def empty (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] :
    RootPairing Empty R M (Module.Dual R M) where
  toLinearMap := Module.Dual.eval R M
  root := ⟨Empty.elim, fun x ↦ x.elim⟩
  coroot := ⟨Empty.elim, fun x ↦ x.elim⟩
  root_coroot_two x := x.elim
  reflectionPerm x := x.elim
  reflectionPerm_root x := x.elim
  reflectionPerm_coroot x := x.elim

/-- The bilinear pairing of `RootPairing.empty R M` is `Module.Dual.eval R M`. -/
@[simp] theorem empty_toLinearMap (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.IsReflexive R M] : (empty R M).toLinearMap = Module.Dual.eval R M := (rfl)

section IsEmpty

variable (P : RootPairing ι R M N) [IsEmpty ι]

/-- **A root-free pairing has trivial Weyl group.** -/
@[simp] theorem weylGroup_eq_bot_of_isEmpty : P.weylGroup = ⊥ := by
  simp [weylGroup, Set.range_eq_empty]

/-- **The unique base of a root-free pairing**, with empty support. -/
def Base.ofIsEmpty : P.Base where
  support := ∅
  linearIndepOn_root := by simp
  linearIndepOn_coroot := by simp
  root_mem_or_neg_mem := isEmptyElim
  coroot_mem_or_neg_mem := isEmptyElim

/-- The empty base has empty support. -/
@[simp] theorem Base.support_ofIsEmpty : (Base.ofIsEmpty P).support = ∅ := (rfl)

/-- Every root-free pairing has a unique base, namely `RootPairing.Base.ofIsEmpty P`. -/
instance Base.instUniqueOfIsEmpty : Unique P.Base where
  default := Base.ofIsEmpty P
  uniq b := by cases b; congr; exact Finset.eq_empty_of_isEmpty _

/-- Every root-free pairing is vacuously reduced. -/
instance instIsReducedOfIsEmpty : P.IsReduced := ⟨isEmptyElim⟩

/-- Every root-free pairing is vacuously valued in any base ring `S` (in particular,
crystallographic when `S = ℤ`). -/
instance instIsValuedInOfIsEmpty (S : Type*) [CommRing S] [Algebra S R] : P.IsValuedIn S :=
  ⟨isEmptyElim⟩

/-- Every root-free pairing is vacuously balanced (`rootSpan R = ⊥` and `corootSpan R = ⊥`). -/
instance instIsBalancedOfIsEmpty : P.IsBalanced where
  isPerfectCompl :=
    { isCompl_left := by simpa [rootSpan, corootSpan, Set.range_eq_empty,
        LinearMap.range_eq_top.mpr P.toPerfPair.symm.surjective] using isCompl_bot_top
      isCompl_right := by simpa [rootSpan, corootSpan, Set.range_eq_empty,
        LinearMap.range_eq_top.mpr P.flip.toPerfPair.symm.surjective] using isCompl_bot_top }

end IsEmpty

end RootPairing
