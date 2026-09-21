/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Correspondence
import TauCeti.RepresentationTheory.Irreducible

/-!
# Injectivity in the Clifford correspondence

Let `N` be a normal subgroup of a finite group `G`, let `V` be an irreducible representation of
`N`, and put `T = inertia V`.  Induction from `T` to `G` sends irreducible representations lying
over `V` to irreducible representations lying over `V`.  This file proves the uniqueness half of
the Clifford correspondence: two such representations of `T` are isomorphic whenever their
inductions to `G` are isomorphic.

The proof uses the off-diagonal Mackey intertwining formula.  A Mackey term indexed by
`s ∉ T` vanishes because the restrictions of both representations are spanned by copies of `V`,
whereas conjugation by `s` moves `V` out of its isomorphism class.  The identity double coset then
recovers the intertwining space over `T`, so an isomorphism between the induced representations
forces an isomorphism before induction.

## Main statements

* `FDRep.subsingleton_hom_res_mackeyToH_of_not_mem_inertia`: the off-inertia Mackey
  intertwining space between two irreducibles lying over `V` is trivial.
* `FDRep.nonempty_iso_of_liesOver_inertia_of_nonempty_iso_indFDRep`: induction from the inertia
  group is injective on the relevant irreducible isomorphism classes.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §11.
-/

public section

open CategoryTheory
open Representation (IntertwiningMap)

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- **Injectivity in the Clifford correspondence.** Two irreducible representations of
`inertia V` lying over `V` are isomorphic if their inductions to `G` are isomorphic. -/
theorem nonempty_iso_of_liesOver_inertia_of_nonempty_iso_indFDRep
    [Finite G] [IsAlgClosed k] [CharZero k]
    (V : FDRep k N) [Simple V] (A B : FDRep k (inertia V)) [Simple A] [Simple B]
    (hA : A.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    (hB : B.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    (hInd : Nonempty (indFDRep A ≅ indFDRep B)) : Nonempty (A ≅ B) := by
  classical
  let _ := Fintype.ofFinite
    (DoubleCoset.Quotient (inertia V : Set G) (inertia V : Set G))
  let _ : Simple (indFDRep A) := simple_indFDRep_of_inertia V A hA
  let _ : Simple (indFDRep B) := simple_indFDRep_of_inertia V B hB
  by_contra hAB
  have hBA : ¬ Nonempty (B ≅ A) := fun ⟨e⟩ ↦ hAB ⟨e.symm⟩
  have hterm (D : DoubleCoset.Quotient (inertia V : Set G) (inertia V : Set G)) :
      Module.finrank k
          (resFDRep ((mackeySubgroup D.out (inertia V) (inertia V)).subgroupOf (inertia V)) B ⟶
            (Action.res (FGModuleCat k)
              (mackeyToH D.out (inertia V) (inertia V))).obj A) = 0 := by
    by_cases hs : D.out ∈ inertia V
    · have hchange := finrank_hom_res_mackeyToH_mul_left_mul_right B A hs
          (one_mem (inertia V)) 1
      have hrepresentative : D.out * 1 * 1 = D.out := by simp
      rw [hrepresentative] at hchange
      rw [hchange, finrank_hom_res_mackeyToH_one, FDRep.finrank_hom_simple_simple,
        ite_eq_right hBA]
    · let _ := subsingleton_hom_res_mackeyToH_of_not_mem_inertia V B A hB hA hs
      exact Module.finrank_zero_of_subsingleton
  have hzero : Module.finrank k (indFDRep A ⟶ indFDRep B) = 0 := by
    rw [finrank_hom_indFDRep_mackey B A, Finset.sum_eq_zero fun D _ ↦ hterm D]
  rw [FDRep.finrank_hom_simple_simple, ite_eq_left hInd] at hzero
  exact one_ne_zero hzero

end FDRep
