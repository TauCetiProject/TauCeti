/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalizationAway
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
import Mathlib.Algebra.Module.PID
import TauCeti.RepresentationTheory.Homological.GroupHomology.Functoriality
import TauCeti.RepresentationTheory.Homological.GroupHomology.LocallyFinite
import TauCeti.RingTheory.Localization.PrincipalIdealRing

/-!
# The classifying space of a uniquely two-divisible group is mod-two acyclic

Let `A` be a uniquely two-divisible abelian group, equivalently a `ℤ[1/2]`-module. Then the
Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` has the mod-two homology of a point:
`Hₙ₊₁(K(A, 1); 𝔽₂) = 0` for every `n`
(`TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology`). The same holds
with coefficients in any commutative semisimple ring `k` in which `2 = 0`, and equivalently for the
group homology of `A` with trivial coefficients `k`
(`TauCeti.IsUniquelyTwoDivisible.subsingleton_groupHomology`). No finiteness or countability is
assumed on `A`.

This is the case `n = 1` of the vanishing of the reduced mod-two homology of `K(A, n)` for every
`ℤ[1/2]`-module `A`, which feeds, through the path-loop fibrations `K(A, n - 1) → P → K(A, n)`,
Serre's theorem that the homotopy groups of a simply connected space with the mod-two homology of a
point are uniquely two-divisible.

The proof assembles the special cases already known.

* `A` is the directed union of its finitely generated `ℤ[1/2]`-submodules, and every homology
  class of a directed union of subgroups comes from one of them
  (`TauCeti.groupHomology.isZero_groupHomology_of_directed`).
* `ℤ[1/2]` is a principal ideal domain (`Localization.isPrincipalIdealRing`), so a finitely
  generated `ℤ[1/2]`-module is the product of its torsion submodule and a free module
  `ℤ[1/2]ʳ`, by the splitting of the torsion-free quotient used in the proof of Mathlib's
  structure theorem `Module.equiv_free_prod_directSum`.
* Every element of the torsion submodule has odd order
  (`TauCeti.odd_addOrderOf_of_smul_eq_zero`), which is a unit of `k`, so its positive-degree
  homology vanishes (`groupHomology.subsingleton_of_forall_isUnit_orderOf`).
* `ℤ[1/2]` itself is `k`-acyclic (`TauCeti.isZero_groupHomology_localizationAway` and
  `TauCeti.isZero_groupHomology_one_localizationAway`).
* Products of `k`-acyclic groups are `k`-acyclic, by the Künneth theorem over the semisimple ring
  `k` (`TauCeti.subsingleton_groupHomology_prod`).

The groups and coefficients live in `Type`, as for the computation of the homology of `ℤ[1/2]`.

## Main results

* `TauCeti.subsingleton_groupHomology_of_module_localizationAway_two`: `Hₙ₊₁(A, k) = 0` for a
  `ℤ[1/2]`-module `A`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_module_localizationAway_two`:
  `Hₙ₊₁(K(A, 1); k) = 0` for a `ℤ[1/2]`-module `A`.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_groupHomology` and
  `TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology`: the same
  statements for a uniquely two-divisible group `A`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294, Chapter I.
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter V, Section 6.
-/

public section

open CategoryTheory

namespace TauCeti

section

open _root_.TauCeti.groupHomology

variable (k : Type) [CommRing k]

/-- The group homology of `ℤ[1/2]` with trivial coefficients in which `2 = 0` vanishes in positive
degrees. -/
private theorem subsingleton_groupHomology_localizationAway_two (h2 : (2 : k) = 0) (n : ℕ) :
    Subsingleton
      (groupHomology (Rep.trivial k (Multiplicative (Localization.Away (2 : ℤ))) k) (n + 1)) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  rcases n with _ | n
  · exact isZero_groupHomology_one_localizationAway k (by exact_mod_cast h2)
  · exact isZero_groupHomology_localizationAway k two_ne_zero (by omega)

/-- A `ℤ[1/2]`-module in which every element is killed by a nonzero scalar has no group homology
in positive degrees with trivial coefficients in which `2 = 0`: its elements have odd order. -/
private theorem subsingleton_groupHomology_of_isTorsion (h2 : (2 : k) = 0) (T : Type)
    [AddCommGroup T] [Module (Localization.Away (2 : ℤ)) T]
    (hT : Module.IsTorsion (Localization.Away (2 : ℤ)) T) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative T) k) (n + 1)) := by
  have := Localization.Away.isDomain (two_ne_zero : (2 : ℤ) ≠ 0)
  have hodd (x : T) : Odd (addOrderOf x) := by
    obtain ⟨a, ha⟩ := @hT x
    exact odd_addOrderOf_of_smul_eq_zero (nonZeroDivisors.coe_ne_zero a) ha
  have := Group.isLocallyFinite_multiplicative_iff.2 fun x : T ↦
    addOrderOf_pos_iff.1 (hodd x).pos
  refine _root_.groupHomology.subsingleton_of_forall_isUnit_orderOf _ (fun g ↦ ?_) n
  rw [← ofAdd_toAdd g, orderOf_ofAdd_eq_addOrderOf,
    natCast_eq_one_of_odd_of_two_eq_zero (hodd _) h2]
  exact isUnit_one

variable [IsSemisimpleRing k]

/-- The free `ℤ[1/2]`-module `ℤ[1/2]ʳ` has no group homology in positive degrees with trivial
coefficients in which `2 = 0`. -/
private theorem subsingleton_groupHomology_pi_localizationAway_two (h2 : (2 : k) = 0)
    (r n : ℕ) : Subsingleton
      (groupHomology (Rep.trivial k (Multiplicative (Fin r → Localization.Away (2 : ℤ))) k)
        (n + 1)) := by
  induction r generalizing n with
  | zero => exact _root_.groupHomology.subsingleton_of_isUnit_natCard _ (by simp) n
  | succ r ih =>
    exact subsingleton_trivial_of_mulEquiv k
      ((AddEquiv.toMultiplicative
        (Fin.consLinearEquiv ℤ fun _ ↦ Localization.Away (2 : ℤ)).toAddEquiv).symm.trans
        (MulEquiv.prodMultiplicative _ _)).symm
      (subsingleton_groupHomology_prod _ _ k
        (subsingleton_groupHomology_localizationAway_two k h2) ih n)

/-- A finitely generated `ℤ[1/2]`-module has no group homology in positive degrees with trivial
coefficients in which `2 = 0`: it is the product of its torsion submodule and a free module. The
splitting follows the proof of Mathlib's `Module.equiv_free_prod_directSum`. -/
private theorem subsingleton_groupHomology_of_finite (h2 : (2 : k) = 0) (M : Type)
    [AddCommGroup M] [Module (Localization.Away (2 : ℤ)) M]
    [Module.Finite (Localization.Away (2 : ℤ)) M] (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative M) k) (n + 1)) := by
  have := Localization.Away.isDomain (two_ne_zero : (2 : ℤ) ≠ 0)
  let T := Submodule.torsion (Localization.Away (2 : ℤ)) M
  -- The torsion-free quotient is free, so the quotient map splits.
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := Localization.Away (2 : ℤ))
    (M := M ⧸ T)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective
  let e : M ≃ₗ[Localization.Away (2 : ℤ)] T × (Fin r → Localization.Away (2 : ℤ)) :=
    (lequivProdOfRightSplitExact T.injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf).symm.trans
      (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
        (b.repr.trans (Finsupp.linearEquivFunOnFinite _ _ _)))
  exact subsingleton_trivial_of_mulEquiv k
    ((AddEquiv.toMultiplicative e.toAddEquiv).trans (MulEquiv.prodMultiplicative _ _)).symm
    (subsingleton_groupHomology_prod _ _ k
      (subsingleton_groupHomology_of_isTorsion k h2 T (Submodule.torsion_isTorsion))
      (subsingleton_groupHomology_pi_localizationAway_two k h2 r) n)

variable {k}

/-- **A `ℤ[1/2]`-module is mod-two acyclic.** A `ℤ[1/2]`-module has no group homology in positive
degrees with trivial coefficients in a commutative semisimple ring `k` in which `2 = 0`, for
instance `𝔽₂`: it is the directed union of its finitely generated submodules. -/
theorem subsingleton_groupHomology_of_module_localizationAway_two (h2 : (2 : k) = 0) (M : Type)
    [AddCommGroup M] [Module (Localization.Away (2 : ℤ)) M] (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative M) k) (n + 1)) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  let N (F : Finset M) : Submodule (Localization.Away (2 : ℤ)) M :=
    Submodule.span (Localization.Away (2 : ℤ)) F
  refine isZero_groupHomology_of_directed
    (S := fun F ↦ AddSubgroup.toSubgroup (N F).toAddSubgroup)
    (Monotone.directed_le fun F F' h ↦ ?_) ?_ fun F ↦ ?_
  · exact AddSubgroup.toSubgroup.monotone (Submodule.span_mono (by exact_mod_cast h))
  · refine eq_top_iff.2 fun x _ ↦ Subgroup.mem_iSup_of_mem {x.toAdd} ?_
    exact (Multiplicative.mem_toSubgroup _ x).2
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_singleton_self x.toAdd)))
  · let e : Multiplicative (N F) ≃* AddSubgroup.toSubgroup (N F).toAddSubgroup :=
      { toFun x := ⟨Multiplicative.ofAdd (x.toAdd : M), x.toAdd.2⟩
        invFun x := Multiplicative.ofAdd ⟨x.1.toAdd, x.2⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_mul' _ _ := rfl }
    exact isZero_res_subtype_trivial_of_mulEquiv k (G := Multiplicative (N F)) e
      (subsingleton_groupHomology_of_finite k h2 _ n)

/-- **`K(A, 1)` is mod-two acyclic for a `ℤ[1/2]`-module `A`.** The Eilenberg--MacLane space
`K(A, 1) = B(Multiplicative A)` of a `ℤ[1/2]`-module `A` has the homology of a point with
coefficients in a commutative semisimple ring `k` in which `2 = 0`, for instance `𝔽₂`:
`Hₙ₊₁(K(A, 1); k) = 0`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_module_localizationAway_two
    (h2 : (2 : k) = 0) (A : Type) [AddCommGroup A] [Module (Localization.Away (2 : ℤ)) A]
    (n : ℕ) : Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_module_localizationAway_two h2 A n
  (classifyingSpaceSingularHomologyIsoGroupHomology k _ (n + 1)).toLinearEquiv.toEquiv.subsingleton

/-- **A uniquely two-divisible group is mod-two acyclic.** If multiplication by two is bijective on
the abelian group `A`, then the group homology of `A` with trivial coefficients in a commutative
semisimple ring `k` in which `2 = 0`, for instance `𝔽₂`, vanishes in positive degrees:
`Hₙ₊₁(A, k) = 0`. -/
theorem IsUniquelyTwoDivisible.subsingleton_groupHomology {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) (h2 : (2 : k) = 0) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1)) :=
  letI := hA.localizationAwayTwoModule
  subsingleton_groupHomology_of_module_localizationAway_two h2 A n

/-- **`K(A, 1)` is mod-two acyclic for a uniquely two-divisible group `A`.** If multiplication by
two is bijective on the abelian group `A`, then the Eilenberg--MacLane space
`K(A, 1) = B(Multiplicative A)` has the homology of a point with coefficients in a commutative
semisimple ring `k` in which `2 = 0`, for instance `𝔽₂`: `Hₙ₊₁(K(A, 1); k) = 0`. -/
theorem IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology {A : Type}
    [AddCommGroup A] (hA : IsUniquelyTwoDivisible A) (h2 : (2 : k) = 0) (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  letI := hA.localizationAwayTwoModule
  subsingleton_classifyingSpace_singularHomology_of_module_localizationAway_two h2 A n

end

end TauCeti
