/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.PID
public import TauCeti.Algebra.Module.LocalizedModule.Away.Int
public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalizationAway
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic
public import TauCeti.RingTheory.Localization.PrincipalIdealRing

/-!
# The classifying space of a uniquely divisible abelian group

Let `m` be an integer and `A` an abelian group on which multiplication by `m` is bijective, that
is, a module over `ℤ[1/m]`. Over a commutative semisimple ring `k` in which `m = 0`, for instance
`k = 𝔽₂` and `m = 2`, the group homology of `A` with trivial coefficients `k` vanishes in every
positive degree, and so the Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` has the
`k`-homology of a point.

The proof follows Serre. The group `A` is the directed union of its finitely generated
`ℤ[1/m]`-submodules, and a class of a directed union comes from a member
(`TauCeti.groupHomology.isZero_groupHomology_of_directed`). For `m ≠ 0`, `ℤ[1/m]` is a principal
ideal domain (`IsLocalization.isPrincipalIdealRing`), so a finitely generated `ℤ[1/m]`-module is
the product of a free module `ℤ[1/m]ⁿ` and a torsion module. The torsion part is a finite group
whose order is prime to `m`, hence a unit of `k`, so its homology vanishes
(`groupHomology.subsingleton_of_isUnit_natCard`); the factor `ℤ[1/m]` is acyclic over `k`
(`TauCeti.isZero_groupHomology_localizationAway`); and a product of acyclic groups is acyclic over
a semisimple ring, by the Künneth theorem (`TauCeti.subsingleton_groupHomology_prod`). The case
`m = 0` is handled separately: multiplication by zero is bijective only on the trivial group.

For `m = 2` this is the vanishing `H_i(K(A, 1); 𝔽₂) = 0` for all `i > 0` and every uniquely
two-divisible group `A`, the case `n = 1` of the mod-two acyclicity of the Eilenberg--MacLane
spaces `K(A, n)` that drives the mod-two Hurewicz theorem.

## Main results

* `TauCeti.subsingleton_groupHomology_of_bijective_zsmul`: an abelian group on which
  multiplication by `m` is bijective has no positive-degree group homology with trivial
  coefficients in a semisimple ring in which `m = 0`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul`: the corresponding
  vanishing of the positive-degree homology of `K(A, 1)`.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology`: `K(A, 1)` has the
  mod-two homology of a point when `A` is uniquely two-divisible.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter I.
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter V.
-/

public section

noncomputable section

open CategoryTheory
open scoped DirectSum

namespace TauCeti

variable (k : Type) [CommRing k] {m : ℤ}

section Homology

open TauCeti.groupHomology

variable [IsSemisimpleRing k]

/-- The homology computation for a group presented as a free `ℤ[1/m]`-module `ℤ[1/m]ʳ` times a
finitely generated `ℤ[1/m]`-module killed by a nonzero element `q`. The free factor is a product of
copies of the acyclic group `ℤ[1/m]`, and the torsion factor is a finite group whose order is a
unit of `k`. -/
private theorem subsingleton_groupHomology_of_addEquiv_pi_prod (hm : m ≠ 0) (hmk : (m : k) = 0)
    {N T : Type} [AddCommGroup N] [AddCommGroup T] [Module (Localization.Away m) T]
    [Module.Finite (Localization.Away m) T] {r : ℕ} {q : Localization.Away m} (hq : q ≠ 0)
    (hqT : ∀ x : T, q • x = 0) (φ : N ≃+ (Fin r → Localization.Away m) × T) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)) := by
  have hR (n : ℕ) :
      Subsingleton (groupHomology (Rep.trivial k (Multiplicative (Localization.Away m)) k)
        (n + 1)) := by
    refine ModuleCat.subsingleton_of_isZero ?_
    rcases n with _ | n
    · exact isZero_groupHomology_one_localizationAway k hmk
    · exact isZero_groupHomology_localizationAway k hm (by omega)
  have hfree : ∀ n, Subsingleton (groupHomology
      (Rep.trivial k (Multiplicative (Fin r → Localization.Away m)) k) (n + 1)) :=
    Module.pi_induction' (ι := Fin r) (Localization.Away m)
      (fun N _ _ ↦ ∀ n, Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)))
      (fun N _ _ ↦ ∀ n, Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)))
      (fun e h n ↦ have := h n
        e.symm.toAddEquiv.toMultiplicative.subsingleton_groupHomology)
      (fun e h n ↦ have := h n
        e.symm.toAddEquiv.toMultiplicative.subsingleton_groupHomology)
      (fun n ↦ ModuleCat.subsingleton_of_isZero (isZero_groupHomology_succ_of_subsingleton _ n))
      (fun hN hN' n ↦ subsingleton_groupHomology_multiplicative_prod k hN hN' n)
      (fun _ ↦ Localization.Away m) (fun _ ↦ hR)
  have : Finite T :=
    finite_of_moduleFinite_localizationAway_of_isAddTorsion (m := m) fun x ↦
      isOfFinAddOrder_of_smul_eq_zero hq (hqT x)
  have htors (n : ℕ) :
      Subsingleton (groupHomology (Rep.trivial k (Multiplicative T) k) (n + 1)) := by
    refine groupHomology.subsingleton_of_isUnit_natCard _ ?_ n
    rw [Nat.card_congr Multiplicative.toAdd]
    exact isUnit_natCard_of_localizationAway hmk
  have := subsingleton_groupHomology_multiplicative_prod k hfree htors n
  exact φ.toMultiplicative.subsingleton_groupHomology

/-- The homology of a finitely generated `ℤ[1/m]`-module vanishes in positive degrees: by the
structure theorem over the principal ideal domain `ℤ[1/m]` it is a free module `ℤ[1/m]ʳ` times a
torsion module killed by a nonzero element. -/
private theorem subsingleton_groupHomology_of_moduleFinite_localizationAway (hm : m ≠ 0)
    (hmk : (m : k) = 0) (N : Type) [AddCommGroup N] [Module (Localization.Away m) N]
    [Module.Finite (Localization.Away m) N] (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)) := by
  have : IsDomain (Localization.Away m) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hm)
  -- `N ≅ ℤ[1/m]ʳ × ⨁ᵢ ℤ[1/m] ⧸ (pᵢ ^ eᵢ)`, and the second factor is killed by `∏ᵢ pᵢ ^ eᵢ`
  obtain ⟨r, ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_free_prod_directSum (Localization.Away m) N
  have hq : ∏ i, p i ^ e i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hp i).ne_zero
  refine subsingleton_groupHomology_of_addEquiv_pi_prod k hm hmk hq (fun x ↦ ?_)
    (φ.trans (LinearEquiv.prodCongr
      (Finsupp.linearEquivFunOnFinite (Localization.Away m) (Localization.Away m) (Fin r))
      (LinearEquiv.refl _ _))).toAddEquiv n
  refine DirectSum.ext fun i ↦ ?_
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun i ↦ p i ^ e i) (Finset.mem_univ i)
  have hi : Module.IsTorsionBy (Localization.Away m)
      (Localization.Away m ⧸ Localization.Away m ∙ p i ^ e i) (p i ^ e i) :=
    (Module.isTorsionBy_quotient_iff _ _).2 fun y ↦
      Submodule.mem_span_singleton.2 ⟨y, by rw [smul_eq_mul, smul_eq_mul, mul_comm]⟩
  rw [DirectSum.smul_apply, DirectSum.zero_apply, hc, mul_comm, mul_smul, hi, smul_zero]

/-- The homology of a `ℤ[1/m]`-module vanishes in positive degrees, as it does for each of its
finitely generated submodules. -/
private theorem subsingleton_groupHomology_of_localizationAway (hm : m ≠ 0) (hmk : (m : k) = 0)
    (A : Type) [AddCommGroup A] [Module (Localization.Away m) A] (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1)) :=
  subsingleton_groupHomology_of_forall_span (R := Localization.Away m) fun _ ↦
    subsingleton_groupHomology_of_moduleFinite_localizationAway k hm hmk _ n

/-- **Abelian groups on which multiplication by `m` is bijective are acyclic modulo `m`.** Let
`k` be a commutative semisimple ring in which the integer `m` vanishes. If multiplication by `m` is
a bijection of the abelian group `A`, then the group homology of `A` with trivial coefficients `k`
vanishes in every positive degree. -/
theorem subsingleton_groupHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun x : A ↦ m • x) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · -- multiplication by zero is injective only on the trivial group
    have : Subsingleton (Multiplicative A) :=
      ⟨fun x y ↦ Multiplicative.toAdd.injective <| hA.1 <| by simp⟩
    exact ModuleCat.subsingleton_of_isZero (isZero_groupHomology_succ_of_subsingleton _ n)
  let _ : Module (Localization.Away m) A := hA.localizationAwayModule
  exact subsingleton_groupHomology_of_localizationAway k hm hmk A n

/-- **The classifying space of a uniquely `m`-divisible abelian group.** If multiplication by `m`
is a bijection of the abelian group `A`, then the Eilenberg--MacLane space
`K(A, 1) = B(Multiplicative A)` has no homology in positive degrees with coefficients in a
commutative semisimple ring `k` in which `m = 0`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0)
    {A : Type} [AddCommGroup A] (hA : Function.Bijective fun x : A ↦ m • x) (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_bijective_zsmul k hmk hA n
  (classifyingSpaceSingularHomologyIsoGroupHomology k _ (n + 1)).toLinearEquiv.toEquiv.subsingleton

/-- **Mod-two acyclicity of `K(A, 1)`.** For a uniquely two-divisible abelian group `A`, the
Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` has the mod-two homology of a point:
`H_i(K(A, 1); 𝔽₂) = 0` for all `i > 0`. -/
theorem IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology {A : Type}
    [AddCommGroup A] (hA : IsUniquelyTwoDivisible A) (n : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2)
    (by decide) ((isUniquelyTwoDivisible_iff A).1 hA) n

end Homology

end TauCeti
