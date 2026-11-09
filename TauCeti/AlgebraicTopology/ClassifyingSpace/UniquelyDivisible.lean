/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
import Mathlib.Algebra.Module.PID
import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalizationAway
import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.RingTheory.Localization.PrincipalIdealRing

/-!
# The classifying space of a uniquely divisible abelian group

Let `m` be an integer and `A` an abelian group on which multiplication by `m` is bijective, that
is, a module over `ℤ[1/m]`. Over a commutative semisimple ring `k` in which `m = 0`, for instance
`𝔽₂` when `m = 2`, the group homology of `A` with trivial coefficients `k` vanishes in every
positive degree (`TauCeti.subsingleton_groupHomology_of_bijective_zsmul`). Equivalently, the
Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` has the `k`-homology of a point
(`TauCeti.subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul`). In particular, for
every uniquely two-divisible abelian group `A`, the reduced mod-two homology of `K(A, 1)` vanishes
(`TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology`). No
finiteness assumption is made on `A`.

The proof reduces to two cases already known.

* `A` is the directed union of its finitely generated `ℤ[1/m]`-submodules, and every class of a
  directed union of subgroups comes from a member
  (`TauCeti.groupHomology.isZero_groupHomology_of_directed`).
* `ℤ[1/m]` is a principal ideal domain (`IsLocalization.isPrincipalIdealRing`), so a finitely
  generated `ℤ[1/m]`-module is the product of its torsion submodule and a free module of finite
  rank. The torsion submodule is an abelian group whose elements have finite order prime to `m`,
  hence invertible in `k`, so its homology vanishes
  (`TauCeti.subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_addOrderOf`). The
  homology of `ℤ[1/m]` vanishes (`TauCeti.isZero_groupHomology_localizationAway` and
  `TauCeti.isZero_groupHomology_one_localizationAway`), and the Künneth formula over the
  semisimple ring `k` passes the vanishing to finite products
  (`TauCeti.subsingleton_groupHomology_prod`). Semisimplicity of `k` is used only there.

This is the case `n = 1` of the vanishing of the reduced mod-two homology of `K(A, n)` for every
`ℤ[1/2]`-module `A`, which feeds the Whitehead-tower proof that a simply connected space with
vanishing reduced mod-two homology has uniquely two-divisible homotopy groups.

## Main results

* `TauCeti.subsingleton_groupHomology_of_bijective_zsmul`: `Hₙ₊₁(A, k) = 0` when multiplication by
  `m` is bijective on `A` and `m = 0` in `k`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul`: the same for the
  singular homology of `K(A, 1)`.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology`: the case
  `m = 2`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter V, Section 5.
-/

public section

open CategoryTheory Limits

namespace TauCeti

variable (k : Type) [CommRing k] {m : ℤ}

private theorem subsingleton_groupHomology_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) {n : ℕ} (h : Subsingleton (groupHomology (Rep.trivial k G k) n)) :
    Subsingleton (groupHomology (Rep.trivial k H k) n) :=
  (groupHomology.mapIso (A := Rep.trivial k G k) (B := Rep.trivial k H k) e
    (LinearEquiv.refl k k) (fun _ ↦ by ext; simp) n).toLinearEquiv.symm.toEquiv.subsingleton

/-- The group homology of `A` with trivial coefficients `k` vanishes in positive degrees. -/
private abbrev Acyclic (A : Type) [AddCommGroup A] : Prop :=
  ∀ n, Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1))

private theorem Acyclic.of_addEquiv {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (h : Acyclic k A) : Acyclic k B := fun n ↦
  subsingleton_groupHomology_of_mulEquiv k (AddEquiv.toMultiplicative e) (h n)

private theorem acyclic_of_forall_isUnit {A : Type} [AddCommGroup A]
    (h : ∀ a : A, IsUnit (addOrderOf a : k)) : Acyclic k A := fun n ↦
  have := subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_addOrderOf k h n
  (classifyingSpaceSingularHomologyIsoGroupHomology k _ (n + 1)).symm.toLinearEquiv
    |>.toEquiv.subsingleton

private theorem acyclic_of_subsingleton {A : Type} [AddCommGroup A] [Subsingleton A] :
    Acyclic k A :=
  acyclic_of_forall_isUnit k fun a ↦ by
    rw [Subsingleton.elim a 0, addOrderOf_zero, Nat.cast_one]
    exact isUnit_one

private theorem acyclic_localizationAway (hm : m ≠ 0) (hmk : (m : k) = 0) :
    Acyclic k (Localization.Away m) := fun n ↦ by
  rw [← ModuleCat.isZero_iff_subsingleton]
  rcases n with _ | n
  · exact isZero_groupHomology_one_localizationAway k hmk
  · exact isZero_groupHomology_localizationAway k hm (by omega)

/-- A torsion `ℤ[1/m]`-module is a torsion group whose orders are prime to `m`, so its homology
vanishes. -/
private theorem acyclic_of_isTorsion (hm : m ≠ 0) (hmk : (m : k) = 0) (T : Type)
    [AddCommGroup T] [Module (Localization.Away m) T]
    (hT : Module.IsTorsion (Localization.Away m) T) : Acyclic k T := by
  have := Localization.Away.isDomain hm
  -- `m` acts invertibly, through its image in `ℤ[1/m]`
  have hu : IsUnit (m : Localization.Away m) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away m) m
  have hinj : Function.Injective fun t : T ↦ m • t := fun t t' h ↦
    hu.smul_left_cancel.1 (by simpa only [Int.cast_smul_eq_zsmul] using h)
  -- the order of `t` is prime to `m`, hence a unit of `k`, in which `m = 0`
  refine acyclic_of_forall_isUnit k fun t ↦ ?_
  suffices ht : IsOfFinAddOrder t by
    have h : IsCoprime (addOrderOf t : ℤ) m :=
      Int.isCoprime_iff_gcd_eq_one.2 (coprime_addOrderOf_of_injective_zsmul ht hinj)
    have := h.intCast (R := k)
    rwa [hmk, isCoprime_zero_right, Int.cast_natCast] at this
  -- clearing the denominator of an annihilator `a / mʲ` of `t` gives a nonzero integer killing `t`
  obtain ⟨a, ha⟩ := @hT t
  obtain ⟨⟨z, s⟩, hz⟩ := IsLocalization.surj (Submonoid.powers m) (a : Localization.Away m)
  refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨z, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hz
    exact nonZeroDivisors.coe_ne_zero a
      ((IsLocalization.map_units (Localization.Away m) s).mul_left_eq_zero.1 hz)
  · rw [← Int.cast_smul_eq_zsmul (Localization.Away m),
      ← eq_intCast (algebraMap ℤ (Localization.Away m)), ← hz, mul_comm, mul_smul,
      ← Submonoid.smul_def, ha, smul_zero]

section Semisimple

variable [IsSemisimpleRing k]

private theorem Acyclic.prod {A B : Type} [AddCommGroup A] [AddCommGroup B] (hA : Acyclic k A)
    (hB : Acyclic k B) : Acyclic k (A × B) := fun n ↦
  subsingleton_groupHomology_of_mulEquiv k (MulEquiv.prodMultiplicative A B).symm
    (subsingleton_groupHomology_prod (Multiplicative A) (Multiplicative B) k hA hB n)

private theorem acyclic_pi_localizationAway (hm : m ≠ 0) (hmk : (m : k) = 0) (ι : Type)
    [Finite ι] : Acyclic k (ι → Localization.Away m) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e h => exact h.of_addEquiv k (LinearEquiv.funCongrLeft ℤ _ e.symm).toAddEquiv
  | h_empty => exact acyclic_of_subsingleton k
  | h_option h =>
    exact ((acyclic_localizationAway k hm hmk).prod k h).of_addEquiv k
      (LinearEquiv.piOptionEquivProd (R := ℤ)).symm.toAddEquiv

/-- A finitely generated `ℤ[1/m]`-module is the product of its torsion submodule and a free
module of finite rank. -/
private theorem acyclic_of_finite (hm : m ≠ 0) (hmk : (m : k) = 0) (N : Type) [AddCommGroup N]
    [Module (Localization.Away m) N] [Module.Finite (Localization.Away m) N] :
    Acyclic k N := by
  have := Localization.Away.isDomain hm
  have := IsLocalization.isPrincipalIdealRing (Submonoid.powers m) (Localization.Away m)
  let T := Submodule.torsion (Localization.Away m) N
  -- the torsion-free quotient is free of finite rank, and the quotient map splits
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id T.mkQ_surjective
  let e := lequivProdOfRightSplitExact T.injective_subtype
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf
  let b := Module.Free.chooseBasis (Localization.Away m) (N ⧸ T)
  exact ((acyclic_of_isTorsion k hm hmk T Submodule.torsion_isTorsion).prod k
    ((acyclic_pi_localizationAway k hm hmk _).of_addEquiv k
      ((Finsupp.linearEquivFunOnFinite (Localization.Away m) (Localization.Away m) _).symm ≪≫ₗ
        b.repr.symm).toAddEquiv)).of_addEquiv k e.toAddEquiv

/-- **A uniquely `m`-divisible abelian group is acyclic modulo `m`.** Let `A` be an abelian group
on which multiplication by `m` is bijective, and `k` a commutative semisimple ring in which
`m = 0`. Then the group homology of `A` with trivial coefficients `k` vanishes in every positive
degree. -/
theorem subsingleton_groupHomology_of_bijective_zsmul {A : Type} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) (hmk : (m : k) = 0) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · -- multiplication by zero is bijective only on the zero group
    have : Subsingleton A := ⟨fun a b ↦ hA.1 (by simp)⟩
    exact acyclic_of_subsingleton k n
  let := hA.localizationAwayModule
  -- `A` is the directed union of its finitely generated `ℤ[1/m]`-submodules
  let S (N : {N : Submodule (Localization.Away m) A // N.FG}) : Subgroup (Multiplicative A) :=
    AddSubgroup.toSubgroup N.1.toAddSubgroup
  have hS : Directed (· ≤ ·) S := fun N₁ N₂ ↦ ⟨⟨N₁.1 ⊔ N₂.1, N₁.2.sup N₂.2⟩,
    AddSubgroup.toSubgroup.monotone (Submodule.toAddSubgroup_mono le_sup_left),
    AddSubgroup.toSubgroup.monotone (Submodule.toAddSubgroup_mono le_sup_right)⟩
  have hG : ⨆ N, S N = ⊤ := eq_top_iff.2 fun x _ ↦
    Subgroup.mem_iSup_of_mem ⟨_, Submodule.fg_span_singleton x.toAdd⟩
      (Submodule.mem_span_singleton_self x.toAdd)
  rw [← ModuleCat.isZero_iff_subsingleton]
  refine groupHomology.isZero_groupHomology_of_directed hS hG fun N ↦ ?_
  have := Module.Finite.iff_fg.2 N.2
  -- each member is the group of a finitely generated `ℤ[1/m]`-module
  let e : Multiplicative N.1 ≃* S N :=
    { toFun x := ⟨Multiplicative.ofAdd (x.toAdd : A), x.toAdd.2⟩
      invFun y := Multiplicative.ofAdd ⟨y.1.toAdd, y.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  have := acyclic_of_finite k hm hmk N.1 n
  rw [ModuleCat.isZero_iff_subsingleton]
  -- the restriction of the trivial representation of `Multiplicative A` to `S N` is,
  -- by definition, the trivial representation of `S N`
  exact subsingleton_groupHomology_of_mulEquiv k e this

/-- **The classifying space of a uniquely `m`-divisible abelian group is acyclic modulo `m`.** Let
`A` be an abelian group on which multiplication by `m` is bijective, and `k` a commutative
semisimple ring in which `m = 0`. Then the Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)`
has no `k`-homology in positive degrees. -/
theorem subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) (hmk : (m : k) = 0) (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_bijective_zsmul k hA hmk n
  (classifyingSpaceSingularHomologyIsoGroupHomology k _ (n + 1)).toLinearEquiv.toEquiv.subsingleton

/-- **Mod-two acyclicity of `K(A, 1)` for a uniquely two-divisible group.** If `A` is a uniquely
two-divisible abelian group and `k` is a commutative semisimple ring in which `2 = 0`, such as
`𝔽₂`, then the Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` has no `k`-homology in
positive degrees. -/
theorem IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology {A : Type}
    [AddCommGroup A] (hA : IsUniquelyTwoDivisible A) (hk : (2 : k) = 0) (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul k
    ((isUniquelyTwoDivisible_iff A).1 hA) (by rwa [Int.cast_two]) n

end Semisimple

end TauCeti
