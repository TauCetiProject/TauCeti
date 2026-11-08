/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.PID
public import TauCeti.Algebra.Module.LocalizedModule.AddOrder
public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalizationAway
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
public import TauCeti.RingTheory.Localization.PrincipalIdealRing

/-!
# The classifying space of a uniquely divisible abelian group

Let `m` be an integer and `k` a commutative semisimple ring, for instance a field, in which
`m = 0`. If multiplication by `m` is a bijection of an abelian group `A`, then the
Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` has the `k`-homology of a point:
`Hₙ₊₁(K(A, 1); k) = 0` for every `n`
(`TauCeti.subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul`). For `m = 2` and
`k = 𝔽₂`: the space `K(A, 1)` of a uniquely two-divisible group `A` has the mod-two homology of a
point (`TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology_zmod_two`).
This is the case `n = 1` of the vanishing of the reduced homology `H_*(K(A, n); 𝔽₂)` for
uniquely two-divisible `A`, on which the mod-two vanishing theorem for simply connected spaces is
built.

The proof works with the group homology of `A`, through the identification
`Hₙ(BG; k) ≅ Hₙ(G, k)`. Multiplication by `m` being bijective, `A` is a module over
`ℤ[1/m] = Localization.Away m`, and it is the directed union of its finitely generated
`ℤ[1/m]`-submodules. Group homology commutes with such unions
(`TauCeti.groupHomology.isZero_groupHomology_of_directed`), so it suffices to treat a finitely
generated `ℤ[1/m]`-module `M`. (The case `m = 0` is separate: multiplication by zero is bijective
only on the zero group.) For `m ≠ 0`, `ℤ[1/m]` is a principal ideal domain
(`Localization.isPrincipalIdealRing`), so `M` splits as the product of its torsion submodule and a
free module `ℤ[1/m]ʳ`, and over the semisimple ring `k` the Künneth theorem shows that a product of
`k`-acyclic groups is `k`-acyclic (`TauCeti.subsingleton_groupHomology_prod`). The two factors are
`k`-acyclic:

* `ℤ[1/m]` is (`TauCeti.isZero_groupHomology_localizationAway` and
  `TauCeti.isZero_groupHomology_one_localizationAway`), hence so is `ℤ[1/m]ʳ` by induction on `r`;
* every element of a torsion `ℤ[1/m]`-module has finite additive order prime to `m`
  (`TauCeti.isUnit_addOrderOf_of_smul_eq_zero`), which is a unit of `k`, and an abelian group
  whose element orders are units of `k` is `k`-acyclic
  (`TauCeti.subsingleton_groupHomology_of_forall_isUnit_addOrderOf`).

The groups and the coefficient ring live in `Type`, as in the computation of the homology of
`ℤ[1/m]` that this file consumes.

## Main results

* `TauCeti.subsingleton_groupHomology_of_bijective_zsmul`: an abelian group on which
  multiplication by `m` is bijective is `k`-acyclic.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul`: its classifying
  space `K(A, 1)` has the `k`-homology of a point.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology_zmod_two`: for a
  uniquely two-divisible group `A`, the space `K(A, 1)` has the mod-two homology of a point.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter V, Section 5.
-/

public section

open CategoryTheory Limits groupHomology

namespace TauCeti

variable (k : Type) [CommRing k] {m : ℤ}

/-- `ℤ[1/m]` is `k`-acyclic when `m = 0` in `k`, in the form used for products. -/
private theorem subsingleton_groupHomology_localizationAway (hm : m ≠ 0) (hmk : (m : k) = 0)
    (n : ℕ) :
    Subsingleton
      (groupHomology (Rep.trivial k (Multiplicative (Localization.Away m)) k) (n + 1)) :=
  ModuleCat.isZero_iff_subsingleton.1 <| by
    rcases n with _ | n
    · exact isZero_groupHomology_one_localizationAway k hmk
    · exact isZero_groupHomology_localizationAway k hm (by omega)

section Semisimple

variable [IsSemisimpleRing k]

/-- **Free `ℤ[1/m]`-modules of finite rank are acyclic.** Over a commutative semisimple ring `k`
in which `m = 0`, the group homology of `ℤ[1/m]ʳ` with trivial coefficients `k` vanishes in every
positive degree. -/
private theorem subsingleton_groupHomology_pi_localizationAway (hm : m ≠ 0) (hmk : (m : k) = 0)
    (r n : ℕ) :
    Subsingleton
      (groupHomology (Rep.trivial k (Multiplicative (Fin r → Localization.Away m)) k) (n + 1)) := by
  induction r generalizing n with
  | zero =>
    -- the zero module is the trivial group
    exact ModuleCat.isZero_iff_subsingleton.1 (isZero_groupHomology_succ_of_subsingleton _ n)
  | succ r ih =>
    let e : Multiplicative (Fin (r + 1) → Localization.Away m) ≃*
        Multiplicative (Localization.Away m) × Multiplicative (Fin r → Localization.Away m) :=
      (AddEquiv.toMultiplicative
        (Fin.consLinearEquiv ℤ fun _ ↦ Localization.Away m).symm.toAddEquiv).trans
        (MulEquiv.prodMultiplicative _ _)
    have := subsingleton_groupHomology_prod _ _ k
      (subsingleton_groupHomology_localizationAway k hm hmk) ih n
    exact (groupHomology.mapIso
      (B := Rep.trivial k
        (Multiplicative (Localization.Away m) × Multiplicative (Fin r → Localization.Away m)) k) e
      (LinearEquiv.refl k k) (fun _ ↦ by ext; simp) (n + 1)).toLinearEquiv.toEquiv.subsingleton

/-- **Finitely generated `ℤ[1/m]`-modules are acyclic.** Over a commutative semisimple ring `k`
in which `m = 0`, the group homology of a finitely generated `ℤ[1/m]`-module with trivial
coefficients `k` vanishes in every positive degree. Such a module is the product of its torsion
submodule and a free module of finite rank. -/
private theorem subsingleton_groupHomology_of_finite (hm : m ≠ 0) (hmk : (m : k) = 0) {M : Type}
    [AddCommGroup M] [Module (Localization.Away m) M] [Module.Finite (Localization.Away m) M]
    (n : ℕ) : Subsingleton (groupHomology (Rep.trivial k (Multiplicative M) k) (n + 1)) := by
  have : IsDomain (Localization.Away m) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hm)
  -- `M` is the product of its torsion submodule `T` and a free module `ℤ[1/m]ʳ`
  obtain ⟨T, _, r, hT, ⟨e⟩⟩ : ∃ (T : Type) (_ : AddCommGroup T) (r : ℕ),
      (∀ x : T, IsUnit (addOrderOf x : k)) ∧
        Nonempty (M ≃+ T × (Fin r → Localization.Away m)) := by
    let T := Submodule.torsion (Localization.Away m) M
    -- the quotient by `T` is free, so the projection onto it splits; this splitting is adapted
    -- from the proof of Mathlib's `Module.equiv_free_prod_directSum`
    obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := Localization.Away m) (M := M ⧸ T)
    obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id T.mkQ_surjective
    refine ⟨T, inferInstance, r, fun x ↦ ?_, ⟨((lequivProdOfRightSplitExact T.injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf).symm.trans
      ((LinearEquiv.refl _ _).prodCongr b.equivFun)).toAddEquiv⟩⟩
    -- the orders of the elements of `T` are units of `k`
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : M)).1 x.2
    rw [← addOrderOf_injective T.subtype.toAddMonoidHom Subtype.val_injective x]
    exact isUnit_addOrderOf_of_smul_eq_zero hmk (nonZeroDivisors.coe_ne_zero a) ha
  let e' : Multiplicative M ≃*
      Multiplicative T × Multiplicative (Fin r → Localization.Away m) :=
    (AddEquiv.toMultiplicative e).trans (MulEquiv.prodMultiplicative _ _)
  have := subsingleton_groupHomology_prod _ _ k
    (subsingleton_groupHomology_of_forall_isUnit_addOrderOf k hT)
    (subsingleton_groupHomology_pi_localizationAway k hm hmk r) n
  exact (groupHomology.mapIso
    (B := Rep.trivial k (Multiplicative T × Multiplicative (Fin r → Localization.Away m)) k) e'
    (LinearEquiv.refl k k) (fun _ ↦ by ext; simp) (n + 1)).toLinearEquiv.toEquiv.subsingleton

/-- **Uniquely divisible groups are acyclic.** Over a commutative semisimple ring `k` in which
`m = 0`, if multiplication by `m` is a bijection of the abelian group `A`, then the group homology
of `A` with trivial coefficients `k` vanishes in every positive degree. The group `A` is a
`ℤ[1/m]`-module, the directed union of its finitely generated submodules. -/
theorem subsingleton_groupHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (Multiplicative A) k) (n + 1)) := by
  classical
  let _ : Module (Localization.Away m) A := hA.localizationAwayModule
  rcases eq_or_ne m 0 with rfl | hm
  · -- multiplication by zero is bijective only on the zero group
    have : Subsingleton A := ⟨fun x y ↦ hA.1 (by simp)⟩
    exact ModuleCat.isZero_iff_subsingleton.1 (isZero_groupHomology_succ_of_subsingleton _ n)
  let S : Finset A → Subgroup (Multiplicative A) := fun s ↦
    AddSubgroup.toSubgroup (Submodule.span (Localization.Away m) (s : Set A)).toAddSubgroup
  have hS : Directed (· ≤ ·) S := fun s t ↦
    ⟨s ∪ t, AddSubgroup.toSubgroup.monotone <| Submodule.toAddSubgroup_mono <|
        Submodule.span_mono <| by simp,
      AddSubgroup.toSubgroup.monotone <| Submodule.toAddSubgroup_mono <|
        Submodule.span_mono <| by simp⟩
  have hG : ⨆ s, S s = ⊤ := eq_top_iff.2 fun g _ ↦ (Subgroup.mem_iSup_of_directed hS).2
    ⟨{g.toAdd}, by simp [S]⟩
  refine ModuleCat.isZero_iff_subsingleton.1
    (groupHomology.isZero_groupHomology_of_directed hS hG fun s ↦ ?_)
  -- each member of the union is a finitely generated `ℤ[1/m]`-module
  let N := Submodule.span (Localization.Away m) (s : Set A)
  let e : Multiplicative N ≃* S s :=
    { toFun x := ⟨Multiplicative.ofAdd (x.toAdd : A), x.toAdd.2⟩
      invFun y := Multiplicative.ofAdd ⟨y.1.toAdd, y.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  exact (ModuleCat.isZero_iff_subsingleton.2 (subsingleton_groupHomology_of_finite k hm hmk
    (M := N) n)).of_iso (groupHomology.mapIso e (LinearEquiv.refl k k)
      (fun _ ↦ by ext; simp) (n + 1)).symm

/-- **The classifying space of a uniquely divisible group is acyclic.** Over a commutative
semisimple ring `k` in which `m = 0`, if multiplication by `m` is a bijection of the abelian group
`A`, then the Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` has the `k`-homology of a
point: `Hₙ₊₁(K(A, 1); k) = 0`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0)
    {A : Type} [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_bijective_zsmul k hmk hA n
  (classifyingSpaceSingularHomologyIsoGroupHomology k _ (n + 1)).toLinearEquiv.toEquiv.subsingleton

end Semisimple

/-- **`K(A, 1)` is mod-two acyclic for uniquely two-divisible `A`.** If multiplication by two is a
bijection of the abelian group `A`, then the Eilenberg--MacLane space
`K(A, 1) = B(Multiplicative A)` has the mod-two homology of a point: `Hₙ₊₁(K(A, 1); 𝔽₂) = 0`. -/
theorem IsUniquelyTwoDivisible.subsingleton_classifyingSpace_singularHomology_zmod_two
    {A : Type} [AddCommGroup A] (hA : IsUniquelyTwoDivisible A) (n : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) :=
  subsingleton_classifyingSpace_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) n

end TauCeti
