/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent

/-!
# `K₀` of rings whose projective modules are stably free

For a ring `A`, not necessarily commutative, the class `[A]` of the regular module
(`TauCeti.finiteProjectiveModulesRegular A`) generates a copy of `ℤ` in the split Grothendieck
group of finitely generated projective `A`-modules as soon as `A` has the invariant basis number
property: `n[A] = m[A]` forces `Aⁿ⁺ᵏ ≃ Aᵐ⁺ᵏ` for some `k`, hence `n = m`. If moreover every
finitely generated projective `A`-module is stably free, every class is a multiple of `[A]`, so
this group is `ℤ`, with `[A] ↦ 1`. Over a ring with the strong rank condition the isomorphism sends
the class of a free module to its rank.

Following the right-module convention of algebraic `K`-theory, `K₀(R)` is the split Grothendieck
group of finitely generated projective right `R`-modules, encoded as left `Rᵐᵒᵖ`-modules:
`TauCeti.FiniteProjectiveRight R` and `TauCeti.KZero R`, defined in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs`. The criterion applies to
division rings, where every module is free, and to commutative principal ideal domains such as
`ℤ`, where every finitely generated projective module is free; for these `K₀(R) ≅ ℤ`. Over the
zero ring every module is zero and `K₀` is trivial.

## Main definitions

* `TauCeti.FiniteProjectiveModules.rankEquiv A h`: the isomorphism of the split `K₀` of finitely
  generated projective `A`-modules with `ℤ`, when `A` has invariant basis number and every such
  module is stably free.

## Main results

* `TauCeti.FiniteProjectiveModules.zsmul_of_finiteProjectiveModulesRegular_injective`: with
  invariant basis number, `n ↦ n[A]` is injective.
* `TauCeti.FiniteProjectiveModules.exists_zsmul_of_finiteProjectiveModulesRegular_eq`: when every
  finitely generated projective module is stably free, every class is a multiple of `[A]`.
* `TauCeti.FiniteProjectiveModules.rankEquiv_of`: the class of a free module goes to its rank.
* `TauCeti.FiniteProjectiveModules.subsingleton_splitK0`: `K₀` of the zero ring is trivial.
* `TauCeti.kZero_divisionRing`: `K₀` of a division ring is `ℤ`, with `[D] ↦ 1`.
* `TauCeti.kZero_of_isPrincipalIdealRing`: `K₀` of a commutative principal ideal domain is `ℤ`,
  with `[R] ↦ 1`, and `TauCeti.kZero_int` the case of `ℤ`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2, the
  examples of division rings and principal ideal domains at the start of the section, p. 5.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Module

universe u

namespace FiniteProjectiveModules

variable (A : Type u) [Ring A]

/-- **Invariant basis number in `K₀`.** If `A` has the invariant basis number property, then the
multiples `n[A]`, `n : ℤ`, of the class of the regular module are pairwise distinct. -/
theorem zsmul_of_finiteProjectiveModulesRegular_injective [InvariantBasisNumber A] :
    Function.Injective fun z : ℤ ↦ z • SplitK0.of.{u} (finiteProjectiveModulesRegular A) := by
  refine (injective_iff_map_eq_zero
    (zmultiplesHom _ (SplitK0.of.{u} (finiteProjectiveModulesRegular A)))).2 fun z hz ↦ ?_
  -- Write `z = n - m` with `n m : ℕ`, so that `n[A] = m[A]`, that is `[Aⁿ] = [Aᵐ]`.
  obtain ⟨n, m, rfl⟩ : ∃ n m : ℕ, z = n - m := ⟨z.toNat, (-z).toNat, by omega⟩
  rw [zmultiplesHom_apply, sub_smul, sub_eq_zero, natCast_zsmul, natCast_zsmul,
    ← SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := ⟨ModuleCat.of A (Fin n → A),
      finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩) (.refl _ _) (.refl _ _),
    ← SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := ⟨ModuleCat.of A (Fin m → A),
      finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩) (.refl _ _) (.refl _ _),
    SplitK0.of_eq_of_iff_stableEquivalent, stableEquivalent_iff] at hz
  obtain ⟨k, ⟨e⟩⟩ := hz
  have := eq_of_fin_equiv A <| (LinearEquiv.piFinAppend A A n k).trans <|
    e.trans (LinearEquiv.piFinAppend A A m k).symm
  omega

/-- If every finitely generated projective `A`-module is stably free, every class in the split
`K₀` of finitely generated projective `A`-modules is an integer multiple of `[A]`. -/
theorem exists_zsmul_of_finiteProjectiveModulesRegular_eq
    (h : ∀ P : (finiteProjectiveModules A).FullSubcategory, IsStablyFree A P.obj)
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    ∃ z : ℤ, z • SplitK0.of.{u} (finiteProjectiveModulesRegular A) = x := by
  refine SplitK0.surjective_of_forall_of_mem_range
    (f := zmultiplesHom (SplitK0.{u} (finiteProjectiveModules A).FullSubcategory)
      (SplitK0.of.{u} (finiteProjectiveModulesRegular A))) (fun P ↦ ?_) x
  -- `P × N` is finite free for a finite free `N`, so `[P] = [P × N] - [N]` is a multiple of `[A]`.
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod A P.obj
  let eP := ((Module.Free.chooseBasis A (P.obj × N)).reindex (Fintype.equivFin _)).equivFun
  let eN := ((Module.Free.chooseBasis A N).reindex (Fintype.equivFin _)).equivFun
  let PN : (finiteProjectiveModules A).FullSubcategory :=
    ⟨ModuleCat.of A (P.obj × N), finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
  let N' : (finiteProjectiveModules A).FullSubcategory :=
    ⟨ModuleCat.of A N, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
  have hPN : SplitK0.of.{u} PN = SplitK0.of.{u} P + SplitK0.of.{u} N' :=
    SplitK0.of_eq_add_of_linearEquiv_prod (.refl _ _)
  refine ⟨(Fintype.card (Module.Free.ChooseBasisIndex A (P.obj × N)) : ℤ) -
    Fintype.card (Module.Free.ChooseBasisIndex A N), ?_⟩
  rw [zmultiplesHom_apply, sub_smul, natCast_zsmul, natCast_zsmul,
    ← SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := PN) eP (.refl _ _),
    ← SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := N') eN (.refl _ _), hPN,
    add_sub_cancel_right]

variable [InvariantBasisNumber A]
  (h : ∀ P : (finiteProjectiveModules A).FullSubcategory, IsStablyFree A P.obj)

/-- **`K₀` is `ℤ` when projective modules are stably free.** If `A` has invariant basis number and
every finitely generated projective `A`-module is stably free, then the split `K₀` of finitely
generated projective `A`-modules is `ℤ`, with inverse `n ↦ n[A]`. -/
noncomputable def rankEquiv : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+ ℤ :=
  (AddEquiv.ofBijective (zmultiplesHom _ (SplitK0.of.{u} (finiteProjectiveModulesRegular A)))
    ⟨zsmul_of_finiteProjectiveModulesRegular_injective A,
      fun x ↦ exists_zsmul_of_finiteProjectiveModulesRegular_eq A h x⟩).symm

@[simp]
theorem rankEquiv_symm_apply (z : ℤ) :
    (rankEquiv A h).symm z = z • SplitK0.of.{u} (finiteProjectiveModulesRegular A) :=
  (rfl)

theorem rankEquiv_zsmul_of_finiteProjectiveModulesRegular (z : ℤ) :
    rankEquiv A h (z • SplitK0.of.{u} (finiteProjectiveModulesRegular A)) = z :=
  (rankEquiv A h).apply_symm_apply z

@[simp]
theorem rankEquiv_of_finiteProjectiveModulesRegular :
    rankEquiv A h (SplitK0.of.{u} (finiteProjectiveModulesRegular A)) = 1 := by
  simpa using rankEquiv_zsmul_of_finiteProjectiveModulesRegular A h 1

/-- Over a ring with the strong rank condition, `TauCeti.FiniteProjectiveModules.rankEquiv` sends
the class of a free module to its rank. -/
@[simp]
theorem rankEquiv_of [StrongRankCondition A] (P : (finiteProjectiveModules A).FullSubcategory)
    [Module.Free A P.obj] : rankEquiv A h (SplitK0.of.{u} P) = finrank A P.obj := by
  rw [SplitK0.of_eq_nsmul_of_linearEquiv_fin (R' := finiteProjectiveModulesRegular A)
    (Module.finBasis A P.obj).equivFun (.refl _ _), ← natCast_zsmul,
    rankEquiv_zsmul_of_finiteProjectiveModulesRegular]

end FiniteProjectiveModules

/-- Over the zero ring every module is zero, so the split `K₀` of finitely generated projective
modules is trivial. -/
instance FiniteProjectiveModules.subsingleton_splitK0 (A : Type u) [Ring A] [Subsingleton A] :
    Subsingleton (SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) := by
  refine ⟨fun x y ↦ ?_⟩
  suffices ∀ x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory, x = 0 by
    rw [this x, this y]
  intro x
  induction x using SplitK0.induction_on with
  | zero => rfl
  | of P =>
    have : Subsingleton ((finiteProjectiveModules A).ι.obj P) := Module.subsingleton A P.obj
    exact SplitK0.of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
      (finiteProjectiveModules A).ι P (ModuleCat.isZero_of_subsingleton _))
  | neg x hx => rw [hx, neg_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- `K₀` of a division ring `D` is `ℤ`, with the class of the free right module of rank one going
to `1`. -/
theorem kZero_divisionRing (D : Type u) [DivisionRing D] :
    ∃ e : KZero D ≃+ ℤ, e (SplitK0.of (finiteProjectiveModulesRegular Dᵐᵒᵖ)) = 1 :=
  ⟨FiniteProjectiveModules.rankEquiv Dᵐᵒᵖ fun _ ↦ inferInstance,
    FiniteProjectiveModules.rankEquiv_of_finiteProjectiveModulesRegular _ _⟩

/-- `K₀` of a commutative principal ideal domain `R` is `ℤ`, with the class of the free right
module of rank one going to `1`: every finitely generated projective module is free. -/
theorem kZero_of_isPrincipalIdealRing (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] :
    ∃ e : KZero R ≃+ ℤ, e (SplitK0.of (finiteProjectiveModulesRegular Rᵐᵒᵖ)) = 1 := by
  have : IsPrincipalIdealRing Rᵐᵒᵖ :=
    .of_surjective (RingEquiv.toOpposite R) (RingEquiv.toOpposite R).surjective
  exact ⟨FiniteProjectiveModules.rankEquiv Rᵐᵒᵖ fun _ ↦ inferInstance,
    FiniteProjectiveModules.rankEquiv_of_finiteProjectiveModulesRegular _ _⟩

/-- `K₀(ℤ)` is `ℤ`, with the class of the free module of rank one going to `1`. -/
theorem kZero_int :
    ∃ e : KZero ℤ ≃+ ℤ, e (SplitK0.of (finiteProjectiveModulesRegular ℤᵐᵒᵖ)) = 1 :=
  kZero_of_isPrincipalIdealRing ℤ

end TauCeti
