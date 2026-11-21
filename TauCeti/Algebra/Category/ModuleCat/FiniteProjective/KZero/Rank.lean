/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.RingTheory.PrincipalIdealDomain.MulOpposite

import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.RingTheory.LocalRing.Module

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
division rings, where every module is free, to principal ideal domains such as `ℤ`, where every
finitely generated projective module is free, and to commutative local rings; for these
`K₀(R) ≅ ℤ`. Over the zero ring every module is zero and `K₀` is trivial.

## Main definitions

* `TauCeti.FiniteProjectiveModules.rankEquiv A h`: the isomorphism of the split `K₀` of finitely
  generated projective `A`-modules with `ℤ`, when `A` has invariant basis number and every such
  module is stably free.
* `TauCeti.finiteProjectiveModulesFinrankSplitK0EquivDivisionRing`,
  `TauCeti.finiteProjectiveModulesFinrankSplitK0EquivPID`, and
  `TauCeti.finiteProjectiveModulesFinrankSplitK0EquivLocalRing`: specializations of `rankEquiv` to
  division rings, nontrivial principal left-ideal domains, and commutative local rings.
* `TauCeti.KZero.finrankEquivDivisionRing`, `TauCeti.KZero.finrankEquivPID`,
  `TauCeti.KZero.finrankEquivInt`, and `TauCeti.KZero.finrankEquivLocalRing`: explicit rank
  isomorphisms `KZero R ≃+ ℤ` sending `[R] ↦ 1`.

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

/-- Over a division ring `D`, `TauCeti.FiniteProjectiveModules.rankEquiv` induces
`K₀(proj D) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivDivisionRing (D : Type u)
    [DivisionRing D] : SplitK0.{u} (finiteProjectiveModules D).FullSubcategory ≃+ ℤ :=
  FiniteProjectiveModules.rankEquiv D fun _ ↦ inferInstance

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_of (D : Type u)
    [DivisionRing D] (P) : finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D
      (SplitK0.of.{u} P) = (Module.finrank D P.obj : ℤ) :=
  FiniteProjectiveModules.rankEquiv_of D _ P

theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_regular (D : Type u)
    [DivisionRing D] : finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D
      (SplitK0.of.{u} (finiteProjectiveModulesRegular D)) = 1 :=
  FiniteProjectiveModules.rankEquiv_of_finiteProjectiveModulesRegular D _

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_symm_apply (D : Type u)
    [DivisionRing D] (n : ℤ) : (finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D).symm n =
      n • SplitK0.of.{u} (finiteProjectiveModulesRegular D) :=
  FiniteProjectiveModules.rankEquiv_symm_apply D _ n

section PID
variable (R : Type u) [Ring R] [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing R]

omit [Nontrivial R] in
private theorem isStablyFree_of_isPrincipalIdealRing
    (P : (finiteProjectiveModules R).FullSubcategory) : Module.IsStablyFree R P.obj :=
  have : Module.Free R P.obj :=
    Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (LinearMap.id : P.obj →ₗ[R] P.obj) Function.injective_id
  inferInstance

/-- Over a nontrivial principal left-ideal domain, `TauCeti.FiniteProjectiveModules.rankEquiv`
induces `K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivPID :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  FiniteProjectiveModules.rankEquiv R (isStablyFree_of_isPrincipalIdealRing R)

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivPID_of (P) :
    finiteProjectiveModulesFinrankSplitK0EquivPID R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) := by
  have : Module.Free R P.obj :=
    Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (LinearMap.id : P.obj →ₗ[R] P.obj) Function.injective_id
  exact FiniteProjectiveModules.rankEquiv_of R _ P

theorem finiteProjectiveModulesFinrankSplitK0EquivPID_regular :
    finiteProjectiveModulesFinrankSplitK0EquivPID R
      (SplitK0.of.{u} (finiteProjectiveModulesRegular R)) = 1 :=
  FiniteProjectiveModules.rankEquiv_of_finiteProjectiveModulesRegular R _

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivPID_symm_apply (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivPID R).symm n =
      n • SplitK0.of.{u} (finiteProjectiveModulesRegular R) :=
  FiniteProjectiveModules.rankEquiv_symm_apply R _ n

end PID

section LocalRing

private theorem isStablyFree_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R]
    (P : (finiteProjectiveModules R).FullSubcategory) : Module.IsStablyFree R P.obj :=
  have : Module.Free R P.obj := Module.free_of_projective_of_isLocalRing
  inferInstance

/-- Over a commutative local ring `R`, `TauCeti.FiniteProjectiveModules.rankEquiv` induces
`K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  FiniteProjectiveModules.rankEquiv R (isStablyFree_of_isLocalRing R)

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of (R : Type u) [CommRing R]
    [IsLocalRing R] (P) : finiteProjectiveModulesFinrankSplitK0EquivLocalRing R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) := by
  have : Module.Free R P.obj := Module.free_of_projective_of_isLocalRing
  exact FiniteProjectiveModules.rankEquiv_of R _ P

theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_regular (R : Type u)
    [CommRing R] [IsLocalRing R] : finiteProjectiveModulesFinrankSplitK0EquivLocalRing R
      (SplitK0.of.{u} (finiteProjectiveModulesRegular R)) = 1 :=
  FiniteProjectiveModules.rankEquiv_of_finiteProjectiveModulesRegular R _

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_symm_apply (R : Type u)
    [CommRing R] [IsLocalRing R] (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivLocalRing R).symm n =
      n • SplitK0.of.{u} (finiteProjectiveModulesRegular R) :=
  FiniteProjectiveModules.rankEquiv_symm_apply R _ n

end LocalRing

namespace KZero

/-- **Rank isomorphism `KZero D ≃+ ℤ` over a division ring `D`**, sending `[D] ↦ 1`. -/
noncomputable def finrankEquivDivisionRing (D : Type u) [DivisionRing D] : KZero D ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivDivisionRing Dᵐᵒᵖ

@[simp] theorem finrankEquivDivisionRing_of (D : Type u) [DivisionRing D] (P) :
    finrankEquivDivisionRing D (SplitK0.of.{u} P) = (Module.finrank Dᵐᵒᵖ P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_of Dᵐᵒᵖ P

@[simp] theorem finrankEquivDivisionRing_one (D : Type u) [DivisionRing D] :
    finrankEquivDivisionRing D (one D) = 1 :=
  one_def D ▸ finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_regular Dᵐᵒᵖ

@[simp] theorem finrankEquivDivisionRing_symm_apply (D : Type u) [DivisionRing D] (n : ℤ) :
    (finrankEquivDivisionRing D).symm n = n • one D :=
  one_def D ▸ finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_symm_apply Dᵐᵒᵖ n

section PID
variable (R : Type u) [Ring R] [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing Rᵐᵒᵖ]

/-- **Rank isomorphism `KZero R ≃+ ℤ` over a principal right-ideal domain `R`** (including any
commutative PID), sending `[R] ↦ 1`. -/
noncomputable def finrankEquivPID : KZero R ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivPID Rᵐᵒᵖ

@[simp] theorem finrankEquivPID_of (P) :
    finrankEquivPID R (SplitK0.of.{u} P) = (Module.finrank Rᵐᵒᵖ P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivPID_of Rᵐᵒᵖ P

@[simp] theorem finrankEquivPID_one : finrankEquivPID R (one R) = 1 :=
  one_def R ▸ finiteProjectiveModulesFinrankSplitK0EquivPID_regular Rᵐᵒᵖ

@[simp] theorem finrankEquivPID_symm_apply (n : ℤ) : (finrankEquivPID R).symm n = n • one R :=
  one_def R ▸ finiteProjectiveModulesFinrankSplitK0EquivPID_symm_apply Rᵐᵒᵖ n

end PID

/-- **Rank isomorphism `KZero ℤ ≃+ ℤ`**, sending `[ℤ]` to `1`. -/
noncomputable def finrankEquivInt : KZero ℤ ≃+ ℤ := finrankEquivPID ℤ

@[simp] theorem finrankEquivInt_of (P) :
    finrankEquivInt (SplitK0.of.{0} P) = (Module.finrank ℤᵐᵒᵖ P.obj : ℤ) := finrankEquivPID_of ℤ P

@[simp] theorem finrankEquivInt_one : finrankEquivInt (one ℤ) = 1 := finrankEquivPID_one ℤ

@[simp] theorem finrankEquivInt_symm_apply (n : ℤ) : finrankEquivInt.symm n = n • one ℤ :=
  finrankEquivPID_symm_apply ℤ n

/-- **Rank isomorphism `KZero R ≃+ ℤ` over a commutative local ring**, sending `[R] ↦ 1`. -/
noncomputable def finrankEquivLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    KZero R ≃+ ℤ := finiteProjectiveModulesFinrankSplitK0EquivLocalRing Rᵐᵒᵖ

@[simp] theorem finrankEquivLocalRing_of (R : Type u) [CommRing R] [IsLocalRing R] (P) :
    finrankEquivLocalRing R (SplitK0.of.{u} P) = (Module.finrank Rᵐᵒᵖ P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of Rᵐᵒᵖ P

@[simp] theorem finrankEquivLocalRing_one (R : Type u) [CommRing R] [IsLocalRing R] :
    finrankEquivLocalRing R (one R) = 1 :=
  one_def R ▸ finiteProjectiveModulesFinrankSplitK0EquivLocalRing_regular Rᵐᵒᵖ

@[simp] theorem finrankEquivLocalRing_symm_apply (R : Type u) [CommRing R] [IsLocalRing R] (n : ℤ) :
    (finrankEquivLocalRing R).symm n = n • one R :=
  one_def R ▸ finiteProjectiveModulesFinrankSplitK0EquivLocalRing_symm_apply Rᵐᵒᵖ n

end KZero

end TauCeti
