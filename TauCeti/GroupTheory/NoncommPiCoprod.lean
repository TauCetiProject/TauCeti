/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.NoncommPiCoprod
import TauCeti.GroupTheory.Finiteness

/-!
# Homomorphisms out of `ℤ^ι`

A homomorphism out of the free abelian group `ι → Multiplicative ℤ` (or additively `ι → ℤ`) on a
finite type `ι` is determined by the images of the standard generators `Pi.mulSingle i (.ofAdd 1)`
(respectively `Pi.single i 1`), and any family of pairwise commuting elements `τ i` of a group `K`
(respectively an additive group `A`) is the image of the standard generators under
`TauCeti.zpowersPiHom τ` (respectively `TauCeti.zmultiplesPiHom τ`), built from Mathlib's
`MonoidHom.noncommPiCoprod` / `AddMonoidHom.noncommPiCoprod` and `zpowersHom` / `zmultiplesHom`.

## Main declarations

* `MonoidHom.pi_ext_mint`, `AddMonoidHom.pi_ext_int`: homomorphisms out of `ι → Multiplicative ℤ`
  or `ι → ℤ` agreeing on the standard generators are equal.
* `TauCeti.zpowersPiHom`, `TauCeti.zmultiplesPiHom`: the homomorphism out of `ι → Multiplicative ℤ`
  or `ι → ℤ` sending the `i`-th standard generator to `τ i`.
* `TauCeti.zpowersPiHomEquiv`, `TauCeti.zmultiplesPiHomEquiv`: universal-property equivalences
  identifying homomorphisms out of `ℤ^ι` with families of pairwise commuting elements.
* `TauCeti.surjective_zpowersPiHom_iff`, `TauCeti.surjective_zmultiplesPiHom_iff`: `zpowersPiHom` /
  `zmultiplesPiHom` is surjective if and only if the `τ i` generate the target group.
* `TauCeti.toMultiplicative_zmultiplesPiHom`, `TauCeti.ofAdd_zmultiplesPiHom_apply`,
  `TauCeti.ofMul_zpowersPiHom_apply`: compatibility between `zmultiplesPiHom` and `zpowersPiHom`
  across `Multiplicative` and `Additive`.
* `Group.fg_iff_exists_fin_multiplicative_int_hom_surjective`,
  `AddGroup.fg_iff_exists_fin_int_hom_surjective`: a commutative group is finitely generated if and
  only if it is a homomorphic image of `Fin n → Multiplicative ℤ` (respectively `Fin n → ℤ`).
-/

public section

variable {ι : Type*}

namespace AddMonoidHom

/-- Homomorphisms out of `ι → ℤ` agree when they agree on the standard generators. -/
theorem pi_ext_int [Finite ι] [DecidableEq ι] {M : Type*} [AddMonoid M]
    {f g : (ι → ℤ) →+ M}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g :=
  pi_ext fun i x => by
    simpa using DFunLike.congr_fun
      (ext_int (f := f.comp (single (fun _ => ℤ) i))
        (g := g.comp (single (fun _ => ℤ) i)) (h i)) x

end AddMonoidHom

namespace MonoidHom

/-- Homomorphisms out of `ι → Multiplicative ℤ` agree when they agree on the standard
generators. -/
theorem pi_ext_mint [Finite ι] [DecidableEq ι] {M : Type*} [Monoid M]
    {f g : (ι → Multiplicative ℤ) →* M}
    (h : ∀ i, f (Pi.mulSingle i (.ofAdd 1)) = g (Pi.mulSingle i (.ofAdd 1))) : f = g :=
  pi_ext fun i x => by
    simpa using DFunLike.congr_fun
      (ext_mint (f := f.comp (mulSingle (fun _ => Multiplicative ℤ) i))
        (g := g.comp (mulSingle (fun _ => Multiplicative ℤ) i)) (h i)) x

end MonoidHom

namespace TauCeti

section Multiplicative

variable [Fintype ι] {K : Type*} [Group K]

/-- The homomorphism `(ι → Multiplicative ℤ) →* K` sending the `i`-th standard generator to `τ i`,
for pairwise commuting `τ i`. -/
def zpowersPiHom (τ : ι → K) (hτ : ∀ i j, Commute (τ i) (τ j)) :
    (ι → Multiplicative ℤ) →* K :=
  MonoidHom.noncommPiCoprod (fun i => zpowersHom K (τ i)) <| by
    intro i j _ x y
    simpa only [zpowersHom_apply] using (hτ i j).zpow_zpow x.toAdd y.toAdd

@[simp] theorem zpowersPiHom_mulSingle [DecidableEq ι] (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) (i : ι) :
    zpowersPiHom τ hτ (Pi.mulSingle i (.ofAdd 1)) = τ i :=
  -- `simp` does not unify the `ι`-indexed family of `noncommPiCoprod_mulSingle` with the constant
  -- family `ι → Multiplicative ℤ`, so apply it directly.
  (MonoidHom.noncommPiCoprod_mulSingle _ i _).trans (by simp)

/-- Uniqueness in the universal property of `zpowersPiHom`: a homomorphism out of
`ι → Multiplicative ℤ` equals `zpowersPiHom τ hτ` if and only if it sends the `i`-th standard
generator to `τ i` for every `i`. -/
theorem eq_zpowersPiHom_iff [DecidableEq ι] {τ : ι → K} {hτ : ∀ i j, Commute (τ i) (τ j)}
    {f : (ι → Multiplicative ℤ) →* K} :
    f = zpowersPiHom τ hτ ↔ ∀ i, f (Pi.mulSingle i (.ofAdd 1)) = τ i :=
  ⟨fun hf i => hf ▸ zpowersPiHom_mulSingle τ hτ i,
    fun hf => MonoidHom.pi_ext_mint fun i => (hf i).trans (zpowersPiHom_mulSingle τ hτ i).symm⟩

/-- Universal property of `zpowersPiHom`: homomorphisms `(ι → Multiplicative ℤ) →* K` correspond
bijectively to `ι`-tuples of pairwise commuting elements of `K`. -/
def zpowersPiHomEquiv (ι K : Type*) [Fintype ι] [DecidableEq ι] [Group K] :
    {τ : ι → K // ∀ i j, Commute (τ i) (τ j)} ≃ ((ι → Multiplicative ℤ) →* K) where
  toFun τ := zpowersPiHom τ.1 τ.2
  invFun f := ⟨fun i => f (Pi.mulSingle i (.ofAdd 1)), fun i j => by
    rcases eq_or_ne i j with rfl | hij
    · exact Commute.refl _
    · exact (Pi.mulSingle_commute hij (.ofAdd 1) (.ofAdd 1)).map f⟩
  left_inv τ := Subtype.ext <| funext <| zpowersPiHom_mulSingle τ.1 τ.2
  right_inv f := (eq_zpowersPiHom_iff.2 fun _ => rfl).symm

@[simp] theorem zpowersPiHomEquiv_apply [DecidableEq ι]
    (τ : {τ : ι → K // ∀ i j, Commute (τ i) (τ j)}) :
    zpowersPiHomEquiv ι K τ = zpowersPiHom τ.1 τ.2 := (rfl)

@[simp] theorem zpowersPiHomEquiv_symm_apply_coe [DecidableEq ι]
    (f : (ι → Multiplicative ℤ) →* K) (i : ι) :
    (zpowersPiHomEquiv ι K |>.symm f : ι → K) i = f (Pi.mulSingle i (.ofAdd 1)) := (rfl)

/-- The image of `zpowersPiHom τ` is the subgroup generated by the `τ i`. -/
theorem range_zpowersPiHom (τ : ι → K) (hτ : ∀ i j, Commute (τ i) (τ j)) :
    (zpowersPiHom τ hτ).range = Subgroup.closure (Set.range τ) := by
  refine (MonoidHom.noncommPiCoprod_range _).trans ?_
  simp [Subgroup.range_zpowersHom, Subgroup.zpowers_eq_closure, ← Subgroup.closure_iUnion]

/-- `zpowersPiHom τ hτ` is surjective if and only if the `τ i` generate `K`. -/
@[simp] theorem surjective_zpowersPiHom_iff (τ : ι → K) (hτ : ∀ i j, Commute (τ i) (τ j)) :
    Function.Surjective (zpowersPiHom τ hτ) ↔ Subgroup.closure (Set.range τ) = ⊤ := by
  rw [← MonoidHom.range_eq_top, range_zpowersPiHom]

/-- An element commuting with every `τ i` commutes with the whole image of `zpowersPiHom τ`. -/
theorem commute_zpowersPiHom {τ : ι → K} {hτ : ∀ i j, Commute (τ i) (τ j)} {x : K}
    (hx : ∀ i, Commute x (τ i)) (v : ι → Multiplicative ℤ) :
    Commute x (zpowersPiHom τ hτ v) :=
  MonoidHom.commute_noncommPiCoprod _ (fun i k => by
    simpa only [zpowersHom_apply] using (hx i).zpow_right k.toAdd) v

/-- In a commutative group, `zpowersPiHom τ` evaluates at `v` as the product `∏ i, τ i ^ (v i)`. -/
theorem zpowersPiHom_apply_eq_prod {G : Type*} [CommGroup G] (τ : ι → G)
    (hτ : ∀ i j, Commute (τ i) (τ j)) (v : ι → Multiplicative ℤ) :
    zpowersPiHom τ hτ v = ∏ i, τ i ^ (v i).toAdd :=
  (MonoidHom.noncommPiCoprod_apply _ v).trans (by simp [Finset.noncommProd_eq_prod])

end Multiplicative

section Additive

variable [Fintype ι] {A : Type*} [AddGroup A]

/-- The homomorphism `(ι → ℤ) →+ A` sending the `i`-th standard generator `Pi.single i 1` to `τ i`,
for pairwise commuting `τ i`. -/
def zmultiplesPiHom (τ : ι → A) (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    (ι → ℤ) →+ A :=
  AddMonoidHom.noncommPiCoprod (fun i => zmultiplesHom A (τ i)) <| by
    intro i j _ x y
    simpa only [zmultiplesHom_apply] using (hτ i j).zsmul_zsmul x y

@[simp] theorem zmultiplesPiHom_single [DecidableEq ι] (τ : ι → A)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) (i : ι) :
    zmultiplesPiHom τ hτ (Pi.single i 1) = τ i :=
  (AddMonoidHom.noncommPiCoprod_single _ i _).trans (by simp)

/-- Uniqueness in the universal property of `zmultiplesPiHom`: an additive homomorphism out of
`ι → ℤ` equals `zmultiplesPiHom τ hτ` if and only if it sends `Pi.single i 1` to `τ i` for every
`i`. -/
theorem eq_zmultiplesPiHom_iff [DecidableEq ι] {τ : ι → A} {hτ : ∀ i j, AddCommute (τ i) (τ j)}
    {f : (ι → ℤ) →+ A} :
    f = zmultiplesPiHom τ hτ ↔ ∀ i, f (Pi.single i 1) = τ i :=
  ⟨fun hf i => hf ▸ zmultiplesPiHom_single τ hτ i,
    fun hf => AddMonoidHom.pi_ext_int fun i => (hf i).trans (zmultiplesPiHom_single τ hτ i).symm⟩

/-- Universal property of `zmultiplesPiHom`: additive homomorphisms `(ι → ℤ) →+ A` correspond
bijectively to `ι`-tuples of pairwise commuting elements of `A`. -/
def zmultiplesPiHomEquiv (ι A : Type*) [Fintype ι] [DecidableEq ι] [AddGroup A] :
    {τ : ι → A // ∀ i j, AddCommute (τ i) (τ j)} ≃ ((ι → ℤ) →+ A) where
  toFun τ := zmultiplesPiHom τ.1 τ.2
  invFun f := ⟨fun i => f (Pi.single i 1), fun i j => by
    rcases eq_or_ne i j with rfl | hij
    · exact AddCommute.refl _
    · exact (Pi.single_addCommute hij 1 1).map f⟩
  left_inv τ := Subtype.ext <| funext <| zmultiplesPiHom_single τ.1 τ.2
  right_inv f := (eq_zmultiplesPiHom_iff.2 fun _ => rfl).symm

@[simp] theorem zmultiplesPiHomEquiv_apply [DecidableEq ι]
    (τ : {τ : ι → A // ∀ i j, AddCommute (τ i) (τ j)}) :
    zmultiplesPiHomEquiv ι A τ = zmultiplesPiHom τ.1 τ.2 := (rfl)

@[simp] theorem zmultiplesPiHomEquiv_symm_apply_coe [DecidableEq ι]
    (f : (ι → ℤ) →+ A) (i : ι) :
    (zmultiplesPiHomEquiv ι A |>.symm f : ι → A) i = f (Pi.single i 1) := (rfl)

/-- The image of `zmultiplesPiHom τ` is the additive subgroup generated by the `τ i`. -/
theorem range_zmultiplesPiHom (τ : ι → A) (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    (zmultiplesPiHom τ hτ).range = AddSubgroup.closure (Set.range τ) := by
  refine (AddMonoidHom.noncommPiCoprod_range _).trans ?_
  simp [AddSubgroup.range_zmultiplesHom, AddSubgroup.zmultiples_eq_closure,
    ← AddSubgroup.closure_iUnion]

/-- `zmultiplesPiHom τ hτ` is surjective if and only if the `τ i` generate `A`. -/
@[simp] theorem surjective_zmultiplesPiHom_iff (τ : ι → A) (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    Function.Surjective (zmultiplesPiHom τ hτ) ↔ AddSubgroup.closure (Set.range τ) = ⊤ := by
  rw [← AddMonoidHom.range_eq_top, range_zmultiplesPiHom]

/-- An element commuting additively with every `τ i` commutes with the whole image of
`zmultiplesPiHom τ`. -/
theorem addCommute_zmultiplesPiHom {τ : ι → A} {hτ : ∀ i j, AddCommute (τ i) (τ j)} {x : A}
    (hx : ∀ i, AddCommute x (τ i)) (v : ι → ℤ) :
    AddCommute x (zmultiplesPiHom τ hτ v) :=
  AddMonoidHom.addCommute_noncommPiCoprod _ (fun i k => by
    simpa only [zmultiplesHom_apply] using (hx i).zsmul_right k) v

/-- In an additive commutative group, `zmultiplesPiHom τ` evaluates at `v` as `∑ i, v i • τ i`. -/
theorem zmultiplesPiHom_apply_eq_sum {B : Type*} [AddCommGroup B] (τ : ι → B)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) (v : ι → ℤ) :
    zmultiplesPiHom τ hτ v = ∑ i, v i • τ i :=
  (AddMonoidHom.noncommPiCoprod_apply _ v).trans (by simp [Finset.noncommSum_eq_sum])

end Additive

section Transport

variable [Fintype ι]

/-- Transporting `zmultiplesPiHom τ hτ` through `AddMonoidHom.toMultiplicative` and
`MulEquiv.piMultiplicative` yields `zpowersPiHom` on `Multiplicative A`. -/
theorem toMultiplicative_zmultiplesPiHom {A : Type*} [AddGroup A] (τ : ι → A)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    (AddMonoidHom.toMultiplicative (zmultiplesPiHom τ hτ)).comp
        (MulEquiv.piMultiplicative fun _ : ι => ℤ).symm.toMonoidHom =
      zpowersPiHom (fun i => Multiplicative.ofAdd (τ i))
        (fun i j => show Multiplicative.ofAdd (τ i + τ j) = Multiplicative.ofAdd (τ j + τ i) from
          congrArg Multiplicative.ofAdd (hτ i j).eq) := by
  classical
  refine eq_zpowersPiHom_iff.2 fun i => ?_
  have hsingle : (MulEquiv.piMultiplicative fun _ : ι => ℤ).symm (Pi.mulSingle i (.ofAdd 1)) =
      Multiplicative.ofAdd (Pi.single i (1 : ℤ)) := by
    ext j
    by_cases hij : j = i <;> simp [MulEquiv.piMultiplicative, hij]
  simp [hsingle]

/-- Pointwise compatibility between `zmultiplesPiHom` and `zpowersPiHom` via
`Multiplicative.ofAdd`. -/
@[simp] theorem ofAdd_zmultiplesPiHom_apply {A : Type*} [AddGroup A] (τ : ι → A)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) (v : ι → ℤ) :
    Multiplicative.ofAdd (zmultiplesPiHom τ hτ v) =
      zpowersPiHom (fun i => Multiplicative.ofAdd (τ i))
        (fun i j => show Multiplicative.ofAdd (τ i + τ j) = Multiplicative.ofAdd (τ j + τ i) from
          congrArg Multiplicative.ofAdd (hτ i j).eq)
        (fun i => Multiplicative.ofAdd (v i)) :=
  DFunLike.congr_fun (toMultiplicative_zmultiplesPiHom τ hτ) (fun i => Multiplicative.ofAdd (v i))

/-- Transporting `zpowersPiHom τ hτ` through `MulEquiv.piMultiplicative` and
`MonoidHom.toAdditiveRight` yields `zmultiplesPiHom` on `Additive K`. -/
theorem toAdditiveRight_zpowersPiHom {K : Type*} [Group K] (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) :
    MonoidHom.toAdditiveRight
        ((zpowersPiHom τ hτ).comp (MulEquiv.piMultiplicative fun _ : ι => ℤ).toMonoidHom) =
      zmultiplesPiHom (fun i => Additive.ofMul (τ i))
        (fun i j => show Additive.ofMul (τ i * τ j) = Additive.ofMul (τ j * τ i) from
          congrArg Additive.ofMul (hτ i j).eq) := by
  classical
  refine eq_zmultiplesPiHom_iff.2 fun i => ?_
  have hsingle : (MulEquiv.piMultiplicative fun _ : ι => ℤ) (Multiplicative.ofAdd (Pi.single i 1)) =
      Pi.mulSingle i (.ofAdd 1) := by
    ext j
    by_cases hij : j = i <;> simp [MulEquiv.piMultiplicative, hij]
  simp [hsingle]

/-- Pointwise compatibility between `zpowersPiHom` and `zmultiplesPiHom` via `Additive.ofMul`. -/
@[simp] theorem ofMul_zpowersPiHom_apply {K : Type*} [Group K] (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) (v : ι → Multiplicative ℤ) :
    Additive.ofMul (zpowersPiHom τ hτ v) =
      zmultiplesPiHom (fun i => Additive.ofMul (τ i))
        (fun i j => show Additive.ofMul (τ i * τ j) = Additive.ofMul (τ j * τ i) from
          congrArg Additive.ofMul (hτ i j).eq)
        (fun i => (v i).toAdd) :=
  DFunLike.congr_fun (toAdditiveRight_zpowersPiHom τ hτ) (fun i => (v i).toAdd)

end Transport

end TauCeti

/-- A commutative group is finitely generated if and only if it admits a surjective homomorphism
from `Fin n → Multiplicative ℤ` for some `n : ℕ`. -/
theorem Group.fg_iff_exists_fin_multiplicative_int_hom_surjective {G : Type*} [CommGroup G] :
    Group.FG G ↔ ∃ (n : ℕ) (φ : (Fin n → Multiplicative ℤ) →* G), Function.Surjective φ := by
  refine ⟨fun h => ?_, fun ⟨n, φ, hφ⟩ => Group.fg_of_surjective hφ⟩
  obtain ⟨n, S, hS⟩ := Group.fg_iff_exists_fin_generating_family.1 h
  exact ⟨n, TauCeti.zpowersPiHom S fun _ _ => .all _ _,
    (TauCeti.surjective_zpowersPiHom_iff _ _).2 hS⟩

/-- An additive commutative group is finitely generated if and only if it admits a surjective
homomorphism from `Fin n → ℤ` for some `n : ℕ`. -/
theorem AddGroup.fg_iff_exists_fin_int_hom_surjective {A : Type*} [AddCommGroup A] :
    AddGroup.FG A ↔ ∃ (n : ℕ) (φ : (Fin n → ℤ) →+ A), Function.Surjective φ := by
  refine ⟨fun h => ?_, fun ⟨n, φ, hφ⟩ => AddGroup.fg_of_surjective hφ⟩
  obtain ⟨n, S, hS⟩ := AddGroup.fg_iff_exists_fin_generating_family.1 h
  exact ⟨n, TauCeti.zmultiplesPiHom S fun _ _ => .all _ _,
    (TauCeti.surjective_zmultiplesPiHom_iff _ _).2 hS⟩

end
