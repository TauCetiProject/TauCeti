/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Homomorphisms out of `ℤ^ι`

A homomorphism out of the free abelian group `ι → Multiplicative ℤ` (or additively `ι → ℤ`) on a
finite type `ι` is determined by the images of the standard generators `Pi.mulSingle i (ofAdd 1)`
(`MonoidHom.pi_ext_mint` and `AddMonoidHom.pi_ext_int`). Conversely, any family of pairwise
commuting elements `τ i` of a group `K` (or additive group `A`) is the image of the standard
generators under `TauCeti.zpowersPiHom τ` (`TauCeti.zmultiplesPiHom τ`), built from Mathlib's
`MonoidHom.noncommPiCoprod` / `AddMonoidHom.noncommPiCoprod` and `zpowersHom` / `zmultiplesHom`.

This yields the universal-property equivalences `TauCeti.zpowersPiHomEquiv` and
`TauCeti.zmultiplesPiHomEquiv` between pairwise commuting `ι`-tuples and homomorphisms out of
`ℤ^ι`, upgraded for commutative targets to the group isomorphisms `TauCeti.zpowersPiMulHom` and
`TauCeti.zmultiplesPiAddHom` (the `ι`-indexed counterparts of Mathlib's `zpowersMulHom` and
`zmultiplesAddHom`), together with the surjectivity criteria in terms of subgroup generation and
explicit compatibility under `AddMonoidHom.toMultiplicative` and `MonoidHom.toAdditive`.

## Main declarations

* `MonoidHom.pi_ext_mint` and `AddMonoidHom.pi_ext_int`: homomorphisms out of
  `ι → Multiplicative ℤ` and `ι → ℤ` agreeing on the standard generators are equal.
* `TauCeti.zpowersPiHom` and `TauCeti.zmultiplesPiHom`: the homomorphisms
  `(ι → Multiplicative ℤ) →* K` and `(ι → ℤ) →+ A` sending the `i`-th standard generator to `τ i`.
* `TauCeti.zpowersPiHom_apply` and `TauCeti.zmultiplesPiHom_apply`: evaluation as a
  noncommutative product or sum, which is an ordinary finite product or sum for commutative
  targets (`TauCeti.zpowersPiHom_apply_eq_prod` and `TauCeti.zmultiplesPiHom_apply_eq_sum`).
* `MonoidHom.comp_zpowersPiHom` and `AddMonoidHom.comp_zmultiplesPiHom`: naturality in the target.
* `TauCeti.zpowersPiHom_surjective` and `TauCeti.zmultiplesPiHom_surjective`: surjectivity is
  equivalent to `τ` generating the target group.
* `TauCeti.zpowersPiHomEquiv` and `TauCeti.zmultiplesPiHomEquiv`: universal-property equivalences
  identifying homomorphisms out of `ℤ^ι` with pairwise commuting `ι`-tuples.
* `TauCeti.zpowersPiMulHom` and `TauCeti.zmultiplesPiAddHom`: the group isomorphisms
  `(ι → G) ≃* ((ι → Multiplicative ℤ) →* G)` and `(ι → B) ≃+ ((ι → ℤ) →+ B)` for commutative
  groups.
* `TauCeti.toMultiplicative_zmultiplesPiHom` and `TauCeti.toAdditive_zpowersPiHom`: compatibility
  with `MulEquiv.funMultiplicative` and `AddEquiv.funAdditive`, with pointwise forms
  `TauCeti.ofAdd_zmultiplesPiHom` and `TauCeti.ofMul_zpowersPiHom`.
-/

public section

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

variable {ι : Type*}

namespace MonoidHom

/-- Homomorphisms out of `ι → Multiplicative ℤ` agree when they agree on the standard
generators. -/
theorem pi_ext_mint [Finite ι] [DecidableEq ι] {M : Type*} [Monoid M]
    {f g : (ι → Multiplicative ℤ) →* M}
    (h : ∀ i, f (Pi.mulSingle i (ofAdd 1)) = g (Pi.mulSingle i (ofAdd 1))) : f = g :=
  pi_ext fun i x => by
    simpa using DFunLike.congr_fun
      (ext_mint (f := f.comp (mulSingle (fun _ => Multiplicative ℤ) i))
        (g := g.comp (mulSingle (fun _ => Multiplicative ℤ) i)) (h i)) x

end MonoidHom

namespace AddMonoidHom

/-- Additive homomorphisms out of `ι → ℤ` agree when they agree on the standard generators
`Pi.single i 1`. -/
theorem pi_ext_int [Finite ι] [DecidableEq ι] {M : Type*} [AddMonoid M]
    {f g : (ι → ℤ) →+ M}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g :=
  pi_ext fun i x => by
    simpa using DFunLike.congr_fun
      (ext_int (f := f.comp (single (fun _ => ℤ) i))
        (g := g.comp (single (fun _ => ℤ) i)) (h i)) x

end AddMonoidHom

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

/-- Pointwise evaluation of `zpowersPiHom` as a noncommutative product. -/
theorem zpowersPiHom_apply (τ : ι → K) (hτ : ∀ i j, Commute (τ i) (τ j))
    (v : ι → Multiplicative ℤ) :
    zpowersPiHom τ hτ v = Finset.univ.noncommProd (fun i => τ i ^ (v i).toAdd)
      (fun i _ j _ _ => (hτ i j).zpow_zpow _ _) :=
  (MonoidHom.noncommPiCoprod_apply (N := fun _ => Multiplicative ℤ) _ v).trans <|
    Finset.noncommProd_congr rfl (fun i _ => zpowersHom_apply K (τ i) (v i)) _

/-- In a commutative group, `zpowersPiHom` evaluates as a finite product. -/
theorem zpowersPiHom_apply_eq_prod {G : Type*} [CommGroup G] (τ : ι → G)
    (hτ : ∀ i j, Commute (τ i) (τ j)) (v : ι → Multiplicative ℤ) :
    zpowersPiHom τ hτ v = ∏ i, τ i ^ (v i).toAdd := by
  rw [zpowersPiHom_apply, Finset.noncommProd_eq_prod]

@[simp] theorem zpowersPiHom_mulSingle [DecidableEq ι] (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) (i : ι) :
    zpowersPiHom τ hτ (Pi.mulSingle i (ofAdd 1)) = τ i :=
  -- `simp` does not unify the `ι`-indexed family of `noncommPiCoprod_mulSingle` with the constant
  -- family `ι → Multiplicative ℤ`, so apply it directly.
  (MonoidHom.noncommPiCoprod_mulSingle _ i _).trans (by simp)

/-- Postcomposing `zpowersPiHom` with a group homomorphism `f` yields `zpowersPiHom` for
`f ∘ τ`. -/
theorem _root_.MonoidHom.comp_zpowersPiHom {L : Type*} [Group L] (f : K →* L) (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) :
    f.comp (zpowersPiHom τ hτ) =
      zpowersPiHom (f ∘ τ) (fun i j => (hτ i j).map f) := by
  classical
  exact MonoidHom.pi_ext_mint fun i => by simp

/-- The image of `zpowersPiHom τ` is the subgroup generated by the `τ i`. -/
theorem range_zpowersPiHom (τ : ι → K) (hτ : ∀ i j, Commute (τ i) (τ j)) :
    (zpowersPiHom τ hτ).range = Subgroup.closure (Set.range τ) := by
  refine (MonoidHom.noncommPiCoprod_range _).trans ?_
  simp [Subgroup.range_zpowersHom, Subgroup.zpowers_eq_closure, ← Subgroup.closure_iUnion]

/-- `zpowersPiHom τ` is surjective if and only if the elements `τ i` generate `K`. -/
theorem zpowersPiHom_surjective (τ : ι → K) (hτ : ∀ i j, Commute (τ i) (τ j)) :
    Function.Surjective (zpowersPiHom τ hτ) ↔ Subgroup.closure (Set.range τ) = ⊤ := by
  rw [← MonoidHom.range_eq_top, range_zpowersPiHom]

/-- An element commuting with every `τ i` commutes with the whole image of `zpowersPiHom τ`. -/
theorem commute_zpowersPiHom {τ : ι → K} {hτ : ∀ i j, Commute (τ i) (τ j)} {x : K}
    (hx : ∀ i, Commute x (τ i)) (v : ι → Multiplicative ℤ) :
    Commute x (zpowersPiHom τ hτ v) :=
  MonoidHom.commute_noncommPiCoprod _ (fun i k => by
    simpa only [zpowersHom_apply] using (hx i).zpow_right k.toAdd) v

/-- **Universal property of `ι → Multiplicative ℤ`.** Homomorphisms `(ι → Multiplicative ℤ) →* K`
correspond bijectively to `ι`-tuples of pairwise commuting elements of `K`, via evaluation at the
standard generators `Pi.mulSingle i (ofAdd 1)`. -/
def zpowersPiHomEquiv [DecidableEq ι] :
    {τ : ι → K // ∀ i j, Commute (τ i) (τ j)} ≃ ((ι → Multiplicative ℤ) →* K) where
  toFun τ := zpowersPiHom τ.val τ.property
  invFun f := ⟨fun i => f (Pi.mulSingle i (ofAdd 1)), fun i j => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, (Commute.all _ _).eq]⟩
  left_inv τ := Subtype.ext <| funext fun i => zpowersPiHom_mulSingle τ.val τ.property i
  right_inv f := MonoidHom.pi_ext_mint fun i => zpowersPiHom_mulSingle _ _ i

/-- Forward evaluation of `zpowersPiHomEquiv`. -/
@[simp]
theorem zpowersPiHomEquiv_apply [DecidableEq ι]
    (τ : {τ : ι → K // ∀ i j, Commute (τ i) (τ j)}) :
    zpowersPiHomEquiv τ = zpowersPiHom τ.val τ.property :=
  (rfl)

/-- Inverse evaluation of `zpowersPiHomEquiv` evaluates at the `i`-th standard generator. -/
@[simp]
theorem zpowersPiHomEquiv_symm_apply_coe [DecidableEq ι]
    (f : (ι → Multiplicative ℤ) →* K) (i : ι) :
    (zpowersPiHomEquiv.symm f : ι → K) i = f (Pi.mulSingle i (ofAdd 1)) :=
  (rfl)

/-- For a commutative group `G`, `zpowersPiHom` identifies `ι → G` with
`(ι → Multiplicative ℤ) →* G` as a group isomorphism. This is the `ι`-indexed counterpart of
`zpowersMulHom`. -/
def zpowersPiMulHom [DecidableEq ι] (G : Type*) [CommGroup G] :
    (ι → G) ≃* ((ι → Multiplicative ℤ) →* G) where
  toFun τ := zpowersPiHom τ fun _ _ => Commute.all _ _
  invFun f i := f (Pi.mulSingle i (ofAdd 1))
  left_inv τ := funext fun i => zpowersPiHom_mulSingle τ _ i
  right_inv f := MonoidHom.pi_ext_mint fun i => zpowersPiHom_mulSingle _ _ i
  map_mul' σ τ := MonoidHom.pi_ext_mint fun i => by simp

/-- Forward evaluation of `zpowersPiMulHom` is `zpowersPiHom`. -/
theorem zpowersPiMulHom_apply [DecidableEq ι] {G : Type*} [CommGroup G] (τ : ι → G) :
    zpowersPiMulHom G τ = zpowersPiHom τ fun _ _ => Commute.all _ _ :=
  (rfl)

/-- `zpowersPiMulHom` sends the `i`-th standard generator to `τ i`. -/
@[simp]
theorem zpowersPiMulHom_apply_mulSingle [DecidableEq ι] {G : Type*} [CommGroup G] (τ : ι → G)
    (i : ι) :
    zpowersPiMulHom G τ (Pi.mulSingle i (ofAdd 1)) = τ i :=
  zpowersPiHom_mulSingle τ (fun _ _ => Commute.all _ _) i

/-- Inverse evaluation of `zpowersPiMulHom` evaluates at the `i`-th standard generator. -/
@[simp]
theorem zpowersPiMulHom_symm_apply [DecidableEq ι] {G : Type*} [CommGroup G]
    (f : (ι → Multiplicative ℤ) →* G) (i : ι) :
    (zpowersPiMulHom G).symm f i = f (Pi.mulSingle i (ofAdd 1)) :=
  (rfl)

end Multiplicative

section Additive

variable [Fintype ι] {A : Type*} [AddGroup A]

/-- The additive homomorphism `(ι → ℤ) →+ A` sending the `i`-th standard generator `Pi.single i 1`
to `τ i`, for pairwise additively commuting `τ i`. -/
def zmultiplesPiHom (τ : ι → A) (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    (ι → ℤ) →+ A :=
  AddMonoidHom.noncommPiCoprod (fun i => zmultiplesHom A (τ i)) <| by
    intro i j _ x y
    simpa only [zmultiplesHom_apply] using (hτ i j).zsmul_zsmul x y

/-- Pointwise evaluation of `zmultiplesPiHom` as a noncommutative sum. -/
theorem zmultiplesPiHom_apply (τ : ι → A) (hτ : ∀ i j, AddCommute (τ i) (τ j)) (v : ι → ℤ) :
    zmultiplesPiHom τ hτ v = Finset.univ.noncommSum (fun i => v i • τ i)
      (fun i _ j _ _ => (hτ i j).zsmul_zsmul _ _) :=
  (AddMonoidHom.noncommPiCoprod_apply (N := fun _ => ℤ) _ v).trans <|
    Finset.noncommSum_congr rfl (fun i _ => zmultiplesHom_apply A (τ i) (v i)) _

/-- In an additive commutative group, `zmultiplesPiHom` evaluates as a finite sum. -/
theorem zmultiplesPiHom_apply_eq_sum {B : Type*} [AddCommGroup B] (τ : ι → B)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) (v : ι → ℤ) :
    zmultiplesPiHom τ hτ v = ∑ i, v i • τ i := by
  rw [zmultiplesPiHom_apply, Finset.noncommSum_eq_sum]

/-- `zmultiplesPiHom` sends the `i`-th standard generator `Pi.single i 1` to `τ i`. -/
@[simp] theorem zmultiplesPiHom_single [DecidableEq ι] (τ : ι → A)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) (i : ι) :
    zmultiplesPiHom τ hτ (Pi.single i 1) = τ i :=
  -- `simp` does not unify the `ι`-indexed family of `noncommPiCoprod_single` with the constant
  -- family `ι → ℤ`, so apply it directly.
  (AddMonoidHom.noncommPiCoprod_single _ i _).trans (by simp)

/-- Postcomposing `zmultiplesPiHom` with an additive group homomorphism `f` yields
`zmultiplesPiHom` for `f ∘ τ`. -/
theorem _root_.AddMonoidHom.comp_zmultiplesPiHom {B : Type*} [AddGroup B] (f : A →+ B) (τ : ι → A)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    f.comp (zmultiplesPiHom τ hτ) =
      zmultiplesPiHom (f ∘ τ) (fun i j => (hτ i j).map f) := by
  classical
  exact AddMonoidHom.pi_ext_int fun i => by simp

/-- The image of `zmultiplesPiHom τ` is the additive subgroup generated by the `τ i`. -/
theorem range_zmultiplesPiHom (τ : ι → A) (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    (zmultiplesPiHom τ hτ).range = AddSubgroup.closure (Set.range τ) := by
  refine (AddMonoidHom.noncommPiCoprod_range _).trans ?_
  simp [AddSubgroup.range_zmultiplesHom, AddSubgroup.zmultiples_eq_closure,
    ← AddSubgroup.closure_iUnion]

/-- `zmultiplesPiHom τ` is surjective if and only if the elements `τ i` generate `A`. -/
theorem zmultiplesPiHom_surjective (τ : ι → A) (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    Function.Surjective (zmultiplesPiHom τ hτ) ↔ AddSubgroup.closure (Set.range τ) = ⊤ := by
  rw [← AddMonoidHom.range_eq_top, range_zmultiplesPiHom]

/-- An element additively commuting with every `τ i` commutes with the whole image of
`zmultiplesPiHom τ`. -/
theorem addCommute_zmultiplesPiHom {τ : ι → A} {hτ : ∀ i j, AddCommute (τ i) (τ j)} {x : A}
    (hx : ∀ i, AddCommute x (τ i)) (v : ι → ℤ) :
    AddCommute x (zmultiplesPiHom τ hτ v) :=
  AddMonoidHom.addCommute_noncommPiCoprod _ (fun i k => by
    simpa only [zmultiplesHom_apply] using (hx i).zsmul_right k) v

/-- **Universal property of `ι → ℤ`.** Additive homomorphisms `(ι → ℤ) →+ A` correspond
bijectively to `ι`-tuples of pairwise commuting elements of `A`, via evaluation at the standard
generators `Pi.single i 1`. -/
def zmultiplesPiHomEquiv [DecidableEq ι] :
    {τ : ι → A // ∀ i j, AddCommute (τ i) (τ j)} ≃ ((ι → ℤ) →+ A) where
  toFun τ := zmultiplesPiHom τ.val τ.property
  invFun f := ⟨fun i => f (Pi.single i 1), fun i j => by
    rw [AddCommute, AddSemiconjBy, ← map_add, ← map_add, (AddCommute.all _ _).eq]⟩
  left_inv τ := Subtype.ext <| funext fun i => zmultiplesPiHom_single τ.val τ.property i
  right_inv f := AddMonoidHom.pi_ext_int fun i => zmultiplesPiHom_single _ _ i

/-- Forward evaluation of `zmultiplesPiHomEquiv`. -/
@[simp]
theorem zmultiplesPiHomEquiv_apply [DecidableEq ι]
    (τ : {τ : ι → A // ∀ i j, AddCommute (τ i) (τ j)}) :
    zmultiplesPiHomEquiv τ = zmultiplesPiHom τ.val τ.property :=
  (rfl)

/-- Inverse evaluation of `zmultiplesPiHomEquiv` evaluates at the `i`-th standard generator. -/
@[simp]
theorem zmultiplesPiHomEquiv_symm_apply_coe [DecidableEq ι]
    (f : (ι → ℤ) →+ A) (i : ι) :
    (zmultiplesPiHomEquiv.symm f : ι → A) i = f (Pi.single i 1) :=
  (rfl)

/-- For an additive commutative group `B`, `zmultiplesPiHom` identifies `ι → B` with
`(ι → ℤ) →+ B` as an additive group isomorphism. This is the `ι`-indexed counterpart of
`zmultiplesAddHom`. -/
def zmultiplesPiAddHom [DecidableEq ι] (B : Type*) [AddCommGroup B] :
    (ι → B) ≃+ ((ι → ℤ) →+ B) where
  toFun τ := zmultiplesPiHom τ fun _ _ => AddCommute.all _ _
  invFun f i := f (Pi.single i 1)
  left_inv τ := funext fun i => zmultiplesPiHom_single τ _ i
  right_inv f := AddMonoidHom.pi_ext_int fun i => zmultiplesPiHom_single _ _ i
  map_add' σ τ := AddMonoidHom.pi_ext_int fun i => by simp

/-- Forward evaluation of `zmultiplesPiAddHom` is `zmultiplesPiHom`. -/
theorem zmultiplesPiAddHom_apply [DecidableEq ι] {B : Type*} [AddCommGroup B] (τ : ι → B) :
    zmultiplesPiAddHom B τ = zmultiplesPiHom τ fun _ _ => AddCommute.all _ _ :=
  (rfl)

/-- `zmultiplesPiAddHom` sends the `i`-th standard generator to `τ i`. -/
@[simp]
theorem zmultiplesPiAddHom_apply_single [DecidableEq ι] {B : Type*} [AddCommGroup B] (τ : ι → B)
    (i : ι) :
    zmultiplesPiAddHom B τ (Pi.single i 1) = τ i :=
  zmultiplesPiHom_single τ (fun _ _ => AddCommute.all _ _) i

/-- Inverse evaluation of `zmultiplesPiAddHom` evaluates at the `i`-th standard generator. -/
@[simp]
theorem zmultiplesPiAddHom_symm_apply [DecidableEq ι] {B : Type*} [AddCommGroup B]
    (f : (ι → ℤ) →+ B) (i : ι) :
    (zmultiplesPiAddHom B).symm f i = f (Pi.single i 1) :=
  (rfl)

end Additive

section Transport

variable [Fintype ι]

/-- Transporting `zmultiplesPiHom` across `Multiplicative` factors `zpowersPiHom` of `ofAdd ∘ τ`
through `MulEquiv.funMultiplicative ι ℤ`. -/
theorem toMultiplicative_zmultiplesPiHom {A : Type*} [AddGroup A] (τ : ι → A)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) :
    (zmultiplesPiHom τ hτ).toMultiplicative =
      (zpowersPiHom (fun i => ofAdd (τ i)) fun i j => by
          rw [Commute, SemiconjBy, ← ofAdd_add, ← ofAdd_add, (hτ i j).eq]).comp
        (MulEquiv.funMultiplicative ι ℤ).toMonoidHom := by
  classical
  let hcomm : ∀ i j, Commute (ofAdd (τ i)) (ofAdd (τ j)) := fun i j => by
    rw [Commute, SemiconjBy, ← ofAdd_add, ← ofAdd_add, (hτ i j).eq]
  -- Check agreement on the standard generators of `ι → Multiplicative ℤ` via `pi_ext_mint`.
  suffices ((zmultiplesPiHom τ hτ).toMultiplicative).comp
        (MulEquiv.funMultiplicative ι ℤ).symm.toMonoidHom =
      zpowersPiHom (fun i => ofAdd (τ i)) hcomm by
    refine DFunLike.ext _ _ fun v => ?_
    have hv := congr($this (MulEquiv.funMultiplicative ι ℤ v))
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hv
  refine MonoidHom.pi_ext_mint fun i => ?_
  have hsingle : (fun j => toAdd ((Pi.mulSingle i (ofAdd (1 : ℤ)) : ι → Multiplicative ℤ) j)) =
      Pi.single i (1 : ℤ) := by
    ext j
    by_cases hij : j = i <;> simp [hij]
  simp [hsingle]

/-- Transporting `zpowersPiHom` across `Additive` factors `zmultiplesPiHom` of `ofMul ∘ τ` through
`AddEquiv.funAdditive ι (Multiplicative ℤ)` and `Pi.congrRight` along
`AddEquiv.additiveMultiplicative ℤ`. -/
theorem toAdditive_zpowersPiHom {K : Type*} [Group K] (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) :
    (zpowersPiHom τ hτ).toAdditive =
      (zmultiplesPiHom (fun i => ofMul (τ i)) fun i j => by
          rw [AddCommute, AddSemiconjBy, ← ofMul_mul, ← ofMul_mul, (hτ i j).eq]).comp
        ((AddEquiv.piCongrRight fun _ : ι => AddEquiv.additiveMultiplicative ℤ).toAddMonoidHom.comp
          (AddEquiv.funAdditive ι (Multiplicative ℤ)).toAddMonoidHom) := by
  classical
  let hcomm : ∀ i j, AddCommute (ofMul (τ i)) (ofMul (τ j)) := fun i j => by
    rw [AddCommute, AddSemiconjBy, ← ofMul_mul, ← ofMul_mul, (hτ i j).eq]
  let e : Additive (ι → Multiplicative ℤ) ≃+ (ι → ℤ) :=
    (AddEquiv.funAdditive ι (Multiplicative ℤ)).trans
      (AddEquiv.piCongrRight fun _ : ι => AddEquiv.additiveMultiplicative ℤ)
  suffices ((zpowersPiHom τ hτ).toAdditive).comp e.symm.toAddMonoidHom =
      zmultiplesPiHom (fun i => ofMul (τ i)) hcomm by
    refine DFunLike.ext _ _ fun x => ?_
    have hx := congr($this (e x))
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, e.symm_apply_apply] at hx
    exact hx
  refine AddMonoidHom.pi_ext_int fun i => ?_
  have hsingle : (fun j => ofAdd ((Pi.single i (1 : ℤ) : ι → ℤ) j)) =
      (Pi.mulSingle i (ofAdd (1 : ℤ)) : ι → Multiplicative ℤ) := by
    ext j
    by_cases hij : j = i <;> simp [hij]
  simp [e, hsingle]

/-- Pointwise form of `toMultiplicative_zmultiplesPiHom`. -/
@[simp] theorem ofAdd_zmultiplesPiHom {A : Type*} [AddGroup A] (τ : ι → A)
    (hτ : ∀ i j, AddCommute (τ i) (τ j)) (v : ι → ℤ) :
    Multiplicative.ofAdd (zmultiplesPiHom τ hτ v) =
      zpowersPiHom (fun i => Multiplicative.ofAdd (τ i))
        (fun i j => by simp [Commute, SemiconjBy, ← ofAdd_add, (hτ i j).eq])
        (fun i => Multiplicative.ofAdd (v i)) :=
  DFunLike.congr_fun (toMultiplicative_zmultiplesPiHom τ hτ) (ofAdd v)

/-- Pointwise form of `toAdditive_zpowersPiHom`. -/
@[simp] theorem ofMul_zpowersPiHom {K : Type*} [Group K] (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) (v : ι → Multiplicative ℤ) :
    Additive.ofMul (zpowersPiHom τ hτ v) =
      zmultiplesPiHom (fun i => Additive.ofMul (τ i))
        (fun i j => by simp [AddCommute, AddSemiconjBy, ← ofMul_mul, (hτ i j).eq])
        (fun i => (v i).toAdd) :=
  DFunLike.congr_fun (toAdditive_zpowersPiHom τ hτ) (ofMul v)

end Transport

end TauCeti
