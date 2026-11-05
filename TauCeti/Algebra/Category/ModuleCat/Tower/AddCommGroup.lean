/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact
public import TauCeti.Algebra.Category.ModuleCat.Tower.MittagLeffler
public import TauCeti.Algebra.Category.ModuleCat.Tower.Padic

/-!
# Towers of abelian groups

A tower of abelian groups `A₀ ← A₁ ← A₂ ← ⋯` is often presented by its terms and its transition
homomorphisms `φₙ : Aₙ₊₁ → Aₙ`, for instance for towers of cochain groups indexed by an exhaustion
of a space. This file sets up that presentation, `TauCeti.CompactCoefficients.Tower`, and
identifies it with the tower of `ℤ`-modules `Tower.toModuleFunctor : ℕᵒᵖ ⥤ ModuleCat ℤ`.
The shift `δ(a)ₙ = aₙ - φₙ(aₙ₊₁)` on `∏ₙ Aₙ` has kernel `lim A` and cokernel `lim¹ A`, and the
comparisons `Tower.limComparison` and `Tower.limOneComparison` identify these with the limit and
first derived limit of `TauCeti.ModuleTower`, naturally in morphisms of towers.

All further results are transported from `TauCeti.ModuleTower` along these comparisons: vanishing
of `lim¹` for surjective transitions and for Mittag-Leffler towers, and the six-term exact sequence

```text
0 → lim A → lim B → lim C → lim¹ A → lim¹ B → lim¹ C → 0
```

of a levelwise short exact sequence of towers, whose connecting map corresponds to
`TauCeti.ModuleTower.connecting`. For a prime `p`, the tower `ℤ ← ℤ ← ⋯` whose transitions are
multiplication by `p` has `lim = 0` and `lim¹ ≃ ℤ_[p] ⧸ ℤ`, so it is not Mittag-Leffler.

## Main declarations

* `TauCeti.CompactCoefficients.Tower`: a tower of abelian groups, with its shift map
  `Tower.shift`, its limit `Tower.lim` and its first derived limit `Tower.limOne`.
* `TauCeti.CompactCoefficients.Tower.toModuleFunctor`: the tower as a tower of `ℤ`-modules.
* `TauCeti.CompactCoefficients.Tower.limComparison`,
  `TauCeti.CompactCoefficients.Tower.limOneComparison`: the identifications of `lim` and `lim¹`
  with those of the tower of `ℤ`-modules.
* `TauCeti.CompactCoefficients.Tower.Hom`: morphisms of towers, with the induced maps
  `Hom.onProduct`, `Hom.limMap` and `Hom.limOneMap`.
* `TauCeti.CompactCoefficients.Tower.subsingleton_limOne_of_isMittagLeffler`: Mittag-Leffler towers
  have vanishing `lim¹`.
* `TauCeti.CompactCoefficients.Tower.connecting`: the connecting map `lim C → lim¹ A`, with the
  exactness statements of the six-term sequence.
* `TauCeti.CompactCoefficients.mulTower`, `TauCeti.CompactCoefficients.limOneMulTowerEquiv`: the
  multiplication-by-`p` tower and its first derived limit `ℤ_[p] ⧸ ℤ`.

## References

* [Stacks: More on Algebra, Lemma 15.88.1, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks: Algebra, Definition 10.86.1, Tag 0594](https://stacks.math.columbia.edu/tag/0594)
* C. A. Weibel, *An introduction to homological algebra*, §3.5.
-/

public section

noncomputable section

namespace TauCeti

namespace CompactCoefficients

open CategoryTheory Opposite

universe u

/-- A tower of abelian groups `A₀ ← A₁ ← A₂ ← ⋯`, presented by its terms `Aₙ` and its transition
homomorphisms `Aₙ₊₁ → Aₙ`. It is identified with a tower of `ℤ`-modules by
`Tower.toModuleFunctor`. -/
structure Tower where
  /-- The terms `Aₙ` of the tower. -/
  obj : ℕ → Type u
  [inst : ∀ n, AddCommGroup (obj n)]
  /-- The transition homomorphisms `Aₙ₊₁ → Aₙ`. -/
  map : ∀ n, obj (n + 1) →+ obj n

attribute [instance] Tower.inst

namespace Tower

section Basic

variable (A : Tower.{u})

/-- The shift map `δ : ∏ₙ Aₙ → ∏ₙ Aₙ`, `δ(a)ₙ = aₙ - φₙ(aₙ₊₁)`. -/
def shift : (∀ n, A.obj n) →+ ∀ n, A.obj n :=
  AddMonoidHom.id _ - AddMonoidHom.pi fun n ↦ (A.map n).comp (Pi.evalAddMonoidHom A.obj (n + 1))

@[simp]
theorem shift_apply (a : ∀ n, A.obj n) (n : ℕ) : A.shift a n = a n - A.map n (a (n + 1)) :=
  (rfl)

/-- The limit `lim A` of a tower, the kernel of the shift map: the families `(aₙ)` with
`φₙ(aₙ₊₁) = aₙ` for every `n`. -/
def lim : AddSubgroup (∀ n, A.obj n) :=
  A.shift.ker

/-- The first derived limit `lim¹ A` of a tower, the cokernel of the shift map. -/
abbrev limOne : Type u :=
  (∀ n, A.obj n) ⧸ A.shift.range

theorem lim_eq_ker : A.lim = A.shift.ker :=
  (rfl)

/-- `a ∈ lim A` if and only if `φₙ(aₙ₊₁) = aₙ` for every `n`. -/
@[simp]
theorem mem_lim {a : ∀ n, A.obj n} : a ∈ A.lim ↔ ∀ n, A.map n (a (n + 1)) = a n := by
  rw [lim_eq_ker, AddMonoidHom.mem_ker, funext_iff]
  simp only [shift_apply, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun n ↦ eq_comm

/-- The tower of abelian groups as a tower of `ℤ`-modules. Its terms are the groups `Aₙ` with their
`ℤ`-module structures, so that the product of its terms is `∏ₙ Aₙ`; the body is exposed for this
identification of carriers. -/
@[expose]
def toModuleFunctor : ModuleTower.{u} ℤ :=
  Functor.ofOpSequence (X := fun n ↦ ModuleCat.of ℤ (A.obj n))
    fun n ↦ ModuleCat.ofHom (A.map n).toIntLinearMap

/-- The terms of the tower of `ℤ`-modules are the groups `Aₙ`. -/
theorem toModuleFunctor_obj (n : ℕ) :
    A.toModuleFunctor.obj (op n) = ModuleCat.of ℤ (A.obj n) :=
  (rfl)

/-- The transitions of the tower of `ℤ`-modules are the transitions `φₙ` of the tower. -/
@[simp]
theorem transition_toModuleFunctor_apply (n : ℕ) (x : A.toModuleFunctor.obj (op (n + 1))) :
    A.toModuleFunctor.transition n x = A.map n x := by
  simp only [ModuleTower.transition_def, toModuleFunctor, Functor.ofOpSequence_map_homOfLE_succ]
  -- `ModuleCat.ofHom` of `(A.map n).toIntLinearMap` has underlying function `A.map n`
  rfl

/-- The transitions of the tower of `ℤ`-modules are surjective exactly when those of the tower
are. -/
theorem transition_toModuleFunctor_surjective_iff {n : ℕ} :
    Function.Surjective (A.toModuleFunctor.transition n) ↔ Function.Surjective (A.map n) :=
  forall_congr' fun y ↦ exists_congr fun x ↦ by
    rw [transition_toModuleFunctor_apply]
    -- the terms of the tower of `ℤ`-modules are the groups `Aₙ`
    exact Iff.rfl

/-- The product `∏ₙ Aₙ` is the product of the terms of the tower of `ℤ`-modules. -/
def productEquiv : (∀ n, A.obj n) ≃+ A.toModuleFunctor.Product :=
  AddEquiv.refl _

@[simp]
theorem productEquiv_apply (a : ∀ n, A.obj n) (n : ℕ) : A.productEquiv a n = a n :=
  (rfl)

@[simp]
theorem productEquiv_symm_apply (a : A.toModuleFunctor.Product) (n : ℕ) :
    A.productEquiv.symm a n = a n :=
  (rfl)

/-- The shift map of the tower of `ℤ`-modules is the shift map of the tower. -/
@[simp]
theorem shift_productEquiv (a : ∀ n, A.obj n) :
    A.toModuleFunctor.shift (A.productEquiv a) = A.productEquiv (A.shift a) := by
  ext n
  rw [ModuleTower.shift_apply, transition_toModuleFunctor_apply]
  -- the subtraction on the terms of the tower of `ℤ`-modules is that of the groups `Aₙ`
  rfl

/-- A family lies in the limit of the tower of `ℤ`-modules if and only if it lies in `lim A`. -/
theorem productEquiv_mem_lim {a : ∀ n, A.obj n} :
    A.productEquiv a ∈ A.toModuleFunctor.lim ↔ a ∈ A.lim := by
  rw [ModuleTower.mem_lim, mem_lim]
  -- the terms of the tower of `ℤ`-modules are the groups `Aₙ`, and `productEquiv` is the identity
  exact forall_congr' fun n ↦ by rw [transition_toModuleFunctor_apply]; rfl

/-- A family lies in the image of the shift map of the tower of `ℤ`-modules if and only if it lies
in the image of the shift map. -/
theorem productEquiv_mem_range_shift {a : ∀ n, A.obj n} :
    A.productEquiv a ∈ LinearMap.range A.toModuleFunctor.shift ↔ a ∈ A.shift.range := by
  refine ⟨fun ⟨b, hb⟩ ↦ ⟨A.productEquiv.symm b, A.productEquiv.injective ?_⟩, ?_⟩
  · rw [← shift_productEquiv, AddEquiv.apply_symm_apply, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨A.productEquiv b, shift_productEquiv A b⟩

/-- The limit of a tower of abelian groups is the limit of the tower of `ℤ`-modules. -/
def limComparison : A.lim ≃+ A.toModuleFunctor.lim where
  toFun a := ⟨A.productEquiv a.1, A.productEquiv_mem_lim.2 a.2⟩
  invFun a := ⟨A.productEquiv.symm a.1, A.productEquiv_mem_lim.1 <| by simp⟩
  left_inv a := Subtype.ext <| A.productEquiv.symm_apply_apply a.1
  right_inv a := Subtype.ext <| A.productEquiv.apply_symm_apply a.1
  map_add' a b := Subtype.ext <| map_add A.productEquiv a.1 b.1

@[simp]
theorem coe_limComparison_apply (a : A.lim) :
    (A.limComparison a : A.toModuleFunctor.Product) = A.productEquiv a.1 :=
  (rfl)

@[simp]
theorem coe_limComparison_symm_apply (a : A.toModuleFunctor.lim) :
    (A.limComparison.symm a : ∀ n, A.obj n) = A.productEquiv.symm a.1 :=
  (rfl)

/-- The comparison of limits is compatible with the projections `lim A → Aₙ`. -/
theorem limπ_limComparison (a : A.lim) (n : ℕ) :
    A.toModuleFunctor.limπ n (A.limComparison a) = (a : ∀ n, A.obj n) n :=
  A.toModuleFunctor.limπ_apply n _

/-- The first derived limit of a tower of abelian groups is that of the tower of
`ℤ`-modules. -/
def limOneComparison : A.limOne ≃+ A.toModuleFunctor.limOne :=
  QuotientAddGroup.congr _ _ A.productEquiv <| by
    ext x
    rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    refine ⟨?_, fun hx ↦ ⟨A.productEquiv.symm x, ?_, A.productEquiv.apply_symm_apply x⟩⟩
    · rintro ⟨a, ha, rfl⟩
      exact A.productEquiv_mem_range_shift.2 ha
    · exact A.productEquiv_mem_range_shift.1 (by rwa [AddEquiv.apply_symm_apply])

@[simp]
theorem limOneComparison_mk (a : ∀ n, A.obj n) :
    A.limOneComparison (QuotientAddGroup.mk a) = Submodule.Quotient.mk (A.productEquiv a) :=
  (rfl)

@[simp]
theorem limOneComparison_symm_mk (a : A.toModuleFunctor.Product) :
    A.limOneComparison.symm (Submodule.Quotient.mk a) =
      QuotientAddGroup.mk (A.productEquiv.symm a) :=
  (rfl)

/-- `lim¹ A` vanishes if and only if the shift map is surjective. -/
theorem subsingleton_limOne_iff : Subsingleton A.limOne ↔ Function.Surjective A.shift := by
  rw [← not_nontrivial_iff_subsingleton, QuotientAddGroup.nontrivial_iff, not_not,
    AddMonoidHom.range_eq_top]

/-- **Towers with surjective transitions have vanishing `lim¹`** (Stacks, Tag 07KW). -/
theorem subsingleton_limOne_of_surjective (h : ∀ n, Function.Surjective (A.map n)) :
    Subsingleton A.limOne :=
  A.limOneComparison.toEquiv.subsingleton_congr.2 <|
    A.toModuleFunctor.subsingleton_limOne_of_surjective fun n ↦
      A.transition_toModuleFunctor_surjective_iff.2 (h n)

end Basic

section MittagLeffler

variable (A : Tower.{u})

/-- The composite transition `Aₖ → Aₙ` of a tower, for `n ≤ k`. -/
def mapOfLE {n k : ℕ} (h : n ≤ k) : A.obj k →+ A.obj n :=
  (A.toModuleFunctor.transitionOfLE h).toAddMonoidHom

@[simp]
theorem mapOfLE_refl (n : ℕ) : A.mapOfLE (le_refl n) = AddMonoidHom.id _ := by
  ext x
  simp only [mapOfLE, ModuleTower.transitionOfLE_refl]
  -- `LinearMap.id.toAddMonoidHom` is the identity of `Aₙ`
  rfl

@[simp]
theorem mapOfLE_succ (n : ℕ) : A.mapOfLE (Nat.le_succ n) = A.map n := by
  ext x
  simp only [mapOfLE, ModuleTower.transitionOfLE_succ]
  exact A.transition_toModuleFunctor_apply n x

@[simp]
theorem mapOfLE_mapOfLE {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (x : A.obj k) :
    A.mapOfLE hmn (A.mapOfLE hnk x) = A.mapOfLE (hmn.trans hnk) x :=
  A.toModuleFunctor.transitionOfLE_transitionOfLE hmn hnk x

/-- A tower of abelian groups is *Mittag-Leffler* if, for every `n`, the images of the composite
transitions `Aₖ → Aₙ` stabilise as `k` grows: Mathlib's `Functor.IsMittagLeffler` for the
underlying functor `ℕᵒᵖ ⥤ Type` (see `isMittagLeffler_iff_ranges`). -/
abbrev IsMittagLeffler : Prop :=
  A.toModuleFunctor.IsMittagLeffler

/-- **Eventual-range form of the Mittag-Leffler condition**: a tower is Mittag-Leffler if and
only if, for every `n`, the images of the composite transitions `Aₖ → Aₙ` are constant for all
`k` beyond some `m ≥ n`. -/
theorem isMittagLeffler_iff_ranges : A.IsMittagLeffler ↔
    ∀ n, ∃ m, ∃ hnm : n ≤ m, ∀ k (hmk : m ≤ k),
      (A.mapOfLE (hnm.trans hmk)).range = (A.mapOfLE hnm).range := by
  refine A.toModuleFunctor.isMittagLeffler_iff_ranges.trans <| forall_congr' fun n ↦
    exists_congr fun m ↦ exists_congr fun hnm ↦ forall_congr' fun k ↦ forall_congr' fun hmk ↦ ?_
  rw [← Submodule.toAddSubgroup_inj, LinearMap.range_toAddSubgroup, LinearMap.range_toAddSubgroup]
  -- `mapOfLE` is `transitionOfLE` of the tower of `ℤ`-modules, whose terms are the groups `Aₙ`
  rfl

/-- **Towers with surjective transitions are Mittag-Leffler.** -/
theorem isMittagLeffler_of_surjective (h : ∀ n, Function.Surjective (A.map n)) :
    A.IsMittagLeffler :=
  A.toModuleFunctor.isMittagLeffler_of_surjective fun n ↦
    A.transition_toModuleFunctor_surjective_iff.2 (h n)

/-- **Towers of finite groups are Mittag-Leffler.** -/
theorem isMittagLeffler_of_finite [∀ n, Finite (A.obj n)] : A.IsMittagLeffler :=
  have (n : ℕ) : IsArtinian ℤ (A.toModuleFunctor.obj (op n)) :=
    isArtinian_of_finite (R := ℤ) (M := A.obj n)
  A.toModuleFunctor.isMittagLeffler_of_isArtinian

/-- **Mittag-Leffler towers have vanishing `lim¹`** (Stacks, Tag 07KW). -/
theorem subsingleton_limOne_of_isMittagLeffler (h : A.IsMittagLeffler) :
    Subsingleton A.limOne :=
  A.limOneComparison.toEquiv.subsingleton_congr.2 <|
    A.toModuleFunctor.subsingleton_limOne_of_isMittagLeffler h

end MittagLeffler

section Hom

/-- A morphism of towers of abelian groups: homomorphisms `Aₙ → Bₙ` commuting with the
transitions. -/
@[ext]
structure Hom (A B : Tower.{u}) where
  /-- The homomorphisms `Aₙ → Bₙ`. -/
  app : ∀ n, A.obj n →+ B.obj n
  /-- The homomorphisms commute with the transitions. -/
  comm : ∀ n x, app n (A.map n x) = B.map n (app (n + 1) x)

attribute [simp] Hom.comm

variable {A B C : Tower.{u}}

/-- The identity morphism of a tower. -/
def Hom.id (A : Tower.{u}) : Hom A A where
  app _ := AddMonoidHom.id _
  comm _ _ := rfl

/-- The composite `g ∘ f` of morphisms of towers. -/
def Hom.comp (g : Hom B C) (f : Hom A B) : Hom A C where
  app n := (g.app n).comp (f.app n)
  comm n x := by simp

/-- The zero morphism between two towers. -/
def Hom.zero (A B : Tower.{u}) : Hom A B where
  app _ := 0
  comm _ _ := by simp

@[simp]
theorem Hom.id_app (A : Tower.{u}) (n : ℕ) : (Hom.id A).app n = AddMonoidHom.id _ :=
  (rfl)

@[simp]
theorem Hom.comp_app (g : Hom B C) (f : Hom A B) (n : ℕ) :
    (g.comp f).app n = (g.app n).comp (f.app n) :=
  (rfl)

@[simp]
theorem Hom.zero_app (A B : Tower.{u}) (n : ℕ) : (Hom.zero A B).app n = 0 :=
  (rfl)

/-- A morphism of towers of abelian groups as a morphism of towers of `ℤ`-modules. -/
def Hom.toNatTrans (f : Hom A B) : A.toModuleFunctor ⟶ B.toModuleFunctor :=
  NatTrans.ofOpSequence (fun n ↦ ModuleCat.ofHom (f.app n).toIntLinearMap) fun n ↦ by
    ext x
    simp only [toModuleFunctor, Functor.ofOpSequence_map_homOfLE_succ]
    exact f.comm n x

@[simp]
theorem Hom.toNatTrans_app_apply (f : Hom A B) (n : ℕ) (x : A.toModuleFunctor.obj (op n)) :
    (f.toNatTrans.app (op n)).hom x = f.app n x :=
  (rfl)

/-- The identity morphism of a tower is the identity of the tower of `ℤ`-modules. -/
@[simp]
theorem Hom.toNatTrans_id (A : Tower.{u}) : (Hom.id A).toNatTrans = 𝟙 A.toModuleFunctor := by
  ext ⟨n⟩ x
  -- both components are the identity of `Aₙ`
  rfl

/-- `Hom.toNatTrans` respects composition of morphisms of towers. -/
@[simp]
theorem Hom.toNatTrans_comp (g : Hom B C) (f : Hom A B) :
    (g.comp f).toNatTrans = f.toNatTrans ≫ g.toNatTrans := by
  ext ⟨n⟩ x
  -- both components are `g.app n ∘ f.app n`
  rfl

/-- The zero morphism of towers is the zero morphism of towers of `ℤ`-modules. -/
@[simp]
theorem Hom.toNatTrans_zero (A B : Tower.{u}) : (Hom.zero A B).toNatTrans = 0 := by
  ext ⟨n⟩ x
  -- both components are the zero map `Aₙ → Bₙ`
  rfl

/-- The underlying function of a component of `Hom.toNatTrans f` is that of `f`. -/
theorem Hom.coe_toNatTrans_app (f : Hom A B) (n : ℕ) :
    ⇑(f.toNatTrans.app (op n)).hom = f.app n :=
  funext (f.toNatTrans_app_apply n)

/-- A levelwise injective morphism of towers gives a levelwise injective morphism of towers of
`ℤ`-modules. -/
theorem Hom.toNatTrans_app_injective (f : Hom A B) (hf : ∀ n, Function.Injective (f.app n))
    (n : ℕ) : Function.Injective (f.toNatTrans.app (op n)).hom := by
  rw [Hom.coe_toNatTrans_app]
  exact hf n

/-- A levelwise surjective morphism of towers gives a levelwise surjective morphism of towers of
`ℤ`-modules. -/
theorem Hom.toNatTrans_app_surjective (f : Hom A B) (hf : ∀ n, Function.Surjective (f.app n))
    (n : ℕ) : Function.Surjective (f.toNatTrans.app (op n)).hom := by
  rw [Hom.coe_toNatTrans_app]
  exact hf n

/-- A levelwise exact pair of morphisms of towers gives a levelwise exact pair of morphisms of
towers of `ℤ`-modules. -/
theorem Hom.exact_toNatTrans_app (f : Hom A B) (g : Hom B C)
    (hfg : ∀ n, Function.Exact (f.app n) (g.app n)) (n : ℕ) :
    Function.Exact (f.toNatTrans.app (op n)).hom (g.toNatTrans.app (op n)).hom := by
  rw [Hom.coe_toNatTrans_app, Hom.coe_toNatTrans_app]
  exact hfg n

/-- The homomorphism `∏ₙ Aₙ → ∏ₙ Bₙ` induced levelwise by a morphism of towers. -/
def Hom.onProduct (f : Hom A B) : (∀ n, A.obj n) →+ ∀ n, B.obj n :=
  AddMonoidHom.piMap f.app

@[simp]
theorem Hom.onProduct_apply (f : Hom A B) (a : ∀ n, A.obj n) (n : ℕ) :
    f.onProduct a n = f.app n (a n) :=
  AddMonoidHom.piMap_apply f.app a n

/-- The identity morphism of a tower acts identically on the product. -/
@[simp]
theorem Hom.onProduct_id (A : Tower.{u}) :
    (Hom.id A).onProduct = AddMonoidHom.id (∀ n, A.obj n) :=
  (rfl)

/-- Product maps respect composition of morphisms of towers. -/
@[simp]
theorem Hom.onProduct_comp (g : Hom B C) (f : Hom A B) :
    (g.comp f).onProduct = g.onProduct.comp f.onProduct :=
  (rfl)

/-- The zero morphism of towers induces the zero map on products. -/
@[simp]
theorem Hom.onProduct_zero (A B : Tower.{u}) : (Hom.zero A B).onProduct = 0 :=
  (rfl)

/-- The product map of a morphism of towers is that of the morphism of towers of
`ℤ`-modules. -/
@[simp]
theorem productMap_toNatTrans_productEquiv (f : Hom A B) (a : ∀ n, A.obj n) :
    ModuleTower.productMap f.toNatTrans (A.productEquiv a) = B.productEquiv (f.onProduct a) := by
  ext n
  rw [ModuleTower.productMap_apply, Hom.toNatTrans_app_apply, productEquiv_apply,
    productEquiv_apply, Hom.onProduct_apply]

/-- The product map of a morphism of towers commutes with the shift maps. -/
theorem Hom.shift_onProduct (f : Hom A B) (a : ∀ n, A.obj n) :
    B.shift (f.onProduct a) = f.onProduct (A.shift a) := by
  ext n
  simp

/-- The homomorphism `lim A → lim B` induced by a morphism of towers. -/
def Hom.limMap (f : Hom A B) : A.lim →+ B.lim :=
  (f.onProduct.comp A.lim.subtype).codRestrict B.lim fun a ↦ by
    have ha : A.shift a = 0 := a.2
    rw [lim_eq_ker, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Hom.shift_onProduct,
      AddSubgroup.subtype_apply, ha, map_zero]

@[simp]
theorem Hom.coe_limMap_apply (f : Hom A B) (a : A.lim) :
    (f.limMap a : ∀ n, B.obj n) = f.onProduct a :=
  (rfl)

/-- The identity morphism of a tower acts identically on `lim`. -/
@[simp]
theorem Hom.limMap_id (A : Tower.{u}) : (Hom.id A).limMap = AddMonoidHom.id A.lim :=
  (rfl)

/-- The induced maps on `lim` respect composition. -/
@[simp]
theorem Hom.limMap_comp (g : Hom B C) (f : Hom A B) :
    (g.comp f).limMap = g.limMap.comp f.limMap :=
  (rfl)

/-- The zero morphism of towers induces the zero map on `lim`. -/
@[simp]
theorem Hom.limMap_zero (A B : Tower.{u}) : (Hom.zero A B).limMap = 0 :=
  (rfl)

/-- The comparison of limits is natural in morphisms of towers. -/
@[simp]
theorem limComparison_limMap (f : Hom A B) (a : A.lim) :
    B.limComparison (f.limMap a) = ModuleTower.limMap f.toNatTrans (A.limComparison a) :=
  Subtype.ext <| by
    rw [coe_limComparison_apply, ModuleTower.coe_limMap_apply, coe_limComparison_apply,
      productMap_toNatTrans_productEquiv, Hom.coe_limMap_apply]

/-- The naturality square of `limComparison`, as an equality of homomorphisms. -/
theorem limComparison_comp_limMap (f : Hom A B) :
    B.limComparison.toAddMonoidHom.comp f.limMap =
      (ModuleTower.limMap f.toNatTrans).toAddMonoidHom.comp A.limComparison.toAddMonoidHom :=
  AddMonoidHom.ext (limComparison_limMap f)

/-- The homomorphism `lim¹ A → lim¹ B` induced by a morphism of towers. -/
def Hom.limOneMap (f : Hom A B) : A.limOne →+ B.limOne :=
  QuotientAddGroup.map _ _ f.onProduct <| by
    rintro _ ⟨a, rfl⟩
    exact ⟨f.onProduct a, f.shift_onProduct a⟩

@[simp]
theorem Hom.limOneMap_mk (f : Hom A B) (a : ∀ n, A.obj n) :
    f.limOneMap (QuotientAddGroup.mk a) = QuotientAddGroup.mk (f.onProduct a) :=
  (rfl)

/-- The comparison of first derived limits is natural in morphisms of towers. -/
@[simp]
theorem limOneComparison_limOneMap (f : Hom A B) (x : A.limOne) :
    B.limOneComparison (f.limOneMap x) =
      ModuleTower.limOneMap f.toNatTrans (A.limOneComparison x) := by
  induction x using QuotientAddGroup.induction_on
  rw [Hom.limOneMap_mk, limOneComparison_mk, limOneComparison_mk, ModuleTower.limOneMap_mk,
    productMap_toNatTrans_productEquiv]

/-- The naturality square of `limOneComparison`, as an equality of homomorphisms. -/
theorem limOneComparison_comp_limOneMap (f : Hom A B) :
    B.limOneComparison.toAddMonoidHom.comp f.limOneMap =
      (ModuleTower.limOneMap f.toNatTrans).toAddMonoidHom.comp A.limOneComparison.toAddMonoidHom :=
  AddMonoidHom.ext (limOneComparison_limOneMap f)

/-- The identity morphism of a tower acts identically on `lim¹`. -/
@[simp]
theorem Hom.limOneMap_id (A : Tower.{u}) : (Hom.id A).limOneMap = AddMonoidHom.id A.limOne := by
  ext x
  rfl

/-- The induced maps on `lim¹` respect composition. -/
@[simp]
theorem Hom.limOneMap_comp (g : Hom B C) (f : Hom A B) :
    (g.comp f).limOneMap = g.limOneMap.comp f.limOneMap := by
  ext x
  rfl

/-- The zero morphism of towers induces the zero map on `lim¹`. -/
@[simp]
theorem Hom.limOneMap_zero (A B : Tower.{u}) : (Hom.zero A B).limOneMap = 0 := by
  ext x
  simp

end Hom

section Exact

/-! ### The six-term sequence -/

variable {A B C : Tower.{u}} (f : Hom A B) (g : Hom B C)

/-- `lim A → lim B` is injective when every `Aₙ → Bₙ` is. -/
theorem limMap_injective (hf : ∀ n, Function.Injective (f.app n)) :
    Function.Injective f.limMap := fun a b hab ↦
  A.limComparison.injective <| ModuleTower.limMap_injective (f.toNatTrans_app_injective hf) <| by
    rw [← limComparison_limMap, ← limComparison_limMap, hab]

/-- Exactness of `lim A → lim B → lim C` for a levelwise exact sequence `0 → A → B → C`. -/
theorem exact_limMap (hf : ∀ n, Function.Injective (f.app n))
    (hfg : ∀ n, Function.Exact (f.app n) (g.app n)) :
    Function.Exact f.limMap g.limMap :=
  (Function.Exact.iff_of_ladder_addEquiv A.limComparison B.limComparison C.limComparison
    (limComparison_comp_limMap f).symm (limComparison_comp_limMap g).symm).1
    (ModuleTower.exact_limMap (f.toNatTrans_app_injective hf)
      (f.exact_toNatTrans_app g hfg))

/-- Exactness of `lim¹ A → lim¹ B → lim¹ C` for a levelwise exact sequence `A → B → C → 0`. -/
theorem exact_limOneMap (hfg : ∀ n, Function.Exact (f.app n) (g.app n))
    (hg : ∀ n, Function.Surjective (g.app n)) :
    Function.Exact f.limOneMap g.limOneMap :=
  (Function.Exact.iff_of_ladder_addEquiv A.limOneComparison B.limOneComparison
    C.limOneComparison (limOneComparison_comp_limOneMap f).symm
    (limOneComparison_comp_limOneMap g).symm).1
    (ModuleTower.exact_limOneMap (f.exact_toNatTrans_app g hfg)
      (g.toNatTrans_app_surjective hg))

/-- `lim¹ B → lim¹ C` is surjective when every `Bₙ → Cₙ` is. -/
theorem limOneMap_surjective (hg : ∀ n, Function.Surjective (g.app n)) :
    Function.Surjective g.limOneMap := by
  refine (EquivLike.comp_surjective _ C.limOneComparison).1 ?_
  convert (ModuleTower.limOneMap_surjective (g.toNatTrans_app_surjective hg)).comp
    B.limOneComparison.surjective using 1
  -- The coercion of a composite of homomorphisms is the composite of the coercions by definition.
  exact congrArg DFunLike.coe (limOneComparison_comp_limOneMap g)

variable (hf : ∀ n, Function.Injective (f.app n)) (hfg : ∀ n, Function.Exact (f.app n) (g.app n))
  (hg : ∀ n, Function.Surjective (g.app n))

/-- The connecting map `lim C → lim¹ A` of the six-term sequence of a levelwise short exact
sequence of towers `0 → A → B → C → 0`, transported from `ModuleTower.connecting`. It sends a
compatible family `c` to the class of any family `a` of `A` with `f(a) = δ(b)` for some lift `b`
of `c`; see `connecting_apply`. -/
def connecting : C.lim →+ A.limOne :=
  A.limOneComparison.symm.toAddMonoidHom.comp <|
    (ModuleTower.connecting f.toNatTrans g.toNatTrans (f.toNatTrans_app_injective hf)
      (f.exact_toNatTrans_app g hfg) (g.toNatTrans_app_surjective hg)).toAddMonoidHom.comp
      C.limComparison.toAddMonoidHom

/-- The comparisons of `lim` and `lim¹` carry the connecting map to the connecting map of the
towers of `ℤ`-modules. -/
@[simp]
theorem limOneComparison_connecting (c : C.lim) :
    A.limOneComparison (connecting f g hf hfg hg c) =
      ModuleTower.connecting f.toNatTrans g.toNatTrans (f.toNatTrans_app_injective hf)
        (f.exact_toNatTrans_app g hfg) (g.toNatTrans_app_surjective hg) (C.limComparison c) :=
  A.limOneComparison.apply_symm_apply _

/-- The square relating `connecting` to the connecting map of the towers of `ℤ`-modules, as an
equality of homomorphisms. -/
theorem limOneComparison_comp_connecting :
    A.limOneComparison.toAddMonoidHom.comp (connecting f g hf hfg hg) =
      (ModuleTower.connecting f.toNatTrans g.toNatTrans (f.toNatTrans_app_injective hf)
        (f.exact_toNatTrans_app g hfg) (g.toNatTrans_app_surjective hg)).toAddMonoidHom.comp
        C.limComparison.toAddMonoidHom :=
  AddMonoidHom.ext (limOneComparison_connecting f g hf hfg hg)

/-- **The connecting map of the six-term sequence.** If `b` lifts the compatible family `c` of
`C` and `f(a) = δ(b)`, then `c` is sent to the class of `a` in `lim¹ A`. -/
theorem connecting_apply (c : C.lim) (b : ∀ n, B.obj n) (hb : g.onProduct b = c)
    (a : ∀ n, A.obj n) (ha : f.onProduct a = B.shift b) :
    connecting f g hf hfg hg c = QuotientAddGroup.mk a :=
  A.limOneComparison.injective <| by
    rw [limOneComparison_connecting, limOneComparison_mk]
    refine ModuleTower.connecting_apply _ _ _ _ _ _ (B.productEquiv b) ?_ (A.productEquiv a) ?_
    · rw [productMap_toNatTrans_productEquiv, hb, coe_limComparison_apply]
    · rw [productMap_toNatTrans_productEquiv, ha, shift_productEquiv]

/-- Exactness of `lim B → lim C → lim¹ A`. -/
theorem exact_limMap_connecting : Function.Exact g.limMap (connecting f g hf hfg hg) :=
  (Function.Exact.iff_of_ladder_addEquiv B.limComparison C.limComparison A.limOneComparison
    (limComparison_comp_limMap g).symm (limOneComparison_comp_connecting f g hf hfg hg).symm).1
    (ModuleTower.exact_limMap_connecting _ _ _ _ _)

/-- Exactness of `lim C → lim¹ A → lim¹ B`. -/
theorem exact_connecting_limOneMap : Function.Exact (connecting f g hf hfg hg) f.limOneMap :=
  (Function.Exact.iff_of_ladder_addEquiv C.limComparison A.limOneComparison B.limOneComparison
    (limOneComparison_comp_connecting f g hf hfg hg).symm
    (limOneComparison_comp_limOneMap f).symm).1
    (ModuleTower.exact_connecting_limOneMap _ _ _ _ _)

end Exact

end Tower

/-! ### The multiplication-by-`p` tower -/

/-- The tower `ℤ ← ℤ ← ℤ ← ⋯` whose transitions are multiplication by an integer `p`. It is
reducible, so that its terms are seen to be `ℤ`. -/
abbrev mulTower (p : ℤ) : Tower.{0} where
  obj _ := ℤ
  map _ := AddMonoidHom.mulRight p

@[simp]
theorem mulTower_map_apply (p : ℤ) (n : ℕ) (x : ℤ) : (mulTower p).map n x = x * p :=
  (rfl)

/-- The multiplication-by-`p` tower of abelian groups is isomorphic to the tower of `ℤ`-modules
`ModuleTower.multiplicationTower p`, by the identity in each degree. -/
def mulTowerIso (p : ℤ) : (mulTower p).toModuleFunctor ≅ ModuleTower.multiplicationTower p :=
  -- both towers have the terms `ℤ` and the transitions `x ↦ x * p`, so the identity commutes
  -- with the transitions in either direction
  have key (n : ℕ) (x : ℤ) :
      ((mulTower p).toModuleFunctor.map (homOfLE (n.le_add_right 1)).op).hom x =
        ((ModuleTower.multiplicationTower p).map (homOfLE (n.le_add_right 1)).op).hom x := by
    rw [← ModuleTower.transition_def, ← ModuleTower.transition_def]
    -- `x * p` and `LinearMap.toSpanSingleton ℤ ℤ p x = x • p` agree by definition on `ℤ`
    exact ((mulTower p).transition_toModuleFunctor_apply n x).trans
      (LinearMap.congr_fun (ModuleTower.multiplicationTower_transition p n) x).symm
  { hom := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) fun n ↦ ModuleCat.hom_ext <| LinearMap.ext (key n)
    inv := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) fun n ↦
      ModuleCat.hom_ext <| LinearMap.ext fun x ↦ (key n x).symm }

/-- The components of `mulTowerIso p` are the identity of `ℤ`. -/
@[simp]
theorem mulTowerIso_hom_app_apply (p : ℤ) (n : ℕ) (x : ℤ) :
    ((mulTowerIso p).hom.app (op n)).hom x = x :=
  -- the components of `NatTrans.ofOpSequence` are the given identities
  (rfl)

/-- The multiplication-by-`p` tower has vanishing limit for every integer `p` that is not a
unit. -/
theorem lim_mulTower_eq_bot {p : ℤ} (hp : ¬IsUnit p) : (mulTower p).lim = ⊥ := by
  have : Subsingleton (ModuleTower.multiplicationTower p).lim := by
    rw [ModuleTower.lim_multiplicationTower_eq_bot hp]
    infer_instance
  -- `lim` of the isomorphic tower of `ℤ`-modules vanishes
  have := ((ModuleTower.limEquivOfIso (mulTowerIso p)).injective.comp
    (mulTower p).limComparison.injective).subsingleton
  exact AddSubgroup.eq_bot_of_subsingleton _

variable (p : ℕ) [Fact p.Prime]

/-- **`lim¹` of the multiplication-by-`p` tower is `ℤ_[p] ⧸ ℤ`**, the isomorphism being induced
by the `p`-adic summation map `(aₙ) ↦ ∑ₙ pⁿ aₙ` (`limOneMulTowerEquiv_mk`). -/
def limOneMulTowerEquiv : (mulTower p).limOne ≃+ ℤ_[p] ⧸ (Int.castAddHom ℤ_[p]).range :=
  (mulTower p).limOneComparison.trans <|
    (ModuleTower.limOneEquivOfIso (mulTowerIso p)).toAddEquiv.trans
      (ModuleTower.limOneMultiplicationTowerEquiv p)

/-- `limOneMulTowerEquiv` sends the class in `lim¹` of a family `(aₙ)` to the class in
`ℤ_[p] ⧸ ℤ` of the convergent sum `∑ₙ pⁿ aₙ`. -/
@[simp]
theorem limOneMulTowerEquiv_mk (a : ℕ → ℤ) :
    limOneMulTowerEquiv p (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (∑' n, (p : ℤ_[p]) ^ n * (a n : ℤ_[p])) := by
  simp [limOneMulTowerEquiv, ModuleTower.padicSum_apply,
    ModuleTower.multiplicationTowerProductEquiv_apply, ModuleTower.productMap_apply]

/-- `lim¹` of the multiplication-by-`p` tower is nonzero. -/
instance nontrivial_limOne_mulTower : Nontrivial (mulTower p).limOne :=
  have := (ModuleTower.limOneMultiplicationTowerEquiv p).injective.nontrivial
  (limOneMulTowerEquiv p).symm.injective.nontrivial

/-- **The multiplication-by-`p` tower is not Mittag-Leffler**, since its `lim¹` does not
vanish. -/
theorem not_isMittagLeffler_mulTower : ¬(mulTower p).IsMittagLeffler := fun h ↦
  not_subsingleton _ ((mulTower p).subsingleton_limOne_of_isMittagLeffler h)

end CompactCoefficients

end TauCeti
