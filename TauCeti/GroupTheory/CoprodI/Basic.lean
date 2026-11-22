/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI

/-!
# Isomorphisms of free products of monoids

A family of isomorphisms `M i ≃* N i` induces an isomorphism `CoprodI M ≃* CoprodI N` of the free
products, acting on each factor by the given isomorphism.  This is the indexed counterpart of
Mathlib's `MulEquiv.coprodCongr` for the free product of two monoids.  It is used to rewrite a
free product of fundamental groups one factor at a time, for instance to recognise the
fundamental group of a wedge of circles as a free group.

The free product of a family of two monoids indexed by `Bool` or `Fin 2` is the binary free
product `Monoid.Coprod` of its two members, by the isomorphism matching the canonical inclusions.
Under the `Bool` isomorphism, the homomorphisms induced by a pair of homomorphisms on the two
members correspond, so one of them is injective exactly when the other is.  Conversely, for any
two monoids or groups `M` and `N` in possibly different universes, `Monoid.Coprod.toCoprodI`
identifies `M ∗ N` with the indexed free product of the universe-lifted `Bool` family
`Monoid.Coprod.Factors M N`.

A free product of trivial monoids is trivial; in particular, so is the free product of an empty
family. The free product of a family indexed by a type with a unique element is that single
monoid. A trivial member of a family indexed by `Option ι`, at the index `none`, can be dropped
from the free product.

## Main declarations

* `MulEquiv.coprodICongr`: the isomorphism of free products induced by a family of isomorphisms.
* `MulEquiv.coprodICongrLeft`: reindexing an indexed free product along an equivalence of index
  types.
* `Monoid.CoprodI.boolEquivCoprod`: `CoprodI M ≃* Coprod (M false) (M true)` for a family `M`
  indexed by `Bool`.
* `Monoid.CoprodI.coprodLift_injective_iff`: for a family `M` indexed by `Bool`, homomorphisms
  `f i : M i →* N` induce an injective homomorphism `Coprod (M false) (M true) →* N` if and only
  if they induce an injective homomorphism `CoprodI M →* N`.
* `Monoid.Coprod.Factors`, `Monoid.Coprod.toCoprodI`: universe-lifted `Bool`-indexed family for
  `M ∗ N` and the comparison isomorphism `M ∗ N ≃* CoprodI (Monoid.Coprod.Factors M N)`.
* `Monoid.CoprodI.finTwoEquivCoprod`: `CoprodI M ≃* Coprod (M 0) (M 1)` for a family `M` indexed
  by `Fin 2`.
* `Monoid.CoprodI.instUnique`: the free product of a family of trivial monoids is trivial.
* `Monoid.CoprodI.instUniqueOfIsEmpty`: the free product of an empty family is trivial.
* `MulEquiv.coprodIUnique`: the free product of a family indexed by a type with a unique element
  is isomorphic to the monoid at the single index.
* `Monoid.CoprodI.optionEquivOfSubsingleton`: `CoprodI M ≃* CoprodI fun i => M (some i)` for a
  family `M` indexed by `Option ι` whose member at `none` is trivial.
-/

public section

open Monoid

namespace Monoid.CoprodI

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]

/-- The free product of a family of trivial monoids is trivial. -/
instance instUnique [∀ i, Subsingleton (M i)] : Unique (CoprodI M) where
  default := 1
  uniq x := DFunLike.congr_fun (ext_hom (.id _) 1 fun _ ↦ Subsingleton.elim _ _) x

/-- The free product of an empty family of monoids is trivial. -/
instance instUniqueOfIsEmpty [IsEmpty ι] : Unique (CoprodI M) :=
  have : ∀ i, Subsingleton (M i) := isEmptyElim
  inferInstance

end Monoid.CoprodI

namespace MulEquiv

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- A family of isomorphisms of monoids `M i ≃* N i` induces an isomorphism of their free
products, acting on the `i`-th factor by the `i`-th isomorphism. -/
def coprodICongr (e : ∀ i, M i ≃* N i) : CoprodI M ≃* CoprodI N :=
  MonoidHom.toMulEquiv (CoprodI.lift fun i => CoprodI.of.comp (e i).toMonoidHom)
    (CoprodI.lift fun i => CoprodI.of.comp (e i).symm.toMonoidHom)
    (by ext; simp) (by ext; simp)

@[simp]
theorem coprodICongr_apply_of (e : ∀ i, M i ≃* N i) {i : ι} (m : M i) :
    coprodICongr e (CoprodI.of m) = CoprodI.of (e i m) :=
  CoprodI.lift_of _ _

@[simp]
theorem coprodICongr_symm (e : ∀ i, M i ≃* N i) :
    (coprodICongr e).symm = coprodICongr fun i => (e i).symm :=
  (rfl)

private theorem of_cast (M : ι → Type*) [∀ i, Monoid (M i)] {i j : ι} (h : i = j) (m : M i) :
    CoprodI.of (i := j) (MulEquiv.cast (M := M) h m) = CoprodI.of (i := i) m := by
  subst h; simp

private theorem of_comp_cast {ι' : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]
    (f : ι' → ι) {a b : ι'} (hab : a = b) (h : f b = f a) (m : M (f b)) :
    CoprodI.of (M := fun x => M (f x)) (i := a) (MulEquiv.cast (M := M) h m) =
      CoprodI.of (M := fun x => M (f x)) (i := b) m := by
  subst hab; simp

/-- Reindexing an indexed free product along an equivalence `e : ι' ≃ ι` of index types. -/
def coprodICongrLeft (M : ι → Type*) [∀ i, Monoid (M i)] {ι' : Type*} (e : ι' ≃ ι) :
    CoprodI (fun i' => M (e i')) ≃* CoprodI M :=
  MonoidHom.toMulEquiv
    (CoprodI.lift fun i' => CoprodI.of (i := e i'))
    (CoprodI.lift fun i =>
      CoprodI.of.comp (MulEquiv.cast (M := M) (e.apply_symm_apply i).symm).toMonoidHom)
    (CoprodI.ext_hom _ _ fun i' => MonoidHom.ext fun m => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, CoprodI.lift_of]
      exact of_comp_cast M e (e.symm_apply_apply i') _ m)
    (CoprodI.ext_hom _ _ fun i => MonoidHom.ext fun m => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, CoprodI.lift_of]
      exact of_cast M (e.apply_symm_apply i).symm m)

@[simp]
theorem coprodICongrLeft_of (M : ι → Type*) [∀ i, Monoid (M i)] {ι' : Type*} (e : ι' ≃ ι)
    {i' : ι'} (m : M (e i')) :
    coprodICongrLeft M e (CoprodI.of (i := i') m) = CoprodI.of (i := e i') m :=
  CoprodI.lift_of _ _

theorem coprodICongrLeft_symm_of (M : ι → Type*) [∀ i, Monoid (M i)] {ι' : Type*} (e : ι' ≃ ι)
    {i' : ι'} (m : M (e i')) :
    (coprodICongrLeft M e).symm (CoprodI.of (i := e i') m) = CoprodI.of (i := i') m :=
  (coprodICongrLeft M e).symm_apply_eq.mpr (coprodICongrLeft_of M e m).symm

variable (M) [Unique ι]

/-- The free product of a family of monoids indexed by a type with a unique element is
isomorphic to the monoid at the single index. -/
def coprodIUnique : CoprodI M ≃* M default :=
  MonoidHom.toMulEquiv (CoprodI.lift <| Pi.mulSingle default (.id _)) CoprodI.of
    (CoprodI.ext_hom _ _ fun i => by obtain rfl := Unique.eq_default i; ext; simp)
    (by ext; simp)

@[simp]
theorem coprodIUnique_apply_of (m : M default) : coprodIUnique M (CoprodI.of m) = m := by
  simp [coprodIUnique]

@[simp]
theorem coprodIUnique_symm_apply (m : M default) : (coprodIUnique M).symm m = CoprodI.of m :=
  (rfl)

end MulEquiv

namespace Monoid.CoprodI

section Bool

variable (M : Bool → Type*) [∀ i, Monoid (M i)]

/-- The free product of a family of monoids indexed by `Bool` is the free product of its two
members: the inclusion of `M false` corresponds to `Monoid.Coprod.inl` and that of `M true` to
`Monoid.Coprod.inr`. -/
def boolEquivCoprod : CoprodI M ≃* Coprod (M false) (M true) :=
  MonoidHom.toMulEquiv
    (lift fun
      | false => Coprod.inl
      | true => Coprod.inr)
    (Coprod.lift (of (i := false)) (of (i := true)))
    (by ext i x; cases i <;> simp) (by ext <;> simp)

variable {M}

@[simp]
theorem boolEquivCoprod_of_false (x : M false) : boolEquivCoprod M (of x) = Coprod.inl x :=
  lift_of _ _

@[simp]
theorem boolEquivCoprod_of_true (x : M true) : boolEquivCoprod M (of x) = Coprod.inr x :=
  lift_of _ _

@[simp]
theorem boolEquivCoprod_symm_inl (x : M false) : (boolEquivCoprod M).symm (Coprod.inl x) = of x :=
  Coprod.lift_apply_inl (of (i := false)) (of (i := true)) x

@[simp]
theorem boolEquivCoprod_symm_inr (x : M true) : (boolEquivCoprod M).symm (Coprod.inr x) = of x :=
  Coprod.lift_apply_inr (of (i := false)) (of (i := true)) x

variable {N : Type*} [Monoid N] (f : ∀ i, M i →* N)

/-- Under `boolEquivCoprod`, the homomorphism `CoprodI M →* N` induced by homomorphisms `f i` on
the two factors is `Monoid.Coprod.lift (f false) (f true)`. -/
@[simp]
theorem lift_comp_boolEquivCoprod_symm :
    (lift f).comp ((boolEquivCoprod M).symm : Coprod (M false) (M true) →* CoprodI M) =
      Coprod.lift (f false) (f true) := by
  ext <;> simp

@[simp]
theorem lift_boolEquivCoprod_symm (x : Coprod (M false) (M true)) :
    lift f ((boolEquivCoprod M).symm x) = Coprod.lift (f false) (f true) x :=
  DFunLike.congr_fun (lift_comp_boolEquivCoprod_symm f) x

/-- The homomorphism `Monoid.Coprod (M false) (M true) →* N` induced by homomorphisms `f i` on the
two factors is injective if and only if the homomorphism `CoprodI M →* N` they induce is. -/
theorem coprodLift_injective_iff :
    Function.Injective (Coprod.lift (f false) (f true)) ↔ Function.Injective (lift f) := by
  rw [← lift_comp_boolEquivCoprod_symm, MonoidHom.coe_comp, MonoidHom.coe_ofClass]
  exact EquivLike.injective_comp _ _

end Bool

section FinTwo

variable (M : Fin 2 → Type*) [∀ i, Monoid (M i)]

/-- The free product of a family of two monoids indexed by `Fin 2` is the free product of its two
members: the inclusion of `M 0` corresponds to `Monoid.Coprod.inl` and that of `M 1` to
`Monoid.Coprod.inr`. -/
def finTwoEquivCoprod : CoprodI M ≃* Coprod (M 0) (M 1) :=
  (MulEquiv.coprodICongrLeft M finTwoEquiv.symm).symm.trans
    (boolEquivCoprod fun b => M (finTwoEquiv.symm b))

variable {M}

@[simp]
theorem finTwoEquivCoprod_of_zero (x : M 0) : finTwoEquivCoprod M (of x) = Coprod.inl x :=
  (congrArg (boolEquivCoprod fun b => M (finTwoEquiv.symm b))
    (MulEquiv.coprodICongrLeft_symm_of M finTwoEquiv.symm (i' := false) x)).trans
    (boolEquivCoprod_of_false (M := fun b => M (finTwoEquiv.symm b)) x)

@[simp]
theorem finTwoEquivCoprod_of_one (x : M 1) : finTwoEquivCoprod M (of x) = Coprod.inr x :=
  (congrArg (boolEquivCoprod fun b => M (finTwoEquiv.symm b))
    (MulEquiv.coprodICongrLeft_symm_of M finTwoEquiv.symm (i' := true) x)).trans
    (boolEquivCoprod_of_true (M := fun b => M (finTwoEquiv.symm b)) x)

@[simp]
theorem finTwoEquivCoprod_symm_inl (x : M 0) : (finTwoEquivCoprod M).symm (Coprod.inl x) = of x :=
  (finTwoEquivCoprod M).symm_apply_eq.mpr (finTwoEquivCoprod_of_zero x).symm

@[simp]
theorem finTwoEquivCoprod_symm_inr (x : M 1) : (finTwoEquivCoprod M).symm (Coprod.inr x) = of x :=
  (finTwoEquivCoprod M).symm_apply_eq.mpr (finTwoEquivCoprod_of_one x).symm

end FinTwo

section Option

variable {ι : Type*} (M : Option ι → Type*) [∀ o, Monoid (M o)] [Subsingleton (M none)]

/-- The free product of a family of monoids indexed by `Option ι` whose member at `none` is
trivial is the free product of its members at `some i`: the factor at `none` goes to `1` and the
factor at `some i` to the factor at `i`. -/
def optionEquivOfSubsingleton : CoprodI M ≃* CoprodI fun i => M (some i) :=
  MonoidHom.toMulEquiv
    (lift fun
      | none => 1
      | some i => of (M := fun j => M (some j)) (i := i))
    (lift fun i => of (i := some i))
    (by
      ext (_ | _) m
      · simp [Subsingleton.elim m 1]
      · simp)
    (by ext; simp)

variable {M}

@[simp]
theorem optionEquivOfSubsingleton_of_none (m : M none) :
    optionEquivOfSubsingleton M (of m) = 1 := by
  simp [Subsingleton.elim m 1]

@[simp]
theorem optionEquivOfSubsingleton_of_some {i : ι} (m : M (some i)) :
    optionEquivOfSubsingleton M (of m) = of (i := i) m :=
  lift_of ..

@[simp]
theorem optionEquivOfSubsingleton_symm_of {i : ι} (m : M (some i)) :
    (optionEquivOfSubsingleton M).symm (of (i := i) m) = of m :=
  lift_of ..

end Option

end Monoid.CoprodI

namespace Monoid.Coprod

universe u v

/-- The factors of `M ∗ N` as a family indexed by `Bool`, lifted to a common universe: `false`
gives `M` and `true` gives `N`. -/
@[expose] def Factors (M : Type u) (N : Type v) : Bool → Type max u v
  | false => ULift.{v} M
  | true => ULift.{u} N

instance instMonoidFactors (M : Type u) (N : Type v) [Monoid M] [Monoid N] :
    ∀ b, Monoid (Factors M N b)
  | false => inferInstanceAs (Monoid (ULift M))
  | true => inferInstanceAs (Monoid (ULift N))

instance instGroupFactors (G : Type u) (H : Type v) [Group G] [Group H] (b : Bool) :
    Group (Factors G H b) :=
  let g : Group (Factors G H b) :=
    Bool.rec (motive := fun b => Group (Factors G H b))
      (inferInstance : Group (ULift.{v} G)) (inferInstance : Group (ULift.{u} H)) b
  { toMonoid := instMonoidFactors G H b
    inv := g.inv
    div := g.div
    zpow := g.zpow
    div_eq_mul_inv := by cases b <;> exact div_eq_mul_inv
    zpow_zero' := by cases b <;> exact zpow_zero
    zpow_succ' := by cases b <;> exact DivInvMonoid.zpow_succ'
    zpow_neg' := by cases b <;> exact DivInvMonoid.zpow_neg'
    inv_mul_cancel := by cases b <;> exact inv_mul_cancel }

section Monoid

variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]

/-- The comparison isomorphism from the free product `M ∗ N` of two monoids (possibly in different
universes) to the indexed free product of the family `Factors M N`. -/
def toCoprodI : M ∗ N ≃* CoprodI (Factors M N) :=
  (MulEquiv.coprodCongr MulEquiv.ulift.symm MulEquiv.ulift.symm).trans
    (CoprodI.boolEquivCoprod (Factors M N)).symm

@[simp]
theorem toCoprodI_inl (m : M) :
    toCoprodI (inl m : M ∗ N) = CoprodI.of (i := false) (ULift.up m) := by
  simp [toCoprodI]
  rfl

@[simp]
theorem toCoprodI_inr (n : N) :
    toCoprodI (inr n : M ∗ N) = CoprodI.of (i := true) (ULift.up n) := by
  simp [toCoprodI]
  rfl

@[simp]
theorem toCoprodI_symm_of_false (m : Factors M N false) :
    toCoprodI.symm (CoprodI.of (i := false) m) = inl m.down := by
  simp [toCoprodI]
  rfl

@[simp]
theorem toCoprodI_symm_of_true (n : Factors M N true) :
    toCoprodI.symm (CoprodI.of (i := true) n) = inr n.down := by
  simp [toCoprodI]
  rfl

end Monoid

end Monoid.Coprod
