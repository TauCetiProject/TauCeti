/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Isomorphisms of free products of monoids

A family of isomorphisms `M i ≃* N i` induces an isomorphism `CoprodI M ≃* CoprodI N` of the free
products, acting on each factor by the given isomorphism.  This is the indexed counterpart of
Mathlib's `MulEquiv.coprodCongr` for the free product of two monoids.  It is used to rewrite a
free product of fundamental groups one factor at a time, for instance to recognise the
fundamental group of a wedge of circles as a free group.

The free product of a family of two monoids indexed by `Bool` is the binary free product
`Monoid.Coprod` of its two members, by the isomorphism matching the canonical inclusions. Under it,
the homomorphisms induced by a pair of homomorphisms on the two members correspond, so one of them
is injective exactly when the other is.

A free product of trivial monoids is trivial; in particular, so is the free product of an empty
family. The free product of a family indexed by a type with a unique element is that single
monoid. A trivial member of a family indexed by `Option ι`, at the index `none`, can be dropped
from the free product; more generally, so can all the members outside a predicate when they are
trivial. Dropping them does not change whether homomorphisms on the factors, together with a
homomorphism on one more monoid, induce a bijection from the free product, which is how free product
decompositions with trivial factors are trimmed to their nontrivial factors.

## Main declarations

* `MulEquiv.coprodICongr`: the isomorphism of free products induced by a family of isomorphisms.
* `Monoid.CoprodI.boolEquivCoprod`: `CoprodI M ≃* Coprod (M false) (M true)` for a family `M`
  indexed by `Bool`.
* `Monoid.CoprodI.coprodLift_injective_iff`: for a family `M` indexed by `Bool`, homomorphisms
  `f i : M i →* N` induce an injective homomorphism `Coprod (M false) (M true) →* N` if and only
  if they induce an injective homomorphism `CoprodI M →* N`.
* `Monoid.CoprodI.instUnique`: the free product of a family of trivial monoids is trivial.
* `Monoid.CoprodI.instUniqueOfIsEmpty`: the free product of an empty family is trivial.
* `MulEquiv.coprodIUnique`: the free product of a family indexed by a type with a unique element
  is isomorphic to the monoid at the single index.
* `Monoid.CoprodI.optionEquivOfSubsingleton`: `CoprodI M ≃* CoprodI fun i => M (some i)` for a
  family `M` indexed by `Option ι` whose member at `none` is trivial.
* `Monoid.CoprodI.subtypeEquivOfSubsingleton`: `CoprodI M ≃* CoprodI fun i : {i // p i} => M i`
  for a family `M` whose members outside `p` are trivial.
* `Monoid.Coprod.lift_coprodI_lift_subtype_bijective_iff`: such trivial members can be dropped from
  a bijective homomorphism `(∗ᵢ Mᵢ) ∗ H → N`.
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

end Monoid.CoprodI

namespace Monoid.CoprodI

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

end Monoid.CoprodI

namespace Monoid.CoprodI

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)] (p : ι → Prop)

open scoped Classical in
/-- The free product of a family of monoids whose members outside a predicate `p` are trivial is
the free product of its members satisfying `p`: a factor outside `p` goes to `1` and the factor at
`i` with `p i` to the factor at `⟨i, _⟩`. -/
noncomputable def subtypeEquivOfSubsingleton (h : ∀ i, ¬p i → Subsingleton (M i)) :
    CoprodI M ≃* CoprodI fun i : {i // p i} => M i :=
  MonoidHom.toMulEquiv
    (lift fun i => if hi : p i then of (M := fun i : {i // p i} => M i) (i := ⟨i, hi⟩) else 1)
    (lift fun i => of (i := i.val))
    (by
      ext i m
      by_cases hi : p i
      · simp [hi]
      · have := h i hi
        simp [Subsingleton.elim m 1])
    (by ext i m; simp [i.property])

variable {M p} {h : ∀ i, ¬p i → Subsingleton (M i)}

@[simp]
theorem subtypeEquivOfSubsingleton_of {i : ι} (hi : p i) (m : M i) :
    subtypeEquivOfSubsingleton M p h (of m) =
      of (M := fun i : {i // p i} => M i) (i := ⟨i, hi⟩) m := by
  simp [subtypeEquivOfSubsingleton, hi]

@[simp]
theorem subtypeEquivOfSubsingleton_of_not {i : ι} (hi : ¬p i) (m : M i) :
    subtypeEquivOfSubsingleton M p h (of m) = 1 := by
  have := h i hi
  simp [Subsingleton.elim m 1]

@[simp]
theorem subtypeEquivOfSubsingleton_symm_of {i : {i // p i}} (m : M i) :
    (subtypeEquivOfSubsingleton M p h).symm (of m) = of (i := i.val) m := by
  simp [subtypeEquivOfSubsingleton]

variable (h) in
/-- Under `subtypeEquivOfSubsingleton`, the homomorphism `CoprodI M →* N` induced by homomorphisms
`f i` on the factors is induced by the `f i` with `p i`. -/
@[simp]
theorem lift_comp_subtypeEquivOfSubsingleton {N : Type*} [Monoid N] (f : ∀ i, M i →* N) :
    (lift fun i : {i // p i} => f i).comp (subtypeEquivOfSubsingleton M p h : _ →* _) = lift f := by
  ext i m
  by_cases hi : p i
  · simp [hi]
  · have := h i hi
    simp [Subsingleton.elim m 1]

end Monoid.CoprodI

namespace Monoid.Coprod

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {p : ι → Prop} {H N : Type*} [Monoid H]
  [Monoid N]

/-- If the members of a family of monoids outside a predicate `p` are trivial, then homomorphisms
`f i : M i →* N` and `F : H →* N` induce a bijection `(∗ᵢ Mᵢ) ∗ H → N` exactly when the `f i` with
`p i` and `F` do. -/
theorem lift_coprodI_lift_subtype_bijective_iff (h : ∀ i, ¬p i → Subsingleton (M i))
    (f : ∀ i, M i →* N) (F : H →* N) :
    Function.Bijective (lift (CoprodI.lift fun i : {i // p i} => f i) F) ↔
      Function.Bijective (lift (CoprodI.lift f) F) := by
  let ψ := CoprodI.subtypeEquivOfSubsingleton M p h
  have key : lift (CoprodI.lift f) F = (lift (CoprodI.lift fun i : {i // p i} => f i) F).comp
      (map ψ.toMonoidHom (MonoidHom.id H)) := by
    ext i m
    · by_cases hi : p i
      · simp [ψ, hi]
      · have := h i hi
        simp [ψ, Subsingleton.elim m 1]
    · simp
  have hmap : Function.Bijective (map ψ.toMonoidHom (MonoidHom.id H)) :=
    Function.bijective_iff_has_inverse.2 ⟨map ψ.symm.toMonoidHom (MonoidHom.id H),
      fun x => by induction x using induction_on <;> simp_all,
      fun x => by induction x using induction_on <;> simp_all⟩
  rw [key, MonoidHom.coe_comp, Function.Bijective.of_comp_iff _ hmap]

end Monoid.Coprod
