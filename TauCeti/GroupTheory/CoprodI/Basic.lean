/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Coprod.Basic
import TauCeti.Algebra.Group.ULift

/-!
# Isomorphisms of free products of monoids

A family of isomorphisms `M i ≃* N i` induces an isomorphism `CoprodI M ≃* CoprodI N` of the free
products, acting on each factor by the given isomorphism.  This is the indexed counterpart of
Mathlib's `MulEquiv.coprodCongr` for the free product of two monoids.  It is used to rewrite a
free product of fundamental groups one factor at a time, for instance to recognise the
fundamental group of a wedge of circles as a free group.  Reindexing a family along an equivalence
`e : ι ≃ κ` likewise induces `MulEquiv.coprodICongrLeft`.

The free product of a family of two monoids indexed by `Bool` or `Fin 2` is the binary free
product `Monoid.Coprod` of its two members, by the isomorphism matching the canonical inclusions.
For two monoids in possibly different universes, lifting both factors to `Type (max u v)` gives
the cross-universe isomorphism `Monoid.CoprodI.uliftBoolEquivCoprod`. Under the `Bool`-indexed
isomorphism, the homomorphisms induced by a pair of homomorphisms on the two members correspond,
so one of them is injective exactly when the other is.

A free product of trivial monoids is trivial; in particular, so is the free product of an empty
family. The free product of a family indexed by a type with a unique element is that single
monoid. A trivial member of a family indexed by `Option ι`, at the index `none`, can be dropped
from the free product; more generally, so can all the members outside a predicate when they are
trivial. Dropping them does not change whether homomorphisms on the factors, together with a
homomorphism on one more monoid, induce a bijection from the free product, which is how free product
decompositions with trivial factors are trimmed to their nontrivial factors.

## Main declarations

* `MulEquiv.coprodICongr`: the isomorphism of free products induced by a family of isomorphisms.
* `MulEquiv.coprodICongrLeft`: the isomorphism of free products induced by reindexing along an
  equivalence of index types.
* `Monoid.CoprodI.boolEquivCoprod`: `CoprodI M ≃* Coprod (M false) (M true)` for a family `M`
  indexed by `Bool`.
* `Monoid.CoprodI.coprodLift_injective_iff`: for a family `M` indexed by `Bool`, homomorphisms
  `f i : M i →* N` induce an injective homomorphism `Coprod (M false) (M true) →* N` if and only
  if they induce an injective homomorphism `CoprodI M →* N`.
* `Monoid.CoprodI.boolFactors`, `Monoid.CoprodI.uliftBoolEquivCoprod`: cross-universe
  comparison between `CoprodI (boolFactors M N)` and `Coprod M N`.
* `Monoid.CoprodI.finTwoEquivCoprod`, `Monoid.CoprodI.lift_comp_finTwoEquivCoprod_symm`:
  `CoprodI M ≃* Coprod (M 0) (M 1)` for a family `M` indexed by `Fin 2`, and lift transport.
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

variable {M}

/-- Casting an element of `M i` along an index equality `h : i = j` does not change its image
under `Monoid.CoprodI.of`. -/
@[simp]
theorem of_cast {i j : ι} (h : i = j) (x : M i) :
    of (M := M) (i := j) (cast (congrArg M h) x) = of (M := M) (i := i) x := by
  subst h
  rfl

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

/-- Reindexing the index type of an indexed free product along an equivalence `e : ι ≃ κ`
induces an isomorphism `CoprodI (fun i => M (e i)) ≃* CoprodI M`. -/
def coprodICongrLeft {ι κ : Type*} (M : κ → Type*) [∀ k, Monoid (M k)] (e : ι ≃ κ) :
    CoprodI (fun i => M (e i)) ≃* CoprodI M :=
  MonoidHom.toMulEquiv
    (CoprodI.lift fun i => CoprodI.of (i := e i))
    (CoprodI.lift fun k =>
      (CoprodI.of (M := fun i => M (e i)) (i := e.symm k)).comp
        (MulEquiv.cast (e.apply_symm_apply k).symm).toMonoidHom)
    (by ext i x; simp)
    (by ext k m; simp)

@[simp]
theorem coprodICongrLeft_apply_of {ι κ : Type*} (M : κ → Type*) [∀ k, Monoid (M k)]
    (e : ι ≃ κ) {i : ι} (m : M (e i)) :
    coprodICongrLeft M e (CoprodI.of (M := fun i => M (e i)) m) = CoprodI.of (i := e i) m :=
  CoprodI.lift_of _ _

/-- Evaluating the inverse of `coprodICongrLeft M e` on `CoprodI.of (i := k) m` casts `m` along
`e.apply_symm_apply k` into the factor at `e.symm k`. -/
@[simp]
theorem coprodICongrLeft_symm_apply_of {ι κ : Type*} (M : κ → Type*) [∀ k, Monoid (M k)]
    (e : ι ≃ κ) {k : κ} (m : M k) :
    (coprodICongrLeft M e).symm (CoprodI.of (i := k) m) =
      CoprodI.of (M := fun i => M (e i)) (i := e.symm k)
        (MulEquiv.cast (e.apply_symm_apply k).symm m) :=
  CoprodI.lift_of _ _

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

section ULiftBool

universe u v

-- Non-reducible (`def` rather than `abbrev`) so `simpNF` keeps `uliftBoolEquivCoprod_of_false` and
-- `uliftBoolEquivCoprod_of_true` applicable; making `boolFactors` reducible unfolds
-- `boolFactors M N false` to `ULift M` under `of`/`DFunLike.coe` and breaks `DiscrTree` lookup.
/-- The factors `M : Type u` and `N : Type v` lifted to `Type (max u v)` as a `Bool`-indexed
family: `false` gives `ULift.{v} M` and `true` gives `ULift.{u} N`. -/
@[expose]
def boolFactors (M : Type u) (N : Type v) : Bool → Type (max u v)
  | false => ULift.{v} M
  | true => ULift.{u} N

instance instMonoidBoolFactors (M : Type u) (N : Type v) [Monoid M] [Monoid N] :
    ∀ b, Monoid (boolFactors M N b)
  | false => inferInstanceAs (Monoid (ULift M))
  | true => inferInstanceAs (Monoid (ULift N))

-- Set `toMonoid := instMonoidBoolFactors G H b` explicitly rather than matching on `b` at the
-- top level with `inferInstanceAs (Group (ULift _))`, so `(instGroupBoolFactors G H b).toMonoid`
-- is definitionally `instMonoidBoolFactors G H b` for symbolic `b : Bool` (avoiding a `Monoid`
-- instance diamond on `CoprodI (boolFactors G H)`).
instance instGroupBoolFactors (G : Type u) (H : Type v) [Group G] [Group H] :
    ∀ b, Group (boolFactors G H b) := fun b =>
  { toMonoid := instMonoidBoolFactors G H b
    inv := match b with
      | false => (inferInstance : Group (ULift G)).inv
      | true => (inferInstance : Group (ULift H)).inv
    div := match b with
      | false => (inferInstance : Group (ULift G)).div
      | true => (inferInstance : Group (ULift H)).div
    div_eq_mul_inv := by
      cases b
      · exact (inferInstance : Group (ULift G)).div_eq_mul_inv
      · exact (inferInstance : Group (ULift H)).div_eq_mul_inv
    zpow := match b with
      | false => (inferInstance : Group (ULift G)).zpow
      | true => (inferInstance : Group (ULift H)).zpow
    zpow_zero' := by cases b <;> exact (inferInstance : Group (ULift _)).zpow_zero'
    zpow_succ' := by cases b <;> exact (inferInstance : Group (ULift _)).zpow_succ'
    zpow_neg' := by cases b <;> exact (inferInstance : Group (ULift _)).zpow_neg'
    inv_mul_cancel := by
      cases b
      · exact (inferInstance : Group (ULift G)).inv_mul_cancel
      · exact (inferInstance : Group (ULift H)).inv_mul_cancel }

/-- Cross-universe comparison between the indexed free product over `Bool` of `ULift`ed factors
and the binary free product `M ∗ N`. -/
def uliftBoolEquivCoprod (M : Type u) (N : Type v) [Monoid M] [Monoid N] :
    CoprodI (boolFactors M N) ≃* Coprod M N :=
  (boolEquivCoprod (boolFactors M N)).trans
    ((MulEquiv.ulift : boolFactors M N false ≃* M).coprodCongr
      (MulEquiv.ulift : boolFactors M N true ≃* N))

/-- `uliftBoolEquivCoprod` maps the `false` factor inclusion to `Coprod.inl`. -/
@[simp]
theorem uliftBoolEquivCoprod_of_false {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (x : ULift.{v} M) :
    uliftBoolEquivCoprod M N (of (i := false) x) = Coprod.inl x.down :=
  congrArg ((MulEquiv.ulift : boolFactors M N false ≃* M).coprodCongr
      (MulEquiv.ulift : boolFactors M N true ≃* N))
    (boolEquivCoprod_of_false (M := boolFactors M N) x)

/-- `uliftBoolEquivCoprod` maps the `true` factor inclusion to `Coprod.inr`. -/
@[simp]
theorem uliftBoolEquivCoprod_of_true {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (y : ULift.{u} N) :
    uliftBoolEquivCoprod M N (of (i := true) y) = Coprod.inr y.down :=
  congrArg ((MulEquiv.ulift : boolFactors M N false ≃* M).coprodCongr
      (MulEquiv.ulift : boolFactors M N true ≃* N))
    (boolEquivCoprod_of_true (M := boolFactors M N) y)

/-- The inverse of `uliftBoolEquivCoprod` maps `Coprod.inl x` to the `false` factor
inclusion. -/
@[simp]
theorem uliftBoolEquivCoprod_symm_inl {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (x : M) :
    (uliftBoolEquivCoprod M N).symm (Coprod.inl x) =
      of (i := false) (MulEquiv.ulift.symm x) :=
  boolEquivCoprod_symm_inl (M := boolFactors M N) (MulEquiv.ulift.symm x)

/-- The inverse of `uliftBoolEquivCoprod` maps `Coprod.inr y` to the `true` factor
inclusion. -/
@[simp]
theorem uliftBoolEquivCoprod_symm_inr {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (y : N) :
    (uliftBoolEquivCoprod M N).symm (Coprod.inr y) =
      of (i := true) (MulEquiv.ulift.symm y) :=
  boolEquivCoprod_symm_inr (M := boolFactors M N) (MulEquiv.ulift.symm y)

/-- The inverse of `uliftBoolEquivCoprod` maps the product of a word `L : List (M ⊕ N)` to the
product of the lifted factor inclusions along `L`. -/
@[simp]
theorem uliftBoolEquivCoprod_symm_mk_ofList {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (L : List (M ⊕ N)) :
    (uliftBoolEquivCoprod M N).symm (Coprod.mk (FreeMonoid.ofList L)) =
      (L.map (Sum.elim (fun m => of (i := false) (MulEquiv.ulift.symm m))
        (fun n => of (i := true) (MulEquiv.ulift.symm n)))).prod := by
  induction L with
  | nil => simp
  | cons s L ih =>
    cases s <;> simp [FreeMonoid.ofList_cons, ih]

end ULiftBool

section FinTwo

variable (M : Fin 2 → Type*) [∀ i, Monoid (M i)]

/-- The free product of a family of monoids indexed by `Fin 2` is the free product of its two
members: the inclusion of `M 0` corresponds to `Monoid.Coprod.inl` and that of `M 1` to
`Monoid.Coprod.inr`. -/
def finTwoEquivCoprod : CoprodI M ≃* Coprod (M 0) (M 1) :=
  (MulEquiv.coprodICongrLeft M finTwoEquiv.symm).symm.trans
    (boolEquivCoprod fun b => M (finTwoEquiv.symm b))

variable {M}

/-- The inverse of `finTwoEquivCoprod` maps `Coprod.inl` to the canonical inclusion of `M 0`. -/
@[simp]
theorem finTwoEquivCoprod_symm_inl (x : M 0) :
    (finTwoEquivCoprod M).symm (Coprod.inl x) = of x :=
  (congrArg (MulEquiv.coprodICongrLeft M finTwoEquiv.symm)
    (boolEquivCoprod_symm_inl (M := fun b => M (finTwoEquiv.symm b)) x)).trans
    (MulEquiv.coprodICongrLeft_apply_of M finTwoEquiv.symm (i := false) x)

/-- The inverse of `finTwoEquivCoprod` maps `Coprod.inr` to the canonical inclusion of `M 1`. -/
@[simp]
theorem finTwoEquivCoprod_symm_inr (x : M 1) :
    (finTwoEquivCoprod M).symm (Coprod.inr x) = of x :=
  (congrArg (MulEquiv.coprodICongrLeft M finTwoEquiv.symm)
    (boolEquivCoprod_symm_inr (M := fun b => M (finTwoEquiv.symm b)) x)).trans
    (MulEquiv.coprodICongrLeft_apply_of M finTwoEquiv.symm (i := true) x)

/-- `finTwoEquivCoprod` maps the canonical inclusion of `M 0` to `Coprod.inl`. -/
@[simp]
theorem finTwoEquivCoprod_of_zero (x : M 0) : finTwoEquivCoprod M (of x) = Coprod.inl x := by
  rw [← finTwoEquivCoprod_symm_inl, MulEquiv.apply_symm_apply]

/-- `finTwoEquivCoprod` maps the canonical inclusion of `M 1` to `Coprod.inr`. -/
@[simp]
theorem finTwoEquivCoprod_of_one (x : M 1) : finTwoEquivCoprod M (of x) = Coprod.inr x := by
  rw [← finTwoEquivCoprod_symm_inr, MulEquiv.apply_symm_apply]

variable {N : Type*} [Monoid N] (f : ∀ i, M i →* N)

/-- Under `finTwoEquivCoprod`, the homomorphism `CoprodI M →* N` induced by homomorphisms `f i` on
the two factors is `Monoid.Coprod.lift (f 0) (f 1)`. -/
@[simp]
theorem lift_comp_finTwoEquivCoprod_symm :
    (lift f).comp ((finTwoEquivCoprod M).symm : Coprod (M 0) (M 1) →* CoprodI M) =
      Coprod.lift (f 0) (f 1) := by
  ext <;> simp

end FinTwo

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
      (MulEquiv.coprodCongr ψ (MulEquiv.refl H)).toMonoidHom := by
    ext i m
    · simp only [MonoidHom.comp_apply, lift_apply_inl, MulEquiv.coe_toMonoidHom,
        MulEquiv.coprodCongr_apply, map_apply_inl]
      exact (DFunLike.congr_fun (CoprodI.lift_comp_subtypeEquivOfSubsingleton h f) _).symm
    · simp
  rw [key, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.Bijective.of_comp_iff _ (MulEquiv.bijective _)]

end Monoid.Coprod
