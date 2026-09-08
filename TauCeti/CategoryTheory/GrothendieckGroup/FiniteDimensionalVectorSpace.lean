/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall

/-!
# Grothendieck groups of finite-dimensional vector spaces

For a division ring `k`, `FGModuleCat k` is Mathlib's category of finite-dimensional left
`k`-vector spaces.
Every object is projective, so every short exact sequence in this category splits. Dimension is
therefore additive for both split and abelian Grothendieck groups.

This file computes both groups. The dimension homomorphisms are upgraded to the additive
equivalences `TauCeti.SplitK0.finrankEquiv` and `TauCeti.AbelianK0.finrankEquiv`. Every
one-dimensional space has class a generator, and every object class is its dimension times that
generator. The corresponding formulas for arbitrary additive invariants record the universal
property in this concrete example. The equivalences assume `Small.{v} k`, ensuring that the
carrier universe `v` contains a model of the one-dimensional space; this is automatic when the
scalars and carriers live in the same universe.

## Main results

* `FGModuleCat.projective`: every finite-dimensional vector space is projective.
* `FGModuleCat.nonempty_splitting_of_shortExact`: every short exact sequence of
  finite-dimensional vector spaces splits.
* `TauCeti.SplitK0.finrankEquiv`: split `K₀` of finite-dimensional vector spaces is `ℤ`.
* `TauCeti.AbelianK0.finrankEquiv`: abelian `K₀` of finite-dimensional vector spaces is `ℤ`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Sections 5--6.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe u v

section Dimension

variable (k : Type u) [DivisionRing k]

private noncomputable def line [Small.{v} k] : FGModuleCat.{v} k :=
  FGModuleCat.of k (Shrink.{v} k)

@[simp] private theorem finrank_line [Small.{v} k] : Module.finrank k (line k) = 1 :=
  (Shrink.linearEquiv k k).finrank_eq.trans (Module.finrank_self k)

private noncomputable def standard (L : FGModuleCat.{v} k) : ℕ → FGModuleCat.{v} k
  | 0 => 0
  | n + 1 => L ⊞ standard L n

private theorem finrank_standard (L : FGModuleCat.{v} k) (hL : Module.finrank k L = 1)
    (n : ℕ) : Module.finrank k (standard k L n) = n := by
  induction n with
  | zero =>
      rw [standard]
      let F := forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)
      let _ : Subsingleton ((0 : FGModuleCat.{v} k) : Type v) :=
        ModuleCat.subsingleton_of_isZero (F.map_isZero (isZero_zero _))
      exact Module.finrank_zero_of_subsingleton
  | succ n ih =>
      rw [standard, FGModuleCat.finrank_biprod, hL, ih, Nat.one_add]

private noncomputable def isoStandard (L : FGModuleCat.{v} k) (hL : Module.finrank k L = 1)
    (X : FGModuleCat.{v} k) : X ≅ standard k L (Module.finrank k X) := by
  let e : X ≃ₗ[k] standard k L (Module.finrank k X) :=
    LinearEquiv.ofFinrankEq X (standard k L (Module.finrank k X))
      (finrank_standard k L hL _).symm
  exact e.toFGModuleCatIso

private theorem class_standard
    {G : Type*} [AddCommGroup G] (c : FGModuleCat.{v} k → G)
    (map_zero : c 0 = 0) (map_biprod : ∀ X Y, c (X ⊞ Y) = c X + c Y) (n : ℕ) :
    ∀ L : FGModuleCat.{v} k, c (standard k L n) = n • c L := by
  intro L
  induction n with
  | zero => simpa [standard] using map_zero
  | succ n ih =>
      rw [standard, map_biprod, ih, succ_nsmul]
      exact add_comm _ _

private theorem class_eq_finrank_nsmul
    {G : Type*} [AddCommGroup G] (c : FGModuleCat.{v} k → G)
    (map_iso : ∀ ⦃X Y⦄, (X ≅ Y) → c X = c Y) (map_zero : c 0 = 0)
    (map_biprod : ∀ X Y, c (X ⊞ Y) = c X + c Y) (L X : FGModuleCat.{v} k)
    (hL : Module.finrank k L = 1) : c X = Module.finrank k X • c L := by
  rw [map_iso (isoStandard k L hL X), class_standard k c map_zero map_biprod]

end Dimension

namespace SplitK0

variable (k : Type u) [DivisionRing k]

private noncomputable def finrankInvariant : AdditiveInvariant (FGModuleCat.{v} k) ℤ where
  obj X := Module.finrank k X
  map_iso {_ _} e := congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv e).finrank_eq
  map_biprod X Y := congrArg Int.ofNat (FGModuleCat.finrank_biprod k X Y)

/-- Dimension as a homomorphism from split `K₀` of finite-dimensional vector spaces to `ℤ`. -/
noncomputable def finrank : SplitK0 (FGModuleCat.{v} k) →+ ℤ :=
  lift (finrankInvariant k)

/-- The dimension homomorphism sends an object class to its dimension. -/
@[simp]
theorem finrank_of (X : FGModuleCat.{v} k) :
    finrank k (of X) = Module.finrank k X :=
  lift_of (finrankInvariant k) X

/-- Every object class in split `K₀` is its dimension times the class of the one-dimensional
space. -/
theorem of_eq_finrank_nsmul (L X : FGModuleCat.{v} k) (hL : Module.finrank k L = 1) :
    (of X : SplitK0 (FGModuleCat.{v} k)) = Module.finrank k X • of L :=
  class_eq_finrank_nsmul k of (fun {_ _} e ↦ of_congr e) of_zero of_biprod L X hL

private theorem eq_finrank_zsmul [Small.{v} k] (x : SplitK0 (FGModuleCat.{v} k)) :
    x = finrank k x • of (line k) := by
  induction x using induction_on with
  | zero => simp
  | of X => simpa [finrank_of] using of_eq_finrank_nsmul k (line k) X (finrank_line k)
  | add x y hx hy =>
      calc
        x + y = finrank k x • of (line k) + finrank k y • of (line k) :=
          congrArg₂ (fun a b ↦ a + b) hx hy
        _ = (finrank k x + finrank k y) • of (line k) :=
          (add_zsmul _ _ _).symm
        _ = finrank k (x + y) • of (line k) := by rw [map_add]
  | neg x hx =>
      calc
        -x = -(finrank k x • of (line k)) := congrArg Neg.neg hx
        _ = (-finrank k x) • of (line k) := (neg_zsmul _ _).symm
        _ = finrank k (-x) • of (line k) := by rw [map_neg]

/-- Dimension identifies split `K₀` of finite-dimensional vector spaces with `ℤ`. -/
noncomputable def finrankEquiv [Small.{v} k] : SplitK0 (FGModuleCat.{v} k) ≃+ ℤ :=
  AddEquiv.ofBijective (finrank k) ⟨
    fun x y h ↦ by rw [eq_finrank_zsmul k x, eq_finrank_zsmul k y, h],
    fun n ↦ ⟨n • of (line k), by simp [finrank_of]⟩⟩

/-- The dimension equivalence agrees with the dimension homomorphism. -/
theorem finrankEquiv_apply [Small.{v} k] (x : SplitK0 (FGModuleCat.{v} k)) :
    finrankEquiv k x = finrank k x :=
  AddEquiv.ofBijective_apply _ _ _

/-- The dimension equivalence sends an object class to its dimension. -/
@[simp]
theorem finrankEquiv_of [Small.{v} k] (X : FGModuleCat.{v} k) :
    finrankEquiv k (of X) = Module.finrank k X :=
  by rw [finrankEquiv_apply, finrank_of]

/-- The inverse dimension equivalence sends an integer to that multiple of the class of any
one-dimensional space. -/
theorem finrankEquiv_symm_apply [Small.{v} k] (L : FGModuleCat.{v} k)
    (hL : Module.finrank k L = 1) (n : ℤ) : (finrankEquiv k).symm n = n • of L := by
  apply (finrankEquiv k).injective
  simp [hL]

/-- A split-additive invariant of finite-dimensional vector spaces is determined by its value on
the one-dimensional space. -/
theorem AdditiveInvariant.obj_eq_finrank_nsmul {G : Type*} [AddCommGroup G]
    (a : AdditiveInvariant (FGModuleCat.{v} k) G) (L X : FGModuleCat.{v} k)
    (hL : Module.finrank k L = 1) : a.obj X = Module.finrank k X • a.obj L := by
  rw [← lift_of a X, of_eq_finrank_nsmul k L X hL, map_nsmul, lift_of]

end SplitK0

namespace AbelianK0

variable (k : Type u) [DivisionRing k]

private theorem nonempty_splitting_of_conflation
    {S : ShortComplex (FGModuleCat.{v} k)}
    (hS : (ExactStructure.abelian (FGModuleCat.{v} k)).Conflation S) :
    Nonempty S.Splitting :=
  FGModuleCat.nonempty_splitting_of_shortExact k
    ((ExactStructure.abelian_conflation S).mp hS)

private noncomputable def fromSplitEquiv :
    SplitK0 (FGModuleCat.{v} k) ≃+ AbelianK0 (FGModuleCat.{v} k) :=
  (ExactK0.fromSplitEquiv (nonempty_splitting_of_conflation k)).trans
    (toExactK0 (FGModuleCat.{v} k)).symm

@[simp] private theorem fromSplitEquiv_of (X : FGModuleCat.{v} k) :
    fromSplitEquiv k (SplitK0.of X) = of X := by
  simp only [fromSplitEquiv, AddEquiv.trans_apply, ExactK0.fromSplitEquiv_apply,
    ExactK0.fromSplit_of, toExactK0_symm_of]

@[simp] private theorem fromSplitEquiv_symm_of (X : FGModuleCat.{v} k) :
    (fromSplitEquiv k).symm (of X) = SplitK0.of X := by
  apply (fromSplitEquiv k).injective
  simp

/-- Dimension as a homomorphism from abelian `K₀` of finite-dimensional vector spaces to `ℤ`. -/
noncomputable def finrank : AbelianK0 (FGModuleCat.{v} k) →+ ℤ :=
  (SplitK0.finrank k).comp (fromSplitEquiv k).symm.toAddMonoidHom

/-- The dimension homomorphism sends an object class to its dimension. -/
@[simp]
theorem finrank_of (X : FGModuleCat.{v} k) :
    finrank k (of X) = Module.finrank k X := by
  simp only [finrank, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, fromSplitEquiv_symm_of, SplitK0.finrank_of]

/-- Every object class in abelian `K₀` is its dimension times the class of the one-dimensional
space. -/
theorem of_eq_finrank_nsmul (L X : FGModuleCat.{v} k) (hL : Module.finrank k L = 1) :
    (of X : AbelianK0 (FGModuleCat.{v} k)) = Module.finrank k X • of L := by
  apply (fromSplitEquiv k).symm.injective
  simpa only [map_nsmul, fromSplitEquiv_symm_of] using
    SplitK0.of_eq_finrank_nsmul k L X hL

/-- Dimension identifies abelian `K₀` of finite-dimensional vector spaces with `ℤ`. -/
noncomputable def finrankEquiv [Small.{v} k] : AbelianK0 (FGModuleCat.{v} k) ≃+ ℤ :=
  (fromSplitEquiv k).symm.trans (SplitK0.finrankEquiv k)

/-- The dimension equivalence agrees with the dimension homomorphism. -/
theorem finrankEquiv_apply [Small.{v} k] (x : AbelianK0 (FGModuleCat.{v} k)) :
    finrankEquiv k x = finrank k x := by
  simp only [finrankEquiv, AddEquiv.trans_apply, finrank, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, SplitK0.finrankEquiv_apply]

/-- The dimension equivalence sends an object class to its dimension. -/
@[simp]
theorem finrankEquiv_of [Small.{v} k] (X : FGModuleCat.{v} k) :
    finrankEquiv k (of X) = Module.finrank k X :=
  by rw [finrankEquiv_apply, finrank_of]

/-- The inverse dimension equivalence sends an integer to that multiple of the class of any
one-dimensional space. -/
theorem finrankEquiv_symm_apply [Small.{v} k] (L : FGModuleCat.{v} k)
    (hL : Module.finrank k L = 1) (n : ℤ) : (finrankEquiv k).symm n = n • of L := by
  apply (finrankEquiv k).injective
  simp [hL]

/-- A short-exact-additive invariant of finite-dimensional vector spaces is determined by its
value on the one-dimensional space. -/
theorem AdditiveInvariant.obj_eq_finrank_nsmul {G : Type*} [AddCommGroup G]
    (a : AdditiveInvariant (FGModuleCat.{v} k) G) (L X : FGModuleCat.{v} k)
    (hL : Module.finrank k L = 1) : a.obj X = Module.finrank k X • a.obj L := by
  rw [← lift_of a X, of_eq_finrank_nsmul k L X hL, map_nsmul, lift_of]

end AbelianK0

end TauCeti
