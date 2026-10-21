/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Tactic.Ring

/-!
# Iterated periodicity isomorphisms

Let `C` be a category with a shift by an additive monoid `A` and let `G : C ⥤ E` be a functor.
An isomorphism `α : shiftFunctor C a ⋙ G ≅ G` says that `G` does not see the shift by `a`.
Two such isomorphisms `α` (in degree `a`) and `β` (in degree `b`) compose to one in degree
`a + b`, whose component at `X` is

`G (X⟦a + b⟧) ≅ G (X⟦a⟧⟦b⟧) ≅ G (X⟦a⟧) ≅ G X`,

the first map being `shiftFunctorAdd'` and the other two `β` at `X⟦a⟧` and `α` at `X`.
This composition `CategoryTheory.Iso.shiftComp` is associative, has the isomorphisms coming from
`shiftFunctorZero'` as two-sided units, and over an additive group every such isomorphism has a
two-sided inverse `CategoryTheory.Iso.shiftInv` in the opposite degree.

A single periodicity isomorphism `φ : shiftFunctor C n ⋙ G ≅ G` for an integral shift therefore
has well-defined integral powers `φ.periodicityZPow i : shiftFunctor C (n * i) ⋙ G ≅ G`, and
these satisfy the cocycle law `φ.periodicityZPow_add_hom_app`. They are the coherence data
needed to descend `G` to the orbit category `D/[n]` (Keller's universal property), where a
morphism `X ⟶ Y⟦n * i⟧` is sent to `G.map f` followed by the `i`-th power of `φ` at `Y`.

## Main definitions

* `CategoryTheory.Iso.shiftComp`: composition of shift-invariance isomorphisms, adding degrees.
* `CategoryTheory.Iso.shiftInv`: the inverse of a shift-invariance isomorphism.
* `CategoryTheory.Iso.periodicityZPow`: the integral powers of a periodicity isomorphism.

## Main results

* `CategoryTheory.Iso.shiftComp_assoc`: associativity of `shiftComp`.
* `CategoryTheory.Iso.periodicityZPow_add_hom_app`: the cocycle law of the powers.
* `CategoryTheory.Iso.periodicityZPow_unique`: the powers are the only family that starts with
  the unit and is built by composing with `φ`.

## References

* B. Keller, *On triangulated orbit categories*, Documenta Mathematica **10** (2005),
  551–581, Section 1.
-/

public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Iso

variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Category.{v₂} E] {A : Type*}
  {G : C ⥤ E}

section AddMonoid

variable [AddMonoid A] [HasShift C A]

/-- The composition of shift-invariance isomorphisms of degrees `a` and `b`, in degree
`c = a + b`. Its component at `X` is `G (X⟦c⟧) ≅ G (X⟦a⟧⟦b⟧) ≅ G (X⟦a⟧) ≅ G X`. -/
def shiftComp {a b c : A} (α : shiftFunctor C a ⋙ G ≅ G) (β : shiftFunctor C b ⋙ G ≅ G)
    (h : a + b = c) : shiftFunctor C c ⋙ G ≅ G :=
  isoWhiskerRight (shiftFunctorAdd' C a b c h) G ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (shiftFunctor C a) β ≪≫ α

@[simp]
theorem shiftComp_hom_app {a b c : A} (α : shiftFunctor C a ⋙ G ≅ G)
    (β : shiftFunctor C b ⋙ G ≅ G) (h : a + b = c) (X : C) :
    (α.shiftComp β h).hom.app X =
      G.map ((shiftFunctorAdd' C a b c h).hom.app X) ≫ β.hom.app (X⟦a⟧) ≫ α.hom.app X := by
  simp [shiftComp]

/-- Composition of shift-invariance isomorphisms is associative. -/
theorem shiftComp_assoc {a b c ab bc abc : A} (α : shiftFunctor C a ⋙ G ≅ G)
    (β : shiftFunctor C b ⋙ G ≅ G) (γ : shiftFunctor C c ⋙ G ≅ G) (hab : a + b = ab)
    (hbc : b + c = bc) (habc : a + b + c = abc) :
    (α.shiftComp β hab).shiftComp (c := abc) γ (by rw [← hab, habc]) =
      α.shiftComp (c := abc) (β.shiftComp γ hbc) (by rw [← hbc, ← add_assoc, habc]) := by
  ext X
  have hγ := γ.hom.naturality ((shiftFunctorAdd' C a b ab hab).hom.app X)
  have hs := G.congr_map (shiftFunctorAdd'_assoc_hom_app a b c ab bc abc hab hbc habc X)
  simp only [Functor.comp_map] at hγ
  simp only [Functor.map_comp] at hs
  simp only [shiftComp_hom_app, Category.assoc, ← reassoc_of% hγ, reassoc_of% hs]

/-- The shift-invariance isomorphism in a degree `a = 0` coming from `shiftFunctorZero'` is a
left unit for `shiftComp`. -/
theorem shiftComp_zero_left {a b : A} (ha : a = 0) (β : shiftFunctor C b ⋙ G ≅ G) :
    (isoWhiskerRight (shiftFunctorZero' C a ha) G ≪≫ G.leftUnitor).shiftComp β
      (by rw [ha, zero_add]) = β := by
  subst ha
  ext X
  have hβ := β.hom.naturality ((shiftFunctorZero C A).inv.app X)
  simp only [Functor.comp_map, Functor.id_obj] at hβ
  simp [shiftFunctorZero'_eq_shiftFunctorZero, shiftFunctorAdd'_zero_add_hom_app,
    reassoc_of% hβ]

/-- The shift-invariance isomorphism in a degree `b = 0` coming from `shiftFunctorZero'` is a
right unit for `shiftComp`. -/
theorem shiftComp_zero_right {a b : A} (α : shiftFunctor C a ⋙ G ≅ G) (hb : b = 0) :
    α.shiftComp (isoWhiskerRight (shiftFunctorZero' C b hb) G ≪≫ G.leftUnitor)
      (by rw [hb, add_zero]) = α := by
  subst hb
  ext X
  simp [shiftFunctorZero'_eq_shiftFunctorZero, shiftFunctorAdd'_add_zero_hom_app]

/-- The inverse of a shift-invariance isomorphism `α` of degree `a`, in a degree `b` with
`b + a = 0`. Its component at `X` is `G (X⟦b⟧) ≅ G (X⟦b⟧⟦a⟧) ≅ G X`. -/
def shiftInv {a : A} (α : shiftFunctor C a ⋙ G ≅ G) (b : A) (h : b + a = 0) :
    shiftFunctor C b ⋙ G ≅ G :=
  isoWhiskerLeft (shiftFunctor C b) α.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftFunctorCompIsoId C b a h) G ≪≫ G.leftUnitor

@[simp]
theorem shiftInv_hom_app {a : A} (α : shiftFunctor C a ⋙ G ≅ G) (b : A) (h : b + a = 0)
    (X : C) : (α.shiftInv b h).hom.app X =
      α.inv.app (X⟦b⟧) ≫ G.map ((shiftFunctorCompIsoId C b a h).hom.app X) := by
  simp [shiftInv]

/-- `α.shiftInv b` is a left inverse of `α` for `shiftComp`. -/
theorem shiftInv_shiftComp {a b c : A} (α : shiftFunctor C a ⋙ G ≅ G) (h : b + a = c)
    (hc : c = 0) :
    (α.shiftInv b (h.trans hc)).shiftComp α h =
      isoWhiskerRight (shiftFunctorZero' C c hc) G ≪≫ G.leftUnitor := by
  subst hc
  ext X
  simp [shiftFunctorZero'_eq_shiftFunctorZero, shiftFunctorCompIsoId]

end AddMonoid

section AddGroup

variable [AddGroup A] [HasShift C A]

/-- `α.shiftInv b` is a right inverse of `α` for `shiftComp`. -/
theorem shiftComp_shiftInv {a b c : A} (α : shiftFunctor C a ⋙ G ≅ G) (h : a + b = c)
    (hc : c = 0) :
    α.shiftComp (α.shiftInv b (by rw [← neg_eq_of_add_eq_zero_left (h.trans hc),
      add_neg_cancel])) h =
      isoWhiskerRight (shiftFunctorZero' C c hc) G ≪≫ G.leftUnitor := by
  subst hc
  ext X
  have hα := α.hom.naturality ((shiftFunctorCompIsoId C a b h).hom.app X)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hα
  rw [shiftComp_hom_app, shiftInv_hom_app, ← shift_shiftFunctorCompIsoId_hom_app a b h X,
    Category.assoc, hα, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  simp [shiftFunctorZero'_eq_shiftFunctorZero, shiftFunctorCompIsoId]

/-- Composition with a shift-invariance isomorphism is cancellable. -/
theorem shiftComp_left_cancel_iff {a b c : A} (α : shiftFunctor C a ⋙ G ≅ G)
    {β β' : shiftFunctor C b ⋙ G ≅ G} (h : a + b = c) :
    α.shiftComp β h = α.shiftComp β' h ↔ β = β' := by
  refine ⟨fun hβ ↦ ?_, fun hβ ↦ hβ ▸ rfl⟩
  have key (γ : shiftFunctor C b ⋙ G ≅ G) :
      (α.shiftInv (-a) (neg_add_cancel a)).shiftComp (α.shiftComp γ h)
        (by rw [← h, neg_add_cancel_left]) = γ := by
    rw [← shiftComp_assoc _ _ _ (neg_add_cancel a) h (by rw [neg_add_cancel, zero_add]),
      shiftInv_shiftComp α (neg_add_cancel a) rfl, shiftComp_zero_left]
  rw [← key β, hβ, key]

end AddGroup

section Periodicity

variable [HasShift C ℤ] {n : ℤ}

/-- The nonnegative powers of a periodicity isomorphism. -/
private def periodicityNatPow (φ : shiftFunctor C n ⋙ G ≅ G) :
    (k : ℕ) → shiftFunctor C (n * k) ⋙ G ≅ G
  | 0 => isoWhiskerRight (shiftFunctorZero' C (n * (0 : ℕ)) (by simp)) G ≪≫ G.leftUnitor
  | k + 1 => φ.shiftComp (periodicityNatPow φ k) (by push_cast; ring)

/-- The negative powers of a periodicity isomorphism. -/
private def periodicityNegPow (φ : shiftFunctor C n ⋙ G ≅ G) :
    (k : ℕ) → shiftFunctor C (n * Int.negSucc k) ⋙ G ≅ G
  | 0 => φ.shiftInv _ (by rw [Int.negSucc_eq]; ring)
  | k + 1 => (φ.shiftInv (-n) (neg_add_cancel n)).shiftComp (periodicityNegPow φ k)
      (by rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring)

/-- The integral powers `φ^i : shiftFunctor C (n * i) ⋙ G ≅ G` of a periodicity isomorphism
`φ : shiftFunctor C n ⋙ G ≅ G`, for the composition `shiftComp`. They are characterised by
`periodicityZPow_zero` and `periodicityZPow_succ`, and satisfy the cocycle law
`periodicityZPow_add`. -/
def periodicityZPow (φ : shiftFunctor C n ⋙ G ≅ G) : (i : ℤ) → shiftFunctor C (n * i) ⋙ G ≅ G
  | Int.ofNat k => periodicityNatPow φ k
  | Int.negSucc k => periodicityNegPow φ k

/-- The zeroth power of a periodicity isomorphism is the unit coming from `shiftFunctorZero'`. -/
theorem periodicityZPow_zero (φ : shiftFunctor C n ⋙ G ≅ G) :
    φ.periodicityZPow 0 =
      isoWhiskerRight (shiftFunctorZero' C (n * 0) (mul_zero n)) G ≪≫ G.leftUnitor := by
  rfl

/-- The zeroth power of a periodicity isomorphism, on components. -/
theorem periodicityZPow_zero_hom_app (φ : shiftFunctor C n ⋙ G ≅ G) (X : C) :
    (φ.periodicityZPow 0).hom.app X =
      G.map ((shiftFunctorZero' C (n * 0) (mul_zero n)).hom.app X) := by
  simp [periodicityZPow_zero]

/-- The power `φ^(i + 1)` is `φ` composed with `φ^i`. -/
theorem periodicityZPow_succ (φ : shiftFunctor C n ⋙ G ≅ G) (i j : ℤ) (h : i + 1 = j) :
    φ.periodicityZPow j = φ.shiftComp (φ.periodicityZPow i) (by rw [← h]; ring) := by
  match i with
  | Int.ofNat k =>
    rw [Int.ofNat_eq_natCast] at h
    obtain rfl : j = Int.ofNat (k + 1) := by rw [Int.ofNat_eq_natCast]; omega
    rfl
  | Int.negSucc 0 =>
    obtain rfl : j = 0 := by omega
    exact (shiftComp_shiftInv φ _ (mul_zero n)).symm
  | Int.negSucc (k + 1) =>
    obtain rfl : j = Int.negSucc k := by omega
    rw [periodicityZPow.eq_2, periodicityZPow.eq_2, periodicityNegPow.eq_2,
      ← shiftComp_assoc (ab := 0) (bc := n * Int.negSucc (k + 1))
      (abc := n * Int.negSucc k) _ _ _ (add_neg_cancel n),
      shiftComp_shiftInv φ (add_neg_cancel n) rfl, shiftComp_zero_left]
    ring

/-- The cocycle law: `φ^(i + j)` is `φ^i` composed with `φ^j`. -/
theorem periodicityZPow_add (φ : shiftFunctor C n ⋙ G ≅ G) (i j k : ℤ) (h : i + j = k) :
    φ.periodicityZPow k =
      (φ.periodicityZPow i).shiftComp (φ.periodicityZPow j) (by rw [← h]; ring) := by
  induction i using Int.induction_on generalizing k with
  | zero =>
    obtain rfl : k = j := by omega
    rw [periodicityZPow_zero, shiftComp_zero_left]
  | succ i ih =>
    rw [periodicityZPow_succ φ (i + j) k (by omega), ih (i + j) rfl,
      periodicityZPow_succ φ i (i + 1) rfl, shiftComp_assoc]
    all_goals subst h; ring
  | pred i ih =>
    rw [← shiftComp_left_cancel_iff φ (by ring : n + n * k = n * (k + 1)),
      ← periodicityZPow_succ φ k (k + 1) rfl, ih (k + 1) (by omega),
      periodicityZPow_succ φ (-i - 1) (-i) (by omega), shiftComp_assoc]
    all_goals subst h; ring

/-- The cocycle law of the powers of a periodicity isomorphism, on components. -/
theorem periodicityZPow_add_hom_app (φ : shiftFunctor C n ⋙ G ≅ G) (i j k : ℤ)
    (h : i + j = k) (X : C) :
    (φ.periodicityZPow k).hom.app X =
      G.map ((shiftFunctorAdd' C (n * i) (n * j) (n * k) (by rw [← h]; ring)).hom.app X) ≫
        (φ.periodicityZPow j).hom.app (X⟦n * i⟧) ≫ (φ.periodicityZPow i).hom.app X := by
  rw [periodicityZPow_add φ i j k h, shiftComp_hom_app]

/-- The first power of a periodicity isomorphism is the isomorphism itself. -/
@[simp]
theorem periodicityZPow_one_hom_app (φ : shiftFunctor C n ⋙ G ≅ G) (X : C) :
    (φ.periodicityZPow 1).hom.app X = G.map (eqToHom (by rw [mul_one])) ≫ φ.hom.app X := by
  have key (z m : ℤ) (hz : z = 0) (h : n + z = m) :
      (shiftFunctorAdd' C n z m h).hom.app X ≫ (shiftFunctorZero' C z hz).hom.app (X⟦n⟧) =
        eqToHom (by rw [← h, hz, add_zero, Functor.id_obj]) := by
    subst hz h
    simp [shiftFunctorZero'_eq_shiftFunctorZero, shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftFunctorAdd_add_zero_hom_app]
  rw [periodicityZPow_succ φ 0 1 rfl, shiftComp_hom_app, periodicityZPow_zero]
  simp [← Functor.map_comp_assoc, key]

/-- The powers of a periodicity isomorphism are the only family of shift-invariance
isomorphisms that starts with the unit and is built by composing with `φ`. -/
theorem periodicityZPow_unique (φ : shiftFunctor C n ⋙ G ≅ G)
    (ψ : (i : ℤ) → shiftFunctor C (n * i) ⋙ G ≅ G)
    (h₀ : ψ 0 = isoWhiskerRight (shiftFunctorZero' C (n * 0) (mul_zero n)) G ≪≫ G.leftUnitor)
    (hsucc : ∀ i j (h : i + 1 = j), ψ j = φ.shiftComp (ψ i) (by rw [← h]; ring)) :
    ψ = φ.periodicityZPow := by
  funext i
  induction i using Int.induction_on with
  | zero => rw [h₀, periodicityZPow_zero]
  | succ i ih => rw [hsucc i (i + 1) rfl, periodicityZPow_succ φ i (i + 1) rfl, ih]
  | pred i ih =>
    rw [← shiftComp_left_cancel_iff φ (by ring : n + n * (-i - 1) = n * (-i)),
      ← hsucc (-i - 1) (-i) (by omega), ← periodicityZPow_succ φ (-i - 1) (-i) (by omega), ih]

end Periodicity

end CategoryTheory.Iso
