/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.Ring.Pi
import TauCeti.Algebra.Star.StarAlgHom

/-!
# `⋆`-algebra homomorphisms, equivalences, and coordinate slices on `Pi` types

1. When `star` fixes `e.symm (Pi.single i 1)` for `e : E ≃+* ∀ i, A i`, `star` preserves the
   `i`-th slice (`RingEquiv.apply_star_eq_coord`, `RingEquiv.apply_star_single`), induces a
   `StarRing` on `ULift.{0} (A i)` (`RingEquiv.coordStarRing`), and lifts `E ≃ₐ[R] ∀ i, A i` to
   `E ≃⋆ₐ[R] ∀ i, ULift.{0} (A i)` (`AlgEquiv.starPiULift`).
2. Single-factor inclusions into dependent products of non-unital `⋆`-algebras and `⋆`-algebra
   equivalences for products indexed by a `Unique` type:
   * `NonUnitalStarAlgHom.single`: the single-coordinate inclusion `A i →⋆ₙₐ[R] ∀ j, A j` sending
     `x` to `Pi.single i x`.
   * `StarAlgEquiv.funUnique`: the `⋆`-algebra equivalence `(ι → A) ≃⋆ₐ[R] A` for `[Unique ι]`,
     built from `AlgEquiv.funUnique`.
   * `NonUnitalStarAlgHom.singleFunUnique`: the single-coordinate inclusion
     `(ι' → A i) →⋆ₙₐ[R] ∀ j, A j` from a `Unique`-indexed copy of factor `A i`.
   * `NonUnitalStarAlgHom.funUniqueEquiv` and `StarAlgHom.funUniqueEquiv`: the equivalences
     `((ι → A) →⋆ₙₐ[R] (κ → B)) ≃ (A →⋆ₙₐ[R] B)` and `((ι → A) →⋆ₐ[R] (κ → B)) ≃ (A →⋆ₐ[R] B)`
     for `[Unique ι] [Unique κ]`, together with application, composition, injectivity, and unitary
     conjugacy transport lemmas.
-/

public section

namespace RingEquiv

section Semiring

variable {E : Type*} [Semiring E] [StarRing E] {ι : Type*} [DecidableEq ι] {A : ι → Type*}
  [∀ i, Semiring (A i)] (e : E ≃+* ∀ i, A i)

/-- When `star` fixes the coordinate central idempotent `e.symm (Pi.single i 1)`, `star` acts on
the `i`-th coordinate via `a ↦ e (star (e.symm (Pi.single i a))) i`. -/
theorem apply_star_eq_coord (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (x : E) :
    e (star x) i = e (star (e.symm (Pi.single i (e x i)))) i := by
  have hst : star x * e.symm (Pi.single i 1) = star (e.symm (Pi.single i (e x i))) := by
    rw [← e.symm_single_one_mul i x, star_mul, hδ]
  simpa using congrFun (congrArg e hst) i

/-- When `star` fixes the coordinate central idempotent `e.symm (Pi.single i 1)`, `star` sends
each `i`-th coordinate slice `e.symm (Pi.single i a)` back into the same coordinate slice. -/
theorem apply_star_single (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (a : A i) :
    e (star (e.symm (Pi.single i a))) = Pi.single i (e (star (e.symm (Pi.single i a))) i) := by
  have hst : star (e.symm (Pi.single i a)) =
      star (e.symm (Pi.single i a)) * e.symm (Pi.single i 1) := by
    conv_lhs => rw [← show e.symm (Pi.single i 1) * e.symm (Pi.single i a) =
      e.symm (Pi.single i a) by simpa using e.symm_single_one_mul i (e.symm (Pi.single i a)),
      star_mul, hδ]
  funext j; rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [hst, map_mul, Pi.mul_apply, e.apply_symm_apply, Pi.single_eq_of_ne hji, mul_zero,
      Pi.single_eq_of_ne hji]

/-- Re-embedding the `i`-th coordinate of `star (e.symm (Pi.single i a))` recovers
`star (e.symm (Pi.single i a))`. -/
theorem symm_single_apply_star_single (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (a : A i) :
    e.symm (Pi.single i (e (star (e.symm (Pi.single i a))) i)) = star (e.symm (Pi.single i a)) := by
  rw [← e.apply_star_single i hδ a, e.symm_apply_apply]

/-- Induced `StarRing` structure on `ULift.{0} (A i)` from a star-invariant coordinate central
idempotent `e.symm (Pi.single i 1)`. -/
@[instance_reducible]
def coordStarRing (i : ι) (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) :
    StarRing (ULift.{0} (A i)) where
  star x := ULift.up (e (star (e.symm (Pi.single i x.down))) i)
  star_involutive x := ULift.ext <| by
    dsimp only
    rw [e.symm_single_apply_star_single i hδ, star_star, e.apply_symm_apply, Pi.single_eq_same]
  star_mul x y := ULift.ext <| by
    rw [ULift.mul_down]
    dsimp only
    rw [ULift.mul_down, e.symm_single_mul, star_mul, map_mul, Pi.mul_apply]
  star_add x y := ULift.ext <| by
    rw [ULift.add_down]
    dsimp only
    rw [ULift.add_down, Pi.single_add, map_add, star_add, map_add, Pi.add_apply]

@[simp] theorem coordStarRing_down_star (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (x : ULift.{0} (A i)) :
    letI := e.coordStarRing i hδ; (star x).down = e (star (e.symm (Pi.single i x.down))) i := (rfl)

end Semiring

end RingEquiv

namespace AlgEquiv

variable {R E : Type*} [CommSemiring R] [Semiring E] [Algebra R E] [StarRing E]
  {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- Bundled product star-algebra isomorphism `E ≃⋆ₐ[R] ∀ i, ULift.{0} (A i)` induced from
`e : E ≃ₐ[R] ∀ i, A i` when `star` fixes every coordinate central idempotent. -/
def starPiULift (e : E ≃ₐ[R] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) :
    letI : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
    E ≃⋆ₐ[R] ∀ i, ULift.{0} (A i) :=
  let _ : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
  StarAlgEquiv.ofAlgEquiv (e.trans (AlgEquiv.piCongrRight fun _ ↦ ULift.algEquiv.symm)) fun x ↦
    funext fun i ↦ ULift.ext <| by
      simp only [AlgEquiv.trans_apply, AlgEquiv.piCongrRight_apply, ULift.algEquiv_symm_apply,
        Pi.star_apply, ULift.down_up]
      rw [RingEquiv.coordStarRing_down_star e.toRingEquiv i (hδ i)]
      exact e.toRingEquiv.apply_star_eq_coord i (hδ i) x

@[simp] theorem starPiULift_apply_down (e : E ≃ₐ[R] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (x : E) (i : ι) :
    letI : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
    (e.starPiULift hδ x i).down = e x i := (rfl)

@[simp] theorem starPiULift_symm_apply (e : E ≃ₐ[R] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (x : ∀ i, ULift.{0} (A i)) :
    letI : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
    (e.starPiULift hδ).symm x = e.symm (fun i ↦ (x i).down) := (rfl)

end AlgEquiv

namespace LinearMap

/-- Precomposing a linear map strictly positive on `x * star x` with `LinearMap.single R B i`
yields a linear map strictly positive on `x * star x` in factor `i`. -/
theorem comp_single_mul_star_pos {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (B i)] [∀ i, Module R (B i)]
    [∀ i, StarAddMonoid (B i)] {M : Type*} [AddCommMonoid M] [PartialOrder M] [Module R M]
    (t : (∀ i, B i) →ₗ[R] M) (hpos : ∀ x, x ≠ 0 → 0 < t (x * star x)) (i : ι) (x : B i)
    (hx : x ≠ 0) :
    0 < (t.comp (LinearMap.single R B i)) (x * star x) := by
  simpa only [LinearMap.comp_apply, LinearMap.single_apply, Pi.single_mul, ← Pi.single_star] using
    hpos (Pi.single i x) fun h0 ↦ hx (by simpa using congrFun h0 i)

end LinearMap

namespace NonUnitalStarAlgHom

section Single

variable (R : Type*) {ι : Type*} [DecidableEq ι] (A : ι → Type*) [Monoid R]
  [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)]
  [∀ i, StarAddMonoid (A i)]

/-- The non-unital `⋆`-algebra homomorphism including a single factor `A i` into the dependent
product `∀ j, A j` as functions supported at `i`. -/
def single (i : ι) : A i →⋆ₙₐ[R] ∀ j, A j :=
  { AddMonoidHom.single A i, MulHom.single i with
    map_smul' := Pi.single_smul i
    map_star' := Pi.single_star i }

/-- Coercion of `NonUnitalStarAlgHom.single` to a function is `Pi.single`. -/
@[simp]
theorem coe_single (i : ι) : ⇑(single R A i) = Pi.single i :=
  (rfl)

/-- Applying `NonUnitalStarAlgHom.single` gives `Pi.single`. -/
theorem single_apply {R : Type*} {ι : Type*} [DecidableEq ι] {A : ι → Type*} [Monoid R]
    [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)]
    [∀ i, StarAddMonoid (A i)] (i : ι) (x : A i) :
    single R A i x = Pi.single i x :=
  (rfl)

/-- Evaluating `NonUnitalStarAlgHom.single R A i` at the same coordinate `i` gives the identity. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_single_same (i : ι) :
    (Pi.evalNonUnitalStarAlgHom R A i).comp (single R A i) = .id R (A i) :=
  ext <| Pi.single_eq_same i

/-- Evaluating `NonUnitalStarAlgHom.single R A i` at a distinct coordinate `j ≠ i` gives zero. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_single_of_ne {i j : ι} (h : j ≠ i) :
    (Pi.evalNonUnitalStarAlgHom R A j).comp (single R A i) = 0 :=
  ext <| Pi.single_eq_of_ne h

end Single

end NonUnitalStarAlgHom

namespace StarAlgEquiv

section Unique

/-- Functions from a `Unique` type `ι` to `A` are `⋆`-algebra equivalent to `A`. -/
def funUnique (R ι A : Type*) [Unique ι] [CommSemiring R] [Semiring A] [Algebra R A] [Star A] :
    (ι → A) ≃⋆ₐ[R] A :=
  StarAlgEquiv.ofAlgEquiv (AlgEquiv.funUnique R ι A) fun _ ↦ by simp

/-- Applying `StarAlgEquiv.funUnique` evaluates at `default`. -/
@[simp low]
theorem funUnique_apply {R ι A : Type*} [Unique ι] [CommSemiring R] [Semiring A] [Algebra R A]
    [Star A] (f : ι → A) :
    funUnique R ι A f = f default := by
  rw [funUnique, StarAlgEquiv.ofAlgEquiv_apply, AlgEquiv.funUnique_apply, Equiv.funUnique_apply]

/-- Applying `(StarAlgEquiv.funUnique R ι A).symm a` at any index returns `a`. -/
@[simp low]
theorem funUnique_symm_apply {R ι A : Type*} [Unique ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [Star A] (a : A) (i : ι) :
    (funUnique R ι A).symm a i = a := by
  have h : (funUnique R ι A).symm a = fun _ ↦ a := by
    rw [symm_apply_eq, funUnique_apply]
  exact congrFun h i

end Unique

end StarAlgEquiv

namespace NonUnitalStarAlgHom

section FunUnique

/-- The single-coordinate inclusion `(ι' → A i) →⋆ₙₐ[R] ∀ j, A j` from a `Unique`-indexed copy of
factor `A i` into the dependent product `∀ j, A j`. -/
def singleFunUnique (R : Type*) {ι : Type*} (ι' : Type*) [DecidableEq ι] [Unique ι']
    (A : ι → Type*) [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, StarAddMonoid (A i)] (i : ι) :
    (ι' → A i) →⋆ₙₐ[R] ∀ j, A j :=
  (single R A i).comp (StarAlgEquiv.funUnique R ι' (A i)).toNonUnitalStarAlgHom

/-- Applying `NonUnitalStarAlgHom.singleFunUnique` embeds `f default` at coordinate `i`. -/
@[simp]
theorem singleFunUnique_apply {R ι ι' : Type*} [DecidableEq ι] [Unique ι'] {A : ι → Type*}
    [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [∀ i, StarAddMonoid (A i)]
    (i : ι) (f : ι' → A i) :
    singleFunUnique R ι' A i f = Pi.single i (f default) := by
  simp [singleFunUnique]

/-- Equivalence between non-unital `⋆`-algebra homomorphisms `(ι → A) →⋆ₙₐ[R] (κ → B)` on
`Unique`-indexed products and single-factor homomorphisms `A →⋆ₙₐ[R] B`. -/
def funUniqueEquiv (R ι κ A B : Type*) [Unique ι] [Unique κ] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] :
    ((ι → A) →⋆ₙₐ[R] (κ → B)) ≃ (A →⋆ₙₐ[R] B) :=
  StarAlgEquiv.arrowCongr' (StarAlgEquiv.funUnique R ι A) (StarAlgEquiv.funUnique R κ B)

variable {R ι κ μ A B C : Type*} [Unique ι] [Unique κ] [Unique μ] [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
  [Semiring C] [Algebra R C] [Star C]

/-- Applying `NonUnitalStarAlgHom.funUniqueEquiv` evaluates on constant functions at `default`. -/
@[simp]
theorem funUniqueEquiv_apply (φ : (ι → A) →⋆ₙₐ[R] (κ → B)) (a : A) :
    funUniqueEquiv R ι κ A B φ a = φ (fun _ ↦ a) default := by
  have h : (StarAlgEquiv.funUnique R ι A).symm a = fun _ ↦ a :=
    funext (StarAlgEquiv.funUnique_symm_apply a)
  simp [funUniqueEquiv, h]

/-- Applying `(NonUnitalStarAlgHom.funUniqueEquiv R ι κ A B).symm` evaluates `φ` at `default`. -/
@[simp]
theorem funUniqueEquiv_symm_apply (φ : A →⋆ₙₐ[R] B) (x : ι → A) (j : κ) :
    (funUniqueEquiv R ι κ A B).symm φ x j = φ (x default) := by
  simp [funUniqueEquiv]

/-- `NonUnitalStarAlgHom.funUniqueEquiv` preserves composition. -/
theorem funUniqueEquiv_comp (ψ : (κ → B) →⋆ₙₐ[R] (μ → C)) (φ : (ι → A) →⋆ₙₐ[R] (κ → B)) :
    funUniqueEquiv R ι μ A C (ψ.comp φ) =
      (funUniqueEquiv R κ μ B C ψ).comp (funUniqueEquiv R ι κ A B φ) := by
  simp only [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr'_comp _ (StarAlgEquiv.funUnique R κ B) _ φ ψ

/-- `(NonUnitalStarAlgHom.funUniqueEquiv).symm` preserves composition. -/
theorem funUniqueEquiv_symm_comp (ψ : B →⋆ₙₐ[R] C) (φ : A →⋆ₙₐ[R] B) :
    (funUniqueEquiv R ι μ A C).symm (ψ.comp φ) =
      ((funUniqueEquiv R κ μ B C).symm ψ).comp ((funUniqueEquiv R ι κ A B).symm φ) := by
  simp only [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr']
  exact StarAlgEquiv.arrowCongr'_comp _ (StarAlgEquiv.funUnique R κ B).symm _ φ ψ

/-- `NonUnitalStarAlgHom.funUniqueEquiv` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_injective_iff (φ : (ι → A) →⋆ₙₐ[R] (κ → B)) :
    Function.Injective (funUniqueEquiv R ι κ A B φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr'_injective_iff _ _ φ

/-- `(NonUnitalStarAlgHom.funUniqueEquiv).symm` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_symm_injective_iff (φ : A →⋆ₙₐ[R] B) :
    Function.Injective ((funUniqueEquiv R ι κ A B).symm φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr']
  exact StarAlgEquiv.arrowCongr'_injective_iff _ _ φ

/-- `NonUnitalStarAlgHom.funUniqueEquiv` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : (ι → A) →⋆ₙₐ[R] (κ → B)) :
    (∃ u : unitary B, ∀ x, (u : B) * funUniqueEquiv R ι κ A B φ x * star (u : B) =
        funUniqueEquiv R ι κ A B ψ x) ↔
      ∃ u : unitary (κ → B), ∀ x, (u : κ → B) * φ x * star (u : κ → B) = ψ x := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr'_iff _ _ φ ψ

/-- `(NonUnitalStarAlgHom.funUniqueEquiv).symm` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_symm_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : A →⋆ₙₐ[R] B) :
    (∃ u : unitary (κ → B), ∀ x, (u : κ → B) * (funUniqueEquiv R ι κ A B).symm φ x *
        star (u : κ → B) = (funUniqueEquiv R ι κ A B).symm ψ x) ↔
      ∃ u : unitary B, ∀ x, (u : B) * φ x * star (u : B) = ψ x := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr']
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr'_iff _ _ φ ψ

end FunUnique

end NonUnitalStarAlgHom

namespace StarAlgHom

section FunUnique

/-- Equivalence between unital `⋆`-algebra homomorphisms `(ι → A) →⋆ₐ[R] (κ → B)` on
`Unique`-indexed products and single-factor homomorphisms `A →⋆ₐ[R] B`. -/
def funUniqueEquiv (R ι κ A B : Type*) [Unique ι] [Unique κ] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] :
    ((ι → A) →⋆ₐ[R] (κ → B)) ≃ (A →⋆ₐ[R] B) :=
  StarAlgEquiv.arrowCongr (StarAlgEquiv.funUnique R ι A) (StarAlgEquiv.funUnique R κ B)

variable {R ι κ μ A B C : Type*} [Unique ι] [Unique κ] [Unique μ] [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
  [Semiring C] [Algebra R C] [Star C]

/-- Forgetting unitality intertwines `StarAlgHom.funUniqueEquiv` with
`NonUnitalStarAlgHom.funUniqueEquiv`. -/
@[simp]
theorem toNonUnitalStarAlgHom_funUniqueEquiv (φ : (ι → A) →⋆ₐ[R] (κ → B)) :
    (funUniqueEquiv R ι κ A B φ).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.funUniqueEquiv R ι κ A B φ.toNonUnitalStarAlgHom := by
  rw [funUniqueEquiv, NonUnitalStarAlgHom.funUniqueEquiv,
    StarAlgEquiv.toNonUnitalStarAlgHom_arrowCongr]

/-- Forgetting unitality intertwines `(StarAlgHom.funUniqueEquiv).symm` with
`(NonUnitalStarAlgHom.funUniqueEquiv).symm`. -/
@[simp]
theorem toNonUnitalStarAlgHom_funUniqueEquiv_symm (φ : A →⋆ₐ[R] B) :
    ((funUniqueEquiv R ι κ A B).symm φ).toNonUnitalStarAlgHom =
      (NonUnitalStarAlgHom.funUniqueEquiv R ι κ A B).symm φ.toNonUnitalStarAlgHom := by
  rw [funUniqueEquiv, NonUnitalStarAlgHom.funUniqueEquiv, StarAlgEquiv.symm_arrowCongr,
    StarAlgEquiv.symm_arrowCongr', StarAlgEquiv.toNonUnitalStarAlgHom_arrowCongr]

/-- Applying `StarAlgHom.funUniqueEquiv` evaluates on constant functions at `default`. -/
@[simp]
theorem funUniqueEquiv_apply (φ : (ι → A) →⋆ₐ[R] (κ → B)) (a : A) :
    funUniqueEquiv R ι κ A B φ a = φ (fun _ ↦ a) default := by
  rw [← coe_toNonUnitalStarAlgHom, toNonUnitalStarAlgHom_funUniqueEquiv,
    NonUnitalStarAlgHom.funUniqueEquiv_apply, coe_toNonUnitalStarAlgHom]

/-- Applying `(StarAlgHom.funUniqueEquiv R ι κ A B).symm` evaluates `φ` at `default`. -/
@[simp]
theorem funUniqueEquiv_symm_apply (φ : A →⋆ₐ[R] B) (x : ι → A) (j : κ) :
    (funUniqueEquiv R ι κ A B).symm φ x j = φ (x default) := by
  rw [← coe_toNonUnitalStarAlgHom, toNonUnitalStarAlgHom_funUniqueEquiv_symm,
    NonUnitalStarAlgHom.funUniqueEquiv_symm_apply, coe_toNonUnitalStarAlgHom]

/-- `StarAlgHom.funUniqueEquiv` preserves composition. -/
theorem funUniqueEquiv_comp (ψ : (κ → B) →⋆ₐ[R] (μ → C)) (φ : (ι → A) →⋆ₐ[R] (κ → B)) :
    funUniqueEquiv R ι μ A C (ψ.comp φ) =
      (funUniqueEquiv R κ μ B C ψ).comp (funUniqueEquiv R ι κ A B φ) := by
  simp only [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr_comp _ (StarAlgEquiv.funUnique R κ B) _ φ ψ

/-- `(StarAlgHom.funUniqueEquiv).symm` preserves composition. -/
theorem funUniqueEquiv_symm_comp (ψ : B →⋆ₐ[R] C) (φ : A →⋆ₐ[R] B) :
    (funUniqueEquiv R ι μ A C).symm (ψ.comp φ) =
      ((funUniqueEquiv R κ μ B C).symm ψ).comp ((funUniqueEquiv R ι κ A B).symm φ) := by
  simp only [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr]
  exact StarAlgEquiv.arrowCongr_comp _ (StarAlgEquiv.funUnique R κ B).symm _ φ ψ

/-- `StarAlgHom.funUniqueEquiv` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_injective_iff (φ : (ι → A) →⋆ₐ[R] (κ → B)) :
    Function.Injective (funUniqueEquiv R ι κ A B φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr_injective_iff _ _ φ

/-- `(StarAlgHom.funUniqueEquiv).symm` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_symm_injective_iff (φ : A →⋆ₐ[R] B) :
    Function.Injective ((funUniqueEquiv R ι κ A B).symm φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr]
  exact StarAlgEquiv.arrowCongr_injective_iff _ _ φ

/-- `StarAlgHom.funUniqueEquiv` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : (ι → A) →⋆ₐ[R] (κ → B)) :
    (∃ u : unitary B, ∀ x, (u : B) * funUniqueEquiv R ι κ A B φ x * star (u : B) =
        funUniqueEquiv R ι κ A B ψ x) ↔
      ∃ u : unitary (κ → B), ∀ x, (u : κ → B) * φ x * star (u : κ → B) = ψ x := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr_iff _ _ φ ψ

/-- `(StarAlgHom.funUniqueEquiv).symm` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_symm_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : A →⋆ₐ[R] B) :
    (∃ u : unitary (κ → B), ∀ x, (u : κ → B) * (funUniqueEquiv R ι κ A B).symm φ x *
        star (u : κ → B) = (funUniqueEquiv R ι κ A B).symm ψ x) ↔
      ∃ u : unitary B, ∀ x, (u : B) * φ x * star (u : B) = ψ x := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr]
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr_iff _ _ φ ψ

end FunUnique

end StarAlgHom
