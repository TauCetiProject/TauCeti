/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The positive part and the indecomposables of a `ℤ`-graded algebra

For an internally `ℤ`-graded algebra `A = ⨁ₚ Aᵖ`, the positive part `A⁺ = ⨁_{p > 0} Aᵖ` and its
module of indecomposables `Q(A) = A⁺ ⧸ A⁺ · A⁺` measure generators: when `A` vanishes in negative
degrees, `A⁺` is a two-sided ideal, and `Q(A)` is the space of elements of positive degree modulo
the decomposable ones, those that are sums of products of two elements of positive degree. For the
free graded-commutative algebra `ΛV` on generators of positive degree, `Q(ΛV)` is spanned by the
classes of the generators, and a Sullivan algebra `(ΛV, d)` is minimal exactly when the map `d`
induces on `Q(ΛV)` vanishes.

Mathlib's irrelevant ideal `HomogeneousIdeal.irrelevant` is the same construction for gradings by
a canonically ordered monoid such as `ℕ`, and its cotangent space `Ideal.Cotangent` the analogue of
`Q(A)` for commutative rings; here the grading is by `ℤ` and `A` need not be commutative.

## Main definitions

* `TauCeti.positivePart 𝒜`: the submodule `A⁺ = ⨆_{p > 0} Aᵖ`.
* `TauCeti.Indecomposables 𝒜`: the indecomposables `A⁺ ⧸ A⁺ · A⁺`, with the projection
  `TauCeti.Indecomposables.mk`.
* `TauCeti.Indecomposables.map`: the map induced on indecomposables by a linear map carrying
  positive parts and decomposables into positive parts and decomposables.

## Main results

* `TauCeti.positivePart_le_iff`: `A⁺` is the least submodule containing every `Aᵖ`, `p > 0`;
  `TauCeti.mem_positivePart_iff`: its elements are those with no component of degree `≤ 0`.
* `TauCeti.map_positivePart_le`, `TauCeti.map_positivePart_mul_positivePart_le`: maps raising
  degrees carry `A⁺` into `B⁺`, and algebra maps carrying `A⁺` into `B⁺` carry `A⁺ · A⁺` into
  `B⁺ · B⁺`, the two hypotheses of `TauCeti.Indecomposables.map`.
* `GradedAlgHom.map_positivePart_le`, `GradedAlgHom.map_positivePart_mul_positivePart_le`: a
  degree-preserving algebra map discharges both hypotheses, so it induces a map on
  indecomposables.
* `TauCeti.mul_mem_positivePart_of_left`, `TauCeti.mul_mem_positivePart_of_right`: when `A`
  vanishes in negative degrees, `A⁺` is a two-sided ideal, and so is `A⁺ · A⁺`
  (`TauCeti.mul_mem_positivePart_mul_positivePart_of_left` and its mirror).
* `TauCeti.Indecomposables.map_id`, `TauCeti.Indecomposables.map_comp`: functoriality of the
  induced maps.
* `TauCeti.Indecomposables.map_eq_zero_iff`: the induced map vanishes exactly when it carries
  `A⁺` into the decomposables.

## References

* J. W. Morgan, *The algebraic topology of smooth algebraic varieties*, Publ. Math. IHÉS 48
  (1978), §5, after Definition 5.2.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational homotopy theory*, Graduate Texts in Mathematics
  205, Springer, 2001, §12.
-/

public section

namespace TauCeti

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

/-- The positive part `A⁺ = ⨆_{p > 0} Aᵖ` of an internally `ℤ`-graded algebra: the elements whose
homogeneous components all have positive degree. -/
def positivePart : Submodule R A :=
  ⨆ (p : ℤ) (_ : 0 < p), 𝒜 p

variable {𝒜}

/-- A homogeneous element of positive degree lies in the positive part. -/
theorem mem_positivePart_of_mem {p : ℤ} (hp : 0 < p) {a : A} (ha : a ∈ 𝒜 p) :
    a ∈ positivePart 𝒜 :=
  (le_iSup₂ (f := fun (p : ℤ) (_ : 0 < p) => 𝒜 p) p hp) ha

/-- The positive part is the least submodule containing every homogeneous component of positive
degree. -/
theorem positivePart_le_iff {P : Submodule R A} :
    positivePart 𝒜 ≤ P ↔ ∀ p, 0 < p → 𝒜 p ≤ P :=
  iSup₂_le_iff

/-- A linear map raising degrees by `n ≥ 0` carries the positive part into the positive part. -/
theorem map_positivePart_le {B : Type*} [Semiring B] [Algebra R B] {ℬ : ℤ → Submodule R B}
    {n : ℤ} (hn : 0 ≤ n) {f : A →ₗ[R] B} (hf : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → f a ∈ ℬ (p + n)) :
    (positivePart 𝒜).map f ≤ positivePart ℬ :=
  Submodule.map_le_iff_le_comap.2 <| positivePart_le_iff.2 fun p hp _ ha =>
    mem_positivePart_of_mem (by omega) (hf ha)

/-- An algebra map carrying the positive part into the positive part carries the decomposables
`A⁺ · A⁺` into the decomposables, as needed to induce a map on indecomposables. -/
theorem map_positivePart_mul_positivePart_le {B : Type*} [Semiring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} {f : A →ₐ[R] B}
    (hf : (positivePart 𝒜).map f.toLinearMap ≤ positivePart ℬ) :
    (positivePart 𝒜 * positivePart 𝒜).map f.toLinearMap ≤ positivePart ℬ * positivePart ℬ := by
  rw [Submodule.map_mul]
  exact mul_le_mul' hf hf

end Semiring

section GradedAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
  [GradedAlgebra 𝒜]

/-- An element lies in the positive part exactly when its homogeneous components of degree `≤ 0`
vanish. -/
theorem mem_positivePart_iff {a : A} :
    a ∈ positivePart 𝒜 ↔ ∀ p ≤ 0, (DirectSum.decompose 𝒜 a p : A) = 0 := by
  constructor
  · intro ha p hp
    refine positivePart_le_iff (P := LinearMap.ker (GradedAlgebra.proj 𝒜 p)).2
      (fun q hq b hb => ?_) ha
    rw [LinearMap.mem_ker, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hb (by omega)]
  · intro ha
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine sum_mem fun p _ => ?_
    by_cases hp0 : p ≤ 0
    · rw [ha p hp0]
      exact zero_mem _
    · exact mem_positivePart_of_mem (by omega) (SetLike.coe_mem _)

/-- When `A` vanishes in negative degrees, the positive part is a right ideal. -/
theorem mul_mem_positivePart_of_left (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) {a : A}
    (ha : a ∈ positivePart 𝒜) (b : A) : a * b ∈ positivePart 𝒜 := by
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q b =>
    obtain ⟨b, hb⟩ := b
    refine positivePart_le_iff (P := (positivePart 𝒜).comap (LinearMap.mulRight R b)).2
      (fun p hp a ha => ?_) ha
    by_cases hq : 0 ≤ q
    · exact mem_positivePart_of_mem (by omega) (SetLike.GradedMul.mul_mem ha hb)
    · simp [(Submodule.eq_bot_iff _).1 (h𝒜 _ (by omega)) b hb]
  | add b b' hb hb' => simpa [mul_add] using add_mem hb hb'

/-- When `A` vanishes in negative degrees, the positive part is a left ideal. -/
theorem mul_mem_positivePart_of_right (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (a : A) {b : A}
    (hb : b ∈ positivePart 𝒜) : a * b ∈ positivePart 𝒜 := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous p a =>
    obtain ⟨a, ha⟩ := a
    refine positivePart_le_iff (P := (positivePart 𝒜).comap (LinearMap.mulLeft R a)).2
      (fun q hq b hb => ?_) hb
    by_cases hp : 0 ≤ p
    · exact mem_positivePart_of_mem (by omega) (SetLike.GradedMul.mul_mem ha hb)
    · simp [(Submodule.eq_bot_iff _).1 (h𝒜 _ (by omega)) a ha]
  | add a a' ha ha' => simpa [add_mul] using add_mem ha ha'

/-- When `A` vanishes in negative degrees, the decomposables `A⁺ · A⁺` form a right ideal. -/
theorem mul_mem_positivePart_mul_positivePart_of_left (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) {a : A}
    (ha : a ∈ positivePart 𝒜 * positivePart 𝒜) (b : A) :
    a * b ∈ positivePart 𝒜 * positivePart 𝒜 := by
  refine Submodule.mul_induction_on ha (fun a ha a' ha' => ?_) fun a a' ha ha' => ?_
  · rw [mul_assoc]
    exact Submodule.mul_mem_mul ha (mul_mem_positivePart_of_left h𝒜 ha' b)
  · simpa [add_mul] using add_mem ha ha'

/-- When `A` vanishes in negative degrees, the decomposables `A⁺ · A⁺` form a left ideal. -/
theorem mul_mem_positivePart_mul_positivePart_of_right (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (a : A) {b : A}
    (hb : b ∈ positivePart 𝒜 * positivePart 𝒜) :
    a * b ∈ positivePart 𝒜 * positivePart 𝒜 := by
  refine Submodule.mul_induction_on hb (fun b hb b' hb' => ?_) fun b b' hb hb' => ?_
  · rw [← mul_assoc]
    exact Submodule.mul_mem_mul (mul_mem_positivePart_of_right h𝒜 a hb) hb'
  · simpa [mul_add] using add_mem hb hb'

end GradedAlgebra

section Indecomposables

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

/-- The module of indecomposables `Q(A) = A⁺ ⧸ A⁺ · A⁺` of an internally `ℤ`-graded algebra: the
elements of positive degree modulo the decomposable ones, the sums of products of two elements of
positive degree. -/
abbrev Indecomposables : Type _ :=
  positivePart 𝒜 ⧸ (positivePart 𝒜 * positivePart 𝒜).comap (positivePart 𝒜).subtype

namespace Indecomposables

/-- The projection `A⁺ → Q(A)` onto the indecomposables. -/
def mk : positivePart 𝒜 →ₗ[R] Indecomposables 𝒜 :=
  Submodule.mkQ _

variable {𝒜}

theorem mk_surjective : Function.Surjective (mk 𝒜) :=
  Submodule.mkQ_surjective _

/-- The projection onto the indecomposables is the quotient map. -/
theorem mk_apply (a : positivePart 𝒜) : mk 𝒜 a = Submodule.Quotient.mk a :=
  (rfl)

/-- Two elements of positive degree have the same class in the indecomposables exactly when they
differ by a decomposable element. -/
theorem mk_eq_mk_iff {a b : positivePart 𝒜} :
    mk 𝒜 a = mk 𝒜 b ↔ (a - b : A) ∈ positivePart 𝒜 * positivePart 𝒜 :=
  Submodule.Quotient.eq _

/-- An element of positive degree has zero class in the indecomposables exactly when it is
decomposable. -/
@[simp]
theorem mk_eq_zero_iff {a : positivePart 𝒜} :
    mk 𝒜 a = 0 ↔ (a : A) ∈ positivePart 𝒜 * positivePart 𝒜 :=
  Submodule.Quotient.mk_eq_zero _

variable {B : Type*} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} {f : A →ₗ[R] B}

/-- The map `Q(f) : Q(A) → Q(B)` induced on indecomposables by a linear map `f : A → B` which
carries `A⁺` into `B⁺` and `A⁺ · A⁺` into `B⁺ · B⁺`. -/
def map (f : A →ₗ[R] B) (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ) :
    Indecomposables 𝒜 →ₗ[R] Indecomposables ℬ :=
  Submodule.mapQ _ _ (f.restrict fun a ha => hf ⟨a, ha, rfl⟩) fun a ha =>
    hf' ⟨a, ha, rfl⟩

@[simp]
theorem map_mk (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ)
    (a : positivePart 𝒜) :
    map f hf hf' (mk 𝒜 a) = mk ℬ ⟨f a, hf ⟨a, a.property, rfl⟩⟩ :=
  (rfl)

/-- The identity induces the identity on indecomposables. -/
@[simp]
theorem map_id :
    map (LinearMap.id : A →ₗ[R] A) (by simp) (by simp) =
      (LinearMap.id : Indecomposables 𝒜 →ₗ[R] Indecomposables 𝒜) :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- The map induced on indecomposables is functorial: `Q(g ∘ f) = Q(g) ∘ Q(f)`. -/
theorem map_comp {C : Type*} [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} {g : B →ₗ[R] C}
    (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ)
    (hg : (positivePart ℬ).map g ≤ positivePart 𝒞)
    (hg' : (positivePart ℬ * positivePart ℬ).map g ≤ positivePart 𝒞 * positivePart 𝒞) :
    map (g ∘ₗ f) (Submodule.map_comp f g _ ▸ (Submodule.map_mono hf).trans hg)
        (Submodule.map_comp f g _ ▸ (Submodule.map_mono hf').trans hg') =
      map g hg hg' ∘ₗ map f hf hf' :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- The map induced on indecomposables vanishes exactly when `f` carries `A⁺` into the
decomposables `B⁺ · B⁺`. -/
theorem map_eq_zero_iff (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ) :
    map f hf hf' = 0 ↔ (positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ := by
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    have := LinearMap.congr_fun h (mk 𝒜 ⟨a, ha⟩)
    rwa [map_mk, LinearMap.zero_apply, mk_eq_zero_iff] at this
  · intro h
    refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := mk_surjective q
    rw [map_mk, LinearMap.zero_apply, mk_eq_zero_iff]
    exact h ⟨a, a.property, rfl⟩

end Indecomposables

end Indecomposables

end TauCeti

namespace GradedAlgHom

open TauCeti

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- A degree-preserving algebra map carries the positive part into the positive part. -/
theorem map_positivePart_le (f : 𝒜 →ₐᵍ[R] ℬ) :
    (positivePart 𝒜).map (f : A →ₐ[R] B).toLinearMap ≤ positivePart ℬ :=
  TauCeti.map_positivePart_le le_rfl fun ha => by
    simpa using Graded.map_mem f ha

/-- A degree-preserving algebra map carries the decomposables `A⁺ · A⁺` into the decomposables
`B⁺ · B⁺`. With `GradedAlgHom.map_positivePart_le` it discharges the hypotheses of
`TauCeti.Indecomposables.map`, so it induces a map on indecomposables. -/
theorem map_positivePart_mul_positivePart_le (f : 𝒜 →ₐᵍ[R] ℬ) :
    (positivePart 𝒜 * positivePart 𝒜).map (f : A →ₐ[R] B).toLinearMap ≤
      positivePart ℬ * positivePart ℬ :=
  TauCeti.map_positivePart_mul_positivePart_le f.map_positivePart_le

end GradedAlgHom
