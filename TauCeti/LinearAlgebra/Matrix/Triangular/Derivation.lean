/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Int.Order.Units

/-!
# Twisted derivations from lower-triangular `2 × 2` matrices

For an `R`-algebra `A` and an algebra endomorphism `σ : A →ₐ[R] A`, lower-triangular `2 × 2`
matrices of the form `!![a, 0; d a, σ a]` multiply as

`!![a, 0; d a, σ a] * !![b, 0; d b, σ b] = !![a * b, 0; d a * b + σ a * d b, σ (a * b)]`.

Multiplicativity of `a ↦ !![a, 0; d a, σ a]` is therefore equivalent to the `σ`-twisted Leibniz
rule `d (a * b) = d a * b + σ a * d b`. Consequently, to extend a generator assignment
`δ : V →ₗ[R] A` along `g : V →ₗ[R] A` to a `σ`-twisted derivation of a presented algebra `A`, one
forms `TauCeti.triangularDerivationMap g σ δ : V →ₗ[R] Matrix (Fin 2) (Fin 2) A`, lifts it to an
algebra homomorphism `Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A` by the algebra's universal property,
and extracts the lower-left `(1, 0)` entry via `TauCeti.triangularDerivation Φ`.

When the generator images obey `ℤˣ`-signed commutation relations compatible with `σ`,
`TauCeti.triangularDerivationMap_mul_eq_smul_mul` shows that the resulting matrices obey the same
commutation relation. Once `Φ` is known to be lower-triangular with diagonal `(x, σ x)` on an
algebra generating set `s` (`Algebra.adjoin R s = ⊤`), `TauCeti.triangularDerivation_mul` deduces
that shape on all of `A` by `Algebra.adjoin_induction` and yields the `σ`-twisted Leibniz rule.

Compared to `TauCeti.SigmaDerivation.ofMatrix` (`TauCeti.Algebra.OreExtension.Triangular`), which
packages the upper-right entry of a matrix representation as an Ore-extension `SigmaDerivation`
once its diagonal entries are already known on all of `A`, this module stays below Ore-extension
and signed-algebra theory and supplies both the generator-level matrix map (with signed commutation)
and the generating-set criterion for the twisted Leibniz rule.

## Main definitions

* `TauCeti.triangularDerivationMap`: the lower-triangular `2 × 2` matrix map
  `x ↦ !![g x, 0; δ x, σ (g x)]`.
* `TauCeti.triangularDerivation`: the lower-left `(1, 0)` entry of an algebra homomorphism
  `A →ₐ[R] Matrix (Fin 2) (Fin 2) A`.

## Main results

* `TauCeti.triangularDerivationMap_apply`: evaluation of `triangularDerivationMap` at a generator.
* `TauCeti.triangularDerivationMap_mul_eq_smul_mul`: signed commutation for lower-triangular
  derivation matrices.
* `TauCeti.triangularDerivation_apply`: evaluation of `triangularDerivation` as the `(1, 0)` entry.
* `TauCeti.triangularDerivation_mul`: the `σ`-twisted Leibniz rule for a lower-triangular matrix
  representation verified on an algebra generating set.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommSemiring R]

/-- The lower-triangular `2 × 2` matrix map `x ↦ !![g x, 0; δ x, σ (g x)]` used to extend a
generator assignment `δ` to a `σ`-twisted derivation along a generator map `g`. -/
def triangularDerivationMap {V : Type*} [AddCommMonoid V] [Module R V] [Semiring A] [Algebra R A]
    (g : V →ₗ[R] A) (σ : A →ₐ[R] A) (δ : V →ₗ[R] A) :
    V →ₗ[R] Matrix (Fin 2) (Fin 2) A where
  toFun x := !![g x, 0; δ x, σ (g x)]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Evaluation of `triangularDerivationMap` at a generator. -/
@[simp]
theorem triangularDerivationMap_apply {V : Type*} [AddCommMonoid V] [Module R V]
    [Semiring A] [Algebra R A] (g : V →ₗ[R] A) (σ : A →ₐ[R] A) (δ : V →ₗ[R] A) (x : V) :
    triangularDerivationMap g σ δ x = !![g x, 0; δ x, σ (g x)] := (rfl)

/-- Lower-triangular derivation matrices satisfy the same signed commutation relation as `g x` and
`g y` whenever `δ x` and `δ y` satisfy the shifted signed commutation relations with `g y` and
`g x` and `σ` scales `g x` and `g y` by the corresponding signs. -/
theorem triangularDerivationMap_mul_eq_smul_mul {V : Type*} [AddCommMonoid V] [Module R V]
    [Ring A] [Algebra R A] (g : V →ₗ[R] A) (σ : A →ₐ[R] A) (δ : V →ₗ[R] A)
    {x y : V} {s₁ s₂ c : ℤˣ}
    (hgg : g x * g y = c • (g y * g x))
    (hdg : δ x * g y = (c * s₂) • (g y * δ x))
    (hgd : g x * δ y = (c * s₁) • (δ y * g x))
    (hσx : σ (g x) = s₁ • g x)
    (hσy : σ (g y) = s₂ • g y) :
    triangularDerivationMap g σ δ x * triangularDerivationMap g σ δ y =
      c • (triangularDerivationMap g σ δ y * triangularDerivationMap g σ δ x) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply] using hgg
  · simp [Matrix.mul_apply]
  · have h10 : δ x * g y + σ (g x) * δ y = c • (δ y * g x + σ (g y) * δ x) := by
      rw [hσx, hσy, smul_mul_assoc, smul_mul_assoc, hdg, hgd, ← mul_smul,
        mul_left_comm, Int.units_mul_self, mul_one, mul_smul, add_comm, ← smul_add]
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h10
  · have h11 : σ (g x) * σ (g y) = c • (σ (g y) * σ (g x)) := by
      rw [← map_mul σ, ← map_mul σ, hgg, Units.smul_def, Units.smul_def, map_zsmul]
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11

/-- The lower-left `(1, 0)` entry of a `2 × 2` matrix-valued algebra map `Φ : A →ₐ[R] Mat₂(A)`.
When `Φ` is lower-triangular with diagonal `(x, σ x)` on algebra generators, this linear map is a
`σ`-twisted derivation (`triangularDerivation_mul`). -/
def triangularDerivation [Semiring A] [Algebra R A]
    (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) : A →ₗ[R] A :=
  Matrix.entryLinearMap R A (1 : Fin 2) (0 : Fin 2) ∘ₗ Φ.toLinearMap

/-- Evaluation of `triangularDerivation` as the lower-left matrix entry. -/
@[simp]
theorem triangularDerivation_apply [Semiring A] [Algebra R A]
    (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) (a : A) :
    triangularDerivation Φ a = Φ a 1 0 := (rfl)

/-- **Twisted Leibniz rule for a lower-triangular matrix representation**: if
`Φ : A →ₐ[R] Mat₂(A)` acts as `x ↦ !![x, 0; _, σ x]` on an algebra generating set `s` of `A`,
then its lower-left entry satisfies `d (a * b) = d a * b + σ a * d b`. -/
theorem triangularDerivation_mul [Semiring A] [Algebra R A]
    (σ : A →ₐ[R] A) {Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A} {s : Set A}
    (hs : Algebra.adjoin R s = ⊤)
    (hgen : ∀ x ∈ s, Φ x 0 0 = x ∧ Φ x 0 1 = 0 ∧ Φ x 1 1 = σ x) (a b : A) :
    triangularDerivation Φ (a * b) =
      triangularDerivation Φ a * b + σ a * triangularDerivation Φ b := by
  have hdiag : ∀ c : A, Φ c 0 0 = c ∧ Φ c 0 1 = 0 ∧ Φ c 1 1 = σ c := by
    intro c
    have hc : c ∈ Algebra.adjoin R s := hs ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap r => simp [Matrix.algebraMap_matrix_apply]
    | add x y _ _ hx hy => simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
    | mul x y _ _ hx hy =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
  simp [Matrix.mul_apply, Fin.sum_univ_two, (hdiag a).2.2, (hdiag b).1]

end TauCeti
