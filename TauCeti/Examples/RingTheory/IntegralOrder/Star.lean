/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Maximal
public import TauCeti.RingTheory.IntegralOrder.Star
public import Mathlib.Algebra.QuadraticAlgebra.Integral

/-!
# Star-order examples

Star-orders in four small algebras with involution:

* the integer order `ℤ ⊆ ℚ` with the identity involution;
* the subring `ℚ ⊆ ℚ`, which is star-stable and spans `ℚ` but is not finitely generated over `ℤ`,
  hence underlies no star-order;
* the matrix order `M₂(ℤ) ⊆ M₂(ℚ)` with the transpose, a noncommutative star-order containing the
  matrix units;
* the conjugation-stable order `ℤ[2i]` in `ℚ(i)`, realised as `QuadraticAlgebra ℚ (-1) 0`, whose
  underlying order is not maximal since it lies strictly inside the order `ℤ[i]`.
-/

public section

open QuadraticAlgebra

namespace TauCeti.IntegralOrder.StarOrderExample

/-! ### The integer order in `ℚ` -/

/-- `1 / 2` is not an integer. -/
theorem half_notMem_range : (1 / 2 : ℚ) ∉ Set.range (algebraMap ℤ ℚ) := by
  rintro ⟨n, hn⟩
  rw [algebraMap_int_eq, eq_intCast] at hn
  have : 2 * n = 1 := by exact_mod_cast (by rw [Int.cast_mul, hn]; norm_num : ((2 * n : ℤ) : ℚ) = 1)
  omega

-- The integer order in `ℚ` contains `2` and excludes `1 / 2`.
example : (2 : ℚ) ∈ StarOrder.bot ℤ ℚ := StarOrder.mem_bot.2 ⟨2, by simp⟩

example : (1 / 2 : ℚ) ∉ StarOrder.bot ℤ ℚ := fun h => half_notMem_range (StarOrder.mem_bot.1 h)

-- Its underlying order is the scalar order `ℤ ⊆ ℚ` ...
example : (StarOrder.orderEquiv ℤ ℚ ℚ (StarOrder.bot ℤ ℚ) : Subalgebra ℤ ℚ) = ⊥ := by simp

-- ... and the involution it inherits is the identity.
example (x : StarOrder.bot ℤ ℚ) : star x = x := Subtype.ext (star_trivial _)

/-! ### A star-stable spanning subring which is not an order -/

-- The whole subring `ℚ ⊆ ℚ` is star-stable and spans `ℚ` ...
example : ∀ x ∈ (⊤ : Subalgebra ℤ ℚ), star x ∈ (⊤ : Subalgebra ℤ ℚ) := fun _ _ => trivial

example : Submodule.span ℚ ((⊤ : Subalgebra ℤ ℚ) : Set ℚ) = ⊤ := by
  simp

/-- The subring `ℚ ⊆ ℚ` is not an order, since `1 / 2` is not integral over `ℤ`. -/
theorem not_isOrder_top : ¬ IsOrder ℚ (⊤ : Subalgebra ℤ ℚ) := fun h =>
  half_notMem_range <| IsIntegrallyClosed.isIntegral_iff.1 <|
    h.isIntegral (x := 1 / 2) Algebra.mem_top

-- ... so it underlies no star-order.
example (O : StarOrder ℤ ℚ ℚ) : O.toSubalgebra ≠ ⊤ := fun h => not_isOrder_top (h ▸ O.isOrder)

/-! ### The matrix star-order `M₂(ℤ) ⊆ M₂(ℚ)` -/

-- The involution of `M₂(ℚ)` is the transpose.
example (M : Matrix (Fin 2) (Fin 2) ℚ) : star M = M.transpose := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

-- The underlying order of the matrix star-order is `M₂(ℤ)`.
example :
    (StarOrder.orderEquiv ℤ ℚ _ ((StarOrder.bot ℤ ℚ).matrix (n := Fin 2)) :
      Subalgebra ℤ (Matrix (Fin 2) (Fin 2) ℚ)) = (⊥ : Subalgebra ℤ ℚ).matrix := by
  simp

-- It contains the matrix units ...
example (i j : Fin 2) :
    Matrix.single i j (1 : ℚ) ∈ (StarOrder.bot ℤ ℚ).matrix (n := Fin 2) := by
  refine StarOrder.mem_matrix.2 fun k l => StarOrder.mem_bot.2 ?_
  rw [Matrix.single_apply]
  split_ifs
  exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]

-- ... and is not commutative.
example : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℚ) * Matrix.single 1 0 1 ≠
    Matrix.single 1 0 1 * Matrix.single 0 1 1 := fun h => by
  simpa using congrFun (congrFun h 0) 0

/-! ### The nonmaximal star-order `ℤ[2i] ⊆ ℚ(i)` -/

/-- `ℤ[2i]` consists of the elements `m + 2 k i` of `ℚ(i)` with `m, k ∈ ℤ`. -/
theorem mem_adjoin_two_omega {x : QuadraticAlgebra ℚ (-1) 0} :
    x ∈ Algebra.adjoin ℤ {2 * ω} ↔ ∃ m k : ℤ, x = ⟨m, 2 * k⟩ := by
  refine ⟨fun hx => ?_, ?_⟩
  · induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact ⟨0, 1, by ext <;> simp⟩
    | algebraMap r => exact ⟨r, 0, by ext <;> simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, k, rfl⟩ := hx
      obtain ⟨m', k', rfl⟩ := hy
      exact ⟨m + m', k + k', by ext <;> simp [mul_add]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨m, k, rfl⟩ := hx
      obtain ⟨m', k', rfl⟩ := hy
      exact ⟨m * m' - 4 * k * k', m * k' + k * m', by ext <;> simp <;> ring⟩
  · rintro ⟨m, k, rfl⟩
    have hω : (2 * ω : QuadraticAlgebra ℚ (-1) 0) ∈ Algebra.adjoin ℤ {2 * ω} :=
      Algebra.subset_adjoin rfl
    have : (⟨m, 2 * k⟩ : QuadraticAlgebra ℚ (-1) 0) = algebraMap ℤ _ m + k • (2 * ω) := by
      ext <;> simp [mul_comm]
    rw [this]
    exact add_mem (Subalgebra.algebraMap_mem _ m) (Subalgebra.smul_mem _ hω k)

/-- `ω = i` is integral over `ℤ`. -/
theorem isIntegral_omega_neg_one : IsIntegral ℤ (ω : QuadraticAlgebra ℚ (-1) 0) :=
  isIntegral_omega ⟨-1, by simp⟩ ⟨0, by simp⟩

/-- For `z ∈ ℚ(i)` integral over `ℤ` with nonzero imaginary part, `ℤ[z]` is an order in `ℚ(i)`. -/
theorem isOrder_adjoin_of_im_ne_zero {z : QuadraticAlgebra ℚ (-1) 0} (hz : IsIntegral ℤ z)
    (hz0 : z.im ≠ 0) : IsOrder ℚ (Algebra.adjoin ℤ {z}) := by
  refine isOrder_iff.2 ⟨.of_fg hz.fg_adjoin_singleton, eq_top_iff.2 fun x _ => ?_⟩
  have h1 : (1 : QuadraticAlgebra ℚ (-1) 0) ∈
      Submodule.span ℚ (Algebra.adjoin ℤ {z} : Set (QuadraticAlgebra ℚ (-1) 0)) :=
    Submodule.subset_span (one_mem _)
  have hz' : z ∈ Submodule.span ℚ (Algebra.adjoin ℤ {z} : Set (QuadraticAlgebra ℚ (-1) 0)) :=
    Submodule.subset_span (Algebra.subset_adjoin rfl)
  have hω : (ω : QuadraticAlgebra ℚ (-1) 0) = z.im⁻¹ • (z - z.re • 1) := by
    ext <;> simp [hz0]
  rw [← re_smul_add_im_smul x, hω]
  exact add_mem (Submodule.smul_mem _ _ h1) <| Submodule.smul_mem _ _ <|
    Submodule.smul_mem _ _ <| sub_mem hz' (Submodule.smul_mem _ _ h1)

-- `ℤ[2i]` is a conjugation-stable order in `ℚ(i)` whose underlying order is not maximal.
example : ∃ O : StarOrder ℤ ℚ (QuadraticAlgebra ℚ (-1) 0),
    O.toSubalgebra = Algebra.adjoin ℤ {2 * ω} ∧ ¬ IsMaximalOrder ℚ O.toSubalgebra := by
  have h2ω : IsIntegral ℤ (2 * ω : QuadraticAlgebra ℚ (-1) 0) :=
    (isIntegral_algebraMap (x := (2 : ℤ))).mul isIntegral_omega_neg_one
  refine ⟨StarOrder.ofSubalgebra _ (isOrder_adjoin_of_im_ne_zero h2ω (by simp)) fun x hx => ?_,
    StarOrder.ofSubalgebra_toSubalgebra .., ?_⟩
  · obtain ⟨m, k, rfl⟩ := mem_adjoin_two_omega.1 hx
    exact mem_adjoin_two_omega.2 ⟨m, -k, by ext <;> simp⟩
  -- `ℤ[2i]` lies strictly inside the order `ℤ[i]`, since `i ∈ ℤ[i]` but `i ∉ ℤ[2i]`
  rw [StarOrder.ofSubalgebra_toSubalgebra]
  refine fun h => h.not_gt (isOrder_adjoin_of_im_ne_zero isIntegral_omega_neg_one (by simp)) ?_
  refine IsConcreteLE.lt_iff_le_and_exists.2
    ⟨Algebra.adjoin_le ?_, ω, Algebra.subset_adjoin rfl, ?_⟩
  · rintro _ rfl
    exact mul_mem (Subalgebra.algebraMap_mem _ (2 : ℤ)) (Algebra.subset_adjoin rfl)
  · rintro hω
    obtain ⟨m, k, h⟩ := mem_adjoin_two_omega.1 hω
    have h1 : (1 : ℚ) = 2 * k := by simpa using congrArg QuadraticAlgebra.im h
    have : (1 : ℤ) = 2 * k := by exact_mod_cast h1
    omega

end TauCeti.IntegralOrder.StarOrderExample
