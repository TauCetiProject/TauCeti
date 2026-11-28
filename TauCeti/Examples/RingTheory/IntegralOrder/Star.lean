/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Maximal
public import TauCeti.RingTheory.IntegralOrder.Star
public import Mathlib.Algebra.QuadraticAlgebra.Integral
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Star-order examples

Star-orders in four small algebras with involution:

* the integer order `ℤ ⊆ ℚ` with the identity involution;
* the subring `ℚ ⊆ ℚ`, which is star-stable and spans `ℚ` but is not finitely generated over `ℤ`,
  hence underlies no star-order;
* the matrix order `M₂(ℤ) ⊆ M₂(ℚ)` with the transpose, a noncommutative star-order containing the
  matrix units;
* the conjugation-stable order `ℤ[2i]` in `ℚ(i)`, realised as `QuadraticAlgebra ℚ (-1) 0`, whose
  underlying order is not maximal since it lies strictly inside the order `ℤ[i]`, with index `2`;
  the localizations of `ℤ[2i]` and `ℤ[i]` at every submonoid of `ℤ` containing `2` agree, so
  the inclusion becomes an equality over `ℤ_(p)` for `p` odd.
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

/-- `ℤ[c i]` consists of the elements `m + c k i` of `ℚ(i)` with `m, k ∈ ℤ`. -/
theorem mem_adjoin_intCast_mul_omega (c : ℤ) {x : QuadraticAlgebra ℚ (-1) 0} :
    x ∈ Algebra.adjoin ℤ {(c : QuadraticAlgebra ℚ (-1) 0) * ω} ↔
      ∃ m k : ℤ, x = ⟨m, c * k⟩ := by
  -- `ℤ[c i]` is the image of `ℤ[√(-c²)]` under `ω ↦ c i`.
  have h : ((c : QuadraticAlgebra ℚ (-1) 0) * ω) * ((c : QuadraticAlgebra ℚ (-1) 0) * ω) =
      (-c ^ 2 : ℤ) • 1 + (0 : ℤ) • ((c : QuadraticAlgebra ℚ (-1) 0) * ω) := by
    ext <;> simp [sq]
  rw [← range_lift h, AlgHom.mem_range]
  refine ⟨fun ⟨y, hy⟩ => ⟨y.re, y.im, ?_⟩, fun ⟨m, k, hx⟩ => ⟨⟨m, k⟩, ?_⟩⟩
  · rw [← hy]
    ext <;> simp [mul_comm]
  · rw [hx]
    ext <;> simp [mul_comm]

/-- `ℤ[2i]` consists of the elements `m + 2 k i` of `ℚ(i)` with `m, k ∈ ℤ`. -/
theorem mem_adjoin_two_omega {x : QuadraticAlgebra ℚ (-1) 0} :
    x ∈ Algebra.adjoin ℤ {2 * ω} ↔ ∃ m k : ℤ, x = ⟨m, 2 * k⟩ := by
  simpa using mem_adjoin_intCast_mul_omega 2

/-- `ℤ[i]` consists of the elements `m + k i` of `ℚ(i)` with `m, k ∈ ℤ`. -/
theorem mem_adjoin_omega {x : QuadraticAlgebra ℚ (-1) 0} :
    x ∈ Algebra.adjoin ℤ {ω} ↔ ∃ m k : ℤ, x = ⟨m, k⟩ := by
  simpa using mem_adjoin_intCast_mul_omega 1

/-- An element `m + k i` of `ℤ[i]` lies in `ℤ[2i]` exactly when `k` is even. -/
theorem mk_mem_adjoin_two_omega_iff {m k : ℤ} :
    (⟨m, k⟩ : QuadraticAlgebra ℚ (-1) 0) ∈ Algebra.adjoin ℤ {2 * ω} ↔ Even k := by
  rw [mem_adjoin_two_omega]
  refine ⟨fun ⟨m', k', h⟩ => ⟨k', ?_⟩, fun ⟨k', hk⟩ => ⟨m, k', by ext <;> simp [hk, two_mul]⟩⟩
  have : (k : ℚ) = 2 * k' := by simpa using congrArg QuadraticAlgebra.im h
  have : k = 2 * k' := by exact_mod_cast this
  omega

/-- `ℤ[2i] ⊆ ℤ[i]`. -/
theorem adjoin_two_omega_le_adjoin_omega :
    Algebra.adjoin ℤ {2 * ω} ≤ Algebra.adjoin ℤ {(ω : QuadraticAlgebra ℚ (-1) 0)} := by
  refine Algebra.adjoin_le ?_
  rintro _ rfl
  exact mul_mem (Subalgebra.algebraMap_mem _ (2 : ℤ)) (Algebra.subset_adjoin rfl)

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
    ⟨adjoin_two_omega_le_adjoin_omega, ω, Algebra.subset_adjoin rfl, fun hω => ?_⟩
  have : (ω : QuadraticAlgebra ℚ (-1) 0) = ⟨((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)⟩ := by
    ext <;> simp
  exact Int.not_even_one (mk_mem_adjoin_two_omega_iff.1 (this ▸ hω))

/-! ### The inclusion `ℤ[2i] ⊆ ℤ[i]` -/

/-- Twice an element of `ℤ[i]` lies in `ℤ[2i]`. -/
theorem add_self_mem_adjoin_two_omega {x : QuadraticAlgebra ℚ (-1) 0}
    (hx : x ∈ Algebra.adjoin ℤ {ω}) : x + x ∈ Algebra.adjoin ℤ {2 * ω} := by
  obtain ⟨m, k, rfl⟩ := mem_adjoin_omega.1 hx
  have : (⟨m, k⟩ + ⟨m, k⟩ : QuadraticAlgebra ℚ (-1) 0) = ⟨(2 * m : ℤ), (2 * k : ℤ)⟩ := by
    ext <;> simp [two_mul]
  rw [this, mk_mem_adjoin_two_omega_iff]
  exact even_two_mul k

/-- The inclusion `ℤ[2i] ⊆ ℤ[i]` has index `2`: `i` represents the nontrivial coset. -/
theorem relIndex_adjoin_two_omega :
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ {2 * ω})).toAddSubgroup.relIndex
      (Subalgebra.toSubmodule
        (Algebra.adjoin ℤ {(ω : QuadraticAlgebra ℚ (-1) 0)})).toAddSubgroup = 2 := by
  refine AddSubgroup.relIndex_eq_two_iff.2 ⟨ω, Algebra.subset_adjoin rfl, fun b hb => ?_⟩
  obtain ⟨m, k, rfl⟩ := mem_adjoin_omega.1 hb
  have : (⟨m, k⟩ + ω : QuadraticAlgebra ℚ (-1) 0) = ⟨m, (k + 1 : ℤ)⟩ := by
    ext <;> simp
  simp only [Submodule.mem_toAddSubgroup, Subalgebra.mem_toSubmodule, this,
    mk_mem_adjoin_two_omega_iff, Int.even_add_one]
  by_cases h : Even k <;> simp [h]

/-- **The inclusion `ℤ[2i] ⊆ ℤ[i]` is an equality away from `2`.** For every submonoid `S` of `ℤ`
containing `2`, the localizations at `S` of the underlying `ℤ`-modules of the orders `ℤ[2i]` and
`ℤ[i]` agree, as `ℤ_S`-submodules of the localization of `ℚ(i)`. This applies in particular to the
complement `S = P.primeCompl` of any prime `P` of `ℤ` not containing `2`, such as `P = (p)` for an
odd prime `p`, giving the equality over `ℤ_(p)`. -/
theorem localized_adjoin_two_omega (S : Submonoid ℤ) (h2 : (2 : ℤ) ∈ S) :
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ {2 * ω})).localized S =
      (Subalgebra.toSubmodule
        (Algebra.adjoin ℤ {(ω : QuadraticAlgebra ℚ (-1) 0)})).localized S := by
  -- Over `ℤ`, Mathlib's lemmas on localized submodules would otherwise use the instance
  -- `AddCommGroup.toIntModule` on the localization, which is not the one of `localized`.
  let : Module ℤ (LocalizedModule S (QuadraticAlgebra ℚ (-1) 0)) :=
    OreLocalization.instModuleOfIsScalarTower
  -- Twice every element of `ℤ[i]` lies in `ℤ[2i]`, and `2` is invertible in `ℤ_S`.
  refine le_antisymm
    ((Submodule.localized'gi _ _ _).gc.monotone_l adjoin_two_omega_le_adjoin_omega)
    (Submodule.localized'_le_localized'_of_smul_le _ _ _ ⟨2, h2⟩ ?_)
  rintro _ ⟨a, ha, rfl⟩
  simpa [Submonoid.smul_def, two_smul] using add_self_mem_adjoin_two_omega ha

end TauCeti.IntegralOrder.StarOrderExample
