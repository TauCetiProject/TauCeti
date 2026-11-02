/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.RootSetup
import TauCeti.RingTheory.Perfect.FrobeniusRootIdeal

/-!
# Examples of root setups

These examples test the root setup of a compatible sequence of `p`-power roots:

* the constant sequence `1` gives the classical setup, and so does every sequence starting with a
  unit, while the constant sequence `0` gives the zero setup;
* a sequence with `ϖ 0 = 0` but `ϖ 1 ≠ 0` has a nonzero ideal, so `ϖ 0 = 0` alone does not force
  the zero setup; its `m~` is flat although no root is a nonzerodivisor;
* if `ϖ 0` does not divide `ϖ 1`, then `V ⧸ (ϖ 0)` is not almost zero, while `V ⧸ m` is;
* in a perfect ring of characteristic `p`, the root setup of the `p`-power roots of `f` has as
  ideal the radical of `(f)`.
-/

open TauCeti TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V] {p : ℕ} (hp : 2 ≤ p)

/-! ### Degenerate sequences -/

-- The constant sequence `1` gives the classical setup.
example : ofCompatibleRoots hp (ϖ := fun _ ↦ (1 : V)) (fun _ ↦ one_pow p) = classical V :=
  BasicSetup.ext (by simp)

-- A sequence starting with a unit gives the classical setup.
example {ϖ : ℕ → V} (hϖ : ∀ n, ϖ (n + 1) ^ p = ϖ n) (hu : IsUnit (ϖ 0)) :
    ofCompatibleRoots hp hϖ = classical V :=
  BasicSetup.ext <| (classical_ideal (V := V)).symm ▸
    Ideal.eq_top_of_isUnit_mem _ (root_mem_ofCompatibleRoots_ideal hp hϖ 0) hu

-- The constant sequence `0` gives the zero setup.
example : ofCompatibleRoots hp (ϖ := fun _ ↦ (0 : V)) (fun _ ↦ zero_pow (by omega)) = zero V :=
  BasicSetup.ext (by simp)

-- If `ϖ 0 = 0` but `ϖ 1 ≠ 0`, the ideal of the root setup is not zero.
example {ϖ : ℕ → V} (hϖ : ∀ n, ϖ (n + 1) ^ p = ϖ n) (h₁ : ϖ 1 ≠ 0) :
    (ofCompatibleRoots hp hϖ).ideal ≠ ⊥ := fun h ↦
  h₁ <| (Submodule.mem_bot V).mp (h ▸ root_mem_ofCompatibleRoots_ideal hp hϖ 1)

-- `m~` is flat for every root setup, even when `ϖ 0 = 0`, so that no root is a nonzerodivisor.
example {ϖ : ℕ → V} (hϖ : ∀ n, ϖ (n + 1) ^ p = ϖ n) :
    Module.Flat V (ofCompatibleRoots hp hϖ).tilde :=
  inferInstance

/-! ### Almost zero quotients -/

-- If `ϖ 0` does not divide `ϖ 1`, then `V ⧸ (ϖ 0)` is not almost zero: `ϖ 1` acts nontrivially.
example {ϖ : ℕ → V} (hϖ : ∀ n, ϖ (n + 1) ^ p = ϖ n) (h : ¬ ϖ 0 ∣ ϖ 1) :
    ¬ (ofCompatibleRoots hp hϖ).IsAlmostZero (V ⧸ Ideal.span {ϖ 0}) := by
  rw [ofCompatibleRoots_isAlmostZero_iff]
  intro h₀
  have := h₀ 1 (Ideal.Quotient.mk _ 1)
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  exact h this

-- The quotient `V ⧸ m` by the root ideal is almost zero.
example {ϖ : ℕ → V} (hϖ : ∀ n, ϖ (n + 1) ^ p = ϖ n) :
    (ofCompatibleRoots hp hϖ).IsAlmostZero (V ⧸ (ofCompatibleRoots hp hϖ).ideal) :=
  (ofCompatibleRoots hp hϖ).isAlmostZero_quotient

/-! ### Perfect rings -/

-- In a perfect ring of characteristic `p`, the root setup of the `p`-power roots of `f` has as
-- ideal the radical of `(f)`.
example {R : Type*} [CommRing R] [hp' : Fact p.Prime] [ExpChar R p] [PerfectRing R p] (f : R) :
    (ofCompatibleRoots hp'.out.two_le (ϖ := fun n ↦ (iterateFrobeniusEquiv R p n).symm f)
      fun n ↦ iterateFrobeniusEquiv_symm_succ_pow f n).ideal = (Ideal.span {f}).radical := by
  rw [ofCompatibleRoots_ideal, ← frobeniusRootIdeal_eq_span_range, frobeniusRootIdeal_eq_radical]
