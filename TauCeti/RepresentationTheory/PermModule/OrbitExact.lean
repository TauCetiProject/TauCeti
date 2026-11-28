/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.LinearAlgebra.Prod


/-!
# Orbit-complement short exact sequence for permutation function modules

This file proves two ingredients for the permutation-module dévissage in the Cartan map /
multiplicative-invariant argument:

* `TauCeti.perm_pow_eq_one_of_map_sub`: a permutation of an abelian group killed by `n` that
  preserves differences is a translation, so its `n`-th power is the identity.
* `TauCeti.exists_exact_orbitCompl_functionModule`: for a `Δ`-set `Y`, a point `y : Y`, and an
  `R`-module `M`, the function module `Y → M` sits in a short exact sequence
  `0 → (C → M) → (Y → M) → (Δ ⧸ stabilizer Δ y → M) → 0`
  where `C` is the orbit complement of `y`, and both maps are `Δ`-equivariant for precomposition
  `(d • f) x = f (d⁻¹ • x)`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/Lib/General/Algebra/CartanMap.lean`
(`New.DiscreteModule.perm_pow_eq_one_of_map_sub`,
`New.DiscreteModule.exists_isShortExact_permModule`).
-/

public section

open MulAction

namespace TauCeti

/-- A permutation of an abelian group killed by `n` that preserves differences is a translation, so
its `n`-th power is trivial. -/
theorem perm_pow_eq_one_of_map_sub {V : Type*} [AddCommGroup V] {n : ℕ}
    (h_killed : ∀ x : V, n • x = 0) {σ : Equiv.Perm V}
    (hσ : ∀ x y : V, σ x - σ y = x - y) :
    σ ^ n = 1 := by
  have h_transl : σ = Equiv.addLeft (σ 0) :=
    Equiv.ext fun x ↦ by simpa [sub_eq_iff_eq_add'] using hσ x 0
  rw [h_transl]
  ext x
  simp [h_killed]

/-- For an `R`-module `M`, a group `Δ` acting on `Y`, and `y : Y`, let `C` be the complement of
the orbit of `y` in `Y`. There exist `R`-linear maps `ι : (C → M) →ₗ[R] (Y → M)` and
`π : (Y → M) →ₗ[R] (Δ ⧸ stabilizer Δ y → M)` forming a short exact sequence that are equivariant
for the precomposition action `(d, f) ↦ (x ↦ f (d⁻¹ • x))`. -/
theorem exists_exact_orbitCompl_functionModule {R M Δ Y : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [Group Δ] [MulAction Δ Y] (y : Y) :
    let C : SubMulAction Δ Y :=
      (SubMulAction.mk (orbit Δ y) fun g : Δ ↦ mem_orbit_of_mem_orbit g)ᶜ
    ∃ (ι : (C → M) →ₗ[R] (Y → M)) (π : (Y → M) →ₗ[R] (Δ ⧸ stabilizer Δ y → M)),
      Function.Injective ι ∧ Function.Exact ι π ∧ Function.Surjective π ∧
      (∀ (d : Δ) (w : C → M) (x : Y),
        ι (fun c : C ↦ w (d⁻¹ • c)) x = ι w (d⁻¹ • x)) ∧
      (∀ (d : Δ) (v : Y → M) (q : Δ ⧸ stabilizer Δ y),
        π (fun x : Y ↦ v (d⁻¹ • x)) q = π v (d⁻¹ • q)) := by
  classical
  intro C
  let e : (Δ ⧸ stabilizer Δ y) ⊕ C ≃ Y :=
    ((orbitEquivQuotientStabilizer Δ y).symm.sumCongr (.refl C)).trans
      (Equiv.sumCompl fun x : Y ↦ x ∈ orbit Δ y)
  let E : (Y → M) ≃ₗ[R] (Δ ⧸ stabilizer Δ y → M) × (C → M) :=
    LinearEquiv.funCongrLeft R M e ≪≫ₗ LinearEquiv.sumArrowLequivProdArrow _ _ R M
  let ι : (C → M) →ₗ[R] (Y → M) := E.symm ∘ₗ LinearMap.inr R (Δ ⧸ stabilizer Δ y → M) (C → M)
  let π : (Y → M) →ₗ[R] (Δ ⧸ stabilizer Δ y → M) :=
    LinearMap.fst R (Δ ⧸ stabilizer Δ y → M) (C → M) ∘ₗ E
  have h_exact : Function.Exact ι π := (E.conj_symm_exact_iff_exact _ _).mpr .inr_fst
  have π_apply (v : Y → M) (d : Δ) : π v (d : Δ ⧸ stabilizer Δ y) = v (d • y) := rfl
  have ι_orbit (w : C → M) (d : Δ) : ι w (d • y) = 0 := by
    simp [← π_apply (ι w), h_exact.apply_apply_eq_zero]
  have ι_compl (w : C → M) (c : C) : ι w c = w c := show ι w (e (.inr c)) = w c by simp [ι, E]
  refine ⟨ι, π, E.symm.injective.comp LinearMap.inr_injective, h_exact,
    Prod.fst_surjective.comp E.surjective, fun d w x ↦ ?_, fun d v q ↦ ?_⟩
  · by_cases hx : x ∈ orbit Δ y
    · obtain ⟨g, rfl⟩ := hx
      simp [smul_smul, ι_orbit]
    · lift x to C using hx
      simpa [ι_compl] using (ι_compl w (d⁻¹ • x)).symm
  · refine Quotient.inductionOn' q fun g ↦ ?_
    simp [π_apply, mul_smul]

end TauCeti
