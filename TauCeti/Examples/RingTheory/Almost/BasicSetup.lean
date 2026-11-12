/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.BasicSetup
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Examples of basic setups

These examples test the basic setups of almost mathematics on their degenerate members, the
classical setup `(V, V)` and the zero setup `(V, 0)`, and on concrete computations over `ℤ`:

* the multiplication maps `m~ → V` and `m~ → m` are computed on explicit tensors, and are
  bijective onto `m` for the classical and the zero setups, while `m~` vanishes for the zero setup;
* the residue module `V ⧸ m` is almost zero for every setup, as are submodules, quotients and
  isomorphic copies of almost zero modules, while `ℤ` is not almost zero for the
  classical setup;
* the inclusion `m → V` is always an almost isomorphism, every map is one for the zero setup, and
  multiplication by `2` on `ℤ` is not one for the classical setup;
* the classical and the zero setups satisfy conditions (A) and (B);
* the maximal ideal of `ℤ_[p]` is not idempotent, so it underlies no basic setup.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.1.
-/

open TensorProduct TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V]

/-! ### The module `m~` and its multiplication maps -/

-- Over the classical setup `(ℤ, ℤ)`, `2 ⊗ 3 + 5 ⊗ 7 ↦ 2 * 3 + 5 * 7 = 41`.
example : (classical ℤ).tildeMul
    ((⟨2, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨3, by simp⟩ : (classical ℤ).ideal) +
      (⟨5, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨7, by simp⟩ : (classical ℤ).ideal)) = 41 := by
  simp only [map_add, tildeMul_tmul]
  norm_num

example : ((classical ℤ).tildeToIdeal
    ((⟨2, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨3, by simp⟩ : (classical ℤ).ideal) +
      (⟨5, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨7, by simp⟩ : (classical ℤ).ideal)) : ℤ) =
    41 := by
  simp only [map_add, Submodule.coe_add, coe_tildeToIdeal, tildeMul_tmul]
  norm_num

example : (classical V).tildeMul ((⟨1, by simp⟩ : (classical V).ideal) ⊗ₜ ⟨1, by simp⟩) = 1 := by
  simp

-- For the zero setup, `m~ = 0 ⊗ 0` vanishes, so the multiplication map `m~ → V` is zero.
example : Subsingleton (zero V).tilde :=
  inferInstance

example : (zero V).tildeMul = 0 := by
  simp

-- Multiplication `m~ → m` is bijective for the classical setup: it is the identification
-- `V ⊗[V] V ≅ V`.
example : Function.Bijective (classical V).tildeToIdeal :=
  classical_tildeToIdeal_bijective

-- Multiplication `m~ → m` is bijective for the zero setup, both sides being zero.
example : Function.Bijective (zero V).tildeToIdeal :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-! ### Almost zero modules -/

-- The residue module `V ⧸ m` and the zero module are almost zero for every setup.
example (S : BasicSetup V) : S.almostZero (ModuleCat.of V (V ⧸ S.ideal)) :=
  (S.almostZero_iff _).mpr S.isAlmostZero_quotient

example (S : BasicSetup V) : S.almostZero (ModuleCat.of V PUnit) :=
  (S.almostZero_iff _).mpr S.isAlmostZero_of_subsingleton

-- Submodules and quotients of almost zero modules are almost zero, and so is every module
-- isomorphic in `ModuleCat V` to an almost zero one.
example (S : BasicSetup V) {M : Type*} [AddCommGroup M] [Module V M] (h : S.IsAlmostZero M)
    (N : Submodule V M) : S.IsAlmostZero N ∧ S.IsAlmostZero (M ⧸ N) :=
  ⟨h.of_injective N.injective_subtype, h.of_surjective N.mkQ_surjective⟩

example (S : BasicSetup V) {M N : ModuleCat V} (e : M ≅ N) (h : S.almostZero M) :
    S.almostZero N :=
  S.almostZero.prop_of_iso e h

-- `ℤ` is not almost zero for the classical setup `(ℤ, ℤ)`.
example : ¬ (classical ℤ).IsAlmostZero ℤ := by
  rw [isAlmostZero_classical_iff]
  exact not_subsingleton ℤ

example : ¬ (classical ℤ).almostZero (ModuleCat.of ℤ ℤ) := by
  rw [almostZero_iff, isAlmostZero_classical_iff]
  exact not_subsingleton ℤ

-- Every module, for instance `ℤ`, is almost zero for the zero setup.
example : (zero ℤ).IsAlmostZero ℤ :=
  isAlmostZero_zero

/-! ### Almost isomorphisms -/

-- The inclusion `m → V` is an almost isomorphism, and every map is one for the zero setup.
example (S : BasicSetup V) : S.IsAlmostIso S.ideal.subtype :=
  S.isAlmostIso_subtype

example : (zero ℤ).IsAlmostIso (LinearMap.mulLeft ℤ (2 : ℤ)) :=
  isAlmostIso_zero _

-- Multiplication by `2` on `ℤ` is injective but not surjective, so it is not an almost
-- isomorphism for the classical setup.
example : ¬ (classical ℤ).IsAlmostIso (LinearMap.mulLeft ℤ (2 : ℤ)) := by
  rw [isAlmostIso_classical_iff]
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := h 1
  rw [LinearMap.mulLeft_apply] at hx
  omega

/-! ### Conditions (A) and (B) -/

-- For the classical setup, `1` is a common divisor in `m`.
example : (classical V).IsFilteredPrincipal :=
  isFilteredPrincipal_iff.mpr fun _ _ _ _ ↦ ⟨1, by simp, one_dvd _, one_dvd _⟩

-- For the zero setup, `0` is a common divisor in `m = 0`.
example : (zero V).IsFilteredPrincipal :=
  isFilteredPrincipal_iff.mpr fun x hx y hy ↦ by
    simp only [zero_ideal, Ideal.mem_bot] at hx hy
    exact ⟨0, by simp, by simp [hx], by simp [hy]⟩

example : (classical V).PowersGenerate :=
  IsFilteredPrincipal.powersGenerate <|
    isFilteredPrincipal_iff.mpr fun _ _ _ _ ↦ ⟨1, by simp, one_dvd _, one_dvd _⟩

example : (zero V).PowersGenerate := by
  refine powersGenerate_iff.mpr fun k hk ↦ ?_
  simp only [zero_ideal, Submodule.bot_coe, Set.image_singleton, zero_pow hk.ne',
    Ideal.span_singleton_eq_bot]

/-! ### A non-example -/

-- The maximal ideal `(p)` of `ℤ_[p]` is not idempotent, since `(p) * (p) = (p ^ 2) ≠ (p)`; so
-- there is no basic setup with this ideal.
example (p : ℕ) [Fact p.Prime] : ¬ IsIdempotentElem (IsLocalRing.maximalIdeal ℤ_[p]) := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  intro h
  have hp : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} * Ideal.span {(p : ℤ_[p])} :=
    h.eq.symm ▸ Ideal.mem_span_singleton_self _
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at hp
  obtain ⟨c, hc⟩ := hp
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpc : (p : ℤ_[p]) * c = 1 :=
    mul_left_cancel₀ hp0 (by rw [← mul_assoc, ← hc, mul_one])
  exact (mem_nonunits_iff.mp PadicInt.p_nonunit) (IsUnit.of_mul_eq_one _ hpc)
