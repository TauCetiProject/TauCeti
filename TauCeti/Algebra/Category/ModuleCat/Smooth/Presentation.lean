/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Smooth.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite-sum presentations by smooth cyclic quotients

For a downward directed family of left ideals `J i`, finitely many vectors in a smooth
module have a common annihilating ideal. If those vectors generate the module, their orbit
maps descend to a surjection from a finite sum of copies of `A ⧸ J i`.

Here finite sums are represented by finite products of modules. These are module quotients:
the left ideals need not be two-sided, and no quotient ring structure is used. The common
ideal kills the chosen generators, not necessarily the whole module.

This supplies presentations from which actions on smooth modules can be descended once
compatible actions on the cyclic quotients have been constructed.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for the use of
  congruence-induced presentations in integration of finitely generated smooth modules.
-/

public section

noncomputable section

namespace TauCeti

variable {A : Type*} [Ring A] {ι : Type*} {J : ι → Submodule A A}

/-- Finitely many vectors of a smooth module have a common annihilating ideal in a
nonempty downward directed family. This does not assert a uniform annihilator for the
whole module. -/
theorem exists_forall_smul_eq_zero_of_smoothModules [Nonempty ι]
    (hJ : Directed (· ≥ ·) J) {M : ModuleCat A} (hM : smoothModules J M)
    {κ : Type*} [Finite κ] (v : κ → M) :
    ∃ i, ∀ k a, a ∈ J i → a • v k = 0 := by
  classical
  let _ := Fintype.ofFinite κ
  rw [smoothModules_iff] at hM
  choose i hi using fun k ↦ hM (v k)
  obtain ⟨i₀, hi₀⟩ := hJ.finset_le (Finset.univ.image i)
  exact ⟨i₀, fun k a ha ↦ hi k a
    (hi₀ (i k) (Finset.mem_image_of_mem i (Finset.mem_univ k)) ha)⟩

/-- A finite generating family in a smooth module gives a surjection from copies of one
cyclic quotient. The map sends the class of `1` in the `k`-th summand to the specified
`k`-th generator. -/
theorem exists_surjective_pi_quotient_of_smoothModules_of_span_eq_top [Nonempty ι]
    (hJ : Directed (· ≥ ·) J) {M : ModuleCat A} (hM : smoothModules J M)
    {κ : Type*} [Finite κ] [DecidableEq κ] (v : κ → M) (hv : Submodule.span A (Set.range v) = ⊤) :
    ∃ i, ∃ f : (κ → A ⧸ J i) →ₗ[A] M, Function.Surjective f ∧
      ∀ k, f (Pi.single k ((J i).mkQ 1)) = v k := by
  classical
  let _ := Fintype.ofFinite κ
  obtain ⟨i, hi⟩ := exists_forall_smul_eq_zero_of_smoothModules hJ hM v
  let g (k : κ) : (A ⧸ J i) →ₗ[A] M :=
    (J i).liftQ (LinearMap.toSpanSingleton A M (v k)) (by
      intro a ha
      exact LinearMap.mem_ker.mpr (by simpa using hi k a ha))
  let f : (κ → A ⧸ J i) →ₗ[A] M := LinearMap.lsum A _ ℕ g
  have hf (k : κ) : f (Pi.single k ((J i).mkQ 1)) = v k := by
    dsimp only [f]
    rw [LinearMap.lsum_piSingle]
    dsimp only [g]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
    simp
  refine ⟨i, f, LinearMap.range_eq_top.mp ?_, hf⟩
  apply top_unique
  rw [← hv]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun k ↦ ⟨_, hf k⟩)

/-- Every finitely generated smooth module is a quotient of a finite sum of copies of
one cyclic quotient `A ⧸ J i`. The indexing number may be zero. -/
theorem exists_surjective_pi_quotient_of_smoothModules [Nonempty ι]
    (hJ : Directed (· ≥ ·) J) {M : ModuleCat A} [Module.Finite A M]
    (hM : smoothModules J M) :
    ∃ (i : ι) (n : ℕ) (f : (Fin n → A ⧸ J i) →ₗ[A] M), Function.Surjective f := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := M)
  obtain ⟨i, f, hf, -⟩ :=
    exists_surjective_pi_quotient_of_smoothModules_of_span_eq_top hJ hM v hv
  exact ⟨i, n, f, hf⟩

/-- If the cyclic quotients are smooth, they detect smoothness of finitely generated
modules by finite-sum presentations. No stability under arbitrary extensions is assumed. -/
theorem smoothModules_iff_exists_surjective_pi_quotient [Nonempty ι]
    (hJ : Directed (· ≥ ·) J)
    (hQ : ∀ i, smoothModules J (ModuleCat.of A (A ⧸ J i)))
    {M : ModuleCat A} [Module.Finite A M] :
    smoothModules J M ↔
      ∃ (i : ι) (n : ℕ) (f : (Fin n → A ⧸ J i) →ₗ[A] M), Function.Surjective f := by
  refine ⟨exists_surjective_pi_quotient_of_smoothModules hJ, ?_⟩
  rintro ⟨i, n, f, hf⟩
  rw [smoothModules_iff]
  intro m
  obtain ⟨x, rfl⟩ := hf m
  obtain ⟨j, hj⟩ := exists_forall_smul_eq_zero_of_smoothModules hJ (hQ i) x
  refine ⟨j, fun a ha ↦ ?_⟩
  rw [← map_smul]
  have hx : a • x = 0 := funext fun k ↦ hj k a ha
  rw [hx, map_zero]

end TauCeti
