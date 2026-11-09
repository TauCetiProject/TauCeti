/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Quotient
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration
public import Mathlib.RingTheory.FilteredAlgebra.Basic

import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The induced filtration on a module completion

The limit of a tower of modules has the decreasing filtration with zeroth term the whole
module and positive terms the kernels of its projections. This filtration is complete and
separated, and carries Mathlib's `IsFiltration` on order-dual natural numbers. For a tower
with surjective transitions, its finite quotients recover the terms of the tower.

For completions along arbitrary decreasing submodules, the canonical map preserves and
reflects the positive filtration terms, and semilinear completion maps retain their cutoff
bounds. Completeness in the sense of `IsCompleteFiltration` is equivalent to bijectivity
of the canonical map into the quotient-tower limit. In particular, completing an induced
filtration again gives the same module.

Adapted from `Mei/LinearAlgebra/ModuleFiltration/Completion.lean` and `Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`61509bfe75ce943898bc99cfa509fb40bb78c614` (Apache 2.0). The constructions here use
Tau Ceti's existing `ModuleTower` limits and completion maps.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe v u
variable {R : Type u} [Ring R] (F : ModuleTower.{v} R)

/-- The induced filtration on a tower limit: order `k + 1` is the kernel of projection to
order `k`, and order zero is the whole limit. -/
def limFiltration : ℕ → Submodule R F.lim
  | 0 => ⊤
  | k + 1 => LinearMap.ker (F.limπ k)

@[simp]
theorem limFiltration_zero : F.limFiltration 0 = ⊤ := (rfl)

@[simp]
theorem limFiltration_succ (k : ℕ) :
    F.limFiltration (k + 1) = LinearMap.ker (F.limπ k) := (rfl)

/-- The induced filtration is decreasing. -/
theorem limFiltration_antitone : Antitone F.limFiltration := by
  intro a b hab
  cases a with
  | zero => simp
  | succ a =>
    cases b with
    | zero => omega
    | succ b => exact F.ker_limπ_antitone (Nat.le_of_succ_le_succ hab)

instance : IsFiltration (fun k : ℕᵒᵈ => F.limFiltration k.ofDual)
    (fun k => F.limFiltration (k.ofDual + 1)) where
  mono := fun _ _ h => F.limFiltration_antitone h
  is_le h := F.limFiltration_antitone (Nat.succ_le_of_lt h)
  is_sup _ k h := h (OrderDual.toDual (k.ofDual + 1)) (Nat.lt_succ_self _)

/-- The induced filtration is separated, even if the transitions are not surjective. -/
@[simp]
theorem iInf_limFiltration : (⨅ k, F.limFiltration k) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply (Submodule.mem_bot R).mpr
  apply F.lim_ext
  intro k
  simpa only [map_zero, limFiltration_succ, LinearMap.mem_ker] using
    (Submodule.mem_iInf _).mp hx (k + 1)

/-- The induced filtration on any tower limit is complete and separated. -/
theorem isCompleteFiltration_lim : IsCompleteFiltration F.limFiltration where
  antitone := F.limFiltration_antitone
  eq_zero_of_forall_mem x hx := by
    have h : x ∈ ⨅ k, F.limFiltration k := (Submodule.mem_iInf _).mpr hx
    simpa using h
  exists_limit x hx := by
    -- Each coordinate stabilizes once the differences lie in its projection kernel.
    have hconst (k m : ℕ) (hkm : k + 1 ≤ m) :
        F.limπ k (x m) = F.limπ k (x (k + 1)) := by
      induction m, hkm using Nat.le_induction with
      | base => rfl
      | succ m hkm ih =>
        have hm := F.limFiltration_antitone hkm (hx m)
        rw [limFiltration_succ, LinearMap.mem_ker, map_sub, sub_eq_zero] at hm
        exact hm.trans ih
    let L : F.lim := ⟨fun k => F.limπ k (x (k + 1)), F.mem_lim.mpr fun k => by
      rw [← LinearMap.comp_apply, F.transition_comp_limπ]
      exact hconst k (k + 1 + 1) (by omega)⟩
    have hL (k : ℕ) : F.limπ k L = F.limπ k (x (k + 1)) := F.limπ_apply k L
    refine ⟨L, fun n => ?_⟩
    cases n with
    | zero => simp
    | succ k =>
      rw [limFiltration_succ, LinearMap.mem_ker, map_sub, hL, sub_self]

/-- If the tower transitions are surjective, quotienting its limit by the order-`k + 1`
filtration term recovers its order-`k` module. -/
def limFiltrationQuotientEquiv (hF : ∀ n, Function.Surjective (F.transition n)) (k : ℕ) :
    (F.lim ⧸ F.limFiltration (k + 1)) ≃ₗ[R] F.obj (op k) :=
  (Submodule.quotEquivOfEq _ _ (F.limFiltration_succ k)).trans
    ((F.limπ k).quotKerEquivOfSurjective (F.limπ_surjective hF k))

@[simp]
theorem limFiltrationQuotientEquiv_mk
    (hF : ∀ n, Function.Surjective (F.transition n)) (k : ℕ) (x : F.lim) :
    F.limFiltrationQuotientEquiv hF k (Submodule.Quotient.mk x) = F.limπ k x := by
  simp [limFiltrationQuotientEquiv]

/-- The finite-quotient comparisons commute with every transition. -/
@[simp]
theorem limFiltrationQuotientEquiv_factor
    (hF : ∀ n, Function.Surjective (F.transition n)) {k l : ℕ} (hkl : k ≤ l)
    (x : F.lim ⧸ F.limFiltration (l + 1)) :
    F.limFiltrationQuotientEquiv hF k
        (Submodule.factor (F.limFiltration_antitone (Nat.add_le_add_right hkl 1)) x) =
      F.transitionOfLE hkl (F.limFiltrationQuotientEquiv hF l x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    simp only [Submodule.factor, Submodule.mapQ_apply, LinearMap.id_apply,
      limFiltrationQuotientEquiv_mk, ← LinearMap.comp_apply, transitionOfLE_comp_limπ]

section Quotients

variable {M : Type v} [AddCommGroup M] [Module R M]
  (J : ℕ → Submodule R M) (hJ : Antitone J)

/-- Every source cutoff bound for a semilinear map is retained on the induced filtrations
of the completions. -/
theorem limFiltration_le_comap_limQuotientsMap
    {S N : Type*} [Ring S] {τ : R →+* S} [AddCommGroup N] [Module S N]
    {J' : ℕ → Submodule S N} (hJ' : Antitone J') (f : M →ₛₗ[τ] N)
    (hf : ∀ n, ∃ m, J m ≤ (J' n).comap f) {m n : ℕ}
    (hm : J m ≤ (J' n).comap f) :
    (quotients J hJ).limFiltration (m + 1) ≤
      ((quotients J' hJ').limFiltration (n + 1)).comap
        (limQuotientsMap hJ hJ' f hf) := by
  intro x hx
  rw [Submodule.mem_comap, limFiltration_succ, LinearMap.mem_ker]
  rw [limFiltration_succ, LinearMap.mem_ker] at hx
  rw [limπ_limQuotientsMap hJ hJ' f hf hm (b := 0) (by simpa using hx.symm),
    map_zero, map_zero]

end Quotients

end TauCeti.ModuleTower

namespace TauCeti.IsCompleteFiltration

open ModuleTower

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  {J : ℕ → Submodule R M} (hJ : IsCompleteFiltration J)

/-- A complete separated filtration identifies the module with its compatible quotient
families. No assumption on the zeroth term is needed. -/
theorem toLimQuotients_bijective :
    Function.Bijective (toLimQuotients J hJ.antitone) := by
  constructor
  · apply (toLimQuotients_injective_iff J hJ.antitone).mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact (Submodule.mem_bot R).mpr
      (hJ.eq_zero_of_forall_mem x ((Submodule.mem_iInf _).mp hx))
  · intro y
    choose x hx using fun n => quotientsπ_surjective J hJ.antitone n
      ((quotients J hJ.antitone).limπ n y)
    have hstep (n : ℕ) : x (n + 1) - x n ∈ J n := by
      apply (quotientsπ_eq_quotientsπ_iff J hJ.antitone).mp
      exact (quotientsπ_eq_limπ_of_le (Nat.le_succ n) (hx (n + 1))).trans (hx n).symm
    obtain ⟨L, hL⟩ := hJ.exists_limit x hstep
    refine ⟨L, (quotients J hJ.antitone).lim_ext fun n => ?_⟩
    rw [← LinearMap.comp_apply, limπ_comp_toLimQuotients]
    exact ((quotientsπ_eq_quotientsπ_iff J hJ.antitone).mpr (hL n)).trans (hx n)

end TauCeti.IsCompleteFiltration

namespace TauCeti

open ModuleTower

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (J : ℕ → Submodule R M) (hJ : Antitone J)

/-- A decreasing submodule filtration is complete and separated exactly when the canonical
map to its quotient-tower limit is bijective. -/
theorem isCompleteFiltration_iff_toLimQuotients_bijective :
    IsCompleteFiltration J ↔ Function.Bijective (toLimQuotients J hJ) := by
  refine ⟨fun h => h.toLimQuotients_bijective, fun h => ?_⟩
  refine ⟨hJ, ?_, ?_⟩
  · intro x hx
    apply h.1
    apply (quotients J hJ).lim_ext
    intro n
    rw [map_zero, ← LinearMap.comp_apply, limπ_comp_toLimQuotients]
    simpa only [map_zero] using (quotientsπ_eq_zero_iff J hJ).mpr (hx n)
  · intro x hx
    let y : (quotients J hJ).lim :=
      ⟨fun n => quotientsπ J hJ n (x n), (quotients J hJ).mem_lim.mpr fun n => by
        rw [transition_quotientsπ]
        exact (quotientsπ_eq_quotientsπ_iff J hJ).mpr (hx n)⟩
    have hy (n : ℕ) : (quotients J hJ).limπ n y = quotientsπ J hJ n (x n) :=
      (quotients J hJ).limπ_apply n y
    obtain ⟨L, hL⟩ := h.2 y
    refine ⟨L, fun n => (quotientsπ_eq_quotientsπ_iff J hJ).mp ?_⟩
    rw [← hy, ← hL, ← LinearMap.comp_apply, limπ_comp_toLimQuotients]

end TauCeti

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

variable {R : Type*} [Ring R] (F : ModuleTower R)

/-- Completing the induced filtration again recovers the original tower limit, via its
canonical map. -/
def limCompletionEquiv :
    F.lim ≃ₗ[R] (quotients F.limFiltration F.limFiltration_antitone).lim :=
  LinearEquiv.ofBijective (toLimQuotients F.limFiltration F.limFiltration_antitone)
    F.isCompleteFiltration_lim.toLimQuotients_bijective

/-- The repeated-completion comparison sends an element to its compatible quotient classes. -/
@[simp]
theorem limCompletionEquiv_apply (x : F.lim) :
    F.limCompletionEquiv x = toLimQuotients F.limFiltration F.limFiltration_antitone x := (rfl)

end TauCeti.ModuleTower
