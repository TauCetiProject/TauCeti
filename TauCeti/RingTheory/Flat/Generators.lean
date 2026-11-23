/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Support

/-!
# Local generators of finite flat modules

From any spanning family of a finite flat module, one can select as many elements as its rank
at a prime so that the selected elements generate on a neighbourhood of that prime. The
neighbourhood is detected by the annihilator of the cokernel.
-/

public section

namespace Module

attribute [local instance] Module.free_of_flat_of_isLocalRing in
/-- From a spanning family of a finite flat module of rank `d` at `p`, one can select `d`
elements whose cokernel has annihilator not contained in `p`. Thus they generate near `p`. -/
theorem exists_generators_annihilator_not_le {A M ι : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Flat A M] (u : ι → M)
    (hu : Submodule.span A (Set.range u) = ⊤) (p : PrimeSpectrum A) {d : ℕ}
    (hp : rankAtStalk M p = d) :
    ∃ y : Fin d → ι, ¬ annihilator A (M ⧸ Submodule.span A (Set.range (u ∘ y))) ≤
      p.asIdeal := by
  classical
  let f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
  have hspan : Submodule.span (Localization.AtPrime p.asIdeal) (Set.range (f ∘ u)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.localized'_span (S := Localization.AtPrime p.asIdeal)
      (p := p.asIdeal.primeCompl) (f := f), hu, Submodule.localized'_top]
  have : FinitePresentation (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := finitePresentation_of_projective _ _
  obtain ⟨κ, a, b, hb⟩ := exists_basis_of_span_of_flat _ hspan
  have : Fintype κ :=
    have := Finite.finite_basis b
    Fintype.ofFinite κ
  have hκ : Fintype.card κ = d := by rw [← hp, rankAtStalk, finrank_eq_card_basis b]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  refine ⟨a ∘ e, fun hle ↦ ?_⟩
  rw [← mem_support_iff_of_finite (p := p)] at hle
  refine ((notMem_support_iff' (p := p)).mpr fun c ↦ ?_) hle
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  let N := Submodule.span A (Set.range (u ∘ (a ∘ e)))
  have hx : f x ∈ N.localized' (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl f := by
    have hr : f '' Set.range (u ∘ (a ∘ e)) = Set.range b := by
      rw [← Set.range_comp', ← e.surjective.range_comp b]
      simp [Function.comp_def, hb]
    rw [Submodule.localized'_span, hr, b.span_eq]
    trivial
  obtain ⟨m, hm⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
    (N.toLocalizedQuotient' (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl f)).mp
      (by rw [Submodule.toLocalizedQuotient'_mk, Submodule.Quotient.mk_eq_zero]; exact hx)
  exact ⟨m, m.property, hm⟩

end Module
