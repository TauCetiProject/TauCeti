/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Conjugation
public import TauCeti.Analysis.Polynomial.Puiseux.Extension

/-!
# Conjugation of analytic branches across the distinguished hyperplane

A complete, distinct analytic splitting on a punctured product extends to the full
product with a unique involutive permutation of its labels implementing complex
conjugation. The extended roots may collide on the hyperplane. Coefficient symmetry
is required only off the hyperplane, where it determines the permutation uniquely;
continuity carries the resulting branch identities through the collisions.

The parameter involution can conjugate several base coordinates. The distinguished
domain can be any open conjugation-invariant complex set whose punctured part is
preconnected, in particular a disc centered at zero. The coefficient tuple describes
a monic polynomial and only needs continuity on the full product. The given punctured
branches can be obtained after a power substitution; this theorem constructs their
analytic extensions together with their conjugation action.

The construction combines `exists_analyticOnNhd_monicOfCoeff_eq_prod_X_sub_C`
with `TauCeti.existsUnique_root_conj_perm_of_subset_closure`, reusing the conjugation
permutation of a distinct root labelling and the analytic hyperplane extension.

Fixed labels give real branches at every parameter fixed by the involution, including
on the hyperplane. The converse requires distinctness and therefore is asserted only
off the hyperplane by `TauCeti.root_conj_perm_apply_eq_self_iff_im_eq_zero`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, §4.
-/

public section

open ComplexConjugate Function Polynomial Set

namespace TauCeti.Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {U : Set V} {s : Set ℂ} {d : ℕ} {τ : V → V}

/-- Extend a distinct punctured analytic splitting across `t = 0` together with its unique
conjugation permutation. The branches may coincide at `t = 0`; neither distinctness nor
separability is required there. Symmetry of the lower coefficients is enough to determine
the action on all the extended branches. -/
theorem exists_analyticOnNhd_monicOfCoeff_eq_prod_X_sub_C_conj
    (c : V × ℂ → Fin d → ℂ) (r : Fin d → V × ℂ → ℂ)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hs : IsOpen s)
    (hsc : IsPreconnected (s \ {0})) (hconj : MapsTo conj s s)
    (hτ : ContinuousOn τ U) (hτU : MapsTo τ U U) (hττ : ∀ x ∈ U, τ (τ x) = x)
    (hc : ContinuousOn c (U ×ˢ s))
    (hr : ∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (s \ {0})))
    (hinj : ∀ p ∈ U ×ˢ (s \ {0}), Injective (fun i => r i p))
    (hfac : ∀ p ∈ U ×ˢ (s \ {0}), monicOfCoeff (c p) = ∏ i, (X - C (r i p)))
    (hcconj : ∀ p ∈ U ×ˢ (s \ {0}), ∀ i,
      c (τ p.1, conj p.2) i = conj (c p i))
    (p₀ : V × ℂ) (hp₀ : p₀ ∈ U ×ˢ (s \ {0})) :
    ∃ g : Fin d → V × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (g i) (U ×ˢ s) ∧ EqOn (g i) (r i) (U ×ˢ (s \ {0}))) ∧
      (∀ p ∈ U ×ˢ s, monicOfCoeff (c p) = ∏ i, (X - C (g i p))) ∧
      ∃! σ : Equiv.Perm (Fin d), Function.Involutive σ ∧
        ∀ i p, p ∈ U ×ˢ s → g (σ i) p = conj (g i (τ p.1, conj p.2)) := by
  obtain ⟨g, hg, hgf⟩ := exists_analyticOnNhd_monicOfCoeff_eq_prod_X_sub_C
    c r hU hs hc hr hfac
  refine ⟨g, hg, hgf, ?_⟩
  let κ : V × ℂ → V × ℂ := fun p => (τ p.1, conj p.2)
  have hκ : ContinuousOn κ (U ×ˢ s) :=
    (hτ.comp continuousOn_fst fun _ hp => hp.1).prodMk
      (Complex.continuous_conj.comp_continuousOn continuousOn_snd)
  have hκT : MapsTo κ (U ×ˢ s) (U ×ˢ s) :=
    fun _ hp => ⟨hτU hp.1, hconj hp.2⟩
  have hκS : MapsTo κ (U ×ˢ (s \ {0})) (U ×ˢ (s \ {0})) := by
    intro p hp
    exact ⟨hτU hp.1, hconj hp.2.1, by simpa [κ] using hp.2.2⟩
  have hκκ : ∀ p ∈ U ×ˢ (s \ {0}), κ (κ p) = p := fun p hp =>
    Prod.ext (hττ p.1 hp.1) (Complex.conj_conj p.2)
  have hdense : U ×ˢ s ⊆ closure (U ×ˢ (s \ {(0 : ℂ)})) := by
    rw [closure_prod_eq, Set.sdiff_eq]
    exact prod_mono subset_closure
      ((dense_compl_singleton (0 : ℂ)).open_subset_closure_inter hs)
  have hginj : ∀ p ∈ U ×ˢ (s \ {0}), Injective (fun i => g i p) := by
    intro p hp i j hij
    apply hinj p hp
    simpa only [(hg i).2 hp, (hg j).2 hp] using hij
  have hroot : ∀ p ∈ U ×ˢ (s \ {0}), ∀ z,
      (monicOfCoeff (c p)).IsRoot z ↔ ∃ i, g i p = z := by
    intro p hp z
    rw [hgf p (prod_mono subset_rfl sdiff_subset hp), isRoot_prod]
    simp [sub_eq_zero, eq_comm]
  have hsymm : ∀ p ∈ U ×ˢ (s \ {0}),
      monicOfCoeff (c (κ p)) = (monicOfCoeff (c p)).map (starRingEnd ℂ) := by
    intro p hp
    rw [map_monicOfCoeff]
    exact congrArg monicOfCoeff (funext (hcconj p hp))
  exact TauCeti.existsUnique_root_conj_perm_of_subset_closure (hUc.prod hsc)
    (prod_mono subset_rfl sdiff_subset) hdense (fun i => (hg i).1.continuousOn)
    hginj hroot hκ hκS hκT hκκ hsymm ⟨p₀, hp₀⟩

end TauCeti.Polynomial
