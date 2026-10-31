/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
import TauCeti.Geometry.Manifold.Connected
import Mathlib.Data.Fintype.Basic

/-!
# Moving finite ordered point configurations

In a boundaryless real manifold of dimension greater than one, two finite configurations
of distinct labelled points in a preconnected open set are related by a diffeotopy supported
in a compact subset of that open set. In particular the motion fixes a neighborhood of every
point outside the prescribed open set. This permits matching marked points while leaving
protected closed sets untouched, whenever the points lie in a common preconnected open
complement of those sets.

The proof matches the labels one at a time. After matching a finite subset, delete its target
points from the open set and use the homogeneity lemma there to match the next label. Removing
finitely many points preserves preconnectedness in real dimension greater than one. The already
matched points stay fixed throughout each subsequent motion. Injectivity of the intermediate
diffeomorphisms keeps all the moving points distinct, even when the source and target
configurations overlap or differ by a permutation.

## Main results

* `TauCeti.exists_diffeotopy_final_eqOn_of_isPreconnected`: match labels in a finite index set.
* `TauCeti.exists_diffeotopy_final_comp_eq_of_isPreconnected`: match a finite ordered
  configuration, with no choice of enumeration of its labels.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint* (1965), §4, Homogeneity Lemma.
  The single-point motion used here is
  `TauCeti.exists_diffeotopy_final_apply_eq_of_isPreconnected`.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M] {m : ℕ∞}

/-- Two configurations indexed by a finite set, each injective on that set and contained in a
preconnected open subset of a manifold of real dimension greater than one, are matched by a
diffeotopy supported in a compact subset of that open set. Source and target configurations
may overlap. The regularity is `C^m` provided `1 ≤ m` and `m + 1 ≤ n`. -/
theorem exists_diffeotopy_final_eqOn_of_isPreconnected
    (hdim : 1 < Module.rank ℝ E) (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) (s : Finset ι)
    {f g : ι → M} (hf : InjOn f s) (hg : InjOn g s)
    (hfU : MapsTo f s U) (hgU : MapsTo g s U) :
    ∃ (Φ : Diffeotopy 𝓘(ℝ, E) m M) (K : Set M), IsCompact K ∧ K ⊆ U ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ EqOn (Φ.final ∘ f) g s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Diffeotopy.refl _ _ _, ∅, isCompact_empty, empty_subset _,
      by intro t z _; simp only [Diffeotopy.refl_apply, id_eq], by simp⟩
  | @insert a s has ih =>
    have hs : (s : Set ι) ⊆ (↑(insert a s) : Set ι) := by simp
    obtain ⟨Φ, K, hK, hKU, hΦK, hΦ⟩ :=
      ih (hf.mono hs) (hg.mono hs) (hfU.mono_left hs) (hgU.mono_left hs)
    let P : Set M := g '' (s : Set ι)
    have hP : P.Finite := s.finite_toSet.image g
    have hfaU : Φ.final (f a) ∈ U :=
      Φ.mapsTo_final_of_eqOn_compl hKU hΦK (hfU (by simp))
    have hfaP : Φ.final (f a) ∉ P := by
      rintro ⟨i, hi, heq⟩
      have hai := hf (by simp) (hs hi) (Φ.final.injective (heq.symm.trans (hΦ hi).symm))
      exact has (hai ▸ hi)
    have hgaP : g a ∉ P := by
      rintro ⟨i, hi, heq⟩
      exact has (hg (hs hi) (by simp) heq ▸ hi)
    obtain ⟨Ψ, L, hL, hLU, hΨL, hΨ⟩ :=
      exists_diffeotopy_final_apply_eq_of_isPreconnected (I := 𝓘(ℝ, E)) hm hmn
        (hU.sdiff hP.isClosed)
        (isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank hdim hU hUc
          hP.isClosed hP.isDiscrete)
        ⟨hfaU, hfaP⟩ ⟨hgU (by simp), hgaP⟩
    have hΨfix (t) (i) (hi : i ∈ s) : Ψ (t, g i) = g i :=
      hΨL t (fun hiL => (hLU hiL).2 ⟨i, hi, rfl⟩)
    refine ⟨Φ.trans Ψ, K ∪ L, hK.union hL,
      union_subset hKU (hLU.trans sdiff_subset), ?_, ?_⟩
    · intro t z hz
      simp only [mem_compl_iff, mem_union, not_or] at hz
      simp [hΦK t hz.1, hΨL t hz.2]
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa only [Diffeotopy.final_trans, Diffeomorph.coe_trans,
          Function.comp_apply] using hΨ
      · have hΦi : Φ.final (f i) = g i := hΦ hi
        simp only [Diffeotopy.final_trans, Diffeomorph.coe_trans,
          Function.comp_apply, hΦi]
        simpa only [Diffeotopy.final_apply] using hΨfix 1 i hi

/-- Two finite ordered configurations of distinct points in a preconnected open subset of a
manifold of real dimension greater than one are related by a compactly supported diffeotopy
inside that open set. All labels are matched by its final diffeomorphism. -/
theorem exists_diffeotopy_final_comp_eq_of_isPreconnected [Finite ι]
    (hdim : 1 < Module.rank ℝ E) (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f g : ι → M} (hf : Function.Injective f) (hg : Function.Injective g)
    (hfU : ∀ i, f i ∈ U) (hgU : ∀ i, g i ∈ U) :
    ∃ (Φ : Diffeotopy 𝓘(ℝ, E) m M) (K : Set M), IsCompact K ∧ K ⊆ U ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ Φ.final ∘ f = g := by
  classical
  cases nonempty_fintype ι
  obtain ⟨Φ, K, hK, hKU, hΦK, hΦ⟩ := exists_diffeotopy_final_eqOn_of_isPreconnected
    hdim hm hmn hU hUc Finset.univ hf.injOn hg.injOn (fun i _ => hfU i) (fun i _ => hgU i)
  exact ⟨Φ, K, hK, hKU, hΦK, funext fun i => hΦ (by simp)⟩

end TauCeti
