/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Localization
import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Integration on overlapping coordinate domains and connected covers

Top compactly supported cohomology on a Euclidean coordinate domain is determined by
integration. Classes of integral one from two overlapping coordinate domains have the
same image in any larger open set: a normalized bump form in the intersection compares
them. Connectedness then identifies all the local generators, and a finite decomposition
of a compactly supported class proves injectivity of integration.
The global integration isomorphism is provided in
`TauCeti.Geometry.Manifold.DeRham.Integration.Bijective`. No positive-dimensional assumption is
needed here.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 17,
  the integration theorem for compactly supported top-degree cohomology.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public noncomputable section

open Set TopologicalSpace Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.compactlySupportedDeRhamCohomology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M] {n : ℕ}

/-- Classes with the same integral on overlapping Euclidean coordinate domains have the same
extension to any larger open set. The intersection need not itself be a coordinate domain
or connected. -/
theorem extendByZero_eq_of_integral_eq_of_nonempty_inter
    (o : Manifold.Orientation I M (Fin n)) {U V W : Opens M}
    [SigmaCompactSpace U] [SigmaCompactSpace V]
    (hU : U ≤ W) (hV : V ≤ W)
    (Φ : E ≃ₘ⟮𝓘(ℝ, E), I⟯ U) (Ψ : E ≃ₘ⟮𝓘(ℝ, E), I⟯ V)
    (hUV : ((U : Set M) ∩ V).Nonempty)
    (a : compactlySupportedDeRhamCohomology I U n)
    (b : compactlySupportedDeRhamCohomology I V n)
    (hab : integral (o.restrict U) a = integral (o.restrict V) b) :
    extendByZero hU n a = extendByZero hV n b := by
  have : SecondCountableTopology U := Φ.toHomeomorph.symm.secondCountableTopology
  have hi := Topology.IsOpenEmbedding.inclusion (inf_le_left : U ⊓ V ≤ U)
    ((U ⊓ V).isOpen.preimage (continuous_subtype_val : Continuous (Subtype.val : U → M)))
  have : SecondCountableTopology (U ⊓ V : Opens M) := hi.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace U := Φ.toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (U ⊓ V : Opens M) := hi.locallyCompactSpace
  have : SigmaCompactSpace (U ⊓ V : Opens M) := inferInstance
  obtain ⟨x, hxU, hxV⟩ := hUV
  have : Nonempty (U ⊓ V : Opens M) := ⟨⟨x, hxU, hxV⟩⟩
  -- The intersection supplies a common class of integral one; Euclidean injectivity
  -- compares its two extensions with the classes being given.
  obtain ⟨d, hd⟩ := surjective_integral (o.restrict (U ⊓ V)) 1
  have ha : a = integral (o.restrict U) a •
      extendByZero (inf_le_left : U ⊓ V ≤ U) n d :=
    (bijective_integral_of_diffeomorph_normedSpace (o.restrict U) Φ).injective
      (by simp [hd])
  have hb : b = integral (o.restrict U) a •
      extendByZero (inf_le_right : U ⊓ V ≤ V) n d :=
    (bijective_integral_of_diffeomorph_normedSpace (o.restrict V) Ψ).injective
      (by simp [hab, hd])
  rw [ha, hb, map_smul, map_smul, extendByZero_extendByZero, extendByZero_extendByZero]

/-- Normalized classes from a coordinate cover have the same image on a connected union. -/
private theorem extendByZero_normalized_eq_of_cover
    (o : Manifold.Orientation I M (Fin n)) {W : Opens M}
    [PreconnectedSpace W] {ι : Type*} (U : ι → Opens M)
    [∀ i, SigmaCompactSpace (U i)] (hU : ∀ i, U i ≤ W) (hcover : W ≤ iSup U)
    (Φ : ∀ i, E ≃ₘ⟮𝓘(ℝ, E), I⟯ U i)
    (b : ∀ i, compactlySupportedDeRhamCohomology I (U i) n)
    (hb : ∀ i, integral (o.restrict (U i)) (b i) = 1) (i j : ι) :
    extendByZero (hU i) n (b i) = extendByZero (hU j) n (b j) := by
  classical
  have hex (x : W) : ∃ i, (x : M) ∈ U i := by
    simpa only [Opens.mem_iSup] using hcover x.property
  choose k hk using hex
  let g (x : W) := extendByZero (hU (k x)) n (b (k x))
  have hg (x : W) (i : ι) (hx : (x : M) ∈ U i) :
      g x = extendByZero (hU i) n (b i) :=
    extendByZero_eq_of_integral_eq_of_nonempty_inter o (hU _) (hU _) (Φ _) (Φ _)
      ⟨x, hk x, hx⟩ _ _ (by rw [hb, hb])
  have hgc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [((U (k x)).isOpen.preimage continuous_subtype_val).mem_nhds (hk x)] with y hy
    exact hg y (k x) hy
  exact (hg ⟨Φ i 0, hU i (Φ i 0).property⟩ i (Φ i 0).property).symm.trans
    ((hgc.apply_eq_of_preconnectedSpace _ _).trans
      (hg ⟨Φ j 0, hU j (Φ j 0).property⟩ j (Φ j 0).property))

/-- Integration is injective on a preconnected open set covered by open sets diffeomorphic to
the model vector space `E`. The cover may be infinite, and its intersections need not be
connected. -/
theorem injective_integral_of_cover
    (o : Manifold.Orientation I M (Fin n)) {W : Opens M}
    [SigmaCompactSpace W] [PreconnectedSpace W] {ι : Type*} (U : ι → Opens M)
    [∀ i, SigmaCompactSpace (U i)] (hU : ∀ i, U i ≤ W) (hcover : W ≤ iSup U)
    (Φ : ∀ i, E ≃ₘ⟮𝓘(ℝ, E), I⟯ U i) : Function.Injective (integral (o.restrict W)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  by_cases hι : Nonempty ι
  · let _ := hι
    have hex (i : ι) : ∃ b : compactlySupportedDeRhamCohomology I (U i) n,
        integral (o.restrict (U i)) b = 1 := by
      have : Nonempty (U i) := ⟨Φ i 0⟩
      exact surjective_integral (o.restrict (U i)) 1
    choose b hb using hex
    obtain ⟨s, a, ha⟩ := exists_sum_smul_extendByZero o U hU hcover Φ b hb c
    let i₀ : ι := Classical.choice hι
    have hgen := extendByZero_normalized_eq_of_cover o U hU hcover Φ b hb
    have heq : c = (∑ i ∈ s, a i) • extendByZero (hU i₀) n (b i₀) := by
      simpa only [hgen _ i₀, ← Finset.sum_smul] using ha
    have hsum : ∑ i ∈ s, a i = 0 := by
      simpa only [heq, map_smul, integral_extendByZero, hb, smul_eq_mul, mul_one] using hc
    simp only [heq, hsum, zero_smul]
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    obtain ⟨s, d, hd⟩ := exists_sum_extendByZero U hU hcover
      (by simpa using o.card_eq.ge) c
    have hs : s = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ ↦ isEmptyElim i)
    simpa only [hs, Finset.sum_empty] using hd

end TauCeti.compactlySupportedDeRhamCohomology
