/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
import TauCeti.Topology.VectorBundle.Riemannian.FiniteDimensional
import TauCeti.Topology.VectorBundle.Thom.Pair

/-!
# Universe-lifted Thom pairs of the negative normal bundle

When `S` and `M` live in an arbitrary universe `u`, the relative homology `Hₙ({f ≤ b}, {f ≤ a})`
across an isolated compact Morse–Bott submanifold `i : S → M` of constant index `r` is isomorphic
to the relative homology of the Thom pair of a vector bundle `V → S` in universe `u` with model
fibre `ULift.{u} (Fin r) → ℝ`, without prescribing a fibre metric on the normal bundle
(`IsNondegenerateCriticalSubmanifold.exists_thomPair_ulift_singularHomology_iso`).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set Topology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

section

variable {E : Type u} {H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' : Type*} {S : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}

/-- **Universe-lifted Thom pair of the negative normal bundle.** Under the hypotheses of
`nonempty_singularHomology_sublevelPair_iso_thomPair`, without prescribing a fibre metric, there
exists a real vector bundle `V → S` in the universe of `S` with model fibre `ULift.{u} (Fin r) → ℝ`
whose Thom pair computes the relative homology across the level `c`. -/
theorem exists_thomPair_ulift_singularHomology_iso
    [T2Space M] [SecondCountableTopology M] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (n : ℕ) :
    ∃ (V : S → Type u) (_ : ∀ s, AddCommGroup (V s)) (_ : ∀ s, Module ℝ (V s))
        (_ : ∀ s, TopologicalSpace (V s))
        (_ : TopologicalSpace (TotalSpace (ULift.{u} (Fin r) → ℝ) V))
        (_ : FiberBundle (ULift.{u} (Fin r) → ℝ) V)
        (_ : VectorBundle ℝ (ULift.{u} (Fin r) → ℝ) V),
      Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
        (thomPair (ULift.{u} (Fin r) → ℝ) V).singularHomology R n) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
    hc hac.le hcb.le hcompact hcrit
  have : T2Space S := i.isEmbedding.t2Space
  let P₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ E'))
  have hdim : Module.finrank ℝ P₀ = Module.finrank ℝ E - Module.finrank ℝ E' :=
    finrank_euclideanSpace_fin
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := i.nonempty_contMDiffRiemannianMetric_normalSpace hn hdim
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  have hVu := hV.hasLocalSubbundleFrames.comp_equiv Equiv.ulift
  let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hVu.fiberBundle
  have := hVu.vectorBundle
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact
    hcrit hdim g hr R n
  exact ⟨fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨e ≪≫ TopPair.singularHomologyMapIso R (subbundleThomPairModelIso P₀ (Fin r → ℝ)
      (ULift.{u} (Fin r) → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)) n⟩⟩

end

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-- The rank of the universe-lifted function space `ULift.{u} (Fin r) → R` over a semiring `R`
satisfying the strong rank condition is `r`. -/
theorem finrank_ulift_fin_fun (R : Type*) [Semiring R] [StrongRankCondition R] (r : ℕ) :
    Module.finrank R (ULift.{u} (Fin r) → R) = r := by
  rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]

end TauCeti
