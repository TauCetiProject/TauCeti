/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Splitting
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
public import Mathlib.Algebra.Exact.Basic

/-!
# Completed tensoring of countable-type exact sequences

A strict short exact sequence whose middle term is an ultrametric Banach space of countable
type splits continuously. Tensoring its splitting and inverse therefore gives a product
decomposition after separated completion. This file supplies that decomposition for the native
`Huber.BanachModule.CompletedTensor`, with the original completed tensor maps as its inclusion
and projection. In particular those maps form a strict short exact sequence: the inclusion is
a closed embedding and the projection is an open surjection.

The other tensor factor may be any topological module. In particular it may be an isometric
extension field, regarded as a module over the original field. All maps here are linear over
the original field. No norm or extension-field scalar structure on the completed tensor is
asserted. The tensor carrier used here is the completion for the nonarchimedean tensor
topology, not a separately chosen projective norm.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §2.7.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.2, Lemma 2.2.9.
-/

public section

open Set Submodule Topology
open TauCeti.Huber.BanachModule

namespace TauCeti

variable {K E M N W : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E] [CompleteSpace E]
  [AddCommGroup M] [Module K M] [TopologicalSpace M]
  [NormedAddCommGroup N] [NormedSpace K N] [CompleteSpace N]
  [AddCommGroup W] [Module K W] [TopologicalSpace W]

/-- A countable-type strict short exact sequence remains continuously split after completed
 tensoring. The decomposition identifies the native completed inclusion with the first-factor
 inclusion and the native completed quotient with the second-factor projection. -/
theorem exists_continuousLinearEquiv_prod_completedTensor_of_countableType
    {v : ℕ → E} (hv : Dense (span K (range v) : Set E))
    (i : M →L[K] E) (q : E →L[K] N) (hi : IsEmbedding i) (hq : Function.Surjective q)
    (hiq : i.range = q.ker) :
    ∃ d : CompletedTensor K E W ≃L[K] CompletedTensor K M W × CompletedTensor K N W,
      (∀ m, d (CompletedTensor.map i (.id K W) m) = (m, 0)) ∧
      ∀ x, (d x).2 = CompletedTensor.map q (.id K W) x := by
  obtain ⟨d, hdi, hdq⟩ := exists_continuousLinearEquiv_prod_of_countableType hv i q hi hq hiq
  let e : CompletedTensor K E W ≃L[K] CompletedTensor K (M × N) W :=
    .equivOfInverse' (CompletedTensor.map (d : E →L[K] M × N) (.id K W))
      (CompletedTensor.map (d.symm : M × N →L[K] E) (.id K W))
      (by apply CompletedTensor.ext; intro x w; simp)
      (by apply CompletedTensor.ext; intro x w; simp)
  let D := e.trans CompletedTensor.prodLeft
  have hI : (D : CompletedTensor K E W →L[K] _).comp
      (CompletedTensor.map i (.id K W)) =
        ContinuousLinearMap.inl K (CompletedTensor K M W) (CompletedTensor K N W) := by
    apply CompletedTensor.ext
    intro m w
    simp [D, e, hdi]
  have hQ : (ContinuousLinearMap.snd K (CompletedTensor K M W) (CompletedTensor K N W)).comp
      (D : CompletedTensor K E W →L[K] _) = CompletedTensor.map q (.id K W) := by
    apply CompletedTensor.ext
    intro x w
    simp [D, e, hdq]
  exact ⟨D, fun m ↦ DFunLike.congr_fun hI m, fun x ↦ DFunLike.congr_fun hQ x⟩

/-- Completed tensoring preserves strict short exactness when the middle Banach space is
 ultrametric and of countable type. This asserts closed embedding, open surjectivity and
 exactness for the native maps, not just for maps conjugated to a chosen product. -/
theorem strictExact_completedTensor_of_countableType
    {v : ℕ → E} (hv : Dense (span K (range v) : Set E))
    (i : M →L[K] E) (q : E →L[K] N) (hi : IsEmbedding i) (hq : Function.Surjective q)
    (hiq : i.range = q.ker) :
    IsClosedEmbedding (CompletedTensor.map i (.id K W)) ∧
      IsOpenMap (CompletedTensor.map q (.id K W)) ∧
      Function.Surjective (CompletedTensor.map q (.id K W)) ∧
      Function.Exact (CompletedTensor.map i (.id K W)) (CompletedTensor.map q (.id K W)) := by
  obtain ⟨d, hdi, hdq⟩ :=
    exists_continuousLinearEquiv_prod_completedTensor_of_countableType
      (W := W) hv i q hi hq hiq
  have hI : CompletedTensor.map i (.id K W) =
      (d.symm : _ →L[K] CompletedTensor K E W).comp
        (ContinuousLinearMap.inl K (CompletedTensor K M W) (CompletedTensor K N W)) := by
    apply ContinuousLinearMap.ext
    intro m
    exact d.injective (by simpa using hdi m)
  have hQ : CompletedTensor.map q (.id K W) =
      (ContinuousLinearMap.snd K (CompletedTensor K M W) (CompletedTensor K N W)).comp
        (d : CompletedTensor K E W →L[K] _) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (hdq x).symm
  have hinl : IsClosedEmbedding (fun m : CompletedTensor K M W ↦
      (m, (0 : CompletedTensor K N W))) :=
    ⟨isEmbedding_prodMkLeft 0, (isClosedMap_prodMk_right 0).isClosed_range⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hI]
    exact d.symm.toHomeomorph.isClosedEmbedding.comp hinl
  · rw [hQ]
    exact isOpenMap_snd.comp d.isOpenMap
  · intro n
    exact ⟨d.symm (0, n), by rw [hQ]; simp⟩
  · rw [hI, hQ]
    exact (d.toLinearEquiv.conj_symm_exact_iff_exact
      (LinearMap.inl K _ _) (LinearMap.snd K _ _)).2 Function.Exact.inl_snd

end TauCeti
