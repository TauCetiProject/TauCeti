/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Basic
public import Mathlib.Topology.WithTopology
public import TauCeti.Geometry.Manifold.Gluing.Basic

import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Overlap
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# The intrinsic topology of integral plaques

A covering family of injective integral immersions of an involutive distribution gives the
ambient point set a finer, intrinsic manifold topology. Its open sets are exactly the sets whose
inverse images in every parametrizing manifold are open. Every parametrization is then a local
diffeomorphism. On a nonempty carrier, the bijection back to the original ambient manifold is an
integral immersion.
No assertion that this bijection is an embedding is made.

The carrier uses `WithTopology` to retain the original ambient manifold and its distribution
without changing their instances. The parametrizing manifolds are boundaryless and share a
common model, which may itself have boundary.
The ambient manifold is also assumed boundaryless.
Smooth overlap compatibility follows from the integral immersions, rather than being an
additional hypothesis on the family.
The parametrizations are `C^m`, with `1 ≤ m`, and the ambient manifold is `C^r` with
`m + 1 ≤ r`. The ambient normed model is finite-dimensional and real.

## Main results

* `TauCeti.isOpenEmbedding_integral_coinduced`: integral parametrizations are open embeddings
  for the intrinsic topology.
* `TauCeti.chartedSpaceOfIntegralManifolds`: the named intrinsic atlas.
* `TauCeti.chartedSpaceOfIntegralManifolds_eq`: comparison with the general glued atlas.
* `TauCeti.exists_contMDiffAt_transition_integral_coinduced`: smooth local transitions.
* `TauCeti.isManifold_chartedSpaceOfIntegralManifolds`: regularity of the intrinsic atlas.
* `TauCeti.isLocalDiffeomorph_chartedSpaceOfIntegralManifolds`: local diffeomorphisms from pieces.
* `TauCeti.isIntegralManifold_ofTopology`: the integral immersion to the original manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Lemma 19.22,
  pp. 503–504 (the topology and smooth structure obtained by gluing integral submanifolds).
-/

public section

noncomputable section

open Set Function Filter TopologicalSpace Topology
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [tM : TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {ι : Type*} {U : ι → Type*} [∀ i, TopologicalSpace (U i)] [∀ i, ChartedSpace H' (U i)]
  {m : ℕ∞} {r : ℕ∞ω} [IsManifold I r M] [∀ i, IsManifold J m (U i)]
  [∀ i, BoundarylessManifold J (U i)]
  [BoundarylessManifold I M]
  {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {f : ∀ i, U i → M}
  (hf : ∀ i, IsIntegralManifold J m D (f i))
  (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
  (hinv : let _ : IsManifold I 1 M :=
    .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
    IsInvolutiveDistribution I D) {k : ℕ}
  (hD : let _ : IsManifold I 1 M :=
    .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
    IsContMDiffDistribution I m k D)
  (hinj : ∀ i, Injective (f i))

include hf hm hmr hinv hD hinj in
/-- Each injective integral parametrization is an open embedding for the topology whose open
sets have open inverse images under every parametrization. -/
theorem isOpenEmbedding_integral_coinduced (i : ι) :
    let t := ⨆ j, TopologicalSpace.coinduced (f j) inferInstance
    IsOpenEmbedding (WithTopology.toTopology t ∘ f i) := by
  let t := ⨆ j, TopologicalSpace.coinduced (f j) inferInstance
  -- Keep the ambient instance after naming the finer topology.
  let : TopologicalSpace M := tM
  have hcont : Continuous (WithTopology.toTopology t ∘ f i) := by
    refine continuous_def.2 fun V hV ↦ ?_
    exact isOpen_iSup_iff.mp ((WithTopology.isOpen_iff t).mp hV) i
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
    ((WithTopology.toTopology_injective t).comp (hinj i)) ?_
  intro V hV
  rw [WithTopology.isOpen_iff, image_comp,
    preimage_image_eq _ (WithTopology.toTopology_injective t)]
  exact isOpen_iSup_iff.2 fun j ↦
    (hf j).isOpen_preimage_image (hf i) hm hmr hinv hD hV

omit tM in
private theorem integral_coinduced_cover (hcover : ∀ x, ∃ i y, f i y = x)
    (x : WithTopology M (⨆ i, coinduced (f i) inferInstance)) :
    ∃ i y, (WithTopology.toTopology (⨆ j, coinduced (f j) inferInstance) ∘ f i) y = x := by
  obtain ⟨i, y, hy⟩ := hcover (WithTopology.ofTopology x)
  exact ⟨i, y, by simp only [comp_apply, hy, WithTopology.toTopology_ofTopology]⟩

include hf hm hmr hinv hD hinj in
/-- The intrinsic charted-space structure obtained by gluing a covering family of injective
integral parametrizations. A set is open exactly when its inverse image under every
parametrization is open.
The atlas is also defined when the ambient point set is empty. -/
@[instance_reducible]
def chartedSpaceOfIntegralManifolds (hcover : ∀ x, ∃ i y, f i y = x) :
    ChartedSpace H' (WithTopology M (⨆ i, coinduced (f i) inferInstance)) :=
  chartedSpaceOfIsOpenEmbedding (H := H')
    (isOpenEmbedding_integral_coinduced hf hm hmr hinv hD hinj)
    (integral_coinduced_cover hcover)

include hf hm hmr hinv hD hinj in
/-- The intrinsic integral atlas is the existing atlas obtained by gluing its open embeddings.
Any proof that the lifted parametrizations cover the carrier gives the same charted structure. -/
theorem chartedSpaceOfIntegralManifolds_eq (hcover : ∀ x, ∃ i y, f i y = x)
    (hcov : ∀ x : WithTopology M (⨆ i, coinduced (f i) inferInstance),
      ∃ i y, (WithTopology.toTopology (⨆ j, coinduced (f j) inferInstance) ∘ f i) y = x) :
    chartedSpaceOfIntegralManifolds hf hm hmr hinv hD hinj hcover =
      chartedSpaceOfIsOpenEmbedding (H := H')
        (isOpenEmbedding_integral_coinduced hf hm hmr hinv hD hinj) hcov := by
  rfl

include hf hm hmr hinv hD hinj in
/-- Integral parametrizations at the same intrinsic point have a smooth local transition
intertwining their maps near that point. -/
theorem exists_contMDiffAt_transition_integral_coinduced (i j : ι) (x : U i) (y : U j)
    (hxy : WithTopology.toTopology (⨆ l, coinduced (f l) inferInstance) (f i x) =
      WithTopology.toTopology (⨆ l, coinduced (f l) inferInstance) (f j y)) :
    ∃ T : U i → U j, ContMDiffAt J J m T x ∧
      (WithTopology.toTopology (⨆ l, coinduced (f l) inferInstance) ∘ f j) ∘ T =ᶠ[𝓝 x]
        WithTopology.toTopology (⨆ l, coinduced (f l) inferInstance) ∘ f i := by
  let t := ⨆ i, coinduced (f i) inferInstance
  -- Retain the original ambient manifold when naming the finer topology.
  let : TopologicalSpace M := tM
  have hcomp (i : ι) : WithTopology.ofTopology ∘ (WithTopology.toTopology t ∘ f i) = f i :=
    funext fun z ↦ WithTopology.ofTopology_toTopology t (f i z)
  exact exists_contMDiffAt_transition_of_isImmersion (H := H') (I := J)
    (g := WithTopology.ofTopology (t := t))
    (isOpenEmbedding_integral_coinduced hf hm hmr hinv hD hinj)
    (fun i ↦ (hcomp i).symm ▸ (hf i).isImmersion) i j x y hxy

include hf hm hmr hinv hD hinj in
/-- The intrinsic integral atlas gives a manifold of the same regularity as its parametrizations.
Smooth compatibility is a consequence of their common integral tangent distribution. -/
theorem isManifold_chartedSpaceOfIntegralManifolds (hcover : ∀ x, ∃ i y, f i y = x) :
    letI := chartedSpaceOfIntegralManifolds hf hm hmr hinv hD hinj hcover
    IsManifold J m (WithTopology M (⨆ i, coinduced (f i) inferInstance)) := by
  rw [chartedSpaceOfIntegralManifolds_eq hf hm hmr hinv hD hinj hcover
    (integral_coinduced_cover hcover)]
  exact isManifold_chartedSpaceOfIsOpenEmbedding
    (isOpenEmbedding_integral_coinduced hf hm hmr hinv hD hinj)
    (integral_coinduced_cover hcover)
    (exists_contMDiffAt_transition_integral_coinduced hf hm hmr hinv hD hinj)

include hf hm hmr hinv hD hinj in
/-- Every integral parametrization in the family is a local diffeomorphism into its intrinsic
charted carrier. -/
theorem isLocalDiffeomorph_chartedSpaceOfIntegralManifolds
    (hcover : ∀ x, ∃ i y, f i y = x) (i : ι) :
    letI := chartedSpaceOfIntegralManifolds hf hm hmr hinv hD hinj hcover
    IsLocalDiffeomorph J J m
      (WithTopology.toTopology (⨆ j, coinduced (f j) inferInstance) ∘ f i) := by
  rw [chartedSpaceOfIntegralManifolds_eq hf hm hmr hinv hD hinj hcover
    (integral_coinduced_cover hcover)]
  exact isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
    (isOpenEmbedding_integral_coinduced hf hm hmr hinv hD hinj)
    (integral_coinduced_cover hcover)
    (exists_contMDiffAt_transition_integral_coinduced hf hm hmr hinv hD hinj) i

include hf hm hmr hinv hD hinj in
/-- On a nonempty carrier, the bijection from the intrinsic integral manifold back to the
original ambient manifold is an integral immersion with exactly the prescribed tangent image.
Nonemptiness is part of the integral-manifold predicate. -/
theorem isIntegralManifold_ofTopology [Nonempty M] (hcover : ∀ x, ∃ i y, f i y = x) :
    letI := chartedSpaceOfIntegralManifolds hf hm hmr hinv hD hinj hcover
    IsIntegralManifold (I := I) J m D
      (WithTopology.ofTopology (t := ⨆ i, coinduced (f i) inferInstance)) := by
  let t := ⨆ i, coinduced (f i) inferInstance
  -- A local topology-valued term is also a typeclass candidate; retain the ambient topology.
  let : TopologicalSpace M := tM
  let φ (i : ι) : U i → WithTopology M t := WithTopology.toTopology t ∘ f i
  let : ChartedSpace H' (WithTopology M t) :=
    chartedSpaceOfIntegralManifolds hf hm hmr hinv hD hinj hcover
  let : IsManifold J m (WithTopology M t) :=
    isManifold_chartedSpaceOfIntegralManifolds hf hm hmr hinv hD hinj hcover
  have hlocal (i : ι) : IsLocalDiffeomorph J J m (φ i) :=
    isLocalDiffeomorph_chartedSpaceOfIntegralManifolds hf hm hmr hinv hD hinj hcover i
  have hcov := integral_coinduced_cover hcover
  have hcomp (i : ι) : WithTopology.ofTopology ∘ φ i = f i :=
    funext fun y ↦ WithTopology.ofTopology_toTopology t (f i y)
  rw [isIntegralManifold_iff]
  refine ⟨inferInstance, ?_, ?_⟩
  · apply isImmersion_iff_forall_isImmersionAt.2
    intro x
    obtain ⟨i, y, rfl⟩ := hcov x
    exact (isImmersionAt_comp_isLocalDiffeomorphAt_iff (hlocal i y)).1
      ((hcomp i).symm ▸ (hf i).isImmersion.isImmersionAt y)
  · intro x
    obtain ⟨i, y, rfl⟩ := hcov x
    have hder := (hlocal i y).range_mfderiv_comp (K := I)
      (g := WithTopology.ofTopology (t := t))
      (by exact_mod_cast (ne_of_gt (zero_lt_one.trans_le hm)))
    rw [hcomp i] at hder
    exact hder ▸ (hf i).range_mfderiv y

end TauCeti
