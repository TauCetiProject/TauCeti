/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Tensoriality of globally smooth operations

This file complements Mathlib's pointwise tensoriality API with a criterion for operations whose
locality, additivity, and smooth-function linearity laws are available for globally smooth sections.
The criterion applies to finite-rank smooth real vector bundles over finite-dimensional Hausdorff
manifolds. The target only needs addition and scalar multiplication; no algebraic laws on
these operations are required beyond the stated laws for the section operation.

## Main results

* `TauCeti.Manifold.eq_of_contMDiff_tensorial`: a local operation satisfying these laws has equal
  values on globally smooth sections which agree at the point of evaluation.
-/

public section

open Bundle FiberBundle Module
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- On a finite-rank smooth real vector bundle over a finite-dimensional Hausdorff manifold,
a local operation which is additive and linear over globally smooth functions on globally
smooth sections depends only on the value of such a section at the point of evaluation.
The target need only carry addition and scalar multiplication, without any algebraic laws. -/
theorem eq_of_contMDiff_tensorial
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W]
    [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
    {A : Type*} [Add A] [SMul ℝ A]
    (Φ : (Π x : M, W x) → A) (x : M)
    (hlocal : ∀ {s s' : Π x : M, W x}, CMDiff ∞ (T% s) → CMDiff ∞ (T% s') →
      Filter.Eventually (fun y ↦ s y = s' y) (nhds x) → Φ s = Φ s')
    (hadd : ∀ {s s' : Π x : M, W x}, CMDiff ∞ (T% s) → CMDiff ∞ (T% s') →
      Φ (s + s') = Φ s + Φ s')
    (hsmul : ∀ {f : M → ℝ} {s : Π x : M, W x}, ContMDiff I 𝓘(ℝ) ∞ f →
      CMDiff ∞ (T% s) → Φ (f • s) = f x • Φ s)
    {s s' : Π x : M, W x} (hs : CMDiff ∞ (T% s)) (hs' : CMDiff ∞ (T% s'))
    (hss' : s x = s' x) : Φ s = Φ s' := by
  classical
  -- Cut off a local frame by a bump function which is one near `x`.  This gives globally smooth
  -- frame sections and coefficients while preserving the local frame expansion near `x`.
  let t := trivializationAt G W x
  have hxt : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt G W x
  have ht : t.baseSet ∈ nhds x := t.open_baseSet.mem_nhds hxt
  obtain ⟨ρ, hρt, -⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.mp ht
  let b := Basis.ofVectorSpace ℝ G
  let frame := t.localFrame b
  let coeff := t.localFrameCoeff I b
  let frame' (i) := (ρ : M → ℝ) • frame i
  let coeff' (u : Π x : M, W x) (i) (y : M) := ρ y * coeff i y (u y)
  let expansion (u : Π x : M, W x) : Π y : M, W y :=
    ∑ i, coeff' u i • frame' i
  have hframe (i) : CMDiff ∞ (T% (frame' i)) := by
    exact ρ.contMDiff.contMDiffOn.smul_section_of_tsupport t.open_baseSet hρt
      (t.contMDiffOn_localFrame_baseSet ∞ b i)
  have hcoeff' (u : Π x : M, W x) (hu : CMDiff ∞ (T% u)) (i) :
      ContMDiff I 𝓘(ℝ) ∞ (coeff' u i) := by
    apply contMDiff_of_tsupport
    intro y hy
    have hyρ : y ∈ tsupport (ρ : M → ℝ) :=
      (tsupport_mul_subset_left : tsupport (coeff' u i) ⊆ tsupport (ρ : M → ℝ)) hy
    exact ρ.contMDiffAt.mul (contMDiffAt_localFrameCoeff b (hρt hyρ) (hu y) i)
  have hexpansion (u : Π x : M, W x) (hu : CMDiff ∞ (T% u)) :
      CMDiff ∞ (T% (expansion u)) := by
    simpa only [expansion, Finset.sum_apply] using
      (ContMDiff.sum_section (s := Finset.univ) fun i _ ↦
        (hcoeff' u hu i).smul_section (hframe i))
  have hexpansion_eq (u : Π x : M, W x) :
      Filter.Eventually (fun y ↦ expansion u y = u y) (nhds x) := by
    filter_upwards [ρ.eventuallyEq_one,
      t.eventually_eq_localFrame_sum_coeff_smul (I := I) b hxt] with y hρ hu
    have hρ' : ρ y = 1 := by simpa using hρ
    dsimp only [expansion]
    simpa [coeff', frame', hρ', coeff, frame] using hu.symm
  -- Compare finite sums directly: no additive identity or scalar-action laws on `A` are needed.
  have hsum (q : Finset (Basis.ofVectorSpaceIndex ℝ G))
      (u v : Basis.ofVectorSpaceIndex ℝ G → Π x : M, W x)
      (hu : ∀ i, CMDiff ∞ (T% (u i))) (hv : ∀ i, CMDiff ∞ (T% (v i)))
      (huv : ∀ i, Φ (u i) = Φ (v i)) :
      CMDiff ∞ (T% (∑ i ∈ q, u i)) ∧ CMDiff ∞ (T% (∑ i ∈ q, v i)) ∧
        Φ (∑ i ∈ q, u i) = Φ (∑ i ∈ q, v i) := by
    induction q using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, and_true]
        exact ⟨contMDiff_zeroSection ℝ W, contMDiff_zeroSection ℝ W⟩
    | @insert i q hi ih =>
        simp only [Finset.sum_insert hi]
        refine ⟨(hu i).add_section ih.1, (hv i).add_section ih.2.1, ?_⟩
        rw [hadd (hu i) ih.1, hadd (hv i) ih.2.1, huv i, ih.2.2]
  rw [hlocal hs (hexpansion s hs) ((hexpansion_eq s).mono fun y hy ↦ hy.symm),
    hlocal hs' (hexpansion s' hs') ((hexpansion_eq s').mono fun y hy ↦ hy.symm)]
  dsimp only [expansion]
  refine (hsum Finset.univ (fun i ↦ coeff' s i • frame' i)
    (fun i ↦ coeff' s' i • frame' i)
    (fun i ↦ (hcoeff' s hs i).smul_section (hframe i))
    (fun i ↦ (hcoeff' s' hs' i).smul_section (hframe i)) ?_).2.2
  intro i
  rw [hsmul (hcoeff' s hs i) (hframe i), hsmul (hcoeff' s' hs' i) (hframe i)]
  congr 1
  simp only [coeff', ρ.eq_one, one_mul]
  exact t.localFrameCoeff_congr (I := I) b (i := i) hss'

end TauCeti.Manifold
