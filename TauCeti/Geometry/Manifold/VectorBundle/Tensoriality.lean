/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Tensoriality of globally smooth operations

This file complements Mathlib's pointwise tensoriality API with a criterion for operations whose
locality, additivity, and smooth-function linearity laws are available for globally smooth sections.

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

/-- A local operation which is additive and linear over globally smooth functions on globally
smooth sections depends only on the value of such a section at the point of evaluation. -/
theorem eq_of_contMDiff_tensorial
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W]
    [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
    {A : Type*} [AddCommGroup A] [Module ℝ A]
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
    -- On the support of the bump function, the local coefficient is the corresponding coordinate
    -- of the section in the chosen trivialization.
    have hcoeffAt : ContMDiffAt I 𝓘(ℝ) ∞ (fun z ↦ coeff i z (u z)) y := by
      let aux := fun z ↦ b.repr (t ((T% u) z)).2 i
      have htriv : CMDiffAt ∞ (fun z ↦ (t ((T% u) z)).2) y := by
        simpa using (t.contMDiffAt_section_iff (hρt hyρ)).1 (hu y)
      let breprl : G →L[ℝ] ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := fun v ↦ b.repr v i
            map_add' := fun v w ↦ by simp
            map_smul' := fun c v ↦ by simp }
      have haux : ContMDiffAt I 𝓘(ℝ) ∞ aux y := by
        exact (contMDiffAt_iff_contDiffAt.mpr (by fun_prop : ContDiffAt ℝ ∞ breprl _)).comp y htriv
      refine haux.congr_of_eventuallyEq ?_
      filter_upwards [t.open_baseSet.mem_nhds (hρt hyρ)] with z hz
      simp [aux, coeff, t.localFrameCoeff_eq_coeff hz]
    exact ρ.contMDiffAt.mul hcoeffAt
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
  have hzero : Φ 0 = 0 := by
    simpa using hsmul (f := (0 : M → ℝ)) (s := (0 : Π x : M, W x))
      contMDiff_const (contMDiff_zeroSection ℝ W)
  -- Binary additivity suffices to distribute `Φ` over the finite local-frame expansion.
  have hsum (u : ∀ _ : Basis.ofVectorSpaceIndex ℝ G, Π x : M, W x)
      (hu : ∀ i, CMDiff ∞ (T% (u i))) :
      Φ (∑ i, u i) = ∑ i, Φ (u i) := by
    let q : Finset (Basis.ofVectorSpaceIndex ℝ G) := Finset.univ
    -- A `Fintype` sum is definitionally a sum over `Finset.univ`; naming that finset `q`
    -- exposes it in the goal so that `Finset.induction_on` can induct over the summation set.
    change Φ (∑ i ∈ q, u i) = ∑ i ∈ q, Φ (u i)
    induction q using Finset.induction_on with
    | empty => simpa using hzero
    | @insert i q hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd (hu i), ih]
        simpa only [Finset.sum_apply] using
          (ContMDiff.sum_section (s := q) fun j _ ↦ hu j)
  rw [hlocal hs (hexpansion s hs) ((hexpansion_eq s).mono fun y hy ↦ hy.symm),
    hlocal hs' (hexpansion s' hs') ((hexpansion_eq s').mono fun y hy ↦ hy.symm)]
  dsimp only [expansion]
  rw [hsum (fun i ↦ coeff' s i • frame' i) fun i ↦
      (hcoeff' s hs i).smul_section (hframe i),
    hsum (fun i ↦ coeff' s' i • frame' i) fun i ↦
      (hcoeff' s' hs' i).smul_section (hframe i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsmul (hcoeff' s hs i) (hframe i), hsmul (hcoeff' s' hs' i) (hframe i)]
  congr 1
  simp only [coeff', ρ.eq_one, one_mul]
  exact t.localFrameCoeff_congr (I := I) b (i := i) hss'

end TauCeti.Manifold
