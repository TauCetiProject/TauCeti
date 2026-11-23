/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Tensoriality of globally `C^n` operations

This file complements Mathlib's pointwise tensoriality API with a criterion for operations whose
additivity and `C^n`-function linearity laws are available for globally `C^n` sections.
The criterion applies to finite-rank `C^n` real vector bundles (`1 ≤ n ≤ ∞`) over
finite-dimensional Hausdorff `C^n` manifolds. The target only needs addition and scalar
multiplication; no algebraic laws on these operations are required beyond the stated laws for the
section operation.

## Main results

* `TauCeti.Manifold.eq_of_contMDiff_smul_of_eventuallyEq`: `C^n`-function linearity (`n ≤ ∞`)
  implies locality.
* `TauCeti.Manifold.eq_of_contMDiff_tensorial`: an operation satisfying these laws for `1 ≤ n ≤ ∞`
  has equal values on globally `C^n` sections which agree at the point of evaluation.
-/

public section

open Bundle FiberBundle Module
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

/-- An operation on sections which is additive on globally `C^n` sections takes equal values on
two finite sums of globally `C^n` sections whenever it takes equal values on the summands.  The
target needs only an addition, without any algebraic laws. -/
theorem map_sum_eq_of_contMDiff_additive
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle 𝕜 G W]
    {A : Type*} [Add A] (Φ : (Π x : M, W x) → A)
    (hadd : ∀ {s s' : Π x : M, W x}, CMDiff n (T% s) → CMDiff n (T% s') →
      Φ (s + s') = Φ s + Φ s')
    {ι : Type*} (q : Finset ι) (u v : ι → Π x : M, W x)
    (hu : ∀ i ∈ q, CMDiff n (T% (u i))) (hv : ∀ i ∈ q, CMDiff n (T% (v i)))
    (huv : ∀ i ∈ q, Φ (u i) = Φ (v i)) :
    Φ (∑ i ∈ q, u i) = Φ (∑ i ∈ q, v i) := by
  classical
  induction q using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]
  | @insert i q hi ih =>
      rw [Finset.forall_mem_insert] at hu hv huv
      -- Partial sums of globally `C^n` sections are globally `C^n`.
      have hsum {w : ι → Π x : M, W x} (hw : ∀ j ∈ q, CMDiff n (T% (w j))) :
          CMDiff n (T% (∑ j ∈ q, w j)) := by
        simpa only [Finset.sum_apply] using ContMDiff.sum_section hw
      simp only [Finset.sum_insert hi]
      rw [hadd hu.1 (hsum hu.2), hadd hv.1 (hsum hv.2), huv.1, ih hu.2 hv.2 huv.2]

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M]

/-- An operation on sections which respects multiplication by globally `C^n` functions (`n ≤ ∞`)
at two sections takes equal values on them whenever they agree near the evaluation point. The
sections need not be `C^n`, and neither additivity nor any laws for scalar multiplication on the
target are required. This is the bump-function version of `TensorialAt.local`, whose cutoff need
only be differentiable at the evaluation point. -/
theorem eq_of_contMDiff_smul_of_eventuallyEq
    {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
    {A : Type*} [SMul ℝ A] (Φ : (Π x : M, W x) → A) (x : M) {s s' : Π x : M, W x}
    (hsmul : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) n f → Φ (f • s) = f x • Φ s)
    (hsmul' : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) n f → Φ (f • s') = f x • Φ s')
    (hss' : ∀ᶠ y in 𝓝 x, s y = s' y) : Φ s = Φ s' := by
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hss').mem_iff.mp hss'
  have hcut : (ρ : M → ℝ) • s = (ρ : M → ℝ) • s' := by
    funext y
    by_cases hy : ρ y = 0
    · simp [hy]
    · exact congrArg (ρ y • ·) (hρ hy)
  -- Multiplying by `ρ`, which is one at `x`, does not change the value of `Φ`: the scalar law for
  -- the constant function one supplies the identity on that value.
  have hρΦ {u : Π x : M, W x}
      (hu : ∀ {f : M → ℝ}, ContMDiff I 𝓘(ℝ) n f → Φ (f • u) = f x • Φ u) :
      Φ ((ρ : M → ℝ) • u) = Φ u := by
    rw [hu ρ.contMDiff_of_isManifold, ρ.eq_one]
    simpa only [Pi.smul_def', one_smul] using (hu (f := fun _ ↦ 1) contMDiff_const).symm
  rw [← hρΦ hsmul, ← hρΦ hsmul', hcut]

/-- On a finite-rank `C^n` real vector bundle over a finite-dimensional Hausdorff `C^n` manifold
(`1 ≤ n ≤ ∞`), an operation which is additive and linear over globally `C^n` functions on globally
`C^n` sections depends only on the value of such a section at the point of evaluation.
The target need only carry addition and scalar multiplication, without any algebraic laws. -/
theorem eq_of_contMDiff_tensorial
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle n G W I]
    {A : Type*} [Add A] [SMul ℝ A]
    (Φ : (Π x : M, W x) → A) (x : M)
    (hadd : ∀ {s s' : Π x : M, W x}, CMDiff n (T% s) → CMDiff n (T% s') →
      Φ (s + s') = Φ s + Φ s')
    (hsmul : ∀ {f : M → ℝ} {s : Π x : M, W x}, ContMDiff I 𝓘(ℝ) n f →
      CMDiff n (T% s) → Φ (f • s) = f x • Φ s)
    {s s' : Π x : M, W x} (hs : CMDiff n (T% s)) (hs' : CMDiff n (T% s'))
    (hss' : s x = s' x) (hn : 1 ≤ n := by simp) : Φ s = Φ s' := by
  have : ContMDiffVectorBundle 1 G W I := ContMDiffVectorBundle.of_le hn
  -- Cut off a local frame by a bump function which is one near `x`.  This gives globally `C^n`
  -- frame sections and coefficients while preserving the local frame expansion near `x`.
  let t := trivializationAt G W x
  have hxt : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt G W x
  have ht : t.baseSet ∈ 𝓝 x := t.open_baseSet.mem_nhds hxt
  obtain ⟨ρ, hρt, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.mp ht
  let b := Basis.ofVectorSpace ℝ G
  let frame' (i) := (ρ : M → ℝ) • t.localFrame b i
  let coeff' (u : Π x : M, W x) (i) (y : M) := ρ y * t.localFrameCoeff I b i y (u y)
  have hframe (i) : CMDiff n (T% (frame' i)) :=
    ρ.contMDiff_of_isManifold.contMDiffOn.smul_section_of_tsupport t.open_baseSet hρt
      (t.contMDiffOn_localFrame_baseSet n b i)
  have hcoeff' (u : Π x : M, W x) (hu : CMDiff n (T% u)) (i) :
      ContMDiff I 𝓘(ℝ) n (coeff' u i) :=
    t.contMDiff_mul_localFrameCoeff b ρ.contMDiff_of_isManifold.contMDiffOn hρt hu.contMDiffOn i
  have hterm (u : Π x : M, W x) (hu : CMDiff n (T% u)) (i) :
      CMDiff n (T% (coeff' u i • frame' i)) :=
    (hcoeff' u hu i).smul_section (hframe i)
  -- Near `x`, a `C^n` section agrees with its expansion in the cut-off frame, which is `C^n`.
  have hexpansion (u : Π x : M, W x) (hu : CMDiff n (T% u)) :
      Φ u = Φ (∑ i, coeff' u i • frame' i) := by
    refine eq_of_contMDiff_smul_of_eventuallyEq Φ x (hsmul · hu) (hsmul · ?_) ?_
    · simpa only [Finset.sum_apply] using ContMDiff.sum_section fun i _ ↦ hterm u hu i
    · filter_upwards [ρ.eventuallyEq_one,
        t.eventually_eq_localFrame_sum_coeff_smul (I := I) b hxt] with y hρ hu
      simpa [coeff', frame', hρ] using hu
  rw [hexpansion s hs, hexpansion s' hs']
  refine map_sum_eq_of_contMDiff_additive Φ hadd Finset.univ _ _ (fun i _ ↦ hterm s hs i)
    (fun i _ ↦ hterm s' hs' i) fun i _ ↦ ?_
  rw [hsmul (hcoeff' s hs i) (hframe i), hsmul (hcoeff' s' hs' i) (hframe i)]
  simp only [coeff', ρ.eq_one, one_mul, t.localFrameCoeff_congr (I := I) b (i := i) hss']

end TauCeti.Manifold
