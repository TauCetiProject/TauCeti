/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.LocalUniqueness

import TauCeti.Geometry.Manifold.Topology
import TauCeti.Topology.LocallyConstant.Lindelof
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Weak embeddedness of integral manifolds

An injective integral immersion of an involutive constant-rank distribution with a
second-countable intrinsic carrier is weakly embedded: every `C^m` map into its image has a
`C^m` factorization through that carrier. The factor is continuous even for a continuous test
map from a locally connected space.

The ambient normed model is finite dimensional and real. The integral immersion has regularity
`m ≥ 1`, and the ambient manifold has regularity `r` with `m + 1 ≤ r`. Both manifolds are
boundaryless, but their models may have boundary. The carrier retains its given topology.

## Main results

* `TauCeti.IsIntegralManifold.continuous_of_comp_eq`: continuity of the intrinsic lift.
* `TauCeti.IsIntegralManifold.exists_contMDiff_factor`: weak embeddedness.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Proposition 19.16
  and Theorem 19.17, pp. 500–501 (local slices and weak embeddedness).
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace
open scoped Topology Manifold ContDiff

namespace TauCeti

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ∞} {r : ℕ∞ω} [IsManifold I r M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J m N]
  [SecondCountableTopology N]
  {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

-- The transverse coordinate is locally constant on the preimage of a flat chart.
omit [IsManifold I r M] [SecondCountableTopology N] in
private theorem locallyConstant_transverse
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m)
    (Φ : PartialEquiv M E) (hopen : IsOpen Φ.source)
    (hΦ : ContMDiffOn I 𝓘(ℝ, E) m Φ Φ.source)
    (W : Submodule ℝ E)
    (hflat : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W) :
    IsLocallyConstant (fun z : f ⁻¹' Φ.source ↦
      (Submodule.Quotient.mk (Φ (f z.val)) : E ⧸ W)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  have he : ∀ᶠ y in 𝓝 z.val, Φ (f y) - Φ (f z.val) ∈ W :=
    hf.eventually_sub_mem_of_flatChart (by exact_mod_cast hm) Φ hopen hΦ W hflat z.property
  filter_upwards [continuous_subtype_val.continuousAt.eventually he] with y hy
  exact (Submodule.Quotient.eq W).mpr hy

-- A continuous map from a locally connected space into the image stays locally in one plaque.
omit [IsManifold I r M] in
private theorem eventually_sub_mem_of_range_subset
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m)
    (Φ : PartialEquiv M E) (hopen : IsOpen Φ.source)
    (hΦ : ContMDiffOn I 𝓘(ℝ, E) m Φ Φ.source)
    (W : Submodule ℝ E)
    (hflat : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W)
    {P : Type*} [TopologicalSpace P] [LocallyConnectedSpace P]
    {g : P → M} (hg : Continuous g) (hr : range g ⊆ range f)
    {x : P} (hx : g x ∈ Φ.source) :
    ∀ᶠ y in 𝓝 x, Φ (g y) - Φ (g x) ∈ W := by
  -- Closedness supplies the quotient norm and its complete regularity.
  let _ : IsClosed (W : Set E) := W.closed_of_finiteDimensional
  let U : Set N := f ⁻¹' Φ.source
  let V : Set P := g ⁻¹' Φ.source
  have hV : IsOpen V := hopen.preimage hg
  let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
  let a : U → E ⧸ W := fun z ↦ Submodule.Quotient.mk (Φ (f z.val))
  let b : V → E ⧸ W := fun z ↦ Submodule.Quotient.mk (Φ (g z.val))
  have ha : IsLocallyConstant a := locallyConstant_transverse hf hm Φ hopen hΦ W hflat
  have hb : Continuous b := W.mkQL.continuous.comp <|
    hΦ.continuousOn.comp_continuous (hg.comp continuous_subtype_val) fun z ↦ z.property
  have hrab : range b ⊆ range a := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hr (mem_range_self z.val)
    exact ⟨⟨w, by simpa only [U, V, mem_preimage, hw] using z.property⟩,
      by simp only [a, b, hw]⟩
  have hlc : IsLocallyConstant b :=
    hb.isLocallyConstant_of_range_subset ha hrab
  let x' : V := ⟨x, hx⟩
  have he : ∀ᶠ y in 𝓝 x', b y = b x' := hlc.eventually_eq x'
  obtain ⟨T, hT, hsub⟩ := (mem_nhds_subtype V x' _).mp he
  filter_upwards [hT, hV.mem_nhds hx] with y hy hyV
  have hyT : (⟨y, hyV⟩ : V) ∈ Subtype.val ⁻¹' T := mem_preimage.mpr hy
  exact (Submodule.Quotient.eq W).mp (hsub hyT)

variable [BoundarylessManifold I M] [BoundarylessManifold J N]

omit [IsManifold I r M] [BoundarylessManifold I M] in
private theorem continuousAt_factor_of_flatChart [IsManifold I (m : ℕ∞ω) M]
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hinj : Injective f)
    (Φ : PartialEquiv M E) (hΦopen : IsOpen Φ.source)
    (hΦsmooth : ContMDiffOn I 𝓘(ℝ, E) m Φ Φ.source) (W : Submodule ℝ E)
    (hflatΦ : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W)
    {P : Type*} [TopologicalSpace P] [LocallyConnectedSpace P]
    {g : P → M} {h : P → N} (hg : Continuous g) (hcomp : f ∘ h = g)
    {x : P} (hxΦ : g x ∈ Φ.source)
    (hΦinj : Injective (mfderiv I 𝓘(ℝ, E) Φ (f (h x)))) : ContinuousAt h x := by
  have hpoint (y : P) : f (h y) = g y := congrFun hcomp y
  have hr : range g ⊆ range f := by
    rintro _ ⟨y, rfl⟩
    exact ⟨h y, hpoint y⟩
  have hfxΦ : f (h x) ∈ Φ.source := (hpoint x).symm ▸ hxΦ
  obtain ⟨c, hxc, hc0, hcsrc, hfc⟩ :=
    hf.exists_plaque_chart_of_flatChart Φ hΦopen hΦsmooth (by exact_mod_cast hm) W hflatΦ
      (BoundarylessManifold.isInteriorPoint (I := J)) hfxΦ hΦinj
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional W
  let a : P → W := fun y ↦ p (Φ (g y) - Φ (g x))
  have ha : ContinuousAt a x := p.continuous.continuousAt.comp
    (((hΦsmooth.continuousOn.continuousAt (hΦopen.mem_nhds hxΦ)).comp hg.continuousAt).sub
      continuousAt_const)
  have ha0 : a x = 0 := by simp only [a, sub_self, map_zero]
  have hxct : a x ∈ c.target := by rw [ha0, ← hc0]; exact c.map_source hxc
  have hct : ∀ᶠ y in 𝓝 x, a y ∈ c.target := ha.preimage_mem_nhds (c.open_target.mem_nhds hxct)
  have hstay := eventually_sub_mem_of_range_subset hf hm Φ hΦopen hΦsmooth W hflatΦ hg hr hxΦ
  have hlift : (fun y ↦ c.symm (a y)) =ᶠ[𝓝 x] h := by
    filter_upwards [hct, hstay, hg.continuousAt.preimage_mem_nhds (hΦopen.mem_nhds hxΦ)]
      with y hyc hyW hyΦ
    apply hinj
    apply Φ.injOn (hcsrc (c.map_target hyc))
      (by simpa only [mem_preimage, hpoint y] using hyΦ)
    rw [hfc _ (c.map_target hyc), c.right_inv hyc, hpoint x, hpoint y]
    have hpval := congrArg Subtype.val (hp ⟨Φ (g y) - Φ (g x), hyW⟩)
    calc
      Φ (g x) + (a y : E) = Φ (g x) + (Φ (g y) - Φ (g x)) :=
        congrArg (fun v : E ↦ Φ (g x) + v) hpval
      _ = Φ (g y) := by abel
  have hccont : ContinuousAt (fun y ↦ c.symm (a y)) x :=
    (c.symm.contMDiffOn.continuousOn.continuousAt (c.open_target.mem_nhds hxct)).comp ha
  exact hccont.congr hlift

/-- A factor of a continuous map through an injective integral immersion of an involutive
constant-rank distribution is continuous when the integral carrier is second countable and the
source is locally connected. The manifolds are boundaryless; the integral immersion is `C^m`,
with `1 ≤ m`, and the ambient manifold is `C^r`, with `m + 1 ≤ r`. -/
theorem IsIntegralManifold.continuous_of_comp_eq
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hinj : Injective f)
    (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    {P : Type*} [TopologicalSpace P] [LocallyConnectedSpace P]
    {g : P → M} {h : P → N} (hg : Continuous g) (hcomp : f ∘ h = g) : Continuous h := by
  let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
  let _ : IsManifold I (m : ℕ∞ω) M := .of_le (le_self_add.trans hmr)
  have hpoint (y : P) : f (h y) = g y := congrFun hcomp y
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨Φ, W, hΦopen, hxΦ, _, hΦsmooth, hflatΦ, hΦinj⟩ :=
    hinv.exists_flatChart_extend (m := m) (n := r) hm hmr hD
      (BoundarylessManifold.isInteriorPoint (I := I) (x := g x))
  exact continuousAt_factor_of_flatChart hf hm hinj Φ hΦopen hΦsmooth W hflatΦ
    hg hcomp hxΦ (hΦinj _ ((hpoint x).symm ▸ hxΦ))

/-- A `C^m` map into the image of an injective integral immersion of an involutive constant-rank
distribution has a `C^m` factorization through its intrinsic carrier when that carrier is second
countable. The integral and ambient manifolds are boundaryless, with ambient regularity `r`
satisfying `m + 1 ≤ r` and `1 ≤ m`. The test source may use any real model with corners. -/
theorem IsIntegralManifold.exists_contMDiff_factor
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hinj : Injective f)
    (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P]
    {g : P → M} (hg : ContMDiff K I m g) (hr : range g ⊆ range f) :
    ∃ h : P → N, ContMDiff K J m h ∧ f ∘ h = g := by
  classical
  let _ : LocallyPathConnectedSpace P := K.locallyPathConnectedSpace_of_chartedSpace P
  choose h hpoint using fun x : P ↦ hr (mem_range_self x)
  have hcomp : f ∘ h = g := funext hpoint
  have hc : Continuous h := hf.continuous_of_comp_eq hm hinj hmr hinv hD hg.continuous hcomp
  exact ⟨h, (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr
    ⟨hc, hcomp.symm ▸ hg⟩, hcomp⟩

end TauCeti
