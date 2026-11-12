/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.FlatChart
public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Submodule
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local uniqueness of integral manifolds

In a finite-dimensional real manifold, two integral immersions of the same involutive
distribution through the same point are related locally by a partial diffeomorphism of their
parameter spaces. In coordinates
flattening the distribution, integral immersions have affine plaque coordinates.

This gives the local compatibility needed to glue integral plaques into intrinsic leaf atlases.
The sources may use different manifold models, and only the distinguished source points and
their common image must be interior points.

## Main results

* `TauCeti.IsIntegralManifold.eventually_sub_mem_of_flatChart`: local containment in an affine
  plaque in flat coordinates.
* `TauCeti.IsIntegralManifold.exists_plaque_chart_of_flatChart`: affine plaque coordinates
  for an integral immersion in a chart flattening its distribution.
* `TauCeti.IsIntegralManifold.exists_partialDiffeomorph`: local equivalence of integral
  parametrizations of a constant-rank involutive distribution.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Proposition 19.16,
  p. 500 (the local structure of integral manifolds).
* `TauCeti.IsInvolutiveDistribution.exists_flatChart`, for Frobenius coordinates.
* `TauCeti.IsHorizontalMap.eventually_sub_mem` and `ContMDiffOn.exists_plaque_chart`, for
  transverse constancy and affine plaque coordinates.
-/

public section

open Set Function Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- An integral immersion of regularity at least one locally stays in a single affine plaque
in any coordinates flattening its distribution onto a finite-dimensional subspace. -/
theorem IsIntegralManifold.eventually_sub_mem_of_flatChart
    {n : ℕ∞ω} [IsManifold J n N]
    {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {f : N → M}
    (hf : IsIntegralManifold J n D f) (hn : 1 ≤ n)
    (Φ : PartialEquiv M E) (hΦopen : IsOpen Φ.source)
    (hΦsmooth : ContMDiffOn I 𝓘(ℝ, E) n Φ Φ.source)
    (W : Submodule ℝ E) [FiniteDimensional ℝ W]
    (hflat : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W)
    {x : N} (hx : f x ∈ Φ.source) :
    ∀ᶠ y in 𝓝 x, Φ (f y) - Φ (f x) ∈ W := by
  let _ : IsManifold J 1 N := .of_le hn
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hhor : IsHorizontalMap J D f :=
    isHorizontalMap_iff_range_mfderiv_le.mpr fun z ↦ (hf.range_mfderiv z).le
  have hDp (z : M) (hz : z ∈ Φ.source) :
      (D z).map (mvfderiv I Φ z).toLinearMap ≤ W := by
    rw [(D z).map_mvfderiv_eq_map_mfderiv (I := I) (x := z) Φ]
    exact (hflat z hz).le
  exact hhor.eventually_sub_mem (hf.contMDiff.mdifferentiable hn0).mdifferentiableOn
    isOpen_univ (hΦsmooth.mdifferentiableOn hn0) hΦopen W.closed_of_finiteDimensional
    hDp (mem_univ x) hx

/-- In `C^n` coordinates flattening its distribution onto a finite-dimensional subspace, an
integral immersion has local parameters at an interior source point whose image is in the
coordinate domain, for `1 ≤ n`, if the coordinate differential is injective at that image point.
The parameter chart sends the point to zero, identifies the coordinate map with an affine
inclusion, and stays inside the coordinate domain. -/
theorem IsIntegralManifold.exists_plaque_chart_of_flatChart
    {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {f : N → M}
    (hf : IsIntegralManifold J n D f)
    (Φ : PartialEquiv M E) (hΦopen : IsOpen Φ.source)
    (hΦsmooth : ContMDiffOn I 𝓘(ℝ, E) n Φ Φ.source)
    (hn : 1 ≤ n)
    (W : Submodule ℝ E) [FiniteDimensional ℝ W]
    (hD : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W)
    {x : N}
    (hx : J.IsInteriorPoint x) (hfx : f x ∈ Φ.source)
    (hΦinj : Injective (mfderiv I 𝓘(ℝ, E) Φ (f x))) :
    ∃ c : PartialDiffeomorph J 𝓘(ℝ, W) N W n,
      x ∈ c.source ∧ c x = 0 ∧ c.source ⊆ f ⁻¹' Φ.source ∧
        ∀ z ∈ c.source, Φ (f z) = Φ (f x) + (c z : E) := by
  let _ : IsManifold J 1 N := .of_le hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hopen : IsOpen (f ⁻¹' Φ.source) := hΦopen.preimage hf.contMDiff.continuous
  have hp : ContMDiffOn J 𝓘(ℝ, E) n (Φ ∘ f) (f ⁻¹' Φ.source) :=
    hΦsmooth.comp hf.contMDiff.contMDiffOn fun _ hz ↦ hz
  have hder : mfderiv J 𝓘(ℝ, E) (Φ ∘ f) x =
      (mfderiv I 𝓘(ℝ, E) Φ (f x)).comp (mfderiv J I f x) :=
    mfderiv_comp x ((hΦsmooth.contMDiffAt (hΦopen.mem_nhds hfx)).mdifferentiableAt hn0)
      ((hf.contMDiff x).mdifferentiableAt hn0)
  have hinj : Injective (mfderiv J 𝓘(ℝ, E) (Φ ∘ f) x) := by
    rw [hder]
    exact hΦinj.comp (hf.isImmersion.mfderiv_injective hn0 x)
  have hrange : LinearMap.range (mfderiv J 𝓘(ℝ, E) (Φ ∘ f) x).toLinearMap = W := by
    simpa only [hder, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      hf.range_mfderiv x] using hD (f x) hfx
  have hplaque := hf.eventually_sub_mem_of_flatChart hn Φ hΦopen hΦsmooth W hD hfx
  exact ContMDiffOn.exists_plaque_chart hp hopen hfx hn hx hinj hrange hplaque

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ F' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- Integral immersions of the same involutive `C^m` distribution through the same point are
locally related by a `C^m` partial diffeomorphism intertwining their ambient maps, for `1 ≤ m`.
The ambient normed model is finite-dimensional.
The ambient regularity `r` satisfies `m + 1 ≤ r`; the two source points and their common image
are interior points. No global injectivity or connectedness of the parametrizations is required. -/
theorem IsIntegralManifold.exists_partialDiffeomorph
    [FiniteDimensional ℝ E] {m : ℕ∞} {r : ℕ∞ω} [IsManifold I r M]
    [IsManifold J m N] [IsManifold K m P]
    {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {f : N → M} {g : P → M}
    (hf : IsIntegralManifold J m D f) (hg : IsIntegralManifold K m D g)
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D) {x : N} {y : P}
    (hx : J.IsInteriorPoint x) (hy : K.IsInteriorPoint y)
    (hfx : I.IsInteriorPoint (f x)) (hfg : f x = g y) :
    ∃ e : PartialDiffeomorph J K N P m,
      x ∈ e.source ∧ e x = y ∧ ∀ z ∈ e.source, f z = g (e z) := by
  let _ : IsManifold I 1 M :=
    .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
  have hm' : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  let _ : IsManifold I (m : ℕ∞ω) M :=
    .of_le (le_self_add.trans hmr)
  -- Both immersions use one set of extended flat coordinates.
  obtain ⟨Φ, W, hΦopen, hxΦ, _, hΦsmooth, hflatΦ, hΦinj⟩ :=
    hinv.exists_flatChart_extend hm hmr hD hfx
  have hyΦ : g y ∈ Φ.source := hfg ▸ hxΦ
  -- Each immersion has local parameters in the same affine direction subspace.
  obtain ⟨c, hxc, hc0, hcsrc, hfc⟩ :=
    hf.exists_plaque_chart_of_flatChart Φ hΦopen hΦsmooth hm' W hflatΦ hx hxΦ
      (hΦinj (f x) hxΦ)
  obtain ⟨d, hyd, hd0, hdsrc, hgd⟩ :=
    hg.exists_plaque_chart_of_flatChart Φ hΦopen hΦsmooth hm' W hflatΦ hy hyΦ
      (hΦinj (g y) hyΦ)
  obtain ⟨τ, hxτ, hτx, hτc, hτd, hτ⟩ :=
    c.exists_transition d hxc hyd (hc0.trans hd0.symm)
  refine ⟨τ, hxτ, hτx, ?_⟩
  intro z hz
  -- The transition intertwines flat coordinates; invert the ambient chart to recover the maps.
  have hcoord : Φ (f z) = Φ (g (τ z)) := by
    rw [hfc z (hτc hz), hgd (τ z) (hτd hz), hfg, hτ z hz]
  calc
    f z = Φ.symm (Φ (f z)) := (Φ.left_inv (hcsrc (hτc hz))).symm
    _ = Φ.symm (Φ (g (τ z))) := congrArg Φ.symm hcoord
    _ = g (τ z) := Φ.left_inv (hdsrc (hτd hz))

end TauCeti
