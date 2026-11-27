/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Analysis.Calculus.Morse.Parametric
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.Morse.ZeroSectionChart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Section
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Topology.FiberBundle.Countable
import TauCeti.Topology.FiberBundle.LocallyCompact
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The parametric Morse lemma in a vector bundle

Let `E → B` be a `C^{n+2}` vector bundle with finite-dimensional normed fibres over a
finite-dimensional, boundaryless, Hausdorff and second-countable manifold, and let `g` be a
`C^{n+2}` function, `1 ≤ n ≤ ∞`, on a neighbourhood of the zero section of `E`, such that every
zero vector `0_b` is a critical point of the fibre restriction `g_b = g ⟨b, ·⟩` and the vertical
Hessian `H_b = D²g_b(0)` is invertible. The value `g (0_b)` may vary with `b`.
This file proves the **parametric Morse lemma on the bundle**
(`TauCeti.exists_parametric_morse_partialDiffeomorph`): the canonical Morse coordinate
`ψ = TauCeti.bundleMorseCoord F g` is a change of coordinates near the whole zero section. That
is, `Φ x = ⟨x.proj, ψ x⟩` is a `C^n` partial diffeomorphism of the total space, defined on a
neighbourhood of the whole zero section, which preserves the fibres, fixes the zero section, and
puts `g` in fibrewise normal form

`g x = g (0_b) + ½ H_b (ψ x, ψ x)`,  `b = x.proj`.

Neither the base nor the zero section needs to be compact. This is the situation of a function
read on the normal bundle of a Morse–Bott critical submanifold through a tubular neighbourhood,
where moreover `g (0_b)` is locally constant; there the result is the Morse–Bott lemma on the
normal bundle.

In the chart of the total space at a zero vector `0_a`, `g` is a family `G (y, w)` on the product
of the base model with the model fibre, and the parametric Morse lemma along the zero section
(`TauCeti.exists_parametricMorseCoord_partialDiffeomorph_prod_ball`) puts it in normal form by the
canonical coordinate `(y, w) ↦ (y, TauCeti.parametricMorseCoord G (y, w))`. That coordinate only
reads `g` along the fibres, so over the domain of the chart it is the canonical Morse coordinate
`ψ` read in the trivialization at `a`. Hence `x ↦ ⟨x.proj, ψ x⟩` is a local diffeomorphism near
the zero section and fixes it, so it is injective on a neighbourhood of the zero section
(`IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section`). No choice of charts enters the
coordinate itself.

## Main results

* `TauCeti.exists_parametric_morse_partialDiffeomorph`: the parametric Morse lemma on a vector
  bundle: the canonical Morse coordinate `TauCeti.bundleMorseCoord` gives one fibre-preserving
  partial diffeomorphism defined near the whole zero section.

## References

* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the operator square root.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, Theorem 15.1,
  p. 143, for the Morse–Bott lemma on the normal bundle.
-/

public section

noncomputable section

open Bundle Filter Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E] {g : TotalSpace F E → ℝ} {W : Set (TotalSpace F E)}

section Chart

private theorem isOpen_chartDomain [IB.Boundaryless] (a : B) (hW : IsOpen W) :
    IsOpen ((extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).target ∩
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm ⁻¹' W) :=
  (continuousOn_extChartAt_symm _).isOpen_inter_preimage (isOpen_extChartAt_target _) hW

variable (IB) in
/-- The coordinate expression of `g` in the extended chart of the total space at the zero vector
`0_a`: a family of functions on the model fibre parametrized by the base model. -/
private def chartFamily (g : TotalSpace F E → ℝ) (a : B) : EB × F → ℝ :=
  g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm

private theorem chartFamily_apply (a : B) {y : EB} {b : B} (hyb : (extChartAt IB a).symm y = b)
    (hb : b ∈ (trivializationAt F E a).baseSet) (w : F) :
    chartFamily IB g a (y, w) = g ⟨b, (trivializationAt F E a).symm b w⟩ := by
  subst hyb
  rw [chartFamily, comp_apply, Bundle.extChartAt_symm_apply_of_mem_baseSet _ hb, zeroSection_proj]

/-- The chart family of a `C^{n+2}` function is `C^{n+2}` where the chart of the total space at
`0_a` lands in its domain. -/
private theorem chartFamily_contDiffOn {n : ℕ∞} [IsManifold IB (n + 2) B] [∀ b, NormedSpace ℝ (E b)]
    [VectorBundle ℝ F E] [ContMDiffVectorBundle (n + 2) F E IB] (a : B)
    (hg : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) (n + 2) g W) :
    ContDiffOn ℝ (n + 2) (chartFamily IB g a)
      ((extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).target ∩
        (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm ⁻¹' W) := by
  have h := (contMDiffOn_iff.mp hg).2 (zeroSection F E a) 0
  simpa [chartFamily, extChartAt_model_space_eq_id] using h

end Chart

section Fibre

variable [∀ b, NormedSpace ℝ (E b)] [VectorBundle ℝ F E]

private theorem chartDomain_mem_nhds [IB.Boundaryless] (a : B) (hW : IsOpen W)
    (hzero : ∀ b, zeroSection F E b ∈ W) :
    (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).target ∩
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm ⁻¹' W ∈
        𝓝 (extChartAt IB a a, (0 : F)) := by
  rw [← Bundle.extChartAt_zeroSection_self (IB := IB) (F := F) (V := E) a]
  refine (isOpen_chartDomain a hW).mem_nhds ⟨mem_extChartAt_target _, ?_⟩
  rw [mem_preimage, extChartAt_to_inv]
  exact hzero a

/-- A fibre restriction of the chart family is the fibre restriction of `g` read through the
trivialization at `a`. -/
private theorem chartFamily_slice (a : B) {y : EB} {b : B} (hyb : (extChartAt IB a).symm y = b)
    (hb : b ∈ (trivializationAt F E a).baseSet) :
    (fun w ↦ chartFamily IB g a (y, w)) =
      (fun v : E b ↦ g ⟨b, v⟩) ∘
        ((trivializationAt F E a).continuousLinearEquivAt ℝ b hb).symm := by
  ext w
  simp [chartFamily_apply a hyb hb]

private theorem fderiv_chartFamily_slice (a : B) {y : EB} {b : B}
    (hyb : (extChartAt IB a).symm y = b) (hb : b ∈ (trivializationAt F E a).baseSet) :
    fderiv ℝ (fun w ↦ chartFamily IB g a (y, w)) 0 =
      fderiv ℝ (fun v : E b ↦ g ⟨b, v⟩) 0 ∘L
        (((trivializationAt F E a).continuousLinearEquivAt ℝ b hb).symm : F →L[ℝ] E b) := by
  rw [chartFamily_slice a hyb hb, ContinuousLinearEquiv.comp_right_fderiv, map_zero]

private theorem fderiv_fderiv_chartFamily_slice (a : B) {y : EB} {b : B}
    (hyb : (extChartAt IB a).symm y = b) (hb : b ∈ (trivializationAt F E a).baseSet) :
    fderiv ℝ (fderiv ℝ (fun w ↦ chartFamily IB g a (y, w))) 0 =
      (fderiv ℝ (fderiv ℝ fun v : E b ↦ g ⟨b, v⟩) 0).bilinearComp
        (((trivializationAt F E a).continuousLinearEquivAt ℝ b hb).symm : F →L[ℝ] E b)
        (((trivializationAt F E a).continuousLinearEquivAt ℝ b hb).symm : F →L[ℝ] E b) := by
  ext w w'
  rw [chartFamily_slice a hyb hb, ContinuousLinearEquiv.fderiv_fderiv_comp_right_apply_apply,
    map_zero, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe]

private theorem eventually_fderiv_chartFamily_slice_eq_zero (a : B)
    (hcrit : ∀ b, fderiv ℝ (fun v : E b ↦ g ⟨b, v⟩) 0 = 0) :
    ∀ᶠ y in 𝓝 (extChartAt IB a a), fderiv ℝ (fun w ↦ chartFamily IB g a (y, w)) 0 = 0 := by
  have ha : (extChartAt IB a).symm (extChartAt IB a a) ∈ (trivializationAt F E a).baseSet := by
    rw [extChartAt_to_inv]
    exact mem_baseSet_trivializationAt F E a
  filter_upwards [(continuousAt_extChartAt_symm a).preimage_mem_nhds
    ((trivializationAt F E a).open_baseSet.mem_nhds ha)] with y hy
  rw [fderiv_chartFamily_slice a rfl hy, hcrit, ContinuousLinearMap.zero_comp]

private theorem isInvertible_fderiv_fderiv_chartFamily_slice (a : B) {y : EB} {b : B}
    (hyb : (extChartAt IB a).symm y = b) (hb : b ∈ (trivializationAt F E a).baseSet)
    (hH : (fderiv ℝ (fderiv ℝ fun v : E b ↦ g ⟨b, v⟩) 0).IsInvertible) :
    (fderiv ℝ (fderiv ℝ (fun w ↦ chartFamily IB g a (y, w))) 0).IsInvertible := by
  rw [fderiv_fderiv_chartFamily_slice a hyb hb]
  exact hH.bilinearComp _ _

end Fibre

section Local

variable [∀ b, NormedSpace ℝ (E b)] [VectorBundle ℝ F E] [FiniteDimensional ℝ EB]
  [FiniteDimensional ℝ F] [IB.Boundaryless] {n : ℕ∞} [IsManifold IB (n + 2) B]
  [ContMDiffVectorBundle (n + 2) F E IB]

variable (IB) in
/-- The fibre component of the canonical parametric Morse coordinate of `g` read in the chart of
the total space at `0_a`, transported back to the fibre through the trivialization at `a`. -/
private def localCoord (g : TotalSpace F E → ℝ) (a : B) (x : TotalSpace F E) : E x.proj :=
  (trivializationAt F E a).symm x.proj
    (parametricMorseCoord (chartFamily IB g a)
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a) x))

/-- **The parametric Morse lemma in the chart at a zero vector.** Near `0_a`, the map
`x ↦ ⟨x.proj, localCoord IB g a x⟩` is a `C^n` partial diffeomorphism of the total space, with
source in `W`, in which `g` is in fibrewise normal form. -/
private theorem exists_partialDiffeomorph_localCoord (a : B) (hW : IsOpen W)
    (hzero : ∀ b, zeroSection F E b ∈ W)
    (hg : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) (n + 2) g W)
    (hcrit : ∀ b, fderiv ℝ (fun v : E b ↦ g ⟨b, v⟩) 0 = 0)
    (hH : ∀ b, (fderiv ℝ (fderiv ℝ fun v : E b ↦ g ⟨b, v⟩) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ D : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F))
        (TotalSpace F E) (TotalSpace F E) n,
      zeroSection F E a ∈ D.source ∧ D.source ⊆ W ∧
      (∀ x ∈ D.source, D x = ⟨x.proj, localCoord IB g a x⟩) ∧
      ∀ x ∈ D.source, g x = g (zeroSection F E x.proj) + 2⁻¹ *
        fderiv ℝ (fderiv ℝ fun v : E x.proj ↦ g ⟨x.proj, v⟩) 0
          (localCoord IB g a x) (localCoord IB g a x) := by
  set τ := extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)
  set e := trivializationAt F E a
  have hτa := Bundle.extChartAt_zeroSection_self (IB := IB) (F := F) (V := E) a
  have : IsManifold (IB.prod 𝓘(ℝ, F)) n (TotalSpace F E) := .of_le (n := n + 2) le_self_add
  -- The parametric Morse chart `Θ` of the chart family, on a product `U₀ ×ˢ ball 0 r`.
  obtain ⟨U₀, r, Θ, -, haU₀, hr, hΘsource, hΘW, hΘeq, hnf⟩ :=
    exists_parametricMorseCoord_partialDiffeomorph_prod_ball (chartDomain_mem_nhds a hW hzero)
      (chartFamily_contDiffOn a hg) (eventually_fderiv_chartFamily_slice_eq_zero a hcrit)
      (isInvertible_fderiv_fderiv_chartFamily_slice a (extChartAt_to_inv a)
        (mem_baseSet_trivializationAt F E a) (hH a)) hn
  -- Conjugate `Θ` by the chart at `0_a`.
  let e₀ := extChartPartialDiffeomorph (IB.prod 𝓘(ℝ, F)) n (zeroSection F E a)
  let D := (e₀.trans Θ).trans e₀.symm
  have hsrc {x : TotalSpace F E} (hx : x ∈ D.source) : x ∈ τ.source ∧ x.proj ∈ e.baseSet ∧
      x.proj ∈ (extChartAt IB a).source ∧ τ x ∈ U₀ ×ˢ Metric.ball 0 r := by
    obtain ⟨h1, h2, -⟩ := (mem_extChartPartialDiffeomorph_trans_trans_symm_source _ _ Θ).1 hx
    have h1 : x ∈ τ.source := ((extChartPartialDiffeomorph_source _ _ _).subset h1).1
    have h3 := (Bundle.mem_extChartAt_source_iff _ _).1 h1
    exact ⟨h1, h3.1, h3.2, hΘsource ▸ h2⟩
  have happly {x : TotalSpace F E} (hx : x ∈ D.source) : D x = ⟨x.proj, localCoord IB g a x⟩ := by
    obtain ⟨-, hxe, hxc, hxΘ⟩ := hsrc hx
    rw [extChartPartialDiffeomorph_trans_trans_symm_apply, hΘeq _ hxΘ, localCoord,
      Bundle.extChartAt_apply_of_mem_baseSet _ hxe]
    exact Bundle.extChartAt_symm_apply_extChartAt_of_mem_baseSet _ hxe hxc _
  refine ⟨D, ?_, fun x hx ↦ ?_, fun x hx ↦ happly hx, fun x hx ↦ ?_⟩
  · have h0 : τ (zeroSection F E a) ∈ U₀ ×ˢ Metric.ball 0 r := hτa ▸ ⟨haU₀, Metric.mem_ball_self hr⟩
    have hΘa : Θ (τ (zeroSection F E a)) = τ (zeroSection F E a) := by
      rw [hΘeq _ h0, hτa, parametricMorseCoord_mk_zero]
    refine (mem_extChartPartialDiffeomorph_trans_trans_symm_source _ _ Θ).2
      ⟨(mem_extChartPartialDiffeomorph_source _ _ _).2 BoundarylessManifold.isInteriorPoint,
        hΘsource ▸ h0, ?_⟩
    rw [hΘa, (isOpen_extChartAt_target _).interior_eq]
    exact mem_extChartAt_target _
  · obtain ⟨hxτ, -, -, hxΘ⟩ := hsrc hx
    have h := (hΘW hxΘ).2
    rwa [mem_preimage, τ.left_inv hxτ] at h
  · -- Read the normal form of the chart family at `τ x` on the fibre over `x.proj`.
    obtain ⟨hxτ, hxe, hxc, hxΘ⟩ := hsrc hx
    have hyb := (extChartAt IB a).left_inv hxc
    have h := hnf _ hxΘ
    have hzero' : e.symm x.proj 0 = 0 := (e.symmL_apply (R := ℝ) hxe 0).symm.trans (map_zero _)
    have hτx : τ x = (extChartAt IB a x.proj, (e x).2) :=
      Bundle.extChartAt_apply_of_mem_baseSet _ hxe
    rw [show chartFamily IB g a (τ x) = g x by rw [chartFamily, comp_apply, τ.left_inv hxτ],
      hτx] at h
    dsimp only at h
    rw [chartFamily_apply a hyb hxe, hzero', fderiv_fderiv_chartFamily_slice a hyb hxe,
      ContinuousLinearMap.bilinearComp_apply] at h
    rw [h, localCoord, hτx]
    simp only [ContinuousLinearEquiv.coe_coe, Trivialization.symm_continuousLinearEquivAt_eq,
      Trivialization.symmL_apply (trivializationAt F E a) hxe]
    -- `zeroSection F E x.proj` is `⟨x.proj, 0⟩` by definition.
    rfl

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless] in
/-- **The chart coordinate is the canonical Morse coordinate.** Over the base set of the
trivialization at `a` and the source of the chart at `a`, the coordinate read in the chart of the
total space at `0_a` is the canonical Morse coordinate `TauCeti.bundleMorseCoord` of `g`. -/
private theorem localCoord_eq_bundleMorseCoord {a : B} {x : TotalSpace F E}
    (hxe : x.proj ∈ (trivializationAt F E a).baseSet) (hxc : x.proj ∈ (extChartAt IB a).source) :
    localCoord IB g a x = bundleMorseCoord F g x := by
  rw [localCoord, Bundle.extChartAt_apply_of_mem_baseSet _ hxe,
    (trivializationAt F E a).bundleMorseCoord_eq hxe]
  -- The canonical coordinate only reads the slice over the base point, on which the chart family
  -- is `g` read in the trivialization at `a`.
  simp only [zeroSection_proj, parametricMorseCoord_def,
    chartFamily_apply a ((extChartAt IB a).left_inv hxc) hxe]

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless] in
/-- Near `0_a`, the canonical Morse coordinate of `g` is the coordinate read in the chart of the
total space at `0_a`. -/
private theorem eventually_bundleMorseCoord_eq_localCoord (a : B) :
    ∀ᶠ x in 𝓝 (zeroSection F E a), bundleMorseCoord F g x = localCoord IB g a x := by
  filter_upwards [(FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
    (((trivializationAt F E a).open_baseSet.inter (isOpen_extChartAt_source (I := IB) a)).mem_nhds
      ⟨mem_baseSet_trivializationAt F E a, mem_extChartAt_source (I := IB) a⟩)] with x hx
  exact (localCoord_eq_bundleMorseCoord hx.1 hx.2).symm

/-- **The canonical Morse coordinate near a zero vector.** The fibre-preserving map
`x ↦ ⟨x.proj, bundleMorseCoord F g x⟩` is a local diffeomorphism at `0_a`, near which `g` is in
fibrewise normal form in the canonical Morse coordinate. -/
private theorem isLocalDiffeomorphAt_and_eventually_normalForm (a : B) (hW : IsOpen W)
    (hzero : ∀ b, zeroSection F E b ∈ W)
    (hg : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) (n + 2) g W)
    (hcrit : ∀ b, fderiv ℝ (fun v : E b ↦ g ⟨b, v⟩) 0 = 0)
    (hH : ∀ b, (fderiv ℝ (fderiv ℝ fun v : E b ↦ g ⟨b, v⟩) 0).IsInvertible) (hn : n ≠ 0) :
    IsLocalDiffeomorphAt (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨x.proj, bundleMorseCoord F g x⟩ : TotalSpace F E)) (zeroSection F E a) ∧
    ∀ᶠ x in 𝓝 (zeroSection F E a), g x = g (zeroSection F E x.proj) + 2⁻¹ *
      fderiv ℝ (fderiv ℝ fun v : E x.proj ↦ g ⟨x.proj, v⟩) 0
        (bundleMorseCoord F g x) (bundleMorseCoord F g x) := by
  obtain ⟨D, haD, -, hDeq, hDnf⟩ := exists_partialDiffeomorph_localCoord a hW hzero hg hcrit hH hn
  have hev : ∀ᶠ x in 𝓝 (zeroSection F E a),
      x ∈ D.source ∧ bundleMorseCoord F g x = localCoord IB g a x :=
    (D.open_source.eventually_mem haD).and (eventually_bundleMorseCoord_eq_localCoord a)
  obtain ⟨N, hNsub, hNo, haN⟩ := eventually_nhds_iff.1 hev
  refine ⟨isLocalDiffeomorphAt_of_eqOn (Φ := D.restrOpen N hNo) ?_ fun x hx ↦ ?_, ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨haD, haN⟩
  · rw [PartialDiffeomorph.restrOpen_source] at hx
    rw [PartialDiffeomorph.coe_restrOpen, hDeq x hx.1, (hNsub x hx.2).2]
  · filter_upwards [hev] with x hx
    rw [hx.2]
    exact hDnf x hx.1

end Local

section Global

variable [FiniteDimensional ℝ EB] [T2Space B] [SecondCountableTopology B]

variable [IB.Boundaryless] [∀ b, NormedSpace ℝ (E b)] [VectorBundle ℝ F E] [FiniteDimensional ℝ F]
  {n : ℕ∞} [IsManifold IB (n + 2) B] [ContMDiffVectorBundle (n + 2) F E IB]

/-- **The parametric Morse lemma on a vector bundle.** Let `E → B` be a `C^{n+2}` vector bundle
with finite-dimensional normed fibres over a finite-dimensional, boundaryless, Hausdorff and
second-countable manifold, `1 ≤ n ≤ ∞`, and let `g` be `C^{n+2}` on an open neighbourhood `W` of
the zero section. Suppose that every zero vector `0_b` is a critical point
of the fibre restriction `v ↦ g ⟨b, v⟩` with invertible Hessian `H_b`. Then the canonical Morse
coordinate `ψ = TauCeti.bundleMorseCoord F g` is a change of coordinates near the zero section:
there is a `C^n` partial diffeomorphism `Φ x = ⟨x.proj, ψ x⟩` of the total space, with source in
`W` containing the whole zero section, so preserving the fibres in both directions and fixing the
zero section (`TauCeti.bundleMorseCoord_zeroSection`), in which `g` is in fibrewise normal form:
`g x = g (0_b) + ½ H_b (ψ x) (ψ x)` for `x` over `b` in the source. -/
theorem exists_parametric_morse_partialDiffeomorph (hW : IsOpen W)
    (hzero : ∀ b, zeroSection F E b ∈ W) (hg : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) (n + 2) g W)
    (hcrit : ∀ b, fderiv ℝ (fun v : E b ↦ g ⟨b, v⟩) 0 = 0)
    (hH : ∀ b, (fderiv ℝ (fderiv ℝ fun v : E b ↦ g ⟨b, v⟩) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ Φ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F))
        (TotalSpace F E) (TotalSpace F E) n,
      (∀ b, zeroSection F E b ∈ Φ.source) ∧ Φ.source ⊆ W ∧
      (∀ x, Φ x = ⟨x.proj, bundleMorseCoord F g x⟩) ∧
      (∀ x ∈ Φ.target, (Φ.symm x).proj = x.proj) ∧
      ∀ x ∈ Φ.source, g x = g (zeroSection F E x.proj) + 2⁻¹ *
        fderiv ℝ (fderiv ℝ fun v : E x.proj ↦ g ⟨x.proj, v⟩) 0
          (bundleMorseCoord F g x) (bundleMorseCoord F g x) := by
  rcases isEmpty_or_nonempty B with hB | hB
  · have : IsEmpty (TotalSpace F E) := ⟨fun x ↦ isEmptyElim x.proj⟩
    exact ⟨(Diffeomorph.refl _ (TotalSpace F E) n).toPartialDiffeomorph,
      fun b ↦ isEmptyElim b, fun x _ ↦ isEmptyElim x, fun x ↦ isEmptyElim x,
      fun x _ ↦ isEmptyElim x, fun x _ ↦ isEmptyElim x⟩
  have : LocallyCompactSpace HB := IB.locallyCompactSpace
  have : LocallyCompactSpace B := ChartedSpace.locallyCompactSpace HB B
  have : MetrizableSpace (TotalSpace F E) := Manifold.metrizableSpace (IB.prod 𝓘(ℝ, F)) _
  have : Nonempty (TotalSpace F E) := hB.map (zeroSection F E)
  let Φ₀ : TotalSpace F E → TotalSpace F E := fun x ↦ ⟨x.proj, bundleMorseCoord F g x⟩
  let NF : TotalSpace F E → Prop := fun x ↦ g x = g (zeroSection F E x.proj) + 2⁻¹ *
    fderiv ℝ (fderiv ℝ fun v : E x.proj ↦ g ⟨x.proj, v⟩) 0
      (bundleMorseCoord F g x) (bundleMorseCoord F g x)
  have hlocal (a : B) := isLocalDiffeomorphAt_and_eventually_normalForm a hW hzero hg hcrit hH hn
  -- On the open set `O` where `Φ₀` is a local diffeomorphism and `g` is in normal form, which
  -- contains the zero section, `Φ₀` is injective near the zero section, which it fixes.
  let O : Set (TotalSpace F E) :=
    {x | IsLocalDiffeomorphAt (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n Φ₀ x} ∩
      interior {x | NF x} ∩ W
  have hU : IsOpen {x | IsLocalDiffeomorphAt (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n Φ₀ x} :=
    isOpen_iff_mem_nhds.mpr fun _ hx ↦ IsLocalDiffeomorphAt.eventually hx
  have hO : IsOpen O := (hU.inter isOpen_interior).inter hW
  have hzO : range (zeroSection F E) ⊆ O := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨(hlocal a).1, mem_interior_iff_mem_nhds.2 (hlocal a).2⟩, hzero a⟩
  have hind : IsInducing (Φ₀ ∘ zeroSection F E) := by
    have h : Φ₀ ∘ zeroSection F E = zeroSection F E := funext fun b ↦ by
      simp only [comp_apply, Φ₀, bundleMorseCoord_zeroSection]
      -- `zeroSection F E b` is `⟨b, 0⟩` by definition.
      rfl
    rw [h]
    exact (Function.LeftInverse.isEmbedding (f := TotalSpace.proj) (zeroSection_proj F E)
      (FiberBundle.continuous_proj F E) (Trivialization.continuous_zeroSection ℝ)).isInducing
  have hOloc : IsLocalDiffeomorphOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n Φ₀ O :=
    fun p ↦ p.property.1.1
  obtain ⟨Φ, hzΦ, hΦO, -, hΦ⟩ := hOloc.exists_partialDiffeomorph_near_section hO hzO
    (Trivialization.continuous_zeroSection ℝ) TotalSpace.proj (FiberBundle.continuous_proj F E)
    (zeroSection_proj F E) hind
  refine ⟨Φ, fun b ↦ hzΦ (mem_range_self b), fun x hx ↦ (hΦO hx).2, fun x ↦ by rw [hΦ],
    fun x hx ↦ ?_, fun x hx ↦ interior_subset (hΦO hx).1.2⟩
  -- `Φ` preserves the base point, hence so does its inverse.
  have h : Φ (Φ.symm x) = x := Φ.toPartialEquiv.right_inv hx
  calc (Φ.symm x).proj = (Φ (Φ.symm x)).proj := by rw [hΦ]
    _ = x.proj := by rw [h]

end Global

end TauCeti
