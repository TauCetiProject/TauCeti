/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.HandleRetraction.Bundle
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.Morse.Deformation
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Attaching the negative disc bundle of a Morse–Bott critical submanifold

Let `f` be a smooth function on a boundaryless manifold `M`, and let `C` be a nondegenerate
critical submanifold of `f` of index `λ` with critical value `c`. After the Morse–Bott lemma, `f`
has the form `f = c - ‖u‖² + ‖v‖²` on a tube around `C`: a neighbourhood of the zero section of the
normal bundle `ν = ν⁻ ⊕ ν⁺`, where `u` runs over the fibre of the negative normal bundle `ν⁻`, of
rank `λ`, and `v` over the fibre of the positive one `ν⁺`. Bott's attachment theorem says that
passing the level `c` attaches the disc bundle `{‖u‖² ≤ ε, v = 0}` of `ν⁻` to the lower sublevel
`M_{c-ε} = {f ≤ c - ε}` along its sphere bundle. For an isolated critical point the base is a
point and this is Milnor's attachment of one `λ`-cell
(`TauCeti.exists_sublevel_union_cells_deformation`).

This file proves the attachment for any such tube. Let `Eᵤ` and `Eₛ` be bundles over a common base
`B` with normed fibres, whose fibre norms are continuous on the total spaces, with `Eₛ` a
topological vector bundle, and let `φ` be an open partial homeomorphism from `M` to the total space
of the Whitney sum `Eᵤ ×ᵇ Eₛ` in which `f = c - ‖u‖² + ‖v‖²`. Several critical components on one
level are covered by a single tube over a disconnected base. Suppose that:

* the target of `φ` contains the closed disc bundle `D = {‖u‖² + ‖v‖² ≤ 2ε}`, whose image in `M`
  is closed, as it is when `D` is compact;
* the squared radius `‖u‖² + ‖v‖²` is smooth on the source of `φ`, and scaling `v` gives
  differentiable curves in `M`; these are the only smoothness properties of the tube that the
  argument uses;
* the band `f⁻¹[c - ε, c + ε]` is compact and its critical points lie in the tube.

Then `M_{c+ε}` strong deformation retracts onto `M_{c-ε}` together with the image of the negative
disc bundle `{‖u‖² ≤ ε, v = 0}` of radius `√ε`
(`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`).

The proof is Milnor's (*Morse Theory*, Theorem 3.2), run in the fibres of the tube. The function
`F = f - μ(‖u‖² + 2‖v‖²)`, where `μ` is a smooth nonincreasing cutoff with `μ = 2ε` on `[0, ε]` and
`μ = 0` on `[2ε, ∞)`, agrees with `f` outside the image of `D` and has the same sublevel
`{F ≤ c + ε} = M_{c+ε}`. It has no critical points in the band `F⁻¹[c - ε, c + ε]`: in the tube,
along the curve scaling `v` it has derivative `2‖v‖²(1 - 2μ')`, so a critical point has `v = 0`,
where `F = c - ‖u‖² - μ(‖u‖²) < c - ε`. So `M_{c+ε}` deformation retracts onto `{F ≤ c - ε}`
(`TauCeti.exists_sublevelDeformation`). Since lowering `v` lowers `F`, the fibrewise handle
retraction `TauCeti.bundleQuadraticHandleDeformation`, read in the tube and extended by the identity
outside the image of `D` (`Topology.IsOpenEmbedding.exists_deformation_of_preimage`), retracts
`{F ≤ c - ε}` onto `M_{c-ε}` with the negative disc bundle attached. The two retractions compose.

## Main results

* `TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`: for a tube in which
  `f = c - ‖u‖² + ‖v‖²`, around the critical points of a compact band `f⁻¹[c - ε, c + ε]`, the
  sublevel `M_{c+ε}` strong deformation retracts onto `M_{c-ε}` with the negative disc bundle of
  the tube attached.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {B Fᵤ Fₛ : Type*} {Eᵤ Eₛ : B → Type*} [∀ b, NormedAddCommGroup (Eᵤ b)]
  [∀ b, NormedAddCommGroup (Eₛ b)]
  [TopologicalSpace (TotalSpace Fᵤ Eᵤ)] [TopologicalSpace (TotalSpace Fₛ Eₛ)]
  {φ : OpenPartialHomeomorph M (TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ))} {f : M → ℝ} {c ε : ℝ}
  {μ : ℝ → ℝ} {x : M}

section MilnorFunction

/-- Milnor's function `f - μ(‖u‖² + 2‖v‖²)`, lowered in the tube `φ` and equal to `f` outside its
source. -/
private def tubeMilnorFunction (φ : OpenPartialHomeomorph M (TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)))
    (f : M → ℝ) (μ : ℝ → ℝ) (x : M) : ℝ :=
  f x - φ.source.indicator (fun y ↦ μ (‖(φ y).2.1‖ ^ 2 + 2 * ‖(φ y).2.2‖ ^ 2)) x

private theorem tubeMilnorFunction_of_mem (hx : x ∈ φ.source) :
    tubeMilnorFunction φ f μ x = f x - μ (‖(φ x).2.1‖ ^ 2 + 2 * ‖(φ x).2.2‖ ^ 2) := by
  rw [tubeMilnorFunction, indicator_of_mem hx]

private theorem tubeMilnorFunction_of_notMem (hx : x ∉ φ.source) :
    tubeMilnorFunction φ f μ x = f x := by
  rw [tubeMilnorFunction, indicator_of_notMem hx, sub_zero]

private theorem tubeMilnorFunction_le (hμ_nonneg : ∀ r, 0 ≤ μ r) (x : M) :
    tubeMilnorFunction φ f μ x ≤ f x :=
  sub_le_self _ (indicator_nonneg (fun _ _ ↦ hμ_nonneg _) _)

/-- Where Milnor's function differs from `f`, the point lies in Milnor's ellipsoid
`‖u‖² + 2‖v‖² < 2ε` of the tube, hence in the image of the closed disc bundle
`{‖u‖² + ‖v‖² ≤ 2ε}`. -/
private theorem mem_image_disc_of_tubeMilnorFunction_ne (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
    (hx : tubeMilnorFunction φ f μ x ≠ f x) :
    x ∈ φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} := by
  by_cases hxs : x ∈ φ.source
  · refine ⟨φ x, ?_, φ.left_inv hxs⟩
    rw [tubeMilnorFunction_of_mem hxs] at hx
    have h : ‖(φ x).2.1‖ ^ 2 + 2 * ‖(φ x).2.2‖ ^ 2 < 2 * ε := by
      by_contra h
      exact hx (by rw [hμ₀ _ (not_lt.1 h), sub_zero])
    rw [mem_ofPred_eq]
    nlinarith [sq_nonneg ‖(φ x).2.2‖]
  · exact absurd (tubeMilnorFunction_of_notMem hxs) hx

/-- Away from the image of the closed disc bundle `{‖u‖² + ‖v‖² ≤ 2ε}`, when it is closed,
Milnor's function agrees with `f` on a neighbourhood. -/
private theorem tubeMilnorFunction_eventuallyEq (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
    (hD : IsClosed (φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}))
    (hx : x ∉ φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}) :
    tubeMilnorFunction φ f μ =ᶠ[𝓝 x] f := by
  filter_upwards [hD.isOpen_compl.mem_nhds hx] with y hy
  by_contra h
  exact hy (mem_image_disc_of_tubeMilnorFunction_ne hμ₀ h)

variable (hf : ∀ y ∈ φ.source, f y = c - ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2)
include hf

/-- In the coordinates `(u, v)` of the tube, `f` is `c - ‖u‖² + ‖v‖²` and Milnor's function is
`c - ‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²)`. -/
private theorem tubeMilnorFunction_symm_apply {z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)}
    (hz : z ∈ φ.target) :
    f (φ.symm z) = c - ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ∧
      tubeMilnorFunction φ f μ (φ.symm z) =
        c - ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 - μ (‖z.2.1‖ ^ 2 + 2 * ‖z.2.2‖ ^ 2) := by
  have hx : φ.symm z ∈ φ.source := φ.map_target hz
  have hfz := hf _ hx
  rw [φ.right_inv hz] at hfz
  rw [tubeMilnorFunction_of_mem hx, φ.right_inv hz, hfz]
  exact ⟨rfl, rfl⟩

/-- Milnor's function lies below `c - ε` on the negative disc bundle `{‖u‖² ≤ ε, v = 0}` of the
tube. -/
private theorem tubeMilnorFunction_le_of_mem_disc (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hx : x ∈ φ.source) (hxε : ‖(φ x).2.1‖ ^ 2 ≤ ε) (hxv : (φ x).2.2 = 0) :
    tubeMilnorFunction φ f μ x ≤ c - ε := by
  rw [tubeMilnorFunction_of_mem hx, hf x hx, hxv, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  rw [hμ_eq _ hxε]
  linarith [sq_nonneg ‖(φ x).2.1‖]

/-- A point of the tube lies in the lower sublevel `{f ≤ c - ε}` or in the negative disc bundle
`{‖u‖² ≤ ε, v = 0}` exactly when its coordinates lie in the model set
`TauCeti.bundleQuadraticSublevelUnionCell`. -/
private theorem symm_mem_sublevel_union_disc_iff
    {z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)} (hz : z ∈ φ.target) :
    φ.symm z ∈ {x | f x ≤ c - ε} ∪ φ.source ∩ φ ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0} ↔
      z ∈ bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε := by
  rw [mem_bundleQuadraticSublevelUnionCell, mem_union, mem_ofPred_eq,
    (tubeMilnorFunction_symm_apply hf (μ := 0) hz).1, mem_inter_iff, mem_preimage,
    φ.right_inv hz, mem_ofPred_eq]
  exact or_congr ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩ (and_iff_right (φ.map_target hz))

/-- Milnor's function has the same sublevel `{F ≤ c + ε}` as `f`: inside Milnor's ellipsoid
`‖u‖² + 2‖v‖² < 2ε` of the tube, `f = c - ‖u‖² + ‖v‖² < c + ε`. -/
private theorem setOf_tubeMilnorFunction_le (hμ_nonneg : ∀ r, 0 ≤ μ r)
    (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) :
    {x | tubeMilnorFunction φ f μ x ≤ c + ε} = {x | f x ≤ c + ε} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (tubeMilnorFunction_le hμ_nonneg x).trans hx⟩
  by_cases hxs : x ∈ φ.source
  · rw [mem_ofPred_eq, tubeMilnorFunction_of_mem hxs, hf x hxs] at hx
    rw [mem_ofPred_eq, hf x hxs]
    rcases le_or_gt (2 * ε) (‖(φ x).2.1‖ ^ 2 + 2 * ‖(φ x).2.2‖ ^ 2) with h | h
    · rwa [hμ₀ _ h, sub_zero] at hx
    · nlinarith [sq_nonneg ‖(φ x).2.1‖]
  · rwa [mem_ofPred_eq, tubeMilnorFunction_of_notMem hxs] at hx

/-- **Milnor's function is smooth.** Its lowering term is supported in the closed image of the
disc bundle `{‖u‖² + ‖v‖² ≤ 2ε}`, inside the source of the tube, where it is a smooth function of
the squared radius `‖u‖² + ‖v‖²` and of `f`. -/
private theorem contMDiff_tubeMilnorFunction (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
    (hDt : {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ φ.target)
    (hD : IsClosed (φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}))
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hρ : ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2) φ.source)
    (hμ : ContDiff ℝ ∞ μ) :
    ContMDiff I 𝓘(ℝ) ∞ (tubeMilnorFunction φ f μ) := by
  have hterm : ContMDiff I 𝓘(ℝ) ∞
      (φ.source.indicator fun y ↦ μ (‖(φ y).2.1‖ ^ 2 + 2 * ‖(φ y).2.2‖ ^ 2)) := by
    refine contMDiff_of_tsupport fun y hy ↦ ?_
    -- The term is supported in the closed image of the disc bundle, inside the source.
    have hsupp : tsupport (φ.source.indicator
        fun y ↦ μ (‖(φ y).2.1‖ ^ 2 + 2 * ‖(φ y).2.2‖ ^ 2)) ⊆
        φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} := by
      refine closure_minimal (fun y hy ↦ mem_image_disc_of_tubeMilnorFunction_ne (f := f) hμ₀ ?_)
        hD
      rw [tubeMilnorFunction, ne_eq, sub_eq_self]
      exact hy
    obtain ⟨z, hz, rfl⟩ := hsupp hy
    have hs : φ.symm z ∈ φ.source := φ.map_target (hDt hz)
    -- In the source, `‖u‖² + 2‖v‖² = (3 (‖u‖² + ‖v‖²) + (f - c)) / 2`.
    have hg : ContMDiffAt I 𝓘(ℝ) ∞
        (fun y ↦ μ ((3 * (‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2) + (f y - c)) / 2)) (φ.symm z) :=
      have hμ' : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ μ ((3 * p.1 + (p.2 - c)) / 2) :=
        hμ.comp (by fun_prop)
      hμ'.contMDiff.contMDiffAt.comp _
        ((hρ.contMDiffAt (φ.open_source.mem_nhds hs)).prodMk_space (hfs _))
    refine hg.congr_of_eventuallyEq (eventuallyEq_of_mem (φ.open_source.mem_nhds hs)
      fun y hy ↦ ?_)
    rw [indicator_of_mem hy, hf y hy]
    congr 1
    ring
  exact ContMDiff.sub hfs hterm

variable [∀ b, NormedSpace ℝ (Eₛ b)]

/-- Scaling `v` by a factor in `[0, 1]` does not increase Milnor's function. -/
private theorem tubeMilnorFunction_symm_smul_le (hμa : Antitone μ)
    {z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)} (hz : z ∈ φ.target) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hsz : (⟨z.proj, (z.2.1, s • z.2.2)⟩ : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) ∈ φ.target) :
    tubeMilnorFunction φ f μ (φ.symm ⟨z.proj, (z.2.1, s • z.2.2)⟩) ≤
      tubeMilnorFunction φ f μ (φ.symm z) := by
  rw [(tubeMilnorFunction_symm_apply hf hsz).2, (tubeMilnorFunction_symm_apply hf hz).2]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
  have hb : 0 ≤ ‖z.2.2‖ ^ 2 := sq_nonneg _
  have hμle := hμa (show ‖z.2.1‖ ^ 2 + 2 * (s ^ 2 * ‖z.2.2‖ ^ 2) ≤
    ‖z.2.1‖ ^ 2 + 2 * ‖z.2.2‖ ^ 2 by nlinarith)
  nlinarith

end MilnorFunction

section Bundle

variable [TopologicalSpace B] [NormedAddCommGroup Fₛ] [∀ b, NormedSpace ℝ (Eₛ b)]
  [FiberBundle Fₛ Eₛ]

/-- At a critical point of Milnor's function in the tube, the positive component `v` vanishes.
Along the curve scaling `v` by `t`, Milnor's function is `c - ‖u‖² + t²‖v‖² - μ(‖u‖² + 2t²‖v‖²)`,
whose derivative `2‖v‖²(1 - 2μ')` at `t = 1` is `0`, while `μ' ≤ 0`. -/
private theorem snd_eq_zero_of_mfderiv_tubeMilnorFunction_eq_zero
    (hf : ∀ y ∈ φ.source, f y = c - ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2)
    (hscale : ∀ z ∈ φ.target,
      MDifferentiableAt 𝓘(ℝ) I (fun t : ℝ ↦ φ.symm ⟨z.proj, (z.2.1, t • z.2.2)⟩) 1)
    (hμ : ContDiff ℝ ∞ μ) (hμa : Antitone μ)
    (hF : MDifferentiableAt I 𝓘(ℝ) (tubeMilnorFunction φ f μ) x) (hx : x ∈ φ.source)
    (h0 : mfderiv I 𝓘(ℝ) (tubeMilnorFunction φ f μ) x = 0) :
    (φ x).2.2 = 0 := by
  set z := φ x
  have hz : z ∈ φ.target := φ.map_source hx
  set a := ‖z.2.1‖ ^ 2
  set b := ‖z.2.2‖ ^ 2
  -- The curve `L` scales the positive component of `z` by `t`.
  set L : ℝ → TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ) := fun t ↦ ⟨z.proj, (z.2.1, t • z.2.2)⟩
  have hL : Continuous L := by
    rw [(FiberBundle.Prod.isInducing_diag Fᵤ Eᵤ Fₛ Eₛ).continuous_iff]
    exact (continuous_const (y := (⟨z.proj, z.2.1⟩ : TotalSpace Fᵤ Eᵤ))).prodMk
      ((FiberBundle.continuous_totalSpaceMk Fₛ Eₛ z.proj).comp
        (continuous_id.smul continuous_const))
  have hL1 : L 1 = z := by simp [L]
  -- `F ∘ φ⁻¹ ∘ L` has derivative `0` at `1`, since `x = φ⁻¹ (L 1)` is a critical point of `F`.
  rw [← show φ.symm (L 1) = x from (congrArg φ.symm hL1).trans (φ.left_inv hx)] at hF h0
  have hd : HasFDerivAt (tubeMilnorFunction φ f μ ∘ fun t ↦ φ.symm (L t)) (0 : ℝ →L[ℝ] ℝ) 1 := by
    have h := hF.hasMFDerivAt.comp 1 (hscale z hz).hasMFDerivAt
    rwa [h0, ContinuousLinearMap.zero_comp, hasMFDerivAt_iff_hasFDerivAt] at h
  -- Explicitly, `F (φ⁻¹ (L t)) = c - a + t² b - μ (a + 2 t² b)` near `t = 1`.
  have heq : tubeMilnorFunction φ f μ ∘ (fun t ↦ φ.symm (L t)) =ᶠ[𝓝 1]
      fun t ↦ c + (-a + t ^ 2 * b) - μ (a + 2 * (t ^ 2 * b)) := by
    filter_upwards [hL.continuousAt.preimage_mem_nhds (φ.open_target.mem_nhds (hL1 ▸ hz))]
      with t ht
    rw [Function.comp_apply, (tubeMilnorFunction_symm_apply hf ht).2]
    simp only [L, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, a, b]
    ring_nf
  have hq := (hasDerivAt_pow 2 (1 : ℝ)).mul_const b
  have hg := ((hq.const_add (-a)).const_add c).sub
    (((hμ.differentiable (by simp)) _).hasDerivAt.comp 1 ((hq.const_mul 2).const_add a))
  have hval := (hg.congr_of_eventuallyEq heq).unique (by simpa using hd.hasDerivAt)
  have h : b * (2 - 4 * deriv μ (a + 2 * (1 ^ 2 * b))) = 0 := by linear_combination hval
  have := hμa.deriv_nonpos (x := a + 2 * (1 ^ 2 * b))
  simpa [b] using (mul_eq_zero.1 h).resolve_right (by linarith)

/-- **Milnor's function has no critical points in the band `F⁻¹[c - ε, c + ε]`**, provided the
critical points of `f` in the band `f⁻¹[c - ε, c + ε]` lie in the tube. At a critical point in the
tube `v = 0`, where `F = c - ‖u‖² - μ(‖u‖²) < c - ε`; outside the image of the closed disc bundle,
`F` agrees with `f` near the point. -/
private theorem mfderiv_tubeMilnorFunction_ne_zero_of_mem_Icc
    (hf : ∀ y ∈ φ.source, f y = c - ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2)
    (hscale : ∀ z ∈ φ.target,
      MDifferentiableAt 𝓘(ℝ) I (fun t : ℝ ↦ φ.symm ⟨z.proj, (z.2.1, t • z.2.2)⟩) 1)
    (hDt : {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ φ.target)
    (hD : IsClosed (φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}))
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hρ : ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2) φ.source)
    (hε : 0 < ε) (hμ : ContDiff ℝ ∞ μ) (hμa : Antitone μ) (hμ_nonneg : ∀ r, 0 ≤ μ r)
    (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ φ.source)
    (h₁ : c - ε ≤ tubeMilnorFunction φ f μ x) (h₂ : tubeMilnorFunction φ f μ x ≤ c + ε) :
    mfderiv I 𝓘(ℝ) (tubeMilnorFunction φ f μ) x ≠ 0 := by
  intro h0
  by_cases hxs : x ∈ φ.source
  · have hv := snd_eq_zero_of_mfderiv_tubeMilnorFunction_eq_zero hf hscale hμ hμa
      ((contMDiff_tubeMilnorFunction hf hμ₀ hDt hD hfs hρ hμ).mdifferentiableAt (by simp)) hxs h0
    rw [tubeMilnorFunction_of_mem hxs, hf x hxs, hv, norm_zero] at h₁
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h₁
    have ha := sq_nonneg ‖(φ x).2.1‖
    rcases le_or_gt (‖(φ x).2.1‖ ^ 2) ε with h | h
    · rw [hμ_eq _ h] at h₁
      linarith
    · linarith [hμ_nonneg (‖(φ x).2.1‖ ^ 2)]
  · have hK : x ∉ φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} := by
      rintro ⟨z, hz, rfl⟩
      exact hxs (φ.map_target (hDt hz))
    rw [(tubeMilnorFunction_eventuallyEq hμ₀ hD hK).mfderiv_eq] at h0
    rw [tubeMilnorFunction_of_notMem hxs] at h₁ h₂
    exact hxs (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 h0, h₁, h₂⟩)

variable [NormedSpace ℝ Fₛ] [VectorBundle ℝ Fₛ Eₛ]
  (hᵤ : Continuous fun u : TotalSpace Fᵤ Eᵤ ↦ ‖u.2‖)
  (hₛ : Continuous fun v : TotalSpace Fₛ Eₛ ↦ ‖v.2‖)

include hᵤ hₛ in
/-- The fibrewise handle deformation keeps a point of the tube in the sublevel `{F ≤ c - ε}` of
Milnor's function in the tube and in that sublevel: it fixes the points of the model set, and
moves the others, which lie in Milnor's ellipsoid `‖u‖² + 2‖v‖² < 2ε`, by scaling `v` by a factor
in `[0, 1]`, which keeps them in the closed disc bundle and does not increase `F`. -/
private theorem bundleQuadraticHandleDeformation_mem_target_and_mem
    (hf : ∀ y ∈ φ.source, f y = c - ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2)
    (hDt : {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ φ.target)
    (hμa : Antitone μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) {z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)}
    (hz : z ∈ φ.target) (hzX : tubeMilnorFunction φ f μ (φ.symm z) ≤ c - ε) (t : unitInterval) :
    bundleQuadraticHandleDeformation hᵤ hₛ ε (t, z) ∈ φ.target ∧
      tubeMilnorFunction φ f μ (φ.symm (bundleQuadraticHandleDeformation hᵤ hₛ ε (t, z))) ≤
        c - ε := by
  set G := bundleQuadraticHandleDeformation hᵤ hₛ ε
  by_cases hQ : z ∈ bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε
  · rw [G.eq_snd t hQ]
    exact ⟨hz, hzX⟩
  obtain ⟨s, hs, hst⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t z.2
  have hGz : G (t, z) = ⟨z.proj, (z.2.1, s • z.2.2)⟩ := by
    rw [bundleQuadraticHandleDeformation_apply, hst]
  obtain ⟨-, hFz⟩ := tubeMilnorFunction_symm_apply hf (μ := μ) hz
  rw [mem_bundleQuadraticSublevelUnionCell, not_or] at hQ
  -- There `F ≤ c - ε < f`, so the point lies in Milnor's ellipsoid `‖u‖² + 2‖v‖² < 2ε`.
  have hlt : ‖z.2.1‖ ^ 2 + 2 * ‖z.2.2‖ ^ 2 < 2 * ε := by
    by_contra h
    rw [hFz, hμ₀ _ (not_lt.1 h)] at hzX
    exact hQ.1 (by linarith)
  have hw : (⟨z.proj, (z.2.1, s • z.2.2)⟩ : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) ∈ φ.target := by
    refine hDt ?_
    rw [mem_ofPred_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [pow_le_one₀ (n := 2) hs.1 hs.2, sq_nonneg ‖z.2.2‖, sq_nonneg s]
  rw [hGz]
  exact ⟨hw, (tubeMilnorFunction_symm_smul_le hf hμa hz hs hw).trans hzX⟩

include hᵤ hₛ in
/-- **Milnor's handle retraction in the tube.** The sublevel `{F ≤ c - ε}` of Milnor's function
strong deformation retracts onto its intersection with the lower sublevel `{f ≤ c - ε}` and the
negative disc bundle `{‖u‖² ≤ ε, v = 0}` of the tube. In the tube the deformation is the fibrewise
handle retraction `TauCeti.bundleQuadraticHandleDeformation`, which only shrinks `v`, and so keeps
points of Milnor's ellipsoid in the sublevel; outside the image of the closed disc bundle it is the
identity. -/
private theorem exists_tubeMilnorFunction_sublevel_deformation
    (hf : ∀ y ∈ φ.source, f y = c - ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2)
    (hDt : {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ φ.target)
    (hD : IsClosed (φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}))
    (hμa : Antitone μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) :
    ∃ r : C({x | tubeMilnorFunction φ f μ x ≤ c - ε}, ↥({x | tubeMilnorFunction φ f μ x ≤ c - ε} ∩
        ({x | f x ≤ c - ε} ∪ φ.source ∩ φ ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
          φ.source ∩ φ ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}}) := by
  set X := {x | tubeMilnorFunction φ f μ x ≤ c - ε}
  set S := {x | f x ≤ c - ε} ∪ φ.source ∩ φ ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}
  set G := bundleQuadraticHandleDeformation hᵤ hₛ ε
  have hmove {z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)} (hz : z ∈ φ.target) (hzX : φ.symm z ∈ X)
      (t : unitInterval) : G (t, z) ∈ φ.target ∧ φ.symm (G (t, z)) ∈ X :=
    bundleQuadraticHandleDeformation_mem_target_and_mem hᵤ hₛ hf hDt hμa hμ₀ hz hzX t
  -- Read the model deformation through the open embedding `φ⁻¹` of the tube.
  set j : φ.symm.source → M := φ.symm.source.domRestrict φ.symm
  have hj : IsOpenEmbedding j := φ.symm.isOpenEmbedding_restrict
  set s : Set φ.symm.source := j ⁻¹' X
  set t : Set φ.symm.source := j ⁻¹' (X ∩ S)
  have hts : t ⊆ s := preimage_mono inter_subset_left
  let K : unitInterval × s → s := fun p ↦
    ⟨⟨G (p.1, p.2.1.1), (hmove p.2.1.2 p.2.2 p.1).1⟩, (hmove p.2.1.2 p.2.2 p.1).2⟩
  have hK : Continuous K :=
    ((G.continuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk
        _).subtype_mk _
  have hK0 (y : s) : (K (0, y)).1 ∈ t := by
    refine ⟨(K (0, y)).2, (symm_mem_sublevel_union_disc_iff hf (hmove y.1.2 y.2 0).1).2 ?_⟩
    rw [G.apply_zero]
    exact bundleQuadraticHandleRetraction_mem hᵤ hₛ _
  have hKt (τ : unitInterval) (y : s) (hy : y.1 ∈ t) : K (τ, y) = y :=
    Subtype.ext (Subtype.ext (G.eq_snd τ ((symm_mem_sublevel_union_disc_iff hf y.1.2).1 hy.2)))
  let r : C(s, t) := ⟨fun y ↦ ⟨(K (0, y)).1, hK0 y⟩,
    (continuous_subtype_val.comp (hK.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  let H : ((ContinuousMap.inclusion hts).comp r).HomotopyRel (.id s)
      {y | (y : φ.symm.source) ∈ t} :=
    { toFun := K
      continuous_toFun := hK
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun y ↦ Subtype.ext (Subtype.ext (G.apply_one _))
      prop' := fun τ y hy ↦ (hKt τ y hy).trans (hKt 0 y hy).symm }
  -- Outside the image of the closed disc bundle, the points of `X` lie in `{f ≤ c - ε}`.
  have hSV : X \ range j ⊆ (φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε})ᶜ := by
    rintro x ⟨-, hx⟩ ⟨z, hz, rfl⟩
    exact hx ⟨⟨z, hDt hz⟩, rfl⟩
  have hVT : X ∩ (φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε})ᶜ ⊆ X ∩ S := by
    rintro x ⟨hxX, hx⟩
    refine ⟨hxX, .inl ?_⟩
    have hFx : tubeMilnorFunction φ f μ x = f x := by
      by_contra h
      exact hx (mem_image_disc_of_tubeMilnorFunction_ne hμ₀ h)
    have hxX' : tubeMilnorFunction φ f μ x ≤ c - ε := hxX
    rwa [hFx] at hxX'
  obtain ⟨r', hr', ⟨H'⟩⟩ := hj.exists_deformation_of_preimage inter_subset_left hts rfl rfl
    hD.isOpen_compl hSV hVT r H
  have e : {x : ↥X | (x : M) ∈ X ∩ S} = {x : ↥X | (x : M) ∈ S} :=
    Set.ext fun x ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨x.2, h⟩⟩
  exact ⟨r', hr', ⟨e ▸ H'⟩⟩

end Bundle

section Attachment

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace B] [NormedAddCommGroup Fₛ] [NormedSpace ℝ Fₛ] [∀ b, NormedSpace ℝ (Eₛ b)]
  [FiberBundle Fₛ Eₛ] [VectorBundle ℝ Fₛ Eₛ]

/-- **Attachment of the negative disc bundle across a Morse–Bott critical level** (Bott; Milnor,
Theorem 3.2, for an isolated critical point). Let `f` be smooth, and let `φ` be a tube: an open
partial homeomorphism from `M` to the total space of the Whitney sum `Eᵤ ×ᵇ Eₛ` of two bundles
with continuous fibre norms, `Eₛ` a topological vector bundle, in which
`f = c - ‖u‖² + ‖v‖²`. Suppose that the target of `φ` contains the closed disc bundle
`{‖u‖² + ‖v‖² ≤ 2ε}`, whose image in `M` is closed, that the squared radius `‖u‖² + ‖v‖²` is smooth
on the source of `φ`, that scaling `v` gives curves in `M` differentiable at `t = 1`, and that the
band `f⁻¹[c - ε, c + ε]` is compact with its critical points in the source of `φ`.

Then the lower sublevel `{f ≤ c - ε}` with the negative disc bundle `{‖u‖² ≤ ε, v = 0}` of the tube
attached is a strong deformation retract of `{f ≤ c + ε}`: there is a retraction of
`{f ≤ c + ε}` onto it, and a homotopy in `{f ≤ c + ε}` from this retraction to the identity which
fixes it pointwise. The disc bundle lies in `{f ≤ c}`, so intersecting with `{f ≤ c + ε}` does not
change the retract. -/
theorem exists_sublevel_union_negativeDiscBundle_deformation (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hᵤ : Continuous fun u : TotalSpace Fᵤ Eᵤ ↦ ‖u.2‖)
    (hₛ : Continuous fun v : TotalSpace Fₛ Eₛ ↦ ‖v.2‖)
    (φ : OpenPartialHomeomorph M (TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ))) (hε : 0 < ε)
    (hDt : {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ φ.target)
    (hD : IsClosed (φ.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}))
    (hf : ∀ y ∈ φ.source, f y = c - ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2)
    (hρ : ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ ‖(φ y).2.1‖ ^ 2 + ‖(φ y).2.2‖ ^ 2) φ.source)
    (hscale : ∀ z ∈ φ.target,
      MDifferentiableAt 𝓘(ℝ) I (fun t : ℝ ↦ φ.symm ⟨z.proj, (z.2.1, t • z.2.2)⟩) 1)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ φ.source) :
    ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
        φ.source ∩ φ ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
          φ.source ∩ φ ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}}) := by
  -- Milnor's cutoff, equal to `2ε` on `(-∞, ε]` and to `0` on `[2ε, ∞)`.
  obtain ⟨μ, hμ, hμa, hμ_nonneg, hμ₀, hμ_eq, -⟩ :=
    exists_contDiff_antitone_cutoff (by linarith : ε < 2 * ε) (by positivity : 0 ≤ 2 * ε)
  set F := tubeMilnorFunction φ f μ
  set S := {x | f x ≤ c - ε} ∪ φ.source ∩ φ ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}
  have hFs : ContMDiff I 𝓘(ℝ) ∞ F := contMDiff_tubeMilnorFunction hf hμ₀ hDt hD hfs hρ hμ
  have hX : {x | F x ≤ c + ε} = {x | f x ≤ c + ε} := setOf_tubeMilnorFunction_le hf hμ_nonneg hμ₀
  have hSY : S ⊆ {x | F x ≤ c - ε} :=
    union_subset (fun x hx ↦ (tubeMilnorFunction_le hμ_nonneg x).trans hx)
      fun x ⟨hxs, hxε, hxv⟩ ↦ tubeMilnorFunction_le_of_mem_disc hf hμ_eq hxs hxε hxv
  have hab : c - ε ≤ c + ε := by linarith
  have hYX : {x | F x ≤ c - ε} ⊆ {x | F x ≤ c + ε} := fun _ hx ↦ le_trans hx hab
  have hFcompact : IsCompact (F ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hFs.continuous) fun x hx ↦
      ⟨hx.1.trans (tubeMilnorFunction_le hμ_nonneg x), (Set.ext_iff.1 hX x).1 hx.2⟩
  -- `{F ≤ c + ε}` retracts onto `{F ≤ c - ε}`, as `F` has no critical points in the compact band,
  -- which retracts onto `S`, as lowering `v` in the tube lowers `F`.
  exact hX ▸ ContinuousMap.HomotopicRel.exists_inter_deformation_trans hYX
    (inter_subset_right.trans hSY)
    (sublevelInclusion_eq_inclusion F hab ▸ exists_sublevelDeformation hFs hab hFcompact
      fun _ ↦ mfderiv_tubeMilnorFunction_ne_zero_of_mem_Icc hf hscale hDt hD hfs hρ hε hμ hμa
        hμ_nonneg hμ₀ hμ_eq hcrit)
    (exists_tubeMilnorFunction_sublevel_deformation hᵤ hₛ hf hDt hD hμa hμ₀)

end Attachment

end TauCeti
