/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CoordinateChange.Basic
public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
public import TauCeti.Analysis.Pseudodifferential.SmoothKernel
import TauCeti.Analysis.Calculus.ApproximatesLinearOn.Extension
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.SmulLeft
import TauCeti.Topology.Algebra.Support

/-!
# Changes of coordinates between open sets

Let `κ` be a diffeomorphism from an open set of `ℝⁿ` onto another, for instance the transition map
between two charts of a manifold, and `a` a classical symbol of order `m`. For cutoffs `φ`, `ψ`
with compact supports in the source of `κ`, the operator

`u ↦ φ · Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ`,

with `(ψ u) ∘ κ⁻¹` extended by `0` off the target of `κ`, is `Op(b)` for a classical symbol `b` of
order `m` whose principal symbol is `φ(x) ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`
(`TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq`). This is the comparison
needed between the compressions of an operator on a manifold to two overlapping charts, and it
shows that the principal symbol transforms as a function on the cotangent bundle.

`TauCeti.ClassicalSymbol.exists_quantizeSchwartzValue_comp_eq` in
`TauCeti.Analysis.Pseudodifferential.CoordinateChange.Basic` proves this for a diffeomorphism of the
whole space whose averaged derivatives `∫₀¹ Dκ(y + t (x - y)) dt` (`hadamardFactor`) are
invertible on the relevant sets. The theorem here applies to every diffeomorphism between open
sets, with no condition on its averaged derivatives.

## The argument

* Near every point of its source, `κ` agrees with a diffeomorphism of the whole space whose
  derivative stays within `‖Dκ(x₀)⁻¹‖⁻¹ / 2` of `Dκ(x₀)`
  (`ContDiffOn.exists_homeomorph_eventuallyEq_nnNorm_fderiv_sub_le`), so all its derivatives and
  averaged derivatives are invertible
  (`OpenPartialHomeomorph.exists_eqOn_homeomorph_isUnit_hadamardFactor`).
* A partition of unity splits `ψ` into pieces `ψ ρᵢ` supported in such neighbourhoods `Nᵢ`, and
  `v = (ψ u) ∘ κ⁻¹` accordingly.
* For one piece, a cutoff `χ` equal to `1` near the support of `ψ ρᵢ` and supported in `Nᵢ` splits
  the output cutoff as `φ = φ χ + φ (1 - χ)`. On the support of `φ χ` the map `κ` is the global
  diffeomorphism, so the theorem for diffeomorphisms of the whole space applies, after cutting the
  symbol off in space (`TauCeti.ClassicalSymbol.smulLeft`). On the support of `φ (1 - χ)`, `κ x`
  stays away from the support of the input, where `Op(a)` is the integral operator with its
  off-diagonal kernel (`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`),
  which is smooth there.
* Such an integral operator, read through `κ`, has the smooth compactly supported kernel
  `φ(x) ψ(y) |det Dκ(y)| K(κ x, κ y)`, so it is the quantization of a smoothing symbol
  (`TauCeti.exists_isSmoothing_smul_integral_comp_eq`).

## Main results

* `TauCeti.exists_isSmoothing_smul_integral_comp_eq`: an integral operator whose kernel is smooth
  where it is used is, after a change of variables and cutoffs, the quantization of a smoothing
  symbol.
* `TauCeti.Symbol.exists_isSmoothing_smul_quantizeSchwartzValue_comp_eq`: with cutoffs of
  disjoint supports, the transported operator `u ↦ φ · Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ` is the
  quantization of a smoothing symbol.
* `TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq`: changes of coordinates by
  diffeomorphisms between open sets preserve classical symbols, and the principal symbol
  transforms by the cotangent map.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.17 and Definition 18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff SchwartzMap

namespace TauCeti

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A function `v` equal to `(ψ u) ∘ κ⁻¹` on the target of `κ` and to `0` off it is supported in
the image of the support of `ψ`. -/
private theorem support_subset_image_support
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    {ψ : CoordinateSpace n → ℝ} {u v : CoordinateSpace n → V}
    (hv : ∀ y ∈ κ.source, v (κ y) = ψ y • u y) (hv0 : ∀ z ∉ κ.target, v z = 0) :
    Function.support v ⊆ κ '' Function.support ψ := fun z hz ↦ by
  have hzt : z ∈ κ.target := by_contra fun h ↦ hz (hv0 z h)
  refine ⟨κ.symm z, fun h ↦ hz ?_, κ.right_inv hzt⟩
  rw [← κ.right_inv hzt, hv _ (κ.map_target hzt), h, zero_smul]

/-- If moreover `ψ` has compact support in the source of `κ`, then `v` has compact support, in the
image of the support of `ψ`. -/
private theorem hasCompactSupport_and_tsupport_subset_image
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    {ψ : CoordinateSpace n → ℝ} (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ κ.source)
    {u v : CoordinateSpace n → V} (hv : ∀ y ∈ κ.source, v (κ y) = ψ y • u y)
    (hv0 : ∀ z ∉ κ.target, v z = 0) :
    HasCompactSupport v ∧ tsupport v ⊆ κ '' tsupport ψ := by
  have hK : IsCompact (κ '' tsupport ψ) :=
    hψc.isCompact.image_of_continuousOn (κ.continuousOn.mono hψs)
  have hvK : Function.support v ⊆ κ '' tsupport ψ :=
    (support_subset_image_support hv hv0).trans (image_mono (subset_tsupport ψ))
  exact ⟨.intro' hK hK.isClosed fun z hz ↦ Function.notMem_support.1 fun h ↦ hz (hvK h),
    hK.isClosed.closure_subset_iff.2 hvK⟩

/-- If `κ` agrees with an injective map `κ'` on a set `N` containing the support of `ψ`, then
`v ∘ κ' = ψ u` everywhere. -/
private theorem apply_eq_smul_of_eqOn
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    {κ' : CoordinateSpace n → CoordinateSpace n} (hκ' : Function.Injective κ')
    {N : Set (CoordinateSpace n)} (hNs : N ⊆ κ.source) (hNκ : EqOn κ' κ N)
    {ψ : CoordinateSpace n → ℝ} (hψN : tsupport ψ ⊆ N) {u v : CoordinateSpace n → V}
    (hv : ∀ y ∈ κ.source, v (κ y) = ψ y • u y) (hv0 : ∀ z ∉ κ.target, v z = 0)
    (y : CoordinateSpace n) : v (κ' y) = ψ y • u y := by
  by_cases hy : y ∈ N
  · rw [hNκ hy]
    exact hv y (hNs hy)
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy (hψN h), zero_smul]
  by_contra h
  obtain ⟨y', hy', hyy'⟩ := support_subset_image_support hv hv0 h
  have hy'N : y' ∈ N := hψN (subset_tsupport _ hy')
  rw [← hNκ hy'N] at hyy'
  exact hy (hκ' hyy' ▸ hy'N)

/-- **Splitting the input.** If `∑ i ∈ t, ρ i = 1` on the support of `ψ`, a function `v` equal to
`(ψ u) ∘ κ⁻¹` on the target of `κ` and to `0` off it is the sum of Schwartz functions `w i` equal to
`(ψ ρ i u) ∘ κ⁻¹` on the target and to `0` off it. -/
private theorem exists_sum_eq
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    (hκ' : ContDiffOn ℝ ∞ κ.symm κ.target) {ψ : CoordinateSpace n → ℝ}
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ κ.source) {ι : Type*} (t : Finset ι)
    {ρ : ι → CoordinateSpace n → ℝ} (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ1 : ∀ x ∈ tsupport ψ, ∑ i ∈ t, ρ i x = 1) {u v : 𝓢(CoordinateSpace n, V)}
    (hv : ∀ y ∈ κ.source, v (κ y) = ψ y • u y) (hv0 : ∀ z ∉ κ.target, v z = 0) :
    ∃ w : ι → 𝓢(CoordinateSpace n, V), ∑ i ∈ t, w i = v ∧
      (∀ i, ∀ y ∈ κ.source, w i (κ y) = (ψ y * ρ i y) • u y) ∧
      ∀ i, ∀ z ∉ κ.target, w i z = 0 := by
  -- Take `w i = (θ · (ρ i ∘ κ⁻¹)) v`, for a cutoff `θ` equal to `1` on the image of the support of
  -- `ψ` and supported in the target of `κ`.
  obtain ⟨θ, hθ, -, hθ1, hθc, hθt⟩ := (hψc.isCompact.image_of_continuousOn
    (κ.continuousOn.mono hψs)).exists_contDiff_cutoff κ.open_target (by
      rintro _ ⟨y, hy, rfl⟩
      exact κ.map_source (hψs hy))
  have hθψ : ∀ y, ψ y ≠ 0 → θ (κ y) = 1 := fun y hψy ↦
    interior_subset (hθ1 ⟨y, subset_tsupport _ hψy, rfl⟩)
  set σ : ι → CoordinateSpace n → ℝ := fun i z ↦ θ z • ρ i (κ.symm z)
  have hσ : ∀ i, (σ i).HasTemperateGrowth := fun i ↦ hθc.mul_right.hasTemperateGrowth
    (((hρ i).comp_contDiffOn hκ').contDiff_smul_of_tsupport_subset κ.open_target
      hθ.contDiffOn hθt)
  have hw : ∀ i z, SchwartzMap.smulLeftCLM V (σ i) v z = σ i z • v z := fun i z ↦
    SchwartzMap.smulLeftCLM_apply_apply (hσ i) v z
  refine ⟨fun i ↦ SchwartzMap.smulLeftCLM V (σ i) v, ?_, fun i y hy ↦ ?_, fun i z hz ↦ ?_⟩
  · ext z
    rw [sum_apply]
    simp only [hw, ← Finset.sum_smul]
    by_cases hz : v z = 0
    · simp [hz]
    obtain ⟨y, hy, rfl⟩ := support_subset_image_support hv hv0 hz
    have hys : y ∈ κ.source := hψs (subset_tsupport _ hy)
    simp only [σ, smul_eq_mul, ← Finset.mul_sum, κ.left_inv hys, hθψ y hy,
      hρ1 y (subset_tsupport _ hy), mul_one, one_smul]
  · rw [hw, hv y hy, smul_smul]
    by_cases hψy : ψ y = 0
    · simp [hψy]
    simp only [σ, smul_eq_mul, κ.left_inv hy, hθψ y hψy]
    ring_nf
  · simp [hw, hv0 z hz]

/-- **Transporting a cut-off Schwartz function.** For a cutoff `ψ` with compact support in the
source of a partial diffeomorphism `κ` and a Schwartz function `u`, the function equal to
`(ψ u) ∘ κ⁻¹` on the target of `κ` and to `0` off it is a Schwartz function. These are the inputs
`v` of the changes of coordinates below. -/
theorem exists_schwartzMap_apply_eq_smul
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    (hκ' : ContDiffOn ℝ ∞ κ.symm κ.target) {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ κ.source) (u : 𝓢(CoordinateSpace n, V)) :
    ∃ v : 𝓢(CoordinateSpace n, V), (∀ y ∈ κ.source, v (κ y) = ψ y • u y) ∧
      ∀ z ∉ κ.target, v z = 0 := by
  -- The cutoff `ψ` transported to the target of `κ`, extended by `0`, has compact support there.
  set ψ' : CoordinateSpace n → ℝ := κ.target.indicator (ψ ∘ κ.symm)
  have hψ'κ : ∀ y ∈ κ.source, ψ' (κ y) = ψ y := fun y hy ↦ by
    simp [ψ', indicator_of_mem (κ.map_source hy), κ.left_inv hy]
  have hψ'0 : ∀ z ∉ κ.target, ψ' z = 0 := fun z hz ↦ indicator_of_notMem hz _
  -- Its support is controlled through its complex-valued copy, which has the same support.
  obtain ⟨hc, hsK⟩ := hasCompactSupport_and_tsupport_subset_image hψc hψs
    (u := fun _ ↦ (1 : ℂ)) (v := ((↑) : ℝ → ℂ) ∘ ψ') (fun y hy ↦ by simp [hψ'κ y hy])
    fun z hz ↦ by simp [hψ'0 z hz]
  rw [tsupport_comp_eq (g := ((↑) : ℝ → ℂ)) Complex.ofReal_eq_zero] at hsK
  replace hc : HasCompactSupport ψ' :=
    (hasCompactSupport_comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_eq_zero).1 hc
  have hst : tsupport ψ' ⊆ κ.target :=
    hsK.trans (image_subset_iff.2 fun y hy ↦ κ.map_source (hψs hy))
  have hψ'd : ContDiffOn ℝ ∞ ψ' κ.target :=
    (hψ.comp_contDiffOn hκ').congr fun z hz ↦ indicator_of_mem hz _
  have hv : ContDiff ℝ ∞ fun z ↦ ψ' z • u (κ.symm z) :=
    ((u.smooth ⊤).comp_contDiffOn hκ').contDiff_smul_of_tsupport_subset κ.open_target hψ'd hst
  refine ⟨(hc.smul_right (f' := fun z ↦ u (κ.symm z))).toSchwartzMap hv, fun y hy ↦ ?_,
    fun z hz ↦ ?_⟩
  · simp [hψ'κ y hy, κ.left_inv hy]
  · simp [hψ'0 z hz]

variable [CompleteSpace V] [CompleteSpace W]

/-- **Integral operators under a change of variables.** Let `κ` be a diffeomorphism from an open
set of `ℝⁿ` onto another, and let `K(z, w)` be smooth on an open set `O`. If `φ` and `ψ` are cutoffs
with compact supports in the source of `κ` such that `(κ x, κ y) ∈ O` for `x` in the support of `φ`
and `y` in that of `ψ`, then the operator `u ↦ φ(x) ∫ K(κ x, w) ((ψ u) ∘ κ⁻¹)(w) dw` is the
quantization of a smoothing symbol: its kernel `φ(x) ψ(y) |det Dκ(y)| K(κ x, κ y)` is smooth and
compactly supported. -/
theorem exists_isSmoothing_smul_integral_comp_eq
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    (hκ : ContDiffOn ℝ ∞ κ κ.source) (hκ' : ContDiffOn ℝ ∞ κ.symm κ.target)
    {K : CoordinateSpace n → CoordinateSpace n → V →L[ℂ] W}
    {O : Set (CoordinateSpace n × CoordinateSpace n)} (hO : IsOpen O)
    (hK : ContDiffOn ℝ ∞ (Function.uncurry K) O)
    {φ ψ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ κ.source) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ κ.source) (hφψ : ∀ x ∈ tsupport φ, ∀ y ∈ tsupport ψ, (κ x, κ y) ∈ O) :
    ∃ r : Symbol n V W m, r.IsSmoothing ∧ ∀ u v : 𝓢(CoordinateSpace n, V),
      (∀ y ∈ κ.source, v (κ y) = ψ y • u y) → (∀ z ∉ κ.target, v z = 0) → ∀ x,
        φ x • ∫ w, K (κ x) w (v w) = quantizeSchwartzValue r.coefficient u x := by
  -- The kernel `g • f` of the transported operator, with the cutoffs in `g`.
  set g : CoordinateSpace n × CoordinateSpace n → ℝ := fun p ↦ ψ p.2 • φ p.1
  set f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun p ↦ |(fderiv ℝ κ p.2).det| • K (κ p.1) (κ p.2)
  set s : Set (CoordinateSpace n × CoordinateSpace n) :=
    (κ.source ×ˢ κ.source) ∩ Prod.map κ κ ⁻¹' O
  have hs : IsOpen s := (κ.continuousOn.prodMap κ.continuousOn).isOpen_inter_preimage
    (κ.open_source.prod κ.open_source) hO
  have hgφψ : tsupport g ⊆ tsupport φ ×ˢ tsupport ψ := tsupport_snd_smul_fst_subset ψ φ
  have hgs : tsupport g ⊆ s := fun p hp ↦ by
    obtain ⟨h1, h2⟩ := hgφψ hp
    exact ⟨⟨hφs h1, hψs h2⟩, hφψ _ h1 _ h2⟩
  have hf : ContDiffOn ℝ ∞ f s := by
    refine ((κ.contDiffOn_abs_det_fderiv_of_contDiffOn (m := ⊤) (by simp) hκ hκ').comp
      (s := s) contDiffOn_snd fun p hp ↦ hp.1.2).smul ?_
    exact hK.comp ((hκ.comp (s := s) contDiffOn_fst fun p hp ↦ hp.1.1).prodMk
      (hκ.comp (s := s) contDiffOn_snd fun p hp ↦ hp.1.2)) fun p hp ↦ hp.2
  have hL : ContDiff ℝ ∞ fun p ↦ g p • f p :=
    hf.contDiff_smul_of_tsupport_subset hs
      ((hψ.comp contDiff_snd).smul (hφ.comp contDiff_fst)).contDiffOn hgs
  have hcpt := hφc.isCompact.prod hψc.isCompact
  have hLc : HasCompactSupport fun p ↦ g p • f p :=
    .intro' hcpt hcpt.isClosed fun p hp ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hp (hgφψ h), zero_smul]
  refine ⟨Symbol.ofKernel _ hL hLc, Symbol.isSmoothing_ofKernel _ _, fun u v hv hv0 x ↦ ?_⟩
  rw [Symbol.quantizeSchwartzValue_ofKernel]
  by_cases hx : φ x = 0
  · simp [g, hx]
  -- Change variables `w = κ y` in the integral over the target of `κ`, where `v` lives.
  have hκd : ∀ y ∈ κ.source, HasFDerivWithinAt κ (fderiv ℝ κ y) κ.source y := fun y hy ↦
    ((hκ.differentiableOn (by simp) y hy).differentiableAt
      (κ.open_source.mem_nhds hy)).hasFDerivAt.hasFDerivWithinAt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := κ.target)
      fun w hw ↦ by simp [hv0 w hw], ← κ.image_source_eq_target,
    integral_image_eq_integral_abs_det_fderiv_smul volume κ.open_source.measurableSet hκd
      κ.injOn, setIntegral_congr_fun κ.open_source.measurableSet fun y hy ↦ by rw [hv y hy],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_, ← integral_smul]
  · refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [g, f, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.map_smul_of_tower,
      smul_smul, smul_eq_mul]
    ring_nf
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy (hψs h)]
    simp

/-- **Changes of coordinates with disjoint cutoffs.** Let `κ` be a diffeomorphism from an open set
of `ℝⁿ` onto another and `φ`, `ψ` cutoffs with compact supports in its source, whose supports are
disjoint. Then for every symbol `a`, the operator `u ↦ φ · Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ` is the
quantization of a smoothing symbol: away from the diagonal the kernel of `Op(a)` is smooth. -/
theorem Symbol.exists_isSmoothing_smul_quantizeSchwartzValue_comp_eq (a : Symbol n V W m)
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    (hκ : ContDiffOn ℝ ∞ κ κ.source) (hκ' : ContDiffOn ℝ ∞ κ.symm κ.target)
    {φ ψ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ κ.source) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ κ.source) (hφψ : Disjoint (tsupport φ) (tsupport ψ)) :
    ∃ r : Symbol n V W m, r.IsSmoothing ∧ ∀ u v : 𝓢(CoordinateSpace n, V),
      (∀ y ∈ κ.source, v (κ y) = ψ y • u y) → (∀ z ∉ κ.target, v z = 0) → ∀ x,
        φ x • quantizeSchwartzValue a.coefficient v (κ x) =
          quantizeSchwartzValue r.coefficient u x := by
  obtain ⟨r, hr, hop⟩ := exists_isSmoothing_smul_integral_comp_eq (m := m) hκ hκ'
    (isOpen_ne_fun continuous_fst continuous_snd) a.contDiffOn_offDiagonalKernel hφ hφc hφs hψ
    hψc hψs fun x hx y hy hxy ↦ hφψ.ne_of_mem hx hy (κ.injOn (hφs hx) (hψs hy) hxy)
  refine ⟨r, hr, fun u v hv hv0 x ↦ ?_⟩
  rw [← hop u v hv hv0 x]
  by_cases hx : φ x = 0
  · simp [hx]
  -- At `κ x` the input `v` vanishes nearby, so `Op(a) v` is given by the off-diagonal kernel.
  obtain ⟨hvc, hvs⟩ := hasCompactSupport_and_tsupport_subset_image hψc hψs hv hv0
  refine congrArg _ (a.quantizeSchwartzValue_eq_integral_offDiagonalKernel hvc fun h ↦ ?_)
  obtain ⟨y, hy, hxy⟩ := hvs h
  exact hφψ.ne_of_mem (subset_tsupport _ hx) hy
    (κ.injOn (hφs (subset_tsupport _ hx)) (hψs hy) hxy.symm)

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Changes of coordinates near a point.** The change of coordinates theorem for an open partial
homeomorphism `κ`, when the cutoffs `φ` and `ψ` are supported in an open set `N` on which `κ` agrees
with a global diffeomorphism `κ'` whose derivatives and Hadamard factors are all invertible. -/
private theorem ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq_of_eqOn
    (a : ClassicalSymbol n V W m)
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    (κ' : CoordinateSpace n ≃ₜ CoordinateSpace n) (hκ'c : ContDiff ℝ ∞ κ')
    (hκ'd : ∀ y, IsUnit (fderiv ℝ κ' y)) (hκ'Φ : ∀ x y, IsUnit (hadamardFactor κ' y x))
    {N : Set (CoordinateSpace n)} (hN : IsOpen N) (hNs : N ⊆ κ.source) (hNκ : EqOn κ' κ N)
    {φ ψ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφN : tsupport φ ⊆ N) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψN : tsupport ψ ⊆ N) :
    ∃ b : ClassicalSymbol n V W m, (∀ x ξ, b.principal.coefficient (x, ξ) =
        (φ x * ψ x) • a.principal.coefficient
          (κ x, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)) ξ)) ∧
      ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y ∈ κ.source, v (κ y) = ψ y • u y) →
        (∀ z ∉ κ.target, v z = 0) → ∀ x,
          φ x • quantizeSchwartzValue a.toSymbol.coefficient v (κ x) =
            quantizeSchwartzValue b.toSymbol.coefficient u x := by
  -- Only the positions `κ' x` with `x` in the compact support of `φ` matter, so the symbol may be
  -- cut off in space by `θ`, and the theorem for the global diffeomorphism `κ'` applies.
  obtain ⟨θ, hθ, -, hθ1, hθc, -⟩ := (hφc.isCompact.image κ'.continuous).exists_contDiff_cutoff
    isOpen_univ (subset_univ _)
  have hθφ : ∀ x, φ x ≠ 0 → θ (κ' x) = 1 := fun x hx ↦
    interior_subset (hθ1 ⟨x, subset_tsupport _ hx, rfl⟩)
  obtain ⟨b, hb, hop⟩ :=
    (a.smulLeft (Complex.ofRealCLM.contDiff.comp hθ)).exists_quantizeSchwartzValue_comp_eq
    hθc.isCompact (fun z hz η ↦ by simp [image_eq_zero_of_notMem_tsupport hz])
    κ' hκ'c hψ hψc (fun y _ ↦ hκ'd y) fun x _ y _ ↦ hκ'Φ x y
  refine ⟨b.smulLeft (Complex.ofRealCLM.contDiff.comp hφ), fun x ξ ↦ ?_, fun u v hv hv0 x ↦ ?_⟩
  · rw [coefficient_principal_smulLeft, hb, coefficient_principal_smulLeft]
    by_cases hx : φ x * ψ x = 0
    · rcases mul_eq_zero.1 hx with h | h <;> simp [h]
    obtain ⟨hφx, hψx⟩ := mul_ne_zero_iff.1 hx
    have hxN : x ∈ N := hψN (subset_tsupport _ hψx)
    simp only [Function.comp_apply]
    rw [hθφ x hφx, (hNκ.eventuallyEq_of_mem (hN.mem_nhds hxN)).fderiv_eq, hNκ hxN]
    simp [smul_smul, Complex.coe_smul]
  · rw [toSymbol_smulLeft, Symbol.quantizeSchwartzValue_smulLeft, ← hop u v
      (apply_eq_smul_of_eqOn κ'.injective hNs hNκ hψN hv hv0), toSymbol_smulLeft,
      Symbol.quantizeSchwartzValue_smulLeft]
    by_cases hx : φ x = 0
    · simp [hx]
    simp only [Function.comp_apply]
    rw [hθφ x hx, hNκ (hφN (subset_tsupport _ hx))]
    simp

/-- **Changes of coordinates for an input cutoff near a point.** The change of coordinates theorem
for an open partial homeomorphism `κ`, when the cutoff `ψ` is supported in an open set `N` on which
`κ` agrees with a global diffeomorphism `κ'` whose derivatives and Hadamard factors are all
invertible. The output cutoff splits as `φ = φ χ + φ (1 - χ)`, with `χ = 1` near the support of `ψ`
and supported in `N`: the first part is
`TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq_of_eqOn`, the second part
`TauCeti.Symbol.exists_isSmoothing_smul_quantizeSchwartzValue_comp_eq`. -/
private theorem ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq_of_tsupport_subset
    (a : ClassicalSymbol n V W m)
    {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)}
    (hκ : ContDiffOn ℝ ∞ κ κ.source) (hκ' : ContDiffOn ℝ ∞ κ.symm κ.target)
    (κ' : CoordinateSpace n ≃ₜ CoordinateSpace n) (hκ'c : ContDiff ℝ ∞ κ')
    (hκ'd : ∀ y, IsUnit (fderiv ℝ κ' y)) (hκ'Φ : ∀ x y, IsUnit (hadamardFactor κ' y x))
    {N : Set (CoordinateSpace n)} (hN : IsOpen N) (hNs : N ⊆ κ.source) (hNκ : EqOn κ' κ N)
    {φ ψ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ κ.source) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψN : tsupport ψ ⊆ N) :
    ∃ b : ClassicalSymbol n V W m, (∀ x ξ, b.principal.coefficient (x, ξ) =
        (φ x * ψ x) • a.principal.coefficient
          (κ x, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)) ξ)) ∧
      ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y ∈ κ.source, v (κ y) = ψ y • u y) →
        (∀ z ∉ κ.target, v z = 0) → ∀ x,
          φ x • quantizeSchwartzValue a.toSymbol.coefficient v (κ x) =
            quantizeSchwartzValue b.toSymbol.coefficient u x := by
  obtain ⟨χ, hχ, -, hχ1, -, hχN⟩ := hψc.isCompact.exists_contDiff_cutoff_eventuallyEq_one hN hψN
  have hχψ : ∀ x, χ x * ψ x = ψ x := fun x ↦ by
    by_cases hx : ψ x = 0
    · simp [hx]
    rw [(hχ1 x (subset_tsupport _ hx)).self_of_nhds, one_mul]
  obtain ⟨b₁, hb₁, hop₁⟩ := a.exists_smul_quantizeSchwartzValue_comp_eq_of_eqOn κ' hκ'c hκ'd
    hκ'Φ hN hNs hNκ (hφ.mul hχ) hφc.mul_right (tsupport_mul_subset_right.trans hχN) hψ hψc hψN
  obtain ⟨r, hr, hop₂⟩ := a.toSymbol.exists_isSmoothing_smul_quantizeSchwartzValue_comp_eq hκ hκ'
    (φ := fun x ↦ φ x * (1 - χ x)) (hφ.mul (contDiff_const.sub hχ)) hφc.mul_right
    (tsupport_mul_subset_left.trans hφs) hψ hψc (hψN.trans hNs) <|
      Set.disjoint_left.2 fun x hx hxψ ↦ by
      -- `1 - χ` vanishes near the support of `ψ`.
      refine notMem_tsupport_iff_eventuallyEq.2 ?_ (tsupport_mul_subset_right hx)
      filter_upwards [hχ1 x hxψ] with z hz
      simp [hz]
  refine ⟨b₁ + ofIsSmoothing r hr, fun x ξ ↦ ?_, fun u v hv hv0 x ↦ ?_⟩
  · simpa [mul_assoc, hχψ] using hb₁ x ξ
  · simp only [toSymbol_add, Symbol.coefficient_add, Symbol.quantizeSchwartzValue_coefficient_add,
      toSymbol_ofIsSmoothing]
    rw [← hop₁ u v hv hv0 x, ← hop₂ u v hv hv0 x, ← add_smul]
    congr 1
    ring

/-- **Changes of coordinates for classical symbols.** Let `κ` be a diffeomorphism from an open set
of `ℝⁿ` onto another, such as a transition map between two charts of a manifold, `a` a classical
symbol of order `m` and `φ`, `ψ` cutoffs with compact supports in the source of `κ`. Then the
operator `u ↦ φ · Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ`, where `(ψ u) ∘ κ⁻¹` is extended by `0` off the target of
`κ`, is `Op(b)` for a classical symbol `b` of order `m`, and **the principal symbol transforms by
the cotangent map**:

`σ(b)(x, ξ) = φ(x) ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`. -/
theorem ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq (a : ClassicalSymbol n V W m)
    (κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n))
    (hκ : ContDiffOn ℝ ∞ κ κ.source) (hκ' : ContDiffOn ℝ ∞ κ.symm κ.target)
    {φ ψ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ κ.source) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ κ.source) :
    ∃ b : ClassicalSymbol n V W m, (∀ x ξ, b.principal.coefficient (x, ξ) =
        (φ x * ψ x) • a.principal.coefficient
          (κ x, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)) ξ)) ∧
      ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y ∈ κ.source, v (κ y) = ψ y • u y) →
        (∀ z ∉ κ.target, v z = 0) → ∀ x,
          φ x • quantizeSchwartzValue a.toSymbol.coefficient v (κ x) =
            quantizeSchwartzValue b.toSymbol.coefficient u x := by
  classical
  -- Cover the support of `ψ` by open sets on which `κ` is a global diffeomorphism, and split `ψ`
  -- by a subordinate partition of unity `ρ`.
  choose N hN hxN hNs κ' hκ'c hκ'd hκ'Φ hNκ using
    fun x : κ.source ↦ κ.exists_eqOn_homeomorph_isUnit_hadamardFactor hκ hκ' le_top x.property
  obtain ⟨t, ρ, hρ, -, -, hρ1⟩ := hψc.isCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one
    hN fun x hx ↦ mem_iUnion.2 ⟨⟨x, hψs hx⟩, hxN _⟩
  choose b hb hop using fun i ↦ a.exists_smul_quantizeSchwartzValue_comp_eq_of_tsupport_subset
    hκ hκ' (κ' i) (hκ'c i) (hκ'd i) (hκ'Φ i) (hN i) (hNs i) (hNκ i) hφ hφc hφs (hψ.mul (hρ i).1)
    hψc.mul_right ((tsupport_mul_subset_right).trans (hρ i).2.2)
  -- The pieces `ψ ρ i` of `ψ`.
  have hψρ : ∀ x, ∑ i ∈ t, ψ x * ρ i x = ψ x := fun x ↦ by
    by_cases hx : ψ x = 0
    · simp [hx]
    rw [← Finset.mul_sum, hρ1 x (subset_tsupport _ hx), mul_one]
  refine ⟨∑ i ∈ t, b i, fun x ξ ↦ ?_, fun u v hv hv0 x ↦ ?_⟩
  · rw [← principalLinearMap_apply, map_sum, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
    simp only [principalLinearMap_apply, hb, ← Finset.sum_smul, ← Finset.mul_sum, hψρ]
  obtain ⟨w, hwv, hwi, hwi0⟩ := exists_sum_eq hκ' hψc hψs t (fun i ↦ (hρ i).1) hρ1 hv hv0
  rw [toSymbol_sum, Symbol.quantizeSchwartzValue_sum_left, ← hwv,
    Symbol.quantizeSchwartzValue_sum_right, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hop i u (w i) (hwi i) (hwi0 i) x

end TauCeti
