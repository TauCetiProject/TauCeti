/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.Runge.SimpleFraction
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.ConnectedComponents

/-!
# Runge's approximation theorem on plane domains

Let `K` be a compact subset of an open set `Ω ⊆ ℂ`. **Runge's theorem** says that every function
holomorphic on a neighbourhood of `K` is a uniform limit on `K` of functions holomorphic on all of
`Ω` exactly when `K` is filled in `Ω` (`TauCeti.IsFilledIn K Ω`): no connected component of
`Ω \ K` is relatively compact in `Ω`. Neither `K` nor `Ω` needs to be connected.

## The argument

Approximation follows from the simple-fraction case
`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt` by the Cauchy–Green formula with a
cutoff. Let `f` be holomorphic on an open `U ⊇ K` and let `α` be a smooth cutoff with compact
support in `U`, equal to `1` near `K`. The compactly supported `C¹` function `u = α f` is the
Cauchy transform of `\bar∂ u` (`HasCompactSupport.cauchyTransform_conjWirtingerDeriv`), and
`\bar∂ u` vanishes near `K`, where `u = f` is holomorphic. Hence on `K`

`f ξ = π⁻¹ ∫ (ξ - z)⁻¹ \bar∂ u (z) dz`

(`DifferentiableOn.exists_eqOn_cauchyTransform`), an integral of simple fractions
`ξ ↦ (ξ - z)⁻¹` with poles `z ∉ K`. Rather than discretising it by Riemann sums, we read it as a
Bochner integral of a continuous compactly supported function with values in the Banach space
`C(K, ℂ)`. Every value lies in the uniform closure of the restrictions to `K` of functions
holomorphic on `Ω`, by the simple-fraction case, and this closure is a closed subspace, so it
contains the integral (`Submodule.integral_mem`).

Conversely, if a component `C` of `Ω \ K` is relatively compact in `Ω`, its frontier lies in `K`.
For `a ∈ C`, an approximation `g` of `(z - a)⁻¹` on `K` makes `(z - a) g(z) - 1` small on `K`,
hence on `C` by the maximum modulus principle, which fails at `z = a`.

## Main results

* `DifferentiableOn.exists_eqOn_cauchyTransform`: the Cauchy–Green formula with a cutoff. On `K`,
  a function holomorphic near `K` is the Cauchy transform of a continuous compactly supported
  density whose support misses `K`.
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: **Runge's theorem.** If `K` is
  compact and filled in the open set `Ω`, every function holomorphic on a neighbourhood of `K` is
  uniformly approximable on `K` by functions holomorphic on `Ω`.
* `TauCeti.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt`: conversely, for closed
  `K`, if the simple fractions with poles in `Ω \ K` are so approximable, then `K` is filled in
  `Ω`.
* `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`: the resulting
  characterisation of compact sets filled in `Ω` by approximation.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.9.
-/

public section

open Set Filter Function MeasureTheory Complex TopologicalSpace
open scoped Topology ContDiff

namespace TauCeti

variable {K Ω : Set ℂ}

/-- The uniform closure, inside `C(K, ℂ)`, of the restrictions to `K` of the functions
holomorphic on the open set `Ω ⊇ K`. -/
private noncomputable def rungeClosure (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) : Submodule ℂ C(K, ℂ) :=
  (LinearMap.range ((ContinuousMap.compRightAlgHom ℂ ℂ
    (⟨inclusion hKΩ, continuous_inclusion hKΩ⟩ : C(K, (⟨Ω, hΩ⟩ : Opens ℂ)))).toLinearMap ∘ₗ
      (holomorphicFunctions ⟨Ω, hΩ⟩).val.toLinearMap)).topologicalClosure

/-- A continuous function on a compact `K` lies in `rungeClosure` exactly when it is a uniform
limit on `K` of functions holomorphic on `Ω`. -/
private theorem mem_rungeClosure_iff [CompactSpace K] (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (F : C(K, ℂ)) : F ∈ rungeClosure hΩ hKΩ ↔
      ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z : K, ‖F z - g z‖ < ε := by
  rw [rungeClosure, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  constructor
  · intro hF ε hε
    obtain ⟨_, ⟨g, rfl⟩, hdist⟩ := hF ε hε
    refine ⟨HolomorphicFunctions.extend g, HolomorphicFunctions.differentiableOn_extend g,
      fun z ↦ ?_⟩
    rw [HolomorphicFunctions.extend_apply g ⟨z, hKΩ z.property⟩]
    rw [dist_eq_norm] at hdist
    refine lt_of_le_of_lt ?_ hdist
    refine le_of_eq_of_le ?_ (ContinuousMap.norm_coe_le_norm (F - _) z)
    simp
  · intro hF ε hε
    obtain ⟨g, hg, hgK⟩ := hF (ε / 2) (half_pos hε)
    refine ⟨_, ⟨HolomorphicFunctions.of ⟨Ω, hΩ⟩ g hg, rfl⟩, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    rw [ContinuousMap.dist_le (half_pos hε).le]
    intro z
    rw [dist_eq_norm]
    simpa using (hgK z).le

/-- **The Cauchy–Green formula with a cutoff.** A function `f` with values in a complex Banach
space, holomorphic on an open neighbourhood `U` of a compact set `K`, is, on `K`, the Cauchy
transform `ξ ↦ π⁻¹ ∫ (ξ - z)⁻¹ • h z` of a continuous compactly supported density `h` whose
support lies in `U` and misses `K`. One may take `h = \bar∂ (α f)` for a smooth cutoff `α` with
compact support in `U`, equal to `1` near `K`. -/
theorem _root_.DifferentiableOn.exists_eqOn_cauchyTransform {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ h : ℂ → F, Continuous h ∧ HasCompactSupport h ∧ tsupport h ⊆ U \ K ∧
      EqOn (cauchyTransform h) f K := by
  -- Cut `f` off to a compactly supported `C¹` function `u`, equal to `f` on an open `W ⊇ K`.
  obtain ⟨α, hα, -, hα1, hαc, hαU⟩ := hK.exists_contDiff_cutoff hU hKU
  set u : ℂ → F := fun z ↦ α z • f z
  have hu : ContDiff ℝ 1 u :=
    ((hf.contDiffOn hU).restrict_scalars (𝕜 := ℝ)).contDiff_smul_of_tsupport_subset hU
      (hα.of_le (m := 1) (by simp)).contDiffOn hαU
  have huc : HasCompactSupport u := hαc.smul_right
  set W := interior (α ⁻¹' {1}) ∩ U
  have hW : IsOpen W := isOpen_interior.inter hU
  have huf {z : ℂ} (hz : z ∈ W) : u =ᶠ[𝓝 z] f := by
    filter_upwards [hW.mem_nhds hz] with y hy
    simp [u, show α y = 1 from interior_subset hy.1]
  -- Its `\bar∂` is supported in `tsupport u ⊆ U` and vanishes on `W`, where `u = f`.
  refine ⟨fun z ↦ conjWirtingerDeriv u z 1, hu.continuous_conjWirtingerDeriv_apply 1,
    huc.mono' fun z hz ↦ ?_, fun z hz ↦ ⟨?_, fun hzK ↦ ?_⟩, fun ξ hξ ↦ ?_⟩
  · by_contra hzu
    exact hz (by simp [conjWirtingerDeriv_of_notMem_tsupport hzu])
  · refine (tsupport_smul_subset_left α f).trans hαU (closure_minimal (fun y hy ↦ ?_)
      (isClosed_tsupport _) hz)
    by_contra hyu
    exact hy (by simp [conjWirtingerDeriv_of_notMem_tsupport (g := u) hyu])
  · have hzW : z ∈ W := subset_inter hα1 hKU hzK
    refine (notMem_tsupport_iff_eventuallyEq.2 ?_) hz
    filter_upwards [hW.mem_nhds hzW] with y hy
    simp only [(huf hy).conjWirtingerDeriv_eq,
      (hf.differentiableAt (hU.mem_nhds hy.2)).conjWirtingerDeriv_eq_zero, zero_apply,
      Pi.zero_apply]
  · rw [huc.cauchyTransform_conjWirtingerDeriv hu ξ]
    exact (huf (subset_inter hα1 hKU hξ)).eq_of_nhds

/-- The Cauchy kernel `(z, ξ) ↦ (ξ - z)⁻¹ h z` is continuous on `ℂ × K` when the density `h` is
continuous and its support misses `K`: near a point of the support the simple fraction has no
pole on `K`, and elsewhere `h` vanishes nearby. -/
private theorem continuous_inv_sub_mul_of_disjoint {h : ℂ → ℂ} (hh : Continuous h)
    (hK : Disjoint (tsupport h) K) : Continuous fun p : ℂ × K ↦ ((p.2 : ℂ) - p.1)⁻¹ * h p.1 := by
  refine continuous_iff_continuousAt.2 fun ⟨z, ξ⟩ ↦ ?_
  by_cases hz : z ∈ tsupport h
  · have hne : (ξ : ℂ) - z ≠ 0 :=
      sub_ne_zero.2 fun hξz ↦ hK.notMem_of_mem_left hz (hξz ▸ ξ.property)
    exact ((continuous_subtype_val.comp continuous_snd).sub continuous_fst).continuousAt.inv₀
      hne |>.mul (hh.comp continuous_fst).continuousAt
  · refine continuousAt_const.congr (f := fun _ ↦ (0 : ℂ)) ?_
    filter_upwards [continuousAt_fst.preimage_mem_nhds
      (notMem_tsupport_iff_eventuallyEq.1 hz)] with p hp
    rw [show h p.1 = 0 from hp, mul_zero]

/-- **Runge's theorem.** Let `K` be a compact subset of an open set `Ω ⊆ ℂ` that is filled in
`Ω`: no connected component of `Ω \ K` is relatively compact in `Ω`. Then every function
holomorphic on an open neighbourhood `U` of `K` is a uniform limit on `K` of functions holomorphic
on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨h, hh, hhc, hhU, hfh⟩ := hf.exists_eqOn_cauchyTransform hU hK hKU
  have hhK : Disjoint (tsupport h) K := disjoint_left.2 fun z hz ↦ (hhU hz).2
  -- Read `f` on `K` as `π⁻¹ ∫ G`, a `C(K, ℂ)`-valued integral of simple fractions.
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : C(ℂ, C(K, ℂ)) := ContinuousMap.curry ⟨_, continuous_inv_sub_mul_of_disjoint hh hhK⟩
  have hG_apply (z : ℂ) (ξ : K) : G z ξ = ((ξ : ℂ) - z)⁻¹ * h z := rfl
  have hGc : HasCompactSupport G := hhc.mono fun z hz hhz ↦
    hz (ContinuousMap.ext fun ξ ↦ by simp [hG_apply, hhz])
  have hfK : (⟨fun ξ : K ↦ f ξ, hf.continuousOn.comp_continuous continuous_subtype_val
      fun ξ ↦ hKU ξ.property⟩ : C(K, ℂ)) = (Real.pi : ℂ)⁻¹ • ∫ z, G z := by
    ext ξ
    rw [ContinuousMap.smul_apply, ContinuousMap.integral_apply
      ((map_continuous G).integrable_of_hasCompactSupport hGc), ContinuousMap.coe_mk,
      ← hfh ξ.property, cauchyTransform_apply]
    simp [hG_apply]
  -- Each value of `G` is a multiple of a simple fraction with pole off `K`, so it lies in the
  -- Runge closure, which is a closed subspace and hence contains the integral.
  have hGA (z : ℂ) : G z ∈ rungeClosure hΩ hKΩ := by
    by_cases hz : z ∈ tsupport h
    · have hzK : z ∉ K := (hhU hz).2
      have hGz : G z = h z • ⟨fun ξ : K ↦ ((ξ : ℂ) - z)⁻¹,
          (continuous_subtype_val.sub continuous_const).inv₀ fun ξ ↦
            sub_ne_zero.2 (ne_of_mem_of_not_mem ξ.property hzK)⟩ :=
        ContinuousMap.ext fun ξ ↦ by simp [hG_apply, mul_comm]
      rw [hGz]
      refine Submodule.smul_mem _ _ ((mem_rungeClosure_iff hΩ hKΩ _).2 fun δ hδ ↦ ?_)
      obtain ⟨g, hg, hgK⟩ := hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ hzK hδ
      exact ⟨g, hg, fun ξ ↦ hgK ξ ξ.property⟩
    · have hG0 : G z = 0 :=
        ContinuousMap.ext fun ξ ↦ by simp [hG_apply, image_eq_zero_of_notMem_tsupport hz]
      rw [hG0]
      exact zero_mem _
  have hmem := Submodule.smul_mem _ (Real.pi : ℂ)⁻¹
    (Submodule.integral_mem (μ := volume) (A := (rungeClosure hΩ hKΩ).restrictScalars ℝ)
      (Submodule.isClosed_topologicalClosure _) (.of_forall hGA))
  rw [← hfK] at hmem
  obtain ⟨g, hg, hgK⟩ := (mem_rungeClosure_iff hΩ hKΩ _).1 hmem ε hε
  exact ⟨g, hg, fun z hz ↦ hgK ⟨z, hz⟩⟩

/-- **The converse of Runge's theorem.** Let `K ⊆ ℂ` be closed and `Ω ⊆ ℂ` open. If for every
`a ∈ Ω \ K` the simple fraction `z ↦ (z - a)⁻¹` is a uniform limit on `K` of functions holomorphic
on `Ω`, then `K` is filled in `Ω`. -/
theorem isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt (hΩ : IsOpen Ω)
    (hK : IsClosed K)
    (h : ∀ a ∈ Ω \ K, ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε) :
    IsFilledIn K Ω := by
  rw [isFilledIn_iff]
  rintro a ha ⟨hCc, hCΩ⟩
  set C := connectedComponentIn (Ω \ K) a
  -- The frontier of the component `C` lies in `K`.
  have hfr : frontier C ⊆ K := fun z hz ↦ by
    by_contra hzK
    exact frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK) a hz
      ⟨hCΩ (frontier_subset_closure hz), hzK⟩
  obtain ⟨R, hR⟩ := hCc.isBounded.subset_closedBall a
  set R' := max R 0
  obtain ⟨g, hg, hgK⟩ := h a ha (R' + 1)⁻¹ (by positivity)
  -- `F z = (z - a) g z - 1` is small on the frontier of `C`, but `F a = -1`.
  set F : ℂ → ℂ := fun z ↦ (z - a) * g z - 1
  have hFK (z : ℂ) (hz : z ∈ frontier C) : ‖F z‖ ≤ R' / (R' + 1) := by
    have hza : z - a ≠ 0 := sub_ne_zero.2 fun hza ↦ ha.2 (hza ▸ hfr hz)
    have hF : F z = -((z - a) * ((z - a)⁻¹ - g z)) := by
      simp only [F, mul_sub, mul_inv_cancel₀ hza]
      ring
    rw [hF, norm_neg, norm_mul, div_eq_mul_inv]
    refine mul_le_mul ?_ (hgK z (hfr hz)).le (norm_nonneg _) (le_max_right R 0)
    exact (mem_closedBall_iff_norm.1 (hR (frontier_subset_closure hz))).trans (le_max_left R 0)
  have hFd : DifferentiableOn ℂ F (closure C) :=
    (((differentiableOn_id.sub_const a).mul hg).sub_const 1).mono hCΩ
  have hFa := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hCc.isBounded.subset subset_closure) hFd.diffContOnCl hFK
    (subset_closure (mem_connectedComponentIn ha))
  have hF1 : ‖F a‖ = 1 := by simp only [F, sub_self, zero_mul, zero_sub, norm_neg, norm_one]
  have hR'1 : R' / (R' + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one R')
  linarith

/-- **Runge's theorem, characterisation.** A compact subset `K` of an open set `Ω ⊆ ℂ` is filled in
`Ω` if and only if every function holomorphic on an open neighbourhood of `K` is a uniform limit on
`K` of functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ ∀ U : Set ℂ, IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hfill U hU hKU f hf ε hε ↦
    hfill.exists_differentiableOn_norm_sub_lt hΩ hK hKΩ hU hKU hf hε, fun h ↦ ?_⟩
  refine isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ hK.isClosed fun a ha ↦
    h {a}ᶜ isOpen_compl_singleton (fun z hz hza ↦ ha.2 (hza ▸ hz)) _ ?_
  exact ((differentiableOn_id.sub_const a).inv fun z hz ↦ sub_ne_zero.2 hz)

end TauCeti
