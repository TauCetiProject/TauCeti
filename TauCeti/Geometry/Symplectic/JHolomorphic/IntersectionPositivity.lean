/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.AdaptedChart
public import TauCeti.Geometry.Symplectic.Manifold.ZeroCharge
import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy

/-!
# Positivity of intersections with an immersed pseudoholomorphic disc

Let `J : V → (V →L[ℝ] V)` be an almost complex structure on a real normed space `V` of
dimension four, written in coordinates, and let `u₀ : ℂ → V` be a `J`-holomorphic disc,
`∂ₛu₀ + J(u₀) ∂ₜu₀ = 0`, immersed at a point `a₀`. The structure `J` need not be integrable. This
file proves that `J`-holomorphic discs meet `u₀` near `u₀ a₀` positively: for a `C¹`
`J`-holomorphic disc with values in the target of a chart adapted to `u₀`, whose preimage of `u₀`
is compact, the zero charge (`ContinuousMap.zeroCharge`) of the disc, counting its intersections
with `u₀` with their topological multiplicities, is positive as soon as the disc meets `u₀`.

* **Adapted coordinates with a complex normal coordinate.** In dimension four the normal space of
  `u₀` is a complex line, so the coordinates adapted to `u₀` of
  `TauCeti.exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le` can be taken with values in
  `ℂ × ℂ`, and shrunk so that the structure read in them differs from `i` by at most a constant
  times the normal coordinate on their whole source
  (`TauCeti.exists_holomorphicAdaptedChart_complex_norm_pullbackEnd_sub_le`). In such a chart `e`,
  the disc `u₀` is the zero section, and a point `x` of the target of `e` lies on `u₀` exactly
  when its normal coordinate `(e.symm x).2` vanishes
  (`OpenPartialHomeomorph.isImage_of_coe_eq_normalExtension`).
* **Positivity.** For a `C¹` `J`-holomorphic disc `u` in the target of such a chart, the normal
  coordinate `b = (e.symm ∘ u).2` satisfies the Cauchy–Riemann inequality
  `‖∂ₛb + i ∂ₜb‖ ≤ C ‖∂ₜ(e.symm ∘ u)‖ ‖b‖` (`TauCeti.norm_fderiv_snd_add_I_smul_le`). By the
  similarity principle `b` is, near each of its zeros, a nonvanishing continuous function times a
  holomorphic function, so each intersection of `u` with `u₀` that is isolated has positive local
  index, and the intersections of a disc whose preimage of `u₀` is compact are isolated. So the
  zero charge of such a disc for the normal coordinate is positive when the disc meets `u₀`
  (`TauCeti.zeroCharge_pos_of_cauchyRiemann`, from
  `ContinuousMap.zeroCharge_pos_of_norm_le`).

The disc `u` may be tangent to `u₀` or singular at an intersection: such intersections are not
excluded. The second disc is only required to be of class `C¹`.

## Main results

* `TauCeti.exists_holomorphicAdaptedChart_complex_norm_pullbackEnd_sub_le`: in dimension four,
  coordinates adapted to an immersed `J`-holomorphic disc with a complex normal coordinate and the
  normal control on their whole source.
* `TauCeti.zeroCharge_pos_of_cauchyRiemann`: positivity of the zero charge, for the normal
  coordinate of such a chart, of a `J`-holomorphic disc meeting the zero section.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section 2.4 (adapted coordinates and the similarity
  principle) and Appendix E.2 (positivity of intersections).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6 (charges of discs).
-/

public noncomputable section

open Set Filter Complex Metric Module
open scoped Topology ContDiff Complex.UnitDisc

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {J : V → V →L[ℝ] V}

/-! ### Adapted coordinates with a complex normal coordinate -/

/-- **Adapted coordinates in dimension four** (McDuff–Salamon, Lemma 2.4.2). Let `V` have real
dimension four, let `u₀` be a `J`-holomorphic disc of class `C^ℓ`, `2 ≤ ℓ`, on an open `U ∋ a₀`,
immersed at `a₀`, and let `J` be an almost complex structure of class `C^ℓ` on an open
`Ω ⊇ u₀ (U)`. Then there are coordinates `e : ℂ × ℂ → V` adapted to `u₀`, the adapted extension
`(a, w) ↦ u₀ a + Θ_a w` of some real-linear map `W : ℂ →L[ℝ] V`, defined near
`(a₀, 0)`, of class `C^ℓ` with `C^ℓ` inverse, in which the structure read in the chart differs from
multiplication by `i` by at most a constant times the normal coordinate on the whole source. -/
theorem exists_holomorphicAdaptedChart_complex_norm_pullbackEnd_sub_le [FiniteDimensional ℝ V]
    (hV : finrank ℝ V = 4) {U : Set ℂ} {Ω : Set V} {u₀ : ℂ → V} {a₀ : ℂ} {ℓ : ℕ∞ω}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (ha₀ : a₀ ∈ U) (hℓ : 2 ≤ ℓ) (hu₀ : ContDiffOn ℝ ℓ u₀ U)
    (hJ : ContDiffOn ℝ ℓ J Ω) (hu₀Ω : MapsTo u₀ U Ω)
    (hsq : ∀ a ∈ U, ∀ v, J (u₀ a) (J (u₀ a) v) = -v)
    (hCR : ∀ a ∈ U, fderiv ℝ u₀ a 1 + J (u₀ a) (fderiv ℝ u₀ a I) = 0)
    (hdu₀ : fderiv ℝ u₀ a₀ ≠ 0) :
    ∃ (W : ℂ →L[ℝ] V) (e : OpenPartialHomeomorph (ℂ × ℂ) V),
      ⇑e = holomorphicNormalExtension J u₀ W ∧ (a₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧
      e.target ⊆ Ω ∧ ContDiffOn ℝ ℓ e e.source ∧ ContDiffOn ℝ ℓ e.symm e.target ∧
      ∃ C : ℝ, ∀ p ∈ e.source,
        ‖e.pullbackEnd J p - I • ContinuousLinearMap.id ℝ (ℂ × ℂ)‖ ≤ C * ‖p.2‖ := by
  have := FiniteDimensional.completeSpace ℝ V
  -- A complex normal frame `ℂⁿ → V`; in dimension four, `n = 1`.
  obtain ⟨n, W, hW, hbij⟩ := exists_euclideanSpace_bijective_coprod
    (ContinuousLinearMap.ext fun v ↦ by simpa using hsq a₀ ha₀ v) (hCR a₀ ha₀) hdu₀
  have hn : n = 1 := by
    have h := (LinearEquiv.ofBijective
      ((fderiv ℝ u₀ a₀).coprod W : ℂ × EuclideanSpace ℂ (Fin n) →ₗ[ℝ] V) hbij).finrank_eq
    rw [finrank_prod, Complex.finrank_real_complex, finrank_real_of_complex,
      finrank_euclideanSpace_fin, hV] at h
    omega
  subst hn
  -- Read the frame on `ℂ` through the unitary identification of `ℂ` with `ℂ¹`.
  set T := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.toContinuousLinearEquiv
  set W' : ℂ →L[ℝ] V := W.comp ((T : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)).restrictScalars ℝ)
  have hW' (w : ℂ) : J (u₀ a₀) (W' w) = W' (I • w) := by
    simp only [W', ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', hW]
    exact congrArg W (map_smul (T : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) I w).symm
  have hbij' : Function.Bijective ((fderiv ℝ u₀ a₀).coprod W') :=
    hbij.comp (Function.bijective_id.prodMap T.bijective)
  obtain ⟨e, he, h₀, hsU, htΩ, hc, hcs, -, C, hC⟩ :=
    exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le hU hΩ ha₀ hℓ hu₀ hJ hu₀Ω hsq hCR hW'
      hbij'
  -- Shrink the chart to an open set on which the normal control holds.
  obtain ⟨t, htC, ht, h₀t⟩ := _root_.eventually_nhds_iff.1 hC
  have hst : (e.restrOpen t ht).source = e.source ∩ t := e.restrOpen_source t ht
  have htt : (e.restrOpen t ht).target ⊆ e.target := by
    rw [e.restrOpen_toPartialEquiv, PartialEquiv.restr_target]
    exact inter_subset_left
  refine ⟨W', e.restrOpen t ht, by rw [e.coe_restrOpen ht, he], hst ▸ ⟨h₀, h₀t⟩,
    hst ▸ inter_subset_left.trans hsU, htt.trans htΩ, ?_, ?_, C, fun p hp ↦ ?_⟩
  · rw [e.coe_restrOpen ht, hst]
    exact hc.mono inter_subset_left
  · rw [e.coe_restrOpen_symm ht]
    exact hcs.mono htt
  · rw [hst] at hp
    rw [OpenPartialHomeomorph.pullbackEnd_def, e.coe_restrOpen ht, e.coe_restrOpen_symm ht,
      ← OpenPartialHomeomorph.pullbackEnd_def]
    exact htC p hp.2

/-! ### Positivity of the zero charge -/

/-- **Positivity of intersections with an immersed pseudoholomorphic disc.** Let `e` be a chart
`ℂ × ℂ → V`, of class `C¹` with `C¹` inverse, in which the structure `J` read in the chart differs
from multiplication by `i` by at most `C` times the normal coordinate, such as the adapted
coordinates of `TauCeti.exists_holomorphicAdaptedChart_complex_norm_pullbackEnd_sub_le`. Let `u` be
a `J`-holomorphic map of class `C¹` on the unit disc with values in the target of `e`, and let `σ`
be a continuous disc in a space `Y` and `f : Y → ℂ` continuous with `f ∘ σ` the normal coordinate
`(e.symm ∘ u).2` of `u`. If `σ⁻¹(f⁻¹(0))` is compact and nonempty, the zero charge of `σ` is
positive. When `e` is adapted to a disc `u₀`, the zeros of `f ∘ σ` are the intersections of `u`
with `u₀`, and the charge counts them with multiplicity. -/
theorem zeroCharge_pos_of_cauchyRiemann {e : OpenPartialHomeomorph (ℂ × ℂ) V} {C : ℝ}
    (he : ContDiffOn ℝ 1 e e.source) (hes : ContDiffOn ℝ 1 e.symm e.target)
    (hC : ∀ p ∈ e.source,
      ‖e.pullbackEnd J p - I • ContinuousLinearMap.id ℝ (ℂ × ℂ)‖ ≤ C * ‖p.2‖)
    {u : ℂ → V} (hu : ContDiffOn ℝ 1 u (ball 0 1)) (hut : MapsTo u (ball 0 1) e.target)
    (hCR : ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    {Y : Type*} [TopologicalSpace Y] {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (hf : ∀ z : 𝔻, f (σ z) = (e.symm (u z)).2) (h : IsCompact (σ ⁻¹' (f ⁻¹' {0})))
    (hZ : ∃ z, f (σ z) = 0) : 0 < f.zeroCharge σ := by
  -- The disc read in the chart, and the Cauchy–Riemann equation it solves there.
  set v : ℂ → ℂ × ℂ := fun w ↦ e.symm (u w)
  have hvC : ContDiffOn ℝ 1 v (ball 0 1) := hes.comp hu hut
  have hCRv (w) (hw : w ∈ ball (0 : ℂ) 1) :
      fderiv ℝ v w 1 + e.pullbackEnd J (v w) (fderiv ℝ v w I) = 0 :=
    e.fderiv_symm_comp_add_pullbackEnd_eq_zero (hut hw)
      ((hu.differentiableOn one_ne_zero w hw).differentiableAt (isOpen_ball.mem_nhds hw))
      ((he.differentiableOn one_ne_zero).differentiableAt
        (e.open_source.mem_nhds (e.map_target (hut hw))))
      ((hes.differentiableOn one_ne_zero).differentiableAt (e.open_target.mem_nhds (hut hw)))
      (hCR w hw)
  -- Its normal component satisfies a Cauchy–Riemann inequality, with a continuous coefficient.
  obtain ⟨hM, hle⟩ := norm_fderiv_snd_add_I_smul_le_of_contDiffOn isOpen_ball
    (A := fun w ↦ e.pullbackEnd J (v w)) hvC hCRv fun w hw ↦ hC _ (e.map_target (hut hw))
  exact ContinuousMap.zeroCharge_pos_of_norm_le h (b := fun w ↦ (v w).2)
    (fun z ↦ (hf z).symm) hvC.snd hM hle hZ

end TauCeti
