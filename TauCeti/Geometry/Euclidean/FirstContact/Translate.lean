/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.ContactTimes
public import TauCeti.Geometry.Euclidean.FirstContact.Graph

/-!
# First contact for translates of a closed set

A closed barrier translated along a unit vector against a closed image has a last contact
when the compact sweep and nonempty-contact assumptions hold. For each graph contained locally
in the unshifted barrier whose translate by `t₀ • e` passes through `f x`, the height inequality
holds for source points near `x` whenever the map is continuous at `x`.

If the last translate avoids the image of the source boundary, every source point mapped into
that translate is interior in the source manifold. Differentiability there gives tangency to
each differentiable local graph translated through `f x`.

The generic compactness and ordered-time attainment results are in
`TauCeti.Topology.Algebra.GroupAction.ContactTimes`.

## References

* R. Brasca, [closed-barrier formalization](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/cfee5e52aa5576999d055c12bd0f004b0d7cba9f).
* G. Franz, [first-contact formalization](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/fde0487c6fe0a19b628b05a2708d65e20ef239c9),
  source of the translated-graph and tangency lemmas in `FirstContact.Graph`.
* O. Chodosh, *Introduction to minimal surfaces*, proof of Theorem 20.1.
-/

public section

open Filter Function Manifold Set Topology TauCeti
open scoped InnerProductSpace Manifold Pointwise

section LocalGraph

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : F}
  {M : Type*} [TopologicalSpace M] {f : M → F} {S : Set F} {g : (ℝ ∙ e)ᗮ → ℝ} {T : ℝ}

/-- If a graph lies locally in the unshifted barrier, its translate by `t₀ • e` passes through
`f x`, and there are no later contacts, the height is at most `t₀` for source points near `x`. -/
theorem ContinuousAt.eventually_heightAboveGraph_le_of_disjoint {x : M} {t₀ : ℝ}
    (hf : ContinuousAt f x) (he : ‖e‖ = 1) (ht₀ : t₀ < T)
    (hdisj : ∀ t ∈ Ioc t₀ T, Disjoint ((t • e) +ᵥ S) (range f))
    (hg : ContinuousAt g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)))
    (hgS : ∀ᶠ k : (ℝ ∙ e)ᗮ in 𝓝 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)),
      (k : F) + g k • e ∈ S)
    (hx : heightAboveGraph e g (f x) = t₀) :
    ∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀ := by
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hPf : ContinuousAt (fun y ↦ P (f y)) x := P.continuous.continuousAt.comp hf
  have hh : ContinuousAt (fun y ↦ heightAboveGraph e g (f y)) x :=
    hg.continuousAt_heightAboveGraph.comp hf
  have hxT : heightAboveGraph e g (f x) < T := by rwa [hx]
  filter_upwards [hPf.eventually hgS, hh.eventually (gt_mem_nhds hxT)] with y hyS hyT
  by_contra hlt
  let t := heightAboveGraph e g (f y)
  have hy : f y ∈ translatedGraph e {k | (k : F) + g k • e ∈ S} g t :=
    (mem_translatedGraph_iff he).2 ⟨hyS, rfl⟩
  have hyS' : f y ∈ (t • e) +ᵥ S := by
    rw [← vadd_translatedGraph_zero] at hy
    exact (vadd_set_mono (by
      intro k hk
      rw [translatedGraph_def, mem_image] at hk
      obtain ⟨k, hk, rfl⟩ := hk
      simpa only [add_zero, mem_ofPred_eq] using hk)) hy
  exact disjoint_left.1 (hdisj t ⟨not_le.1 hlt, hyT.le⟩) hyS' (mem_range_self y)

/-- A closed barrier against a closed image has a last contact in `[0,T)` under the compact
sweep and endpoint-exclusion assumptions. For any graph contained locally in the unshifted
barrier whose translate by `t₀ • e` passes through `f x`, the height is at most `t₀` for source
points near `x`, provided the map is continuous at `x`. -/
theorem IsClosed.exists_firstContact_translate (hC : IsClosed (range f))
    (he : ‖e‖ = 1) (hS : IsClosed S) (hT : Disjoint ((T • e) +ᵥ S) (range f))
    (hcontact : ∃ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty)
    {K : Set F} (hK : IsCompact K)
    (hsweep : ∀ t ∈ Icc 0 T, ((t • e) +ᵥ S) ∩ range f ⊆ K) :
    ∃ t₀ ∈ Ico 0 T, (((t₀ • e) +ᵥ S) ∩ range f).Nonempty ∧
      (∀ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty → t ≤ t₀) ∧
      ∀ (x : M) (g : (ℝ ∙ e)ᗮ → ℝ),
        ContinuousAt g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)) →
        (∀ᶠ k : (ℝ ∙ e)ᗮ in 𝓝 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)),
          (k : F) + g k • e ∈ S) →
        heightAboveGraph e g (f x) = t₀ →
        ContinuousAt f x → ∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀ := by
  obtain ⟨t₀, ⟨ht₀, hne⟩, hmax⟩ := (isCompact_Icc.isCompact_contactTimes
    (continuous_id.smul continuous_const).continuousOn hS hC hK hsweep).exists_isGreatest hcontact
  have hlt : t₀ < T := lt_of_le_of_ne ht₀.2 fun ht ↦ hne.not_disjoint (ht.symm ▸ hT)
  refine ⟨t₀, ⟨ht₀.1, hlt⟩, hne, fun t ht h ↦ hmax ⟨ht, h⟩,
    fun x g hg hgS hx hf ↦ ?_⟩
  refine hf.eventually_heightAboveGraph_le_of_disjoint he hlt ?_ hg hgS hx
  intro t ht
  by_contra hd
  exact ht.1.not_ge (hmax ⟨⟨ht₀.1.trans ht.1.le, ht.2⟩,
    not_disjoint_iff_nonempty_inter.mp hd⟩)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

/-- If the last translate avoids the image of the source boundary, every source point mapped
into it is interior in the source manifold. For each differentiable graph locally in the
unshifted barrier whose translate by `t₀ • e` passes through `f x`, continuity at `x` gives the
height inequality for source points near `x`; differentiability at `x` gives tangency. -/
theorem IsClosed.exists_firstContact_translate_tangent (hC : IsClosed (range f))
    (he : ‖e‖ = 1) (hS : IsClosed S) (hT : Disjoint ((T • e) +ᵥ S) (range f))
    (hcontact : ∃ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty)
    {K : Set F} (hK : IsCompact K)
    (hsweep : ∀ t ∈ Icc 0 T, ((t • e) +ᵥ S) ∩ range f ⊆ K)
    (hbdry : ∀ t, IsGreatest {t ∈ Icc 0 T | (((t • e) +ᵥ S) ∩ range f).Nonempty} t →
      ∀ x, I.IsBoundaryPoint x → f x ∉ (t • e) +ᵥ S) :
    ∃ t₀ ∈ Ico 0 T, (((t₀ • e) +ᵥ S) ∩ range f).Nonempty ∧
      (∀ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty → t ≤ t₀) ∧
      ∀ x, f x ∈ (t₀ • e) +ᵥ S → I.IsInteriorPoint x ∧
        ∀ g : (ℝ ∙ e)ᗮ → ℝ, DifferentiableAt ℝ g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)) →
          (∀ᶠ k : (ℝ ∙ e)ᗮ in 𝓝 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)),
            (k : F) + g k • e ∈ S) →
          heightAboveGraph e g (f x) = t₀ →
          (ContinuousAt f x → ∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀) ∧
          (MDifferentiableAt I 𝓘(ℝ, F) f x →
            ∀ v : TangentSpace I x, ⟪e, mvfderiv I f x v⟫_ℝ =
              fderiv ℝ g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x))
                ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (mvfderiv I f x v))) := by
  obtain ⟨t₀, ht₀, hne, hmax, hside⟩ :=
    hC.exists_firstContact_translate he hS hT hcontact hK hsweep
  refine ⟨t₀, ht₀, hne, hmax, fun x hx ↦ ?_⟩
  have hxI : I.IsInteriorPoint x := (I.isInteriorPoint_iff_not_isBoundaryPoint x).2
    (fun hb ↦ hbdry t₀ ⟨⟨⟨ht₀.1, ht₀.2.le⟩, hne⟩, fun _ ht ↦ hmax _ ht.1 ht.2⟩ x hb hx)
  refine ⟨hxI, fun g hg hgS hxg ↦ ?_⟩
  have hle := hside x g hg.continuousAt hgS hxg
  refine ⟨hle, fun hfd v ↦ ?_⟩
  have hmax' : IsLocalMax (fun y ↦ heightAboveGraph e g (f y)) x := by
    filter_upwards [hle hfd.continuousAt] with y hy
    simpa only [hxg] using hy
  exact inner_mvfderiv_eq_fderiv_of_isLocalExtr hxI (Or.inr hmax') hfd hg v

end LocalGraph
