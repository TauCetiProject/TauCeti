/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import Mathlib.Analysis.Convex.GaugeRescale
import TauCeti.Analysis.Complex.UpperHalfPlane.Parabola
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Height
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Disk
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Truncation

/-!
# Adjoining ideal vertices to a convex hyperbolic polygon gives a closed disk

For an arbitrary convex hyperbolic polygon `P : ConvexPolygon n`, adjoining its ideal vertices
identifies `P.carrier ⊕ {i : Fin n // (P.vertex i).isRight}` with `closedBall (0 : ℂ) 1`
(`ConvexPolygon.exists_equiv_closedBall`): `P.carrier` embeds openly, `interior P.carrier` maps
onto `ball (0 : ℂ) 1`, the sides map onto `sphere (0 : ℂ) 1` minus the ideal vertices, and
punctured neighborhoods of each ideal vertex come from arbitrarily deep horodiscs.

## Main result

* `ConvexPolygon.exists_equiv_closedBall`: adjoining the ideal vertices of a convex hyperbolic
  polygon compactifies its carrier to the closed unit disk, with horodisc neighborhoods at each
  ideal vertex.
-/

public section

noncomputable section

open Filter Metric Set Topology UpperHalfPlane
open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n]

/-! ### Normalizing a convex polygon underneath a semicircle -/

private theorem exists_smul_infty_mem_boundaryLeftHalfPlane_mul_pslS (P : ConvexPolygon n) :
    ∃ h₀ : PSL(2, ℝ),
      (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane ((h₀ • P).sideGeodesic 0 * pslS) := by
  obtain ⟨a₀, ha₀⟩ := MulAction.exists_smul_eq PSL(2, ℝ) ((-1 : ℝ) : OnePoint ℝ) ∞
  refine ⟨a₀ * (P.sideGeodesic 0 * pslS)⁻¹, ?_⟩
  set h₀ := a₀ * (P.sideGeodesic 0 * pslS)⁻¹
  have hg₁ := isGeodesicFromTo_mul_pslS_iff.2 ((h₀ • P).isGeodesicFromTo_sideGeodesic 0)
  have ha₀_eq : a₀ = h₀ * P.sideGeodesic 0 * pslS := by simp [h₀, mul_assoc]
  have hg₂ : IsGeodesicFromTo a₀ ((h₀ • P).vertex (0 + 1)) ((h₀ • P).vertex 0) := by
    rw [ha₀_eq]
    simpa only [vertex_smul] using
      isGeodesicFromTo_mul_pslS_iff.2 ((P.isGeodesicFromTo_sideGeodesic 0).smul h₀)
  rw [hg₂.boundaryLeftHalfPlane_eq hg₁, ← mul_one a₀, ← smul_boundaryLeftHalfPlane, ← ha₀]
  refine Set.smul_mem_smul_set ((coe_mem_boundaryLeftHalfPlane_iff 1 (-1)).2 ?_)
  rw [sideForm_one]; norm_num

private theorem vertex_ne_infty_of_infty_mem {Q : ConvexPolygon n}
    (hinf : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)) (i : Fin n) :
    Q.vertex i ≠ .inr ∞ := by
  intro hi
  have hmem := Q.vertex_mem_extClosedLeftHalfPlane_sideGeodesic 0 i
  rw [hi, inr_mem_extClosedLeftHalfPlane_iff] at hmem
  rcases hmem with h₀ | h₁ | hleft
  · exact smul_infty_notMem_boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)
      (by rwa [mul_smul, pslS_smul_infty, ← h₀])
  · exact smul_zero_notMem_boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)
      (by rwa [mul_smul, pslS_smul_zero, ← h₁])
  · obtain ⟨B, hB⟩ := (atImInfty_mem _).1
      ((eventually_mem_leftHalfPlane_of_infty_mem_boundaryLeftHalfPlane hleft).and
        (eventually_mem_leftHalfPlane_of_infty_mem_boundaryLeftHalfPlane hinf))
    let z₀ : ℍ := ⟨⟨0, max B 0 + 1⟩, by positivity⟩
    obtain ⟨hz₁, hz₂⟩ := hB z₀ (by dsimp [z₀]; linarith [le_max_left B 0])
    rw [leftHalfPlane_mul_pslS, mem_rightHalfPlane_iff] at hz₂
    exact ((mem_leftHalfPlane_iff _ _).1 hz₁).not_gt hz₂

private def parabolaExt (ζ : ℂ) : ℂ := ⟨ζ.re, Complex.normSq ζ⟩

private theorem continuous_parabolaExt : Continuous parabolaExt := by
  unfold parabolaExt; simp only [Complex.mk_eq_add_mul_I]; fun_prop

private theorem parabolaExt_coe (z : ℍ) : parabolaExt (z : ℂ) = parabolaMap z := by
  apply Complex.ext <;> simp [parabolaExt]

private theorem isBounded_and_vertex_ne_infty {Q : ConvexPolygon n}
    (hinf : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)) :
    Bornology.IsBounded (parabolaMap '' Q.carrier) ∧ ∀ i, Q.vertex i ≠ .inr ∞ := by
  obtain ⟨m, ρ, κ, hρ, hκ, hform⟩ := exists_sideForm_eq_of_infty_mem_boundaryLeftHalfPlane hinf
  refine ⟨((isCompact_closedBall (m : ℂ) ρ).image continuous_parabolaExt).isBounded.subset ?_,
    vertex_ne_infty_of_infty_mem hinf⟩
  rintro _ ⟨z, hz, rfl⟩
  have hnot : z ∉ leftHalfPlane (Q.sideGeodesic 0 * pslS) := by
    rw [leftHalfPlane_mul_pslS, mem_rightHalfPlane_iff]
    exact not_lt.2
      ((mem_closure_leftHalfPlane_iff _ _).1 (Q.carrier_subset_closure_leftHalfPlane 0 hz))
  have hnonneg : 0 ≤ sideForm (Q.sideGeodesic 0 * pslS) z :=
    not_lt.1 fun hneg ↦ hnot ((mem_leftHalfPlane_iff_sideForm_neg _ _).2 hneg)
  rw [hform] at hnonneg
  have hnsq : ‖(z : ℂ) - m‖ ^ 2 ≤ ρ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; linarith [nonneg_of_mul_nonneg_right hnonneg hκ]
  refine ⟨(z : ℂ), ?_, parabolaExt_coe z⟩
  rw [mem_closedBall, Complex.dist_eq]; nlinarith [norm_nonneg ((z : ℂ) - m)]

/-! ### Closure and horodisc neighborhoods in parabolic coordinates -/

private def parabolaLift (w : ℂ) : ℂ := ⟨w.re, Real.sqrt (max 0 (w.im - w.re ^ 2))⟩

private theorem continuous_parabolaLift : Continuous parabolaLift := by
  unfold parabolaLift; simp only [Complex.mk_eq_add_mul_I]; fun_prop

private theorem parabolaLift_parabolaMap (z : ℍ) : parabolaLift (parabolaMap z) = (z : ℂ) := by
  apply Complex.ext
  · simp [parabolaLift]
  · simp only [parabolaLift, parabolaMap_re, parabolaMap_im, Complex.normSq_apply, coe_re, coe_im]
    have hsub : z.re * z.re + z.im * z.im - z.re ^ 2 = z.im ^ 2 := by ring
    rw [hsub, max_eq_right (sq_nonneg z.im), Real.sqrt_sq z.im_pos.le]

private theorem eventually_parabolaMap_horodisc {Q : ConvexPolygon n}
    (hne : ∀ i, Q.vertex i ≠ .inr ∞) {g : Fin n → PSL(2, ℝ)}
    (hg : ∀ i ξ, Q.vertex i = .inr ξ → g i • ξ = ∞) (x : ℝ) {A : Fin n → ℝ}
    (hA : ∀ j, Q.vertex j ≠ .inr (x : OnePoint ℝ) → 1 ≤ A j) :
    ∀ᶠ w in 𝓝 (⟨x, x ^ 2⟩ : ℂ), ∀ z ∈ Q.carrier, parabolaMap z = w →
      ∃ i, Q.vertex i = .inr (x : OnePoint ℝ) ∧ A i < (g i • z).im := by
  set K := Q.carrier \ ⋃ j, ⋃ (_ : (Q.vertex j).isRight), {z : ℍ | A j < (g j • z).im}
  have hU₀ : ∀ᶠ ζ in 𝓝 (x : ℂ), ζ ∉ ((↑) : ℍ → ℂ) '' K :=
    ((Q.isCompact_carrier_diff_iUnion g hg A).image continuous_coe).isClosed.isOpen_compl.mem_nhds
      fun ⟨z, _, hz⟩ ↦ z.im_pos.ne' (by simpa using congrArg Complex.im hz)
  have hother (j : Fin n) :
      ∀ᶠ ζ : ℂ in 𝓝 (x : ℂ), Q.vertex j ≠ .inr (x : OnePoint ℝ) →
        ∀ z : ℍ, (z : ℂ) = ζ → (Q.vertex j).isRight → (g j • z).im ≤ A j := by
    by_cases hj : (Q.vertex j).isRight
    · obtain ⟨ξ, hξ⟩ := Sum.isRight_iff.1 hj
      obtain ⟨xj, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hne j (hξ.trans (congrArg _ h))
      by_cases hxj : xj = x
      · subst hxj; exact Eventually.of_forall fun _ hne' ↦ (hne' hξ).elim
      · obtain ⟨c, hc, hgc⟩ := exists_im_smul_eq_div_of_smul_coe_eq_infty (hg j xj hξ)
        have hcont : ContinuousAt (fun ζ : ℂ ↦ ζ.im / (c * Complex.normSq (ζ - xj))) (x : ℂ) :=
          Complex.continuous_im.continuousAt.div (by fun_prop) <| mul_ne_zero hc.ne'
            (Complex.normSq_pos.2 (sub_ne_zero.2 (Complex.ofReal_injective.ne (Ne.symm hxj)))).ne'
        filter_upwards [hcont.eventually (gt_mem_nhds (by simp : (x : ℂ).im /
          (c * Complex.normSq ((x : ℂ) - xj)) < 1))] with ζ hζ hne' z rfl _
        exact (hgc z).symm ▸ hζ.le.trans (hA j hne')
    · exact Eventually.of_forall fun _ _ _ _ hj' ↦ (hj hj').elim
  have hlift : parabolaLift ⟨x, x ^ 2⟩ = (x : ℂ) := by apply Complex.ext <;> simp [parabolaLift]
  have hpull : Tendsto parabolaLift (𝓝 (⟨x, x ^ 2⟩ : ℂ)) (𝓝 (x : ℂ)) :=
    hlift ▸ continuous_parabolaLift.continuousAt
  filter_upwards [hpull.eventually (hU₀.and (Filter.eventually_all.2 hother))] with w ⟨hwK, hwj⟩
    z hz rfl
  rw [parabolaLift_parabolaMap] at hwK hwj
  have hmemU : z ∈ ⋃ j, ⋃ (_ : (Q.vertex j).isRight), {z : ℍ | A j < (g j • z).im} := by
    by_contra hnotU; exact hwK ⟨z, ⟨hz, hnotU⟩, rfl⟩
  obtain ⟨i, hi, hAi⟩ := by simpa only [mem_iUnion, mem_ofPred_eq] using hmemU
  exact ⟨i, by by_contra hne'; exact hAi.not_ge (hwj i hne' z rfl hi), hAi⟩

private theorem mk_sq_mem_closure_parabolaMap_image_carrier {Q : ConvexPolygon n} {i : Fin n}
    {x : ℝ} (hx : Q.vertex i = .inr (x : OnePoint ℝ)) :
    (⟨x, x ^ 2⟩ : ℂ) ∈ closure (parabolaMap '' Q.carrier) := by
  have hg := Q.isGeodesicFromTo_sideGeodesic i; rw [hx] at hg
  have hmem : ∀ᶠ t in atBot, geodesicLine (Q.sideGeodesic i) t ∈ Q.carrier := by
    have hside : ∃ t₀ : ℝ, ∀ t ≤ t₀, geodesicLine (Q.sideGeodesic i) t ∈ Q.side i := by
      rw [Q.side_def, hx]
      rcases hq : Q.vertex (i + 1) with w | η
      · rw [hq] at hg; obtain ⟨hg₀, t₀, rfl⟩ := isGeodesicFromTo_inr_inl.1 hg
        exact ⟨t₀, fun t ht ↦ by rw [← hg₀, ← geodesicLine_image_Iic]; exact ⟨t, ht, rfl⟩⟩
      · rw [hq] at hg; obtain ⟨hg₀, hg₁⟩ := isGeodesicFromTo_inr_inr.1 hg
        exact ⟨0, fun t _ ↦ by
          rw [← hg₀, ← hg₁, ← range_geodesicLine_eq_extGeodesicSegment]; exact ⟨t, rfl⟩⟩
    obtain ⟨t₀, ht₀⟩ := hside
    exact (eventually_le_atBot t₀).mono fun t ht ↦ Q.side_subset_carrier i (ht₀ t ht)
  have hval : parabolaExt (x : ℂ) = ⟨x, x ^ 2⟩ := by apply Complex.ext <;> simp [parabolaExt, sq]
  exact mem_closure_of_tendsto
    ((hval ▸ (continuous_parabolaExt.tendsto (x : ℂ)).comp
      (tendsto_geodesicLine_atBot_coe hg.smul_zero_eq)).congr fun t ↦ parabolaExt_coe _)
    (hmem.mono fun t ht ↦ ⟨_, ht, rfl⟩)

private theorem mem_parabolaMap_image_carrier_of_mem_closure {Q : ConvexPolygon n} {w : ℂ}
    (hw : w ∈ closure (parabolaMap '' Q.carrier)) (hlt : w.re ^ 2 < w.im) :
    w ∈ parabolaMap '' Q.carrier := by
  have hf := isOpenEmbedding_parabolaMap
  obtain ⟨z, rfl⟩ : w ∈ range parabolaMap := by rwa [range_parabolaMap]
  refine ⟨z, ?_, rfl⟩
  rw [← hf.isOpenMap.preimage_closure_image hf.injective hf.continuous Q.carrier Q.isClosed_carrier]
  exact hw

private theorem exists_smul_vertex_eq_infty (Q : ConvexPolygon n) :
    ∃ gQ : Fin n → PSL(2, ℝ), ∀ j η, Q.vertex j = .inr η → gQ j • η = ∞ := by
  have haux (j : Fin n) : ∃ g : PSL(2, ℝ), ∀ η, Q.vertex j = .inr η → g • η = ∞ := by
    rcases _ : Q.vertex j with _ | η
    · exact ⟨1, fun _ h ↦ by simp at h⟩
    · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) η ∞
      exact ⟨g, fun _ h ↦ by rwa [← Sum.inr.inj h]⟩
  exact ⟨fun j ↦ (haux j).choose, fun j ↦ (haux j).choose_spec⟩

private theorem mem_closure_parabolaMap_image_carrier_iff {Q : ConvexPolygon n}
    (hne : ∀ i, Q.vertex i ≠ .inr ∞) (w : ℂ) :
    w ∈ closure (parabolaMap '' Q.carrier) ↔
      w ∈ parabolaMap '' Q.carrier ∨
        ∃ i : Fin n, Q.vertex i = .inr (w.re : OnePoint ℝ) ∧ w = ⟨w.re, w.re ^ 2⟩ := by
  refine ⟨fun hw ↦ ?_, fun h ↦ h.elim (fun hw ↦ subset_closure hw)
    fun ⟨_, hi, hw'⟩ ↦ hw' ▸ mk_sq_mem_closure_parabolaMap_image_carrier hi⟩
  have hle : w.re ^ 2 ≤ w.im :=
    (isClosed_le (Complex.continuous_re.pow 2) Complex.continuous_im).closure_subset_iff.2
      (by rintro _ ⟨z, -, hz⟩; exact hz ▸ (sq_re_lt_im_parabolaMap z).le) hw
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl (mem_parabolaMap_image_carrier_of_mem_closure hw hlt)
  · have hw' : w = ⟨w.re, w.re ^ 2⟩ := Complex.ext rfl heq.symm
    obtain ⟨gQ, hgQ⟩ := exists_smul_vertex_eq_infty Q
    have hev : {w₁ : ℂ | ∀ z ∈ Q.carrier, parabolaMap z = w₁ →
        ∃ i, Q.vertex i = .inr (w.re : OnePoint ℝ) ∧ 1 < (gQ i • z).im} ∈ 𝓝 w :=
      hw' ▸ eventually_parabolaMap_horodisc hne hgQ w.re (A := fun _ ↦ 1) (fun _ _ ↦ le_rfl)
    obtain ⟨w₁, hw₁U, z₁, hz₁, rfl⟩ := mem_closure_iff_nhds.1 hw _ hev
    obtain ⟨j, hj, -⟩ := hw₁U z₁ hz₁ rfl
    exact Or.inr ⟨j, hj, hw'⟩

/-! ### Identification with the closure and the disk compactification -/

section Normalized

variable (P : ConvexPolygon n) (h₀ : PSL(2, ℝ))
  (hQne : ∀ j, (h₀ • P).vertex j ≠ .inr ∞)
  (x : {i : Fin n // (P.vertex i).isRight} → ℝ)
  (hx : ∀ i, (h₀ • P).vertex i.val = .inr (x i : OnePoint ℝ))

private def equivClosureParabolaMapImage :
    P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} ≃
      closure (parabolaMap '' (h₀ • P).carrier) := by
  set Q := h₀ • P
  let toCls : P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} → closure (parabolaMap '' Q.carrier)
    | .inl z => ⟨parabolaMap (h₀ • (z : ℍ)), subset_closure ⟨h₀ • z, by simp [Q, z.property], rfl⟩⟩
    | .inr i => ⟨⟨x i, (x i) ^ 2⟩, mk_sq_mem_closure_parabolaMap_image_carrier (hx i)⟩
  refine Equiv.ofBijective toCls ⟨?_, ?_⟩
  · rintro (z₁ | i₁) (z₂ | i₂) h
    · exact congrArg Sum.inl (Subtype.ext (MulAction.injective h₀
        (isOpenEmbedding_parabolaMap.injective (congrArg Subtype.val h))))
    · have hval : parabolaMap (h₀ • (z₁ : ℍ)) = ⟨x i₂, (x i₂) ^ 2⟩ := congrArg Subtype.val h
      exact (lt_irrefl _ (hval ▸ sq_re_lt_im_parabolaMap (h₀ • (z₁ : ℍ)))).elim
    · have hval : parabolaMap (h₀ • (z₂ : ℍ)) = ⟨x i₁, (x i₁) ^ 2⟩ := (congrArg Subtype.val h).symm
      exact (lt_irrefl _ (hval ▸ sq_re_lt_im_parabolaMap (h₀ • (z₂ : ℍ)))).elim
    · have hre : x i₁ = x i₂ := congrArg (Complex.re ∘ Subtype.val) h
      exact congrArg Sum.inr (Subtype.ext (Q.vertex_injective (by rw [hx i₁, hx i₂, hre])))
  · rintro ⟨w, hw⟩
    rcases (mem_closure_parabolaMap_image_carrier_iff hQne w).1 hw with
      ⟨z, hz, rfl⟩ | ⟨j, hj, hw'⟩
    · exact ⟨.inl ⟨h₀⁻¹ • z, (smul_mem_smul_set_iff (a := h₀)).1 (by simpa [Q] using hz)⟩,
        Subtype.ext (by simp [toCls])⟩
    · have hjP : (P.vertex j).isRight := by
        simp only [Q, vertex_smul] at hj
        cases hv : P.vertex j with | inl z => simp [hv] at hj | inr η => rfl
      have hxj : x ⟨j, hjP⟩ = w.re :=
        OnePoint.coe_injective (Sum.inr.inj ((hx ⟨j, hjP⟩).symm.trans hj))
      exact ⟨.inr ⟨j, hjP⟩, Subtype.ext (by simp [toCls, hxj, ← hw'])⟩

private theorem coe_equivClosureParabolaMapImage_inl (z : P.carrier) :
    (equivClosureParabolaMapImage P h₀ hQne x hx (.inl z) : ℂ) = parabolaMap (h₀ • (z : ℍ)) :=
  rfl

private theorem coe_equivClosureParabolaMapImage_inr (i : {i : Fin n // (P.vertex i).isRight}) :
    (equivClosureParabolaMapImage P h₀ hQne x hx (.inr i) : ℂ) = ⟨x i, (x i) ^ 2⟩ :=
  rfl

private theorem isOpenEmbedding_equivClosureParabolaMapImage_inl :
    IsOpenEmbedding (fun z : P.carrier ↦
      equivClosureParabolaMapImage P h₀ hQne x hx (.inl z)) := by
  set Q := h₀ • P
  have hf := isOpenEmbedding_parabolaMap
  have hcomp : (Subtype.val : closure (parabolaMap '' Q.carrier) → ℂ) ∘
      (fun z : P.carrier ↦ equivClosureParabolaMapImage P h₀ hQne x hx (.inl z)) =
      fun z : P.carrier ↦ parabolaMap (h₀ • (z : ℍ)) :=
    funext (coe_equivClosureParabolaMapImage_inl P h₀ hQne x hx)
  refine ⟨Topology.IsEmbedding.subtypeVal.of_comp_iff.1 <| hcomp.symm ▸
    ((hf.isEmbedding.comp (Homeomorph.smul h₀).isEmbedding).comp .subtypeVal), ?_⟩
  have hrange : range (fun z : P.carrier ↦ equivClosureParabolaMapImage P h₀ hQne x hx (.inl z)) =
      (Subtype.val : closure (parabolaMap '' Q.carrier) → ℂ) ⁻¹' range parabolaMap := by
    ext ⟨w, hw⟩
    simp only [mem_range, mem_preimage, range_parabolaMap, mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz⟩
      have hval : parabolaMap (h₀ • (z : ℍ)) = w := by
        rw [← coe_equivClosureParabolaMapImage_inl P h₀ hQne x hx z, hz]
      exact hval ▸ sq_re_lt_im_parabolaMap (h₀ • (z : ℍ))
    · intro hlt
      obtain ⟨z, hz, rfl⟩ := mem_parabolaMap_image_carrier_of_mem_closure hw hlt
      refine ⟨⟨h₀⁻¹ • z, (smul_mem_smul_set_iff (a := h₀)).1 (by simpa [Q] using hz)⟩,
        Subtype.ext ?_⟩
      rw [coe_equivClosureParabolaMapImage_inl, smul_inv_smul]
  rw [hrange]
  exact hf.isOpen_range.preimage continuous_subtypeVal

private theorem eventually_horodisc_of_equivClosureParabolaMapImage
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (φCls : closure (parabolaMap '' (h₀ • P).carrier) ≃ₜ Y)
    (i : {i : Fin n // (P.vertex i).isRight}) {ξ : OnePoint ℝ} {g : PSL(2, ℝ)}
    (hξ : P.vertex i = .inr ξ) (hgξ : g • ξ = ∞) (B : ℝ) :
    let e := (equivClosureParabolaMapImage P h₀ hQne x hx).trans φCls.toEquiv
    ∀ᶠ u in 𝓝 (e (.inr i)),
      u = e (.inr i) ∨ ∃ z : P.carrier, e (.inl z) = u ∧ B < (g • (z : ℍ)).im := by
  classical
  let Q := h₀ • P; let eCls := equivClosureParabolaMapImage P h₀ hQne x hx
  let e := eCls.trans φCls.toEquiv
  obtain ⟨gQ, hgQ⟩ := exists_smul_vertex_eq_infty Q
  let g' : Fin n → PSL(2, ℝ) := Function.update gQ i.val (g * h₀⁻¹)
  have hg' (j : Fin n) (η : OnePoint ℝ) (hj : Q.vertex j = .inr η) : g' j • η = ∞ := by
    by_cases hji : j = i.val
    · subst hji
      have hη : η = h₀ • ξ := Sum.inr.inj (hj.symm.trans (by simp [Q, hξ]))
      simp [g', hη, mul_smul, hgξ]
    · simpa [g', hji] using hgQ j η hj
  let A : Fin n → ℝ := Function.update (fun _ ↦ (1 : ℝ)) i.val (max B 1)
  have hA (j : Fin n) (hj : Q.vertex j ≠ .inr (x i : OnePoint ℝ)) : 1 ≤ A j := by
    by_cases hji : j = i.val
    · exact (hj (hji ▸ hx i)).elim
    · simp [A, hji]
  have hval_i : (φCls.symm (e (.inr i)) : ℂ) = ⟨x i, (x i) ^ 2⟩ := by
    rw [Equiv.trans_apply, Homeomorph.coe_toEquiv, φCls.symm_apply_apply,
      coe_equivClosureParabolaMapImage_inr]
  have hpull : Tendsto (fun u : Y ↦ (φCls.symm u : ℂ)) (𝓝 (e (.inr i))) (𝓝 ⟨x i, (x i) ^ 2⟩) :=
    hval_i ▸ continuous_subtypeVal.continuousAt.comp (φCls.symm.continuous.tendsto _)
  have hsep : ∀ᶠ u in 𝓝 (e (.inr i)),
      ∀ j : {k : Fin n // (P.vertex k).isRight}, j ≠ i → u ≠ e (.inr j) :=
    Filter.eventually_all.2 fun j ↦ by
      by_cases hji : j = i
      · exact Eventually.of_forall fun _ h ↦ (h hji).elim
      · exact (eventually_ne_nhds (e.injective.ne (Sum.inr_injective.ne (Ne.symm hji)))).mono
          fun _ h _ ↦ h
  filter_upwards [hpull.eventually (eventually_parabolaMap_horodisc hQne hg' (x i) hA), hsep]
    with u hu hne_j
  rcases eq_or_ne u (e (.inr i)) with rfl | hne_u
  · exact Or.inl rfl
  · rcases hsurj : e.symm u with z | j
    · have huz : e (.inl z) = u := by rw [← hsurj, e.apply_symm_apply]
      have hval_z : (φCls.symm u : ℂ) = parabolaMap (h₀ • (z : ℍ)) := by
        rw [← huz, Equiv.trans_apply, Homeomorph.coe_toEquiv, φCls.symm_apply_apply,
          coe_equivClosureParabolaMapImage_inl]
      obtain ⟨k, hk, hAk⟩ := hu (h₀ • z) (by simp [z.property]) hval_z.symm
      obtain rfl : k = i.val := Q.vertex_injective (hk.trans (hx i).symm)
      simp only [A, g', Function.update_self, mul_smul, inv_smul_smul] at hAk
      exact Or.inr ⟨z, huz, (le_max_left B 1).trans_lt hAk⟩
    · have huj : u = e (.inr j) := by rw [← hsurj, e.apply_symm_apply]
      exact (hne_j j (fun h ↦ hne_u (h ▸ huj)) huj).elim

end Normalized

/-- **Adjoining the ideal vertices of a convex hyperbolic polygon gives a closed disk.** For every
convex polygon `P`, there is a bijection `e` from `P.carrier ⊕ {i : Fin n // (P.vertex i).isRight}`
onto `closedBall (0 : ℂ) 1` embedding `P.carrier` openly, carrying `interior P.carrier` onto
`ball (0 : ℂ) 1`, the sides onto `sphere (0 : ℂ) 1` minus the adjoined ideal vertices, and
giving horodisc neighborhoods at every ideal vertex. -/
theorem exists_equiv_closedBall (P : ConvexPolygon n) :
    ∃ e : P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} ≃ closedBall (0 : ℂ) 1,
      IsOpenEmbedding (fun z : P.carrier ↦ e (.inl z)) ∧
      (∀ z : P.carrier, (e (.inl z) : ℂ) ∈ ball (0 : ℂ) 1 ↔ (z : ℍ) ∈ interior P.carrier) ∧
      (∀ z : P.carrier, (e (.inl z) : ℂ) ∈ sphere (0 : ℂ) 1 ↔ ∃ j, (z : ℍ) ∈ P.side j) ∧
      (∀ i : {i : Fin n // (P.vertex i).isRight}, (e (.inr i) : ℂ) ∈ sphere (0 : ℂ) 1) ∧
      ∀ (i : {i : Fin n // (P.vertex i).isRight}) {ξ : OnePoint ℝ} {g : PSL(2, ℝ)},
        P.vertex i = .inr ξ → g • ξ = ∞ → ∀ B : ℝ,
          ∀ᶠ u in 𝓝 (e (.inr i)),
            u = e (.inr i) ∨ ∃ z : P.carrier, e (.inl z) = u ∧ B < (g • (z : ℍ)).im := by
  classical
  obtain ⟨h₀, hinf⟩ := P.exists_smul_infty_mem_boundaryLeftHalfPlane_mul_pslS
  set Q := h₀ • P
  obtain ⟨hbdd, hQne⟩ := isBounded_and_vertex_ne_infty hinf
  set s : Set ℂ := parabolaMap '' Q.carrier
  have hf := isOpenEmbedding_parabolaMap
  obtain ⟨φ, hφint, hφcl, hφfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      Q.convex_parabolaMap_image_carrier
      ((Q.nonempty_interior_carrier.image parabolaMap).mono (hf.isOpenMap.image_interior_subset _))
      hbdd
  have hideal (i : {i : Fin n // (P.vertex i).isRight}) :
      ∃ x : ℝ, Q.vertex i.val = .inr (x : OnePoint ℝ) := by
    obtain ⟨ξ, hξ⟩ := Sum.isRight_iff.1 i.property
    have hQξ : Q.vertex i.val = .inr (h₀ • ξ) := by simp [Q, hξ]
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hQne i.val (hQξ.trans (congrArg _ h))
    exact ⟨x, hQξ.trans (congrArg _ hx.symm)⟩
  choose x hx using hideal
  let φCls : closure s ≃ₜ closedBall (0 : ℂ) 1 :=
    φ.subtype fun w ↦ by rw [← hφcl, φ.injective.mem_set_image]
  let e := (equivClosureParabolaMapImage P h₀ hQne x hx).trans φCls.toEquiv
  have he_inl (z : P.carrier) : (e (.inl z) : ℂ) = φ (parabolaMap (h₀ • (z : ℍ))) := by
    simp [e, φCls, coe_equivClosureParabolaMapImage_inl]
  have he_inr (i : {i : Fin n // (P.vertex i).isRight}) :
      (e (.inr i) : ℂ) = φ ⟨x i, (x i) ^ 2⟩ := by
    simp [e, φCls, coe_equivClosureParabolaMapImage_inr]
  refine ⟨e,
    φCls.isOpenEmbedding.comp (isOpenEmbedding_equivClosureParabolaMapImage_inl P h₀ hQne x hx),
    fun z ↦ ?_, fun z ↦ ?_, fun i ↦ ?_,
    fun i {ξ g} hξ hgξ B ↦
      eventually_horodisc_of_equivClosureParabolaMapImage P h₀ hQne x hx φCls i hξ hgξ B⟩
  · have hQcar : Q.carrier = ⇑(Homeomorph.smul h₀) '' P.carrier :=
      (P.carrier_smul h₀).trans Set.image_smul.symm
    rw [he_inl, ← hφint, φ.injective.mem_set_image, ← mem_preimage,
      hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
      hf.injective.preimage_image, hQcar, ← (Homeomorph.smul h₀).image_interior]
    exact (Homeomorph.smul h₀).injective.mem_set_image
  · rw [he_inl, ← hφfr, φ.injective.mem_set_image, ← mem_preimage,
      hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
      hf.injective.preimage_image, Q.frontier_carrier, mem_iUnion]
    simp_rw [Q, side_smul, smul_mem_smul_set_iff]
  · rw [he_inr, ← hφfr, φ.injective.mem_set_image]
    refine ⟨mk_sq_mem_closure_parabolaMap_image_carrier (hx i), fun hint ↦ ?_⟩
    obtain ⟨z, -, hz⟩ := interior_subset hint
    exact lt_irrefl _ (hz ▸ sq_re_lt_im_parabolaMap z)

end TauCeti.UpperHalfPlane.ConvexPolygon

end
