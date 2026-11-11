/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Collar
public import TauCeti.Analysis.InnerProductSpace.Polar.Det
public import TauCeti.Geometry.Manifold.Morse.Cell.Annulus
public import TauCeti.Geometry.Manifold.Morse.Cell.NegativeDisc
public import TauCeti.Geometry.Manifold.Morse.Cell.Width

/-!
# Comparing the characteristic maps of two Morse charts

Let `ψ₀` and `ψ₁` be two charts of a manifold `M` with values in `ℝⁿ`, centred at the same critical
point of a smooth function `f`, in which

`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`,

and whose targets contain the closed ball of radius `√ε`. Each carries a characteristic map
`χᵢ : (D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`, `w ↦ ψᵢ⁻¹(√ε • (w, 0))`, where `M_a = {f ≤ a}`
(`OpenPartialHomeomorph.morseCharacteristicMap`). Milnor's comparison of the cells attached by
two charts (`TauCeti.morseCellReattachment`) takes as input a homotopy of maps of pairs
`K : χ₁ ≃ χ₀ ∘ h`, that is, a homotopy keeping the boundary sphere in `M_{c-ε}`, for an orthogonal
map `h` of `ℝᵏ`. This file constructs that homotopy
(`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`), when `f⁻¹[c - ε, c]` is compact
and has no critical point below the level `c`, and the transition `ψ₀ ∘ ψ₁⁻¹` is differentiable at
the origin. The orthogonal map is the polar factor `h = A_uu (A_uuᵀ A_uu)^{-1/2}` of the negative
block `A_uu = ι† A ι` of the derivative `A` of the transition at the origin, where `ι : ℝᵏ → ℝⁿ`
extends by zero onto the first `k` coordinates.

The homotopy follows Milnor's Remark 3.3. Fix a small radius `0 < d < 1`. On the boundary
circles of the discs of radius `d` of both cells `f = c - εd²`, and `R` deforms the sublevel
`M_{c-εd²}` onto `M_{c-ε}` across the band without critical points
(`TauCeti.exists_sublevelDeformation`). The unit disc is split into the disc of radius `d` and
the collar `d ≤ ‖w‖ ≤ 1`.

* On the disc of radius `d`, the small negative discs of the two charts are joined by
  `OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean`, staying below `c - ε‖w‖²`.
* On the collar, the annuli of `χ₁` and `χ₀ ∘ h` are joined by
  `ContinuousMap.HomotopyRel.exists_annulus_homotopy`: the annulus of `χ₁` is deformed to the
  retraction track `(s, θ) ↦ R_s(χ₁(d θ))` of its inner circle, the track moves with the inner
  circle, and the deformation is undone for `χ₀ ∘ h`. Throughout, the outer edge of the collar,
  which is the boundary sphere of the disc, stays in `M_{c-ε}`.

The two pieces agree along the circle of radius `d` and are glued by
`TauCeti.TopCat.diskCollar`.

The comparison also holds continuously over a compact parameter space `P`
(`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor_family`). For families of charts
`ψ₀ p`, `ψ₁ p` whose inverses are jointly continuous in `p` and whose transitions have jointly
continuous derivatives near the origin, the polar factors `h p` depend continuously on `p`, and a
single homotopy `K`, continuous in `p`, deforms `χ₁ p` to `χ₀ p ∘ h p` keeping the boundary sphere
in `M_{c-ε}`. These are the homotopies over `P` from which the comparison of the cells attached by
two families of charts is built, as `TauCeti.morseCellReattachment` is built from `K` for a single
pair. The same radius `d` and deformation `R` serve every `p`, and the small negative discs are
joined by `TauCeti.exists_negativeDisc_homotopy_family_of_charts_euclidean`; the single pair of
charts is the case of a one-point parameter space.

When `det A_uu > 0` the polar factor lies in the special orthogonal group and can be removed, so
the attaching maps `∂D^k → M_{c-ε}` of the two charts are homotopic
(`TauCeti.homotopic_morseAttachingMap_of_det_pos`).

The two charts may also be used at different widths: `ψ₀` at width `ε₀` and `ψ₁` at width `ε₁`,
each chart containing only its own closed ball. One compares the charts at the smaller width, where
both balls fit, and then widens the chart with the larger ball through its negative-coordinate
annulus (`OpenPartialHomeomorph.homotopic_morseAttachingMap_comp_retraction`). For any retraction
`r` of the larger lower sublevel onto the smaller one, for instance the retraction of a compact
critical-free band (`TauCeti.exists_sublevelDeformation`), this gives `α₁ ≃ r ∘ α₀ ∘ h` when
`ε₀ ≤ ε₁` (`TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`) and
`r ∘ α₁ ≃ α₀ ∘ h` when `ε₁ ≤ ε₀`
(`TauCeti.exists_homotopic_retraction_comp_morseAttachingMap_polarFactor`), with the same polar
factor `h`, which does not depend on the widths.

## Main results

* `TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`: the characteristic map of `ψ₁` is
  homotopic as a map of pairs to that of `ψ₀` composed with the polar factor of the negative block
  of the transition.
* `TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor_family`: the same comparison for two
  compact families of charts, continuously in the parameter.
* `TauCeti.homotopic_morseAttachingMap_of_det_pos`: when that negative block preserves
  orientation, the two attaching maps are homotopic.
* `TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`,
  `TauCeti.exists_homotopic_retraction_comp_morseAttachingMap_polarFactor`: the comparison of the
  attaching maps of the two charts at unequal widths, through a retraction of the band between
  the two lower sublevels.
* `TauCeti.homotopic_morseAttachingMap_retraction_comp_of_det_pos`,
  `TauCeti.homotopic_retraction_comp_morseAttachingMap_of_det_pos`: at unequal widths, when the
  negative block preserves orientation, the polar factor can be dropped.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval CategoryTheory
open LinearIsometry (piLpExtendByZero)
open scoped ContDiff Manifold

namespace TauCeti

section Assembly

variable {M : Type u} [TopologicalSpace M] {n k : ℕ} {f : M → ℝ} {c ε : ℝ}

/-- The point `(√ε * d) • w` of the closed ball of radius `√ε * d`, for `‖w‖ ≤ 1`. -/
private def smallDiscPoint (ε : ℝ) (d : I) (w : EuclideanSpace ℝ (Fin k)) (hw : ‖w‖ ≤ 1) :
    closedBall (0 : EuclideanSpace ℝ (Fin k)) (√ε * d) :=
  ⟨(√ε * d) • w, by
    rw [mem_closedBall_zero_iff, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg ε) d.2.1)]
    exact mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg ε) d.2.1) hw⟩

private theorem norm_smallDiscPoint_sq (hε : 0 ≤ ε) (d : I) (w : EuclideanSpace ℝ (Fin k))
    (hw : ‖w‖ ≤ 1) :
    ‖(smallDiscPoint ε d w hw : EuclideanSpace ℝ (Fin k))‖ ^ 2 = ε * (d : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  rw [smallDiscPoint, norm_smul, Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg ε) d.2.1),
    mul_pow, mul_pow, Real.sq_sqrt hε]

private theorem map_smallDiscPoint (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (d : I) (w : EuclideanSpace ℝ (Fin k)) (hw : ‖w‖ ≤ 1) :
    g (smallDiscPoint ε d w hw) =
      smallDiscPoint ε d (g w) ((g.norm_map w).trans_le hw) := by
  simp only [smallDiscPoint, map_smul]

/-- Read through a normal-form chart, the small disc point is a point of the cell of width
`ε * d²`. -/
private theorem symm_smallDiscPoint (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hk : k ≤ n) (hε : 0 ≤ ε) (d : I) (w : EuclideanSpace ℝ (Fin k)) (hw : ‖w‖ ≤ 1) :
    ψ.symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) (smallDiscPoint ε d w hw)) =
      ψ.morseCellMap hk (ε * (d : ℝ) ^ 2) w := by
  rw [smallDiscPoint, OpenPartialHomeomorph.morseCellMap_def, map_smul, Real.sqrt_mul hε,
    Real.sqrt_sq d.2.1]

variable {P : Type*} [TopologicalSpace P]
  (ψ₀ ψ₁ : P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 < ε)
  (hball₀ : ∀ p, closedBall 0 √ε ⊆ (ψ₀ p).target) (hball₁ : ∀ p, closedBall 0 √ε ⊆ (ψ₁ p).target)
  (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ p y j ^ 2)
  (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ p y j ^ 2)
  (hs₀ : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1).symm q.2)
    (univ ×ˢ closedBall 0 √ε))
  (hs₁ : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1).symm q.2)
    (univ ×ˢ closedBall 0 √ε))
  (g : P → EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
  (hg : Continuous fun q : P × EuclideanSpace ℝ (Fin k) ↦ g q.1 q.2) (d : I)
  (G : C(P × I × closedBall (0 : EuclideanSpace ℝ (Fin k)) (√ε * d), M))
  (hG0 : ∀ p w, G (p, 0, w) = (ψ₁ p).symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w))
  (hG1 : ∀ p w, G (p, 1, w) = (ψ₀ p).symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) (g p w)))
  (hGf : ∀ p t w, f (G (p, t, w)) ≤ c - ‖(w : EuclideanSpace ℝ (Fin k))‖ ^ 2)
  {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
  (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε})
  (hr : ∀ x, f (r x).val ≤ c - ε)

/-- The identity isometries of `ℝᵏ`, as a family over `P`. -/
private theorem continuous_refl_apply :
    Continuous fun q : P × EuclideanSpace ℝ (Fin k) ↦
      (fun _ : P ↦ LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin k))) q.1 q.2 :=
  continuous_snd

include hG0 hG1 hGf R hr in
/-- The annuli `d ≤ ‖w‖ ≤ 1` of the characteristic maps `χ₁ p` and `χ₀ p ∘ g p` are homotopic,
continuously in `p`, keeping their outer edges in `M_{c-ε}`. Their inner circles run through the
small negative circles given by `G`. -/
private theorem exists_morseAnnulus_homotopy :
    ∃ H : (morseAnnulusFamilyMap ψ₁ hk hε.le hball₁ hf₁ hs₁ (fun _ ↦ .refl ℝ _)
        continuous_refl_apply d).Homotopy (morseAnnulusFamilyMap ψ₀ hk hε.le hball₀ hf₀ hs₀ g hg d),
      (∀ t s, f (H (t, 1, s)) ≤ c - ε) ∧ ∀ t p (θ : TopCat.diskBoundary.{u} k),
        (H (t, 0, p, θ) : M) = G (p, projIcc 0 1 zero_le_one (4 * t - 2),
          smallDiscPoint ε d θ.down.1 (mem_sphere_zero_iff_norm.1 θ.down.2).le) := by
  let Kc : (⟨fun q ↦ morseAnnulusFamilyMap ψ₁ hk hε.le hball₁ hf₁ hs₁ (fun _ ↦ .refl ℝ _)
        continuous_refl_apply d (0, q), by fun_prop⟩ :
      C(P × TopCat.diskBoundary.{u} k, _)).Homotopy
      ⟨fun q ↦ morseAnnulusFamilyMap ψ₀ hk hε.le hball₀ hf₀ hs₀ g hg d (0, q), by fun_prop⟩ :=
    { toFun q := ⟨G (q.2.1, q.1, smallDiscPoint ε d q.2.2.down.1
          (mem_sphere_zero_iff_norm.1 q.2.2.down.2).le), (hGf _ _ _).trans_eq <| by
          rw [norm_smallDiscPoint_sq hε.le, mem_sphere_zero_iff_norm.1 q.2.2.down.2, one_pow,
            mul_one]⟩
      continuous_toFun := (G.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.prodMk (Continuous.subtype_mk (by fun_prop) _)))).subtype_mk _
      map_zero_left q := Subtype.ext <| by
        dsimp only
        rw [hG0, symm_smallDiscPoint (ψ₁ q.1) hk hε.le, ContinuousMap.coe_mk,
          coe_morseAnnulusFamilyMap_zero, LinearIsometryEquiv.coe_refl, id_eq]
      map_one_left q := Subtype.ext <| by
        dsimp only
        rw [hG1, map_smallDiscPoint, symm_smallDiscPoint (ψ₀ q.1) hk hε.le, ContinuousMap.coe_mk,
          coe_morseAnnulusFamilyMap_zero] }
  have hKc (t : I) (p : P) (θ : TopCat.diskBoundary.{u} k) : (Kc (t, p, θ) : M) =
      G (p, t, smallDiscPoint ε d θ.down.1 (mem_sphere_zero_iff_norm.1 θ.down.2).le) := rfl
  obtain ⟨H, hH1, hH0⟩ := R.exists_annulus_homotopy hr
    (fun q ↦ apply_morseAnnulusFamilyMap_one_le ψ₁ hk hε.le hball₁ hf₁ hs₁ _ _ d q.1 q.2)
    (fun q ↦ apply_morseAnnulusFamilyMap_one_le ψ₀ hk hε.le hball₀ hf₀ hs₀ g hg d q.1 q.2) Kc
  exact ⟨H, hH1, fun t p θ ↦ by rw [hH0, hKc]⟩

include hs₀ hs₁ hg hG0 hG1 hGf R hr in
/-- Milnor's comparison of the characteristic maps of two families of charts, given its two
ingredients: a homotopy `G` of the small negative discs of radius `√ε * d`, continuous in the
parameter, that stays below `c - ‖w‖²`, and a deformation `R` of `M_{c-εd²}` onto `M_{c-ε}`. The
homotopy of pairs is `G`, rescaled onto the disc of radius `d`, glued to the homotopy of the
surrounding annuli of `exists_morseAnnulus_homotopy`. The gluing takes place in the space of
continuous maps from `P`, which carries the parameter along. -/
private theorem exists_homotopy_morseCharacteristicMap_of_negativeDisc [LocallyCompactSpace P]
    (hd : 0 < (d : ℝ)) (hd1 : (d : ℝ) < 1) :
    ∃ K : C(I × (P × TopCat.disk.{u} k), {x : M | f x ≤ c + ε}),
      (∀ p w, K (0, p, w) = (ψ₁ p).morseCharacteristicMap hk hε.le (hball₁ p) (hf₁ p) w) ∧
      (∀ p w, K (1, p, w) =
        (ψ₀ p).morseCharacteristicMap hk hε.le (hball₀ p) (hf₀ p) ((g p).diskMap w)) ∧
      ∀ t p (s : TopCat.diskBoundary.{u} k),
        f (K (t, p, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  obtain ⟨H, hH1, hH0⟩ := exists_morseAnnulus_homotopy ψ₀ ψ₁ hk hε hball₀ hball₁ hf₀ hf₁ hs₀ hs₁
    g hg d G hG0 hG1 hGf R hr
  -- The disc piece is `G` at the time at which `H` runs it on its inner circle.
  let τ : C(I, I) := ⟨fun t ↦ projIcc 0 1 zero_le_one (4 * t - 2), by fun_prop⟩
  let inner : C(I × TopCat.disk.{u} k, C(P, {x : M | f x ≤ c + ε})) := ContinuousMap.curry
    ⟨fun q ↦ ⟨G (q.2, τ q.1.1, smallDiscPoint ε d q.1.2.down.1
        (mem_closedBall_zero_iff.1 q.1.2.down.2)),
      (hGf _ _ _).trans (by nlinarith [sq_nonneg ‖(smallDiscPoint ε d q.1.2.down.1
        (mem_closedBall_zero_iff.1 q.1.2.down.2) : EuclideanSpace ℝ (Fin k))‖])⟩,
      (G.continuous.comp (continuous_snd.prodMk ((τ.continuous.comp
        (continuous_fst.comp continuous_fst)).prodMk
          (Continuous.subtype_mk (by fun_prop) _)))).subtype_mk _⟩
  let ιd := sublevelInclusion f (c - ε * (d : ℝ) ^ 2) (c + ε) (by nlinarith [sq_nonneg (d : ℝ)])
  let outer : C(I × (I × TopCat.diskBoundary.{u} k), C(P, {x : M | f x ≤ c + ε})) :=
    ContinuousMap.curry (ιd.comp (H.toContinuousMap.comp
      ⟨fun q ↦ (q.1.1, q.1.2.1, q.2, q.1.2.2), by fun_prop⟩))
  have hinner (t : I) (w : TopCat.disk.{u} k) (p : P) : (inner (t, w) p : M) =
      G (p, τ t, smallDiscPoint ε d w.down.1 (mem_closedBall_zero_iff.1 w.down.2)) := rfl
  have houter (t s : I) (θ : TopCat.diskBoundary.{u} k) (p : P) :
      (outer (t, s, θ) p : M) = H (t, s, p, θ) := by
    simp only [outer, ιd, ContinuousMap.curry_apply, ContinuousMap.comp_apply,
      coe_sublevelInclusion_apply, ContinuousMap.coe_mk, ContinuousMap.Homotopy.coe_toContinuousMap]
  have hseam (t : I) (θ : TopCat.diskBoundary.{u} k) :
      outer (t, 0, θ) = inner (t, TopCat.diskBoundaryInclusion k θ) :=
    ContinuousMap.ext fun p ↦ Subtype.ext <| by
      rw [houter, hH0, hinner]
      simp only [TopCat.coe_diskBoundaryInclusion_apply_down, τ, ContinuousMap.coe_mk]
  have hτ0 : τ 0 = 0 :=
    projIcc_of_le_left zero_le_one (by norm_num : 4 * ((0 : I) : ℝ) - 2 ≤ 0)
  have hτ1 : τ 1 = 1 :=
    projIcc_of_right_le zero_le_one (by norm_num : (1 : ℝ) ≤ 4 * ((1 : I) : ℝ) - 2)
  -- Glue; at the two ends the pieces are the two characteristic maps in polar coordinates.
  let K := TopCat.diskCollar hd inner outer hseam
  have hK (t : I) (p : P) (w : TopCat.disk.{u} k) :
      (K.uncurry.comp ⟨fun q : I × (P × TopCat.disk.{u} k) ↦ ((q.1, q.2.2), q.2.1), by fun_prop⟩)
        (t, p, w) = K (t, w) p := rfl
  refine ⟨K.uncurry.comp ⟨fun q ↦ ((q.1, q.2.2), q.2.1), by fun_prop⟩, fun p w ↦ ?_,
    fun p w ↦ ?_, fun t p s ↦ ?_⟩
  · rw [hK]
    exact Subtype.ext <| (TopCat.apply_diskCollar_eq_of_radial hd _ _ hseam hd1
      (fun F ↦ (F p : M)) (Φ := (ψ₁ p).morseCellMap hk ε)
      (fun y ↦ by rw [hinner, hτ0, hG0, symm_smallDiscPoint (ψ₁ p) hk hε.le,
        OpenPartialHomeomorph.morseCellMap_smul hk d.2.1])
      (fun s θ ↦ by rw [houter, ContinuousMap.Homotopy.apply_zero,
        coe_morseAnnulusFamilyMap_apply, LinearIsometryEquiv.coe_refl, id_eq]) w).trans
      (OpenPartialHomeomorph.coe_morseCharacteristicMap_apply (hball₁ p) (hf₁ p) hk hε.le w).symm
  · rw [hK]
    exact Subtype.ext <| (TopCat.apply_diskCollar_eq_of_radial hd _ _ hseam hd1
      (fun F ↦ (F p : M)) (Φ := fun v ↦ (ψ₀ p).morseCellMap hk ε (g p v))
      (fun y ↦ by rw [hinner, hτ1, hG1, map_smallDiscPoint, symm_smallDiscPoint (ψ₀ p) hk hε.le,
        map_smul, OpenPartialHomeomorph.morseCellMap_smul hk d.2.1])
      (fun s θ ↦ by rw [houter, ContinuousMap.Homotopy.apply_one,
        coe_morseAnnulusFamilyMap_apply]) w).trans <|
      ((OpenPartialHomeomorph.coe_morseCharacteristicMap_apply (hball₀ p) (hf₀ p) hk hε.le
        ((g p).diskMap w)).trans (congrArg _ ((g p).coe_diskMap_apply_down w))).symm
  · rw [hK, TopCat.diskCollar_diskBoundaryInclusion hd _ _ hseam hd1 t s]
    exact (houter t 1 s p).symm ▸ hH1 t (p, s)

end Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n k : ℕ}

/-- **The characteristic maps of two Morse charts are homotopic as maps of pairs, up to the
polar factor of their transition.** Let `ψ₀` and `ψ₁` be charts with a common centre in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain the closed ball of radius `√ε`
and whose transition `ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin, with derivative `A`. Suppose
that `f⁻¹[c - ε, c]` is compact and that `f` has no critical point with value in `[c - ε, c)`.
Let `g` be the polar factor of the negative block `ι† A ι` of `A`, where `ι : ℝᵏ → ℝⁿ` extends by
zero onto the first `k` coordinates. Then `g` is a linear isometry, and the characteristic map
`χ₁ : D^k → M_{c+ε}` of `ψ₁` is homotopic to `χ₀ ∘ g` through maps sending the boundary sphere
into the lower sublevel `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_polarFactor (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 < ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∧
      ∃ K : (ψ₁.morseCharacteristicMap hk hε.le hball₁ hf₁).hom.Homotopy
          (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε.le hball₀ hf₀).hom,
        ∀ t (s : TopCat.diskBoundary.{u} k),
          f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  have h0 (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hball : closedBall 0 √ε ⊆ ψ.target) : (0 : EuclideanSpace ℝ (Fin n)) ∈ ψ.target :=
    hball (mem_closedBall_self (Real.sqrt_nonneg ε))
  obtain ⟨g, hg, δ₀, hδ₀, hG⟩ := OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean
    ψ₀ ψ₁ hk hf₀ hf₁ (h0 ψ₀ hball₀) (h0 ψ₁ hball₁) hp hT
  -- Compare the negative discs of radius `√ε * d`, for some `0 < d < 1`.
  have hsε : 0 < √ε := Real.sqrt_pos.2 hε
  have hd : 0 < min (1 / 2) (δ₀ / √ε) := lt_min (by norm_num) (div_pos hδ₀ hsε)
  set d : I := ⟨min (1 / 2) (δ₀ / √ε), hd.le, (min_le_left _ _).trans (by norm_num)⟩
  obtain ⟨G, hG0, hG1, hGf⟩ := hG (√ε * d) ⟨mul_pos hsε hd,
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hsε.le).trans_eq (mul_div_cancel₀ _ hsε.ne')⟩
  -- Deform `M_{c-εd²}` onto `M_{c-ε}` across the band without critical points.
  have hεd : 0 < ε * (d : ℝ) ^ 2 := by positivity
  have hab : c - ε ≤ c - ε * (d : ℝ) ^ 2 :=
    sub_le_sub_left (mul_le_of_le_one_right hε.le (pow_le_one₀ d.2.1 d.2.2)) c
  obtain ⟨r₀, -, ⟨R₀⟩⟩ := exists_sublevelDeformation hf hab
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc le_rfl (by linarith))))
    (fun x h₁ h₂ ↦ hreg x h₁ (by linarith))
  have hs (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hball : closedBall 0 √ε ⊆ ψ.target) :
      ContinuousOn (fun q : Unit × EuclideanSpace ℝ (Fin n) ↦ ψ.symm q.2)
        (univ ×ˢ closedBall 0 √ε) :=
    ψ.continuousOn_symm.comp continuousOn_snd fun q hq ↦ hball hq.2
  -- Apply the comparison of families to the constant families over a point.
  obtain ⟨K, hK0, hK1, hKb⟩ := exists_homotopy_morseCharacteristicMap_of_negativeDisc
    (fun _ : Unit ↦ ψ₀) (fun _ ↦ ψ₁) hk hε (fun _ ↦ hball₀) (fun _ ↦ hball₁) (fun _ ↦ hf₀)
    (fun _ ↦ hf₁) (hs ψ₀ hball₀) (hs ψ₁ hball₁) (fun _ ↦ g) (g.continuous.comp continuous_snd) d
    (G.comp ⟨fun q ↦ q.2, by fun_prop⟩) (fun _ w ↦ hG0 w) (fun _ w ↦ hG1 w) (fun _ t w ↦ hGf t w)
    R₀.symm (fun x ↦ by
      rw [ContinuousMap.comp_apply, coe_sublevelInclusion_apply]
      exact (r₀ x).property) hd ((min_le_left _ _).trans_lt (by norm_num))
  exact ⟨g, hg, ⟨K.comp ⟨fun q ↦ (q.1, (), q.2), by fun_prop⟩, fun w ↦ hK0 () w,
    fun w ↦ hK1 () w⟩, fun t s ↦ hKb t () s⟩

/-- **The characteristic maps of two compact families of Morse charts are homotopic as maps of
pairs, continuously in the parameter, up to the polar factors of their transitions.** Let `ψ₀ p`
and `ψ₁ p`, for `p` in a compact space `P`, be charts with a common centre in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²` and whose targets contain the closed ball of radius `√ε`.
Suppose that their inverses are jointly continuous in `p` and the point on that ball, and that on a
ball of radius `r` about the origin the transitions `ψ₀ p ∘ (ψ₁ p)⁻¹` are defined and
differentiable with derivatives `D p y` jointly continuous in `p` and `y`. Suppose that
`f⁻¹[c - ε, c]` is compact and that `f` has no critical point with value in `[c - ε, c)`. Let
`g p` be the polar factor of the negative block `ι† (D p 0) ι` of `D p 0`, where `ι : ℝᵏ → ℝⁿ`
extends by zero onto the first `k` coordinates. Then each `g p` is a linear isometry depending
continuously on `p`, and a single homotopy `K`, continuous in `p`, deforms the characteristic maps
`χ₁ p : D^k → M_{c+ε}` of the charts `ψ₁ p` to the maps `χ₀ p ∘ g p`, through maps sending the
boundary sphere into the lower sublevel `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_polarFactor_family (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [LocallyCompactSpace P]
    (ψ₀ ψ₁ : P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 < ε)
    (hball₀ : ∀ p, closedBall 0 √ε ⊆ (ψ₀ p).target)
    (hball₁ : ∀ p, closedBall 0 √ε ⊆ (ψ₁ p).target)
    (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ p y j ^ 2)
    (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ p y j ^ 2)
    (hs₀ : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ p, (ψ₀ p).symm 0 = (ψ₁ p).symm 0) {r : ℝ} (hr : 0 < r)
    (htr : ∀ p, ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ (ψ₁ p).symm ⁻¹' (ψ₀ p).source)
    {D : P → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      HasFDerivAt (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) (D p y) y)
    (hD : ContinuousOn (Function.uncurry D) (univ ×ˢ ball 0 r))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ g : P → EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      (∀ p, ⇑(g p) = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D p 0 ∘L
            (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor) ∧
      Continuous (fun p ↦ (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D p 0 ∘L
            (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor) ∧
      ∃ K : C(I × (P × TopCat.disk.{u} k), {x : M | f x ≤ c + ε}),
        (∀ p w, K (0, p, w) = (ψ₁ p).morseCharacteristicMap hk hε.le (hball₁ p) (hf₁ p) w) ∧
        (∀ p w, K (1, p, w) =
          (ψ₀ p).morseCharacteristicMap hk hε.le (hball₀ p) (hf₀ p) ((g p).diskMap w)) ∧
        ∀ t p (s : TopCat.diskBoundary.{u} k),
          f (K (t, p, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  have hsε : 0 < √ε := Real.sqrt_pos.2 hε
  -- Work on a ball inside both the ball of radius `r` and the closed ball of radius `√ε`.
  have hr₀ : 0 < min r √ε := lt_min hr hsε
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) (min r √ε) ⊆ closedBall 0 √ε :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))
  have hsubr : ball (0 : EuclideanSpace ℝ (Fin n)) (min r √ε) ⊆ ball 0 r :=
    ball_subset_ball (min_le_left _ _)
  obtain ⟨hcont, δ₀, hδ₀, hG⟩ := exists_negativeDisc_homotopy_family_of_charts_euclidean ψ₀ ψ₁ hk
    hf₀ hf₁ hp hr₀ (fun p ↦ hsub.trans (hball₀ p)) (fun p _ hy ↦ ⟨hball₁ p (hsub hy),
      htr p (hsubr hy)⟩) (hs₀.mono (prod_mono subset_rfl hsub))
    (fun p y hy ↦ hT p y (hsubr hy)) (hD.mono (prod_mono subset_rfl hsubr))
  -- Each polar factor is a linear isometry, by the comparison of the single pair at `p`.
  have hiso (p : P) : ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
        (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D p 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor := by
    obtain ⟨g, hg, -⟩ := OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean (ψ₀ p)
      (ψ₁ p) hk (hf₀ p) (hf₁ p) (hball₀ p (mem_closedBall_self hsε.le))
      (hball₁ p (mem_closedBall_self hsε.le)) (hp p)
      (hT p 0 (mem_ball_self hr)).differentiableAt
    exact ⟨g, by rw [hg, (hT p 0 (mem_ball_self hr)).fderiv]⟩
  choose g hg using hiso
  have hgc : Continuous fun q : P × EuclideanSpace ℝ (Fin k) ↦ g q.1 q.2 :=
    ((hcont.comp continuous_fst).clm_apply continuous_snd).congr fun q ↦ by
      simp only [Function.comp_apply, hg]
  -- Compare the negative discs of radius `√ε * d`, for some `0 < d < 1`.
  have hd : 0 < min (1 / 2) (δ₀ / √ε) := lt_min (by norm_num) (div_pos hδ₀ hsε)
  set d : I := ⟨min (1 / 2) (δ₀ / √ε), hd.le, (min_le_left _ _).trans (by norm_num)⟩
  obtain ⟨G, hG0, hG1, hGf⟩ := hG (√ε * d) ⟨mul_pos hsε hd,
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hsε.le).trans_eq (mul_div_cancel₀ _ hsε.ne')⟩
  -- Deform `M_{c-εd²}` onto `M_{c-ε}` across the band without critical points.
  have hεd : 0 < ε * (d : ℝ) ^ 2 := by positivity
  have hab : c - ε ≤ c - ε * (d : ℝ) ^ 2 :=
    sub_le_sub_left (mul_le_of_le_one_right hε.le (pow_le_one₀ d.2.1 d.2.2)) c
  obtain ⟨r₀, -, ⟨R₀⟩⟩ := exists_sublevelDeformation hf hab
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc le_rfl (by linarith))))
    (fun x h₁ h₂ ↦ hreg x h₁ (by linarith))
  refine ⟨g, hg, hcont, exists_homotopy_morseCharacteristicMap_of_negativeDisc ψ₀ ψ₁ hk hε hball₀
    hball₁ hf₀ hf₁ hs₀ hs₁ g hgc d G hG0 (fun p w ↦ by rw [hG1, hg]) hGf R₀.symm (fun x ↦ ?_) hd
    ((min_le_left _ _).trans_lt (by norm_num))⟩
  rw [ContinuousMap.comp_apply, coe_sublevelInclusion_apply]
  exact (r₀ x).property

/-- **Two Morse charts whose negative blocks preserve orientation have homotopic attaching
maps.** Under the hypotheses of `TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`, if
the negative block `ι† A ι` of the derivative `A` of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin has
positive determinant, then the attaching maps `∂D^k → M_{c-ε}` of the two charts are homotopic. -/
theorem homotopic_morseAttachingMap_of_det_pos (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 < ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (hdet : 0 < (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).det) :
    (ψ₁.morseAttachingMap hk hε.le hball₁ hf₁).hom.Homotopic
      (ψ₀.morseAttachingMap hk hε.le hball₀ hf₀).hom := by
  obtain ⟨g, hg, K, hK⟩ := exists_homotopy_morseCharacteristicMap_polarFactor hf ψ₀ ψ₁ hk hε
    hball₀ hball₁ hf₀ hf₁ hp hT hcompact hreg
  refine homotopic_morseAttachingMap_of_det_eq_one hk hε.le hball₀ hball₁ hf₀ hf₁ ?_ K hK
  have hg' : g.toLinearMap = ((ContinuousLinearMap.adjoint
      (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor :
            EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :=
    LinearMap.ext (congrFun hg)
  rw [hg']
  exact ContinuousLinearMap.det_polarFactor_eq_one_iff.2 hdet

section UnequalLevels

variable {ε₀ ε₁ : ℝ}

/-- **Attaching maps of two Morse charts at unequal levels, lower level for the first chart.**
Let `ψ₀` and `ψ₁` be charts with a common centre in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, with `0 < ε₀ ≤ ε₁`, such that the target of `ψ₀`
contains the closed ball of radius `√ε₀` and that of `ψ₁` the closed ball of radius `√ε₁`, and
whose transition `ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin. Suppose that `f⁻¹[c - ε₀, c]` is
compact and that `f` has no critical point with value in `[c - ε₀, c)`. Let `g` be the polar
factor of the negative block of the derivative of the transition, as in
`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`, and let `r` be any retraction of
`M_{c-ε₀}` onto `M_{c-ε₁}`. Then the attaching map `α₁ : ∂D^k → M_{c-ε₁}` of `ψ₁` at width `ε₁`
is homotopic to `r ∘ α₀ ∘ g`, where `α₀` is the attaching map of `ψ₀` at width `ε₀`. The chart
`ψ₀` need not contain the closed ball of radius `√ε₁`. -/
theorem exists_homotopic_morseAttachingMap_retraction_comp_polarFactor
    (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₀ : 0 < ε₀)
    (hε : ε₀ ≤ ε₁) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₀) c))
    (hreg : ∀ x, c - ε₀ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₀}, {x : M | f x ≤ c - ε₁}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₁) (c - ε₀) (sub_le_sub_left hε c) x) = x) :
    ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∧
      (ψ₁.morseAttachingMap hk (h₀.le.trans hε) hball₁ hf₁).hom.Homotopic
        (r.comp (g.diskBoundaryMap ≫ ψ₀.morseAttachingMap hk h₀.le hball₀ hf₀).hom) := by
  have hball₁' : closedBall 0 √ε₀ ⊆ ψ₁.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₁
  -- Compare the two charts at the common width `ε₀`, then widen `ψ₁` to `ε₁`.
  obtain ⟨g, hg, K, hK⟩ := exists_homotopy_morseCharacteristicMap_polarFactor hf ψ₀ ψ₁ hk h₀
    hball₀ hball₁' hf₀ hf₁ hp hT hcompact hreg
  refine ⟨g, hg, ?_⟩
  exact (ψ₁.homotopic_morseAttachingMap_comp_retraction hk h₀.le hε hball₁ hf₁ r hr).symm.trans
    ((ContinuousMap.Homotopic.refl r).comp
      (homotopic_morseAttachingMap_diskBoundaryMap_comp hk h₀.le hball₀ hball₁' hf₀ hf₁ K hK))

/-- **Attaching maps of two Morse charts at unequal levels, lower level for the second chart.**
This is the counterpart of `TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`
for `0 < ε₁ ≤ ε₀`, where now the target of `ψ₀` contains the closed ball of radius `√ε₀` and that
of `ψ₁` the closed ball of radius `√ε₁`. Suppose that `f⁻¹[c - ε₁, c]` is compact and that `f` has
no critical point with value in `[c - ε₁, c)`, and let `r` be any retraction of `M_{c-ε₁}` onto
`M_{c-ε₀}`. Then `r ∘ α₁` is homotopic to `α₀ ∘ g`, where `α₁` is the attaching map of `ψ₁` at
width `ε₁`, `α₀` that of `ψ₀` at width `ε₀`, and `g` the polar factor of the negative block of the
derivative of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin. The chart `ψ₁` need not contain the closed
ball of radius `√ε₀`. -/
theorem exists_homotopic_retraction_comp_morseAttachingMap_polarFactor
    (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₁ : 0 < ε₁)
    (hε : ε₁ ≤ ε₀) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₁) c))
    (hreg : ∀ x, c - ε₁ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₁}, {x : M | f x ≤ c - ε₀}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₀) (c - ε₁) (sub_le_sub_left hε c) x) = x) :
    ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∧
      (r.comp (ψ₁.morseAttachingMap hk h₁.le hball₁ hf₁).hom).Homotopic
        (g.diskBoundaryMap ≫ ψ₀.morseAttachingMap hk (h₁.le.trans hε) hball₀ hf₀).hom := by
  have hball₀' : closedBall 0 √ε₁ ⊆ ψ₀.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₀
  -- Compare the two charts at the common width `ε₁`, then widen `ψ₀` to `ε₀`.
  obtain ⟨g, hg, K, hK⟩ := exists_homotopy_morseCharacteristicMap_polarFactor hf ψ₀ ψ₁ hk h₁
    hball₀' hball₁ hf₀ hf₁ hp hT hcompact hreg
  refine ⟨g, hg, ?_⟩
  have hwiden := (ψ₀.homotopic_morseAttachingMap_comp_retraction hk h₁.le hε hball₀ hf₀ r hr).comp
    (ContinuousMap.Homotopic.refl g.diskBoundaryMap.hom)
  rw [ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← TopCat.hom_comp] at hwiden
  exact ((ContinuousMap.Homotopic.refl r).comp
    (homotopic_morseAttachingMap_diskBoundaryMap_comp hk h₁.le hball₀' hball₁ hf₀ hf₁ K hK)).trans
    hwiden

/-- **Orientation-compatible Morse charts have homotopic attaching maps at unequal levels, lower
level for the first chart.** Under the hypotheses of
`TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`, if the negative block
of the derivative of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin has positive determinant, then the
attaching map `α₁ : ∂D^k → M_{c-ε₁}` of `ψ₁` at width `ε₁` is homotopic to `r ∘ α₀`, where `α₀` is
the attaching map of `ψ₀` at width `ε₀ ≤ ε₁` and `r` is any retraction of `M_{c-ε₀}` onto
`M_{c-ε₁}`. -/
theorem homotopic_morseAttachingMap_retraction_comp_of_det_pos (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₀ : 0 < ε₀)
    (hε : ε₀ ≤ ε₁) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₀) c))
    (hreg : ∀ x, c - ε₀ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₀}, {x : M | f x ≤ c - ε₁}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₁) (c - ε₀) (sub_le_sub_left hε c) x) = x)
    (hdet : 0 < (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).det) :
    (ψ₁.morseAttachingMap hk (h₀.le.trans hε) hball₁ hf₁).hom.Homotopic
      (r.comp (ψ₀.morseAttachingMap hk h₀.le hball₀ hf₀).hom) := by
  have hball₁' : closedBall 0 √ε₀ ⊆ ψ₁.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₁
  exact (ψ₁.homotopic_morseAttachingMap_comp_retraction hk h₀.le hε hball₁ hf₁ r hr).symm.trans
    ((ContinuousMap.Homotopic.refl r).comp (homotopic_morseAttachingMap_of_det_pos hf ψ₀ ψ₁ hk h₀
      hball₀ hball₁' hf₀ hf₁ hp hT hcompact hreg hdet))

/-- **Orientation-compatible Morse charts have homotopic attaching maps at unequal levels, lower
level for the second chart.** Under the hypotheses of
`TauCeti.exists_homotopic_retraction_comp_morseAttachingMap_polarFactor`, if the negative block
of the derivative of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin has positive determinant, then
`r ∘ α₁` is homotopic to `α₀`, where `α₁` is the attaching map of `ψ₁` at width `ε₁`, `α₀` that
of `ψ₀` at width `ε₀ ≥ ε₁`, and `r` is any retraction of `M_{c-ε₁}` onto `M_{c-ε₀}`. -/
theorem homotopic_retraction_comp_morseAttachingMap_of_det_pos (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₁ : 0 < ε₁)
    (hε : ε₁ ≤ ε₀) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₁) c))
    (hreg : ∀ x, c - ε₁ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₁}, {x : M | f x ≤ c - ε₀}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₀) (c - ε₁) (sub_le_sub_left hε c) x) = x)
    (hdet : 0 < (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).det) :
    (r.comp (ψ₁.morseAttachingMap hk h₁.le hball₁ hf₁).hom).Homotopic
      (ψ₀.morseAttachingMap hk (h₁.le.trans hε) hball₀ hf₀).hom := by
  have hball₀' : closedBall 0 √ε₁ ⊆ ψ₀.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₀
  exact ((ContinuousMap.Homotopic.refl r).comp (homotopic_morseAttachingMap_of_det_pos hf ψ₀ ψ₁ hk
    h₁ hball₀' hball₁ hf₀ hf₁ hp hT hcompact hreg hdet)).trans
    (ψ₀.homotopic_morseAttachingMap_comp_retraction hk h₁.le hε hball₀ hf₀ r hr)

end UnequalLevels

end TauCeti
