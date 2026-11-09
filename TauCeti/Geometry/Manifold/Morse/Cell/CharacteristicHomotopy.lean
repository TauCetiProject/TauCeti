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
  `OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean`, staying below `c - ‖w‖²`.
* On the collar, the annuli of `χ₁` and `χ₀ ∘ h` are joined by
  `ContinuousMap.HomotopyRel.exists_annulus_homotopy`: the annulus of `χ₁` is deformed to the
  retraction track `(s, θ) ↦ R_s(χ₁(d θ))` of its inner circle, the track moves with the inner
  circle, and the deformation is undone for `χ₀ ∘ h`. Throughout, the outer edge of the collar,
  which is the boundary sphere of the disc, stays in `M_{c-ε}`.

The two pieces agree along the circle of radius `d` and are glued by
`TauCeti.TopCat.diskCollar`.

When `det A_uu > 0` the polar factor lies in the special orthogonal group and can be removed, so
the attaching maps `∂D^k → M_{c-ε}` of the two charts are homotopic
(`TauCeti.homotopic_morseAttachingMap_of_det_pos`).

## Main results

* `TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`: the characteristic map of `ψ₁` is
  homotopic as a map of pairs to that of `ψ₀` composed with the polar factor of the negative block
  of the transition.
* `TauCeti.homotopic_morseAttachingMap_of_det_pos`: when that negative block preserves
  orientation, the two attaching maps are homotopic.

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

section Annulus

variable {M : Type u} [TopologicalSpace M] {n k : ℕ} {f : M → ℝ} {c ε : ℝ}

/-- The negative-coordinate annulus `OpenPartialHomeomorph.morseAnnulusMap` of a Morse chart,
reparametrized by a linear isometry `g` of `ℝᵏ`: `(s, θ) ↦ ψ⁻¹(√ε • (r • g θ, 0))` with radius
`r = d + (1 - d) s`. -/
private def morseAnnulusIsometryMap (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hk : k ≤ n) (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (d : I) :
    C(I × TopCat.diskBoundary.{u} k, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}) :=
  (ψ.morseAnnulusMap hk hε hball hf d).comp ((ContinuousMap.id I).prodMap g.diskBoundaryMap.hom)

variable (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 ≤ ε)
  (hball : closedBall 0 √ε ⊆ ψ.target)
  (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
  (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (d : I)

private theorem coe_morseAnnulusIsometryMap_apply (s : I) (θ : TopCat.diskBoundary.{u} k) :
    (morseAnnulusIsometryMap ψ hk hε hball hf g d (s, θ) : M) =
      ψ.morseCellMap hk ε (g (((d : ℝ) + (1 - d) * s) • θ.down.1)) := by
  rw [morseAnnulusIsometryMap, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    Prod.map_apply, ContinuousMap.id_apply, ψ.coe_morseAnnulusMap_apply,
    LinearIsometryEquiv.coe_diskBoundaryMap_apply_down, map_smul]
  congr 3
  simp only [unitInterval.coe_symm_eq, Set.Icc.coe_mul]
  ring

private theorem coe_morseAnnulusIsometryMap_zero (θ : TopCat.diskBoundary.{u} k) :
    (morseAnnulusIsometryMap ψ hk hε hball hf g d (0, θ) : M) =
      ψ.morseCellMap hk (ε * (d : ℝ) ^ 2) (g θ.down.1) := by
  rw [coe_morseAnnulusIsometryMap_apply, Set.Icc.coe_zero, mul_zero, add_zero, map_smul,
    OpenPartialHomeomorph.morseCellMap_smul hk d.2.1]

private theorem apply_morseAnnulusIsometryMap_one_le (θ : TopCat.diskBoundary.{u} k) :
    f (morseAnnulusIsometryMap ψ hk hε hball hf g d (1, θ)) ≤ c - ε := by
  rw [morseAnnulusIsometryMap, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    Prod.map_apply, ContinuousMap.id_apply, ψ.coe_morseAnnulusMap_one]
  exact (ψ.morseAttachingMap hk hε hball hf _).property

end Annulus

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

variable (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 < ε)
  (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
  (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
  (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
  (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (d : I)
  (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) (√ε * d), M))
  (hG0 : ∀ w, G (0, w) = ψ₁.symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w))
  (hG1 : ∀ w, G (1, w) = ψ₀.symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) (g w)))
  (hGf : ∀ t w, f (G (t, w)) ≤ c - ‖(w : EuclideanSpace ℝ (Fin k))‖ ^ 2)
  {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
  (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε})
  (hr : ∀ x, f (r x).val ≤ c - ε)

include hG0 hG1 hGf R hr in
/-- The annuli `d ≤ ‖w‖ ≤ 1` of the characteristic maps `χ₁` and `χ₀ ∘ g` are homotopic,
keeping their outer edges in `M_{c-ε}`. Their inner circles run through the small negative
circles given by `G`. -/
private theorem exists_morseAnnulus_homotopy :
    ∃ H : (morseAnnulusIsometryMap ψ₁ hk hε.le hball₁ hf₁ (.refl ℝ _) d).Homotopy
        (morseAnnulusIsometryMap ψ₀ hk hε.le hball₀ hf₀ g d),
      (∀ t s, f (H (t, 1, s)) ≤ c - ε) ∧ ∀ t (θ : TopCat.diskBoundary.{u} k),
        (H (t, 0, θ) : M) = G (projIcc 0 1 zero_le_one (4 * t - 2),
          smallDiscPoint ε d θ.down.1 (mem_sphere_zero_iff_norm.1 θ.down.2).le) := by
  let Kc : (⟨fun θ ↦ morseAnnulusIsometryMap ψ₁ hk hε.le hball₁ hf₁ (.refl ℝ _) d (0, θ),
      by fun_prop⟩ : C(TopCat.diskBoundary.{u} k, _)).Homotopy
      ⟨fun θ ↦ morseAnnulusIsometryMap ψ₀ hk hε.le hball₀ hf₀ g d (0, θ), by fun_prop⟩ :=
    { toFun p := ⟨G (p.1, smallDiscPoint ε d p.2.down.1
          (mem_sphere_zero_iff_norm.1 p.2.down.2).le), (hGf _ _).trans_eq <| by
          rw [norm_smallDiscPoint_sq hε.le, mem_sphere_zero_iff_norm.1 p.2.down.2, one_pow,
            mul_one]⟩
      continuous_toFun := (G.continuous.comp (continuous_fst.prodMk
        (Continuous.subtype_mk (by fun_prop) _))).subtype_mk _
      map_zero_left θ := Subtype.ext <| by
        dsimp only
        rw [hG0, symm_smallDiscPoint ψ₁ hk hε.le, ContinuousMap.coe_mk,
          coe_morseAnnulusIsometryMap_zero, LinearIsometryEquiv.coe_refl, id_eq]
      map_one_left θ := Subtype.ext <| by
        dsimp only
        rw [hG1, map_smallDiscPoint, symm_smallDiscPoint ψ₀ hk hε.le, ContinuousMap.coe_mk,
          coe_morseAnnulusIsometryMap_zero] }
  obtain ⟨H, hH1, hH0⟩ := R.exists_annulus_homotopy hr (ContinuousMap.id I) rfl rfl
    (apply_morseAnnulusIsometryMap_one_le ψ₁ hk hε.le hball₁ hf₁ _ d)
    (apply_morseAnnulusIsometryMap_one_le ψ₀ hk hε.le hball₀ hf₀ g d) Kc
  exact ⟨H, hH1, fun t θ ↦ by rw [hH0]; rfl⟩

include hG0 hG1 hGf R hr in
/-- Milnor's comparison of two characteristic maps, given its two ingredients: a homotopy `G` of
the small negative discs of radius `√ε * d` that stays below `c - ‖w‖²`, and a deformation `R` of
`M_{c-εd²}` onto `M_{c-ε}`. The homotopy of pairs is `G`, rescaled onto the disc of radius `d`,
glued to the homotopy of the surrounding annuli of `exists_morseAnnulus_homotopy`. -/
private theorem exists_homotopy_morseCharacteristicMap_of_negativeDisc (hd : 0 < (d : ℝ))
    (hd1 : (d : ℝ) < 1) :
    ∃ K : (ψ₁.morseCharacteristicMap hk hε.le hball₁ hf₁).hom.Homotopy
        (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε.le hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{u} k), f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  obtain ⟨H, hH1, hH0⟩ := exists_morseAnnulus_homotopy ψ₀ ψ₁ hk hε hball₀ hball₁ hf₀ hf₁ g d G
    hG0 hG1 hGf R hr
  have hεd : 0 ≤ ε * (d : ℝ) ^ 2 := by positivity
  -- The disc piece is `G` at the time at which `H` runs it on its inner circle.
  let τ : C(I, I) := ⟨fun t ↦ projIcc 0 1 zero_le_one (4 * t - 2), by fun_prop⟩
  let inner : C(I × TopCat.disk.{u} k, {x : M | f x ≤ c + ε}) :=
    ⟨fun p ↦ ⟨G (τ p.1, smallDiscPoint ε d p.2.down.1 (mem_closedBall_zero_iff.1 p.2.down.2)),
      (hGf _ _).trans (by nlinarith [sq_nonneg ‖(smallDiscPoint ε d p.2.down.1
        (mem_closedBall_zero_iff.1 p.2.down.2) : EuclideanSpace ℝ (Fin k))‖])⟩,
      (G.continuous.comp ((τ.continuous.comp continuous_fst).prodMk
        (Continuous.subtype_mk (by fun_prop) _))).subtype_mk _⟩
  let ιd := sublevelInclusion f (c - ε * (d : ℝ) ^ 2) (c + ε) (by linarith)
  let outer := ιd.comp H.toContinuousMap
  have hinner (t : I) (w : TopCat.disk.{u} k) : (inner (t, w) : M) =
      G (τ t, smallDiscPoint ε d w.down.1 (mem_closedBall_zero_iff.1 w.down.2)) := rfl
  have houter (p : I × (I × TopCat.diskBoundary.{u} k)) : (outer p : M) = H p := by
    rw [ContinuousMap.comp_apply, coe_sublevelInclusion_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap]
  have hseam (t : I) (θ : TopCat.diskBoundary.{u} k) :
      outer (t, 0, θ) = inner (t, TopCat.diskBoundaryInclusion k θ) := Subtype.ext <| by
    rw [houter, hH0, hinner]
    congr 2
  have hτ0 : τ 0 = 0 :=
    projIcc_of_le_left zero_le_one (by norm_num : 4 * ((0 : I) : ℝ) - 2 ≤ 0)
  have hτ1 : τ 1 = 1 :=
    projIcc_of_right_le zero_le_one (by norm_num : (1 : ℝ) ≤ 4 * ((1 : I) : ℝ) - 2)
  -- Glue; at the two ends the pieces are the two characteristic maps in polar coordinates.
  let K := TopCat.diskCollar hd inner outer hseam
  have hK0 (w : TopCat.disk.{u} k) :
      K (0, w) = (ψ₁.morseCharacteristicMap hk hε.le hball₁ hf₁).hom w := Subtype.ext <|
    (TopCat.apply_diskCollar_eq_of_radial hd _ _ hseam hd1 Subtype.val (Φ := ψ₁.morseCellMap hk ε)
      (fun y ↦ by rw [hinner, hτ0, hG0, symm_smallDiscPoint ψ₁ hk hε.le,
        OpenPartialHomeomorph.morseCellMap_smul hk d.2.1])
      (fun s θ ↦ by rw [houter, ContinuousMap.Homotopy.apply_zero,
        coe_morseAnnulusIsometryMap_apply, LinearIsometryEquiv.coe_refl, id_eq]) w).trans
    (OpenPartialHomeomorph.coe_morseCharacteristicMap_apply hball₁ hf₁ hk hε.le w).symm
  have hK1 (w : TopCat.disk.{u} k) :
      K (1, w) = (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε.le hball₀ hf₀).hom w :=
    Subtype.ext <| (TopCat.apply_diskCollar_eq_of_radial hd _ _ hseam hd1 Subtype.val
      (Φ := fun v ↦ ψ₀.morseCellMap hk ε (g v))
      (fun y ↦ by rw [hinner, hτ1, hG1, map_smallDiscPoint, symm_smallDiscPoint ψ₀ hk hε.le,
        map_smul, OpenPartialHomeomorph.morseCellMap_smul hk d.2.1])
      (fun s θ ↦ by rw [houter, ContinuousMap.Homotopy.apply_one,
        coe_morseAnnulusIsometryMap_apply]) w).trans <|
    ((OpenPartialHomeomorph.coe_morseCharacteristicMap_apply hball₀ hf₀ hk hε.le
      (g.diskMap w)).trans (congrArg _ (g.coe_diskMap_apply_down w))).symm
  let KH : (ψ₁.morseCharacteristicMap hk hε.le hball₁ hf₁).hom.Homotopy
      (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε.le hball₀ hf₀).hom := ⟨K, hK0, hK1⟩
  have hKH (p : I × TopCat.disk.{u} k) : KH p = K p := rfl
  refine ⟨KH, fun t s ↦ ?_⟩
  rw [hKH, TopCat.diskCollar_diskBoundaryInclusion hd _ _ hseam hd1 t s, houter]
  exact hH1 t s

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
  refine ⟨g, hg, exists_homotopy_morseCharacteristicMap_of_negativeDisc ψ₀ ψ₁ hk hε hball₀ hball₁
    hf₀ hf₁ g d G hG0 hG1 hGf R₀.symm (fun x ↦ ?_) hd ((min_le_left _ _).trans_lt (by norm_num))⟩
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


end TauCeti
