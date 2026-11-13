/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Annulus
import TauCeti.AlgebraicTopology.Disk.Annulus

/-!
# Extending a homotopy of small Morse discs to the characteristic maps

Let `χ₀, χ₁ : P × D^k → M` be two families, over a parameter space `P`, of characteristic maps of
Morse cells at a critical level `c` of a function `f : M → ℝ`, in the sense that
`f (χⱼ (p, w)) ≤ c - ε ‖w‖²`. For instance, `χ(w) = ψ⁻¹(√ε • (w, 0))` for a normal-form chart `ψ`
in which `f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, where equality holds, and the same map
precomposed with a linear isometry of `ℝᵏ`. Write `M_a = {f ≤ a}`. For `ε ≥ 0` each `χⱼ (p, ·)` is
then a map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`.

Milnor's comparison of the cells attached by two charts first compares only small discs: for a
radius `0 < d ≤ 1` one constructs a homotopy `G` from `χ₁` to `χ₀` on the discs `‖w‖ ≤ d` which
stays in `M_{c+ε}` and keeps the small spheres `‖w‖ = d` in `M_{c-εd²}`. This file shows that such
a homotopy of small discs extends to a homotopy `K : χ₁ ≃ χ₀` on the whole discs, keeping the
boundary spheres in the lower sublevel `M_{c-ε}`
(`TauCeti.exists_homotopy_morseCharacteristicFamily_of_innerDisc_of_homotopyRel`), provided the
band `f⁻¹[c - ε, c - εd²]` is compact and free of critical points
(`TauCeti.exists_homotopy_morseCharacteristicFamily_of_innerDisc`). Everything depends
continuously on `p ∈ P`, as needed for the fiberwise reattachment map
`TauCeti.fiberwiseCellReattachment`, which takes such a homotopy of families as input; the
critical-free band and its deformation do not depend on `p`.
For a single pair of charts (`P` a point) this is the homotopy of pairs that the change-of-chart
comparison, the reattachment map `TauCeti.morseCellReattachment`, takes as input
(`TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`).

The construction follows Milnor. Let `R` deform `M_{c-εd²}` onto `M_{c-ε}` across the band
(`TauCeti.exists_sublevelDeformation`). Write a point of the annulus `d ≤ ‖w‖ ≤ 1` of the disc
as `(d + (1 - d) s) • θ` with `s ∈ [0, 1]` and `θ` on the unit sphere. The annuli of `χ₁` and
`χ₀`, parametrized by `I × (P × ∂D^k)`, take values in `M_{c-εd²}`, their outer circles lie in
`M_{c-ε}`, and their inner circles are joined by `G` restricted to the small spheres. So they are
homotopic keeping the outer circles in `M_{c-ε}`
(`ContinuousMap.HomotopyRel.exists_annulus_homotopy`): deform each annulus to the retraction
track of its inner circle and move the tracks along `G`. Glued along the seam `‖w‖ = d` with `G`,
run at the time at which the annulus homotopy runs it on the inner circles
(`TauCeti.TopCat.discGlue`), this is the homotopy `K`. No overlap of the whole characteristic
discs of the two families is used.

## Main results

* `TauCeti.exists_homotopy_morseCharacteristicFamily_of_innerDisc_of_homotopyRel`: a homotopy of
  the small discs of two families of characteristic maps, keeping the small spheres in
  `M_{c-εd²}`, extends to a homotopy of the families keeping the boundary spheres in `M_{c-ε}`,
  given a deformation of `M_{c-εd²}` into `M_{c-ε}` fixing `M_{c-ε}`.
* `TauCeti.exists_homotopy_morseCharacteristicFamily_of_innerDisc`: the same when `M` is a
  manifold and the band `f⁻¹[c - ε, c - εd²]` is compact and free of critical points, which
  supplies the deformation.
* `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel`,
  `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`: the case of the characteristic
  maps `χ₁` and `χ₀ ∘ g` of two Morse charts and a linear isometry `g`, as maps of pairs into
  `M_{c+ε}`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

section Family

variable {P M : Type*} [TopologicalSpace P] [TopologicalSpace M] {f : M → ℝ} {c ε : ℝ} {k : ℕ}

/-- The annulus `(s, (p, θ)) ↦ χ (p, (d + (1 - d) s) • θ)` of a family of characteristic maps,
with values in `M_{c-εd²}`. -/
private def familyAnnulus (hε : 0 ≤ ε) (d : I) (χ : C(P × TopCat.disk.{u} k, M))
    (hχ : ∀ p w, f (χ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) :
    C(I × (P × TopCat.diskBoundary.{u} k), {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}) where
  toFun x := ⟨χ (x.2.1, TopCat.annulusPoint d.2.1 d.2.2 x.1 x.2.2), (hχ _ _).trans <| by
    rw [TopCat.norm_annulusPoint]
    have hds : (d : ℝ) ≤ d + (1 - d) * x.1 := by nlinarith [d.2.2, x.1.2.1]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ d.2.1 hds 2) hε) c⟩
  continuous_toFun := (χ.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
    ((TopCat.continuous_annulusPoint d.2.1 d.2.2).comp (continuous_fst.prodMk
      (continuous_snd.comp continuous_snd))))).subtype_mk _

private theorem coe_familyAnnulus_apply (hε : 0 ≤ ε) (d : I) (χ : C(P × TopCat.disk.{u} k, M))
    (hχ : ∀ p w, f (χ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) (x : I × (P × TopCat.diskBoundary.{u} k)) :
    (familyAnnulus hε d χ hχ x : M) = χ (x.2.1, TopCat.annulusPoint d.2.1 d.2.2 x.1 x.2.2) :=
  (rfl)

/-- The outer circle of the annulus of a family lies in `M_{c-ε}`. -/
private theorem familyAnnulus_one_mem (hε : 0 ≤ ε) (d : I) (χ : C(P × TopCat.disk.{u} k, M))
    (hχ : ∀ p w, f (χ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) (x : P × TopCat.diskBoundary.{u} k) :
    familyAnnulus hε d χ hχ (1, x) ∈ {x | f x.val ≤ c - ε} := by
  refine (hχ _ _).trans_eq ?_
  rw [TopCat.norm_annulusPoint, Set.Icc.coe_one]
  ring

/-- **A homotopy of small discs extends to families of characteristic maps, given a deformation
of the band.** Let `χ₀, χ₁ : P × D^k → M` be families of maps with `f (χⱼ (p, w)) ≤ c - ε ‖w‖²`,
for instance families of characteristic maps of Morse charts, so that `χⱼ (p, ·)` sends the
boundary sphere into `M_{c-ε}`. Let `0 < d ≤ 1`, and let `R` be a homotopy from the identity of
`M_{c-εd²}` to a self-map `r` with values in `M_{c-ε}`, fixing `M_{c-ε}`. Suppose that `G` is a
homotopy, on the discs `‖w‖ ≤ d`, from `χ₁` to `χ₀`, with values in `M_{c+ε}`, which keeps the
spheres `‖w‖ = d` in `M_{c-εd²}`. Then `χ₁` is homotopic to `χ₀` through maps with values in
`M_{c+ε}` which send `P × ∂D^k` into `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicFamily_of_innerDisc_of_homotopyRel (hε : 0 ≤ ε)
    {χ₀ χ₁ : C(P × TopCat.disk.{u} k, M)}
    (hχ₀ : ∀ p w, f (χ₀ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
    (hχ₁ : ∀ p w, f (χ₁ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) {d : I} (hd : 0 < d)
    {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
    (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε})
    (hr : ∀ x, f (r x).val ≤ c - ε)
    (G : C(I × (P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d), M))
    (hG₀ : ∀ p (w : TopCat.disk.{u} k) (hw : ‖w.down.1‖ ≤ d),
      G (0, p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) = χ₁ (p, w))
    (hG₁ : ∀ p (w : TopCat.disk.{u} k) (hw : ‖w.down.1‖ ≤ d),
      G (1, p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) = χ₀ (p, w))
    (hGf : ∀ q, f (G q) ≤ c + ε)
    (hGd : ∀ t p (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, p, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : χ₁.Homotopy χ₀, (∀ q, f (K q) ≤ c + ε) ∧
      ∀ t p (s : TopCat.diskBoundary.{u} k),
        f (K (t, p, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  have hd' : (0 : ℝ) < d := unitInterval.coe_pos.2 hd
  -- `G` at a point of the small disc given as a point of the whole disc.
  have hGeq (t : I) (G' : C(P × TopCat.disk.{u} k, M))
      (hG' : ∀ p (w : TopCat.disk.{u} k) (hw : ‖w.down.1‖ ≤ d),
        G (t, p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) = G' (p, w))
      (p : P) (v : closedBall (0 : EuclideanSpace ℝ (Fin k)) d) (w : TopCat.disk.{u} k)
      (h : w.down.1 = v) : G (t, p, v) = G' (p, w) := by
    have hv : v = ⟨w.down.1, mem_closedBall_zero_iff.2 (h ▸ mem_closedBall_zero_iff.1 v.2)⟩ :=
      Subtype.ext h.symm
    rw [hv]
    exact hG' p w (by rw [h]; exact mem_closedBall_zero_iff.1 v.2)
  -- The homotopy `G` on the small spheres joins the inner circles of the two annuli.
  let Kc : (⟨fun x ↦ familyAnnulus hε d χ₁ hχ₁ (0, x), by fun_prop⟩ :
      C(P × TopCat.diskBoundary.{u} k, _)).Homotopy
      ⟨fun x ↦ familyAnnulus hε d χ₀ hχ₀ (0, x), by fun_prop⟩ :=
    { toFun y := ⟨G (y.1, y.2.1,
          ⟨(d : ℝ) • y.2.2.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 y.2.2⟩),
        hGd _ _ _ (by rw [norm_smul, mem_sphere_zero_iff_norm.1 y.2.2.down.2,
          Real.norm_of_nonneg d.2.1, mul_one])⟩
      continuous_toFun := (G.continuous.comp (continuous_fst.prodMk
        ((continuous_fst.comp continuous_snd).prodMk
          (Continuous.subtype_mk (by fun_prop) _)))).subtype_mk _
      map_zero_left x := Subtype.ext <| hGeq 0 χ₁ hG₀ _ _ _ (by simp)
      map_one_left x := Subtype.ext <| hGeq 1 χ₀ hG₁ _ _ _ (by simp) }
  have hKc (y : I × (P × TopCat.diskBoundary.{u} k)) : (Kc y : M) =
      G (y.1, y.2.1,
        ⟨(d : ℝ) • y.2.2.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 y.2.2⟩) :=
    rfl
  obtain ⟨H, hH1, hH0⟩ := R.exists_annulus_homotopy hr (familyAnnulus_one_mem hε d χ₁ hχ₁)
    (familyAnnulus_one_mem hε d χ₀ hχ₀) Kc
  -- The disc piece is `G` at the time at which `H` runs it on the inner circles.
  let τ : C(I, I) := ⟨fun t ↦ projIcc 0 1 zero_le_one (4 * t - 2), by fun_prop⟩
  have hτ (t : I) : τ t = projIcc 0 1 zero_le_one (4 * (t : ℝ) - 2) := rfl
  have hτ0 : τ 0 = 0 :=
    projIcc_of_le_left zero_le_one (by norm_num : 4 * ((0 : I) : ℝ) - 2 ≤ 0)
  have hτ1 : τ 1 = 1 :=
    projIcc_of_right_le zero_le_one (by norm_num : (1 : ℝ) ≤ 4 * ((1 : I) : ℝ) - 2)
  let A : C((I × P) × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M) :=
    ⟨fun q ↦ G (τ q.1.1, q.1.2, q.2), by fun_prop⟩
  let B : C((I × P) × (I × TopCat.diskBoundary.{u} k), M) :=
    ⟨fun q ↦ H (q.1.1, q.2.1, q.1.2, q.2.2), by fun_prop⟩
  have hA (q : (I × P) × closedBall (0 : EuclideanSpace ℝ (Fin k)) d) :
      A q = G (τ q.1.1, q.1.2, q.2) := rfl
  have hB (q : (I × P) × (I × TopCat.diskBoundary.{u} k)) :
      B q = H (q.1.1, q.2.1, q.1.2, q.2.2) := rfl
  have hAB (q : I × P) (θ : TopCat.diskBoundary.{u} k) :
      B (q, 0, θ) =
        A (q, ⟨(d : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 θ⟩) := by
    rw [hB, hH0, hKc, hA, hτ]
  let F := TopCat.discGlue hd' A B hAB
  -- At the two ends, the glued map is the given family on the small disc and its annulus.
  have hend (j : I) (χ : C(P × TopCat.disk.{u} k, M))
      (hχ : ∀ p w, f (χ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
      (hGj : ∀ p (w : TopCat.disk.{u} k) (hw : ‖w.down.1‖ ≤ d),
        G (τ j, p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) = χ (p, w))
      (hH : ∀ x, (H (j, x) : M) = familyAnnulus hε d χ hχ x) (p : P) (w : TopCat.disk.{u} k) :
      F ((j, p), w) = χ (p, w) := by
    rcases le_total ‖w.down.1‖ d with hw | hw
    · exact (TopCat.discGlue_apply_of_norm_le hd' A B hAB _ hw).trans (hGj p w hw)
    · refine (TopCat.discGlue_apply_of_le_norm hd' A B hAB _ hw).trans ?_
      rw [hB, hH, coe_familyAnnulus_apply]
      congr 2
      exact ULift.ext (Subtype.ext ((TopCat.coe_annulusPoint _ _ _ _).trans
        (TopCat.add_one_sub_mul_annulusParam_smul_annulusDir hd' d.2.2 ⟨w, hw⟩)))
  refine ⟨{ toFun x := F ((x.1, x.2.1), x.2.2)
            continuous_toFun := by fun_prop
            map_zero_left x := hend 0 χ₁ hχ₁ (fun p w hw ↦ by rw [hτ0]; exact hG₀ p w hw)
              (fun x ↦ by rw [ContinuousMap.Homotopy.apply_zero]) x.1 x.2
            map_one_left x := hend 1 χ₀ hχ₀ (fun p w hw ↦ by rw [hτ1]; exact hG₁ p w hw)
              (fun x ↦ by rw [ContinuousMap.Homotopy.apply_one]) x.1 x.2 },
    fun q ↦ ?_, fun t p s ↦ ?_⟩
  · refine TopCat.discGlue_mem (S := {x | f x ≤ c + ε}) hd' A B hAB (fun q ↦ hGf _) (fun q ↦ ?_) _
    rw [mem_ofPred_eq, hB]
    exact (H _).2.trans (by nlinarith [mul_nonneg hε (sq_nonneg (d : ℝ))])
  · exact TopCat.discGlue_mem_of_norm_eq_one (S := {x | f x ≤ c - ε}) hd' A B hAB
      (fun q v hv ↦ by
        -- A unit vector of the small disc forces `d = 1`.
        have hd₁ : (d : ℝ) = 1 := le_antisymm d.2.2 (hv ▸ mem_closedBall_zero_iff.1 v.2)
        rw [mem_ofPred_eq, hA]
        simpa [hd₁] using hGd _ _ v (hv.trans hd₁.symm))
      (fun q θ ↦ hH1 _ _) _ (TopCat.norm_diskBoundaryInclusion s)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]

/-- A compact band `f⁻¹[c - ε, c - εd²]` free of critical points gives a deformation `R` of
`M_{c-εd²}` into `M_{c-ε}` fixing `M_{c-ε}`, as used by
`TauCeti.exists_homotopy_morseCharacteristicFamily_of_innerDisc_of_homotopyRel`. -/
private theorem exists_homotopyRel_of_band (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f) (hε : 0 ≤ ε) (d : I)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ (r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}))
      (_ : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε}), ∀ x, f (r x).val ≤ c - ε := by
  have hab : c - ε ≤ c - ε * (d : ℝ) ^ 2 := by
    have := pow_le_one₀ d.2.1 d.2.2 (n := 2)
    nlinarith
  obtain ⟨r, -, ⟨R⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  refine ⟨_, R.symm, fun x ↦ ?_⟩
  rw [ContinuousMap.comp_apply, coe_sublevelInclusion_apply]
  exact (r x).2

/-- **A homotopy of small discs extends to families of characteristic maps.** Let
`χ₀, χ₁ : P × D^k → M` be families of maps with `f (χⱼ (p, w)) ≤ c - ε ‖w‖²`, for instance
families of characteristic maps of Morse charts. Let `0 < d ≤ 1` be such that the band
`f⁻¹[c - ε, c - εd²]` is compact and free of critical points. Suppose that `G` is a homotopy, on
the discs `‖w‖ ≤ d`, from `χ₁` to `χ₀`, with values in `M_{c+ε}`, which keeps the spheres
`‖w‖ = d` in `M_{c-εd²}`. Then `χ₁` is homotopic to `χ₀` through maps with values in `M_{c+ε}`
which send `P × ∂D^k` into `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicFamily_of_innerDisc (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (hε : 0 ≤ ε)
    {χ₀ χ₁ : C(P × TopCat.disk.{u} k, M)}
    (hχ₀ : ∀ p w, f (χ₀ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2)
    (hχ₁ : ∀ p w, f (χ₁ (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2) {d : I} (hd : 0 < d)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (G : C(I × (P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d), M))
    (hG₀ : ∀ p (w : TopCat.disk.{u} k) (hw : ‖w.down.1‖ ≤ d),
      G (0, p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) = χ₁ (p, w))
    (hG₁ : ∀ p (w : TopCat.disk.{u} k) (hw : ‖w.down.1‖ ≤ d),
      G (1, p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) = χ₀ (p, w))
    (hGf : ∀ q, f (G q) ≤ c + ε)
    (hGd : ∀ t p (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, p, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : χ₁.Homotopy χ₀, (∀ q, f (K q) ≤ c + ε) ∧
      ∀ t p (s : TopCat.diskBoundary.{u} k),
        f (K (t, p, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  obtain ⟨r, R, hr⟩ := exists_homotopyRel_of_band hf hε d hcompact hreg
  exact exists_homotopy_morseCharacteristicFamily_of_innerDisc_of_homotopyRel hε hχ₀ hχ₁ hd R hr
    G hG₀ hG₁ hGf hGd

end Family

section Charts

variable {M : Type u} [TopologicalSpace M] {f : M → ℝ} {c ε : ℝ} {n k : ℕ}

/-- The characteristic map `w ↦ χ (g w)` of a chart precomposed with a linear isometry, as a
family over a point. -/
private def chartFamily (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hball : closedBall 0 √ε ⊆ ψ.target)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    C(PUnit.{1} × TopCat.disk.{u} k, M) where
  toFun q := ψ.morseCellMap hk ε (g q.2.down)
  continuous_toFun := (ψ.continuousOn_morseCellMap hball hk).comp_continuous (by fun_prop)
    fun q ↦ by
      rw [mem_closedBall_zero_iff, g.norm_map]
      exact mem_closedBall_zero_iff.1 q.2.down.2

private theorem chartFamily_apply (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hk : k ≤ n) (hball : closedBall 0 √ε ⊆ ψ.target)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (q : PUnit.{1} × TopCat.disk.{u} k) :
    chartFamily ψ hk hball g q = ψ.morseCellMap hk ε (g q.2.down) :=
  (rfl)

private theorem apply_chartFamily_le (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hk : k ≤ n) (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (p : PUnit.{1})
    (w : TopCat.disk.{u} k) :
    f (chartFamily ψ hk hball g (p, w)) ≤ c - ε * ‖w.down.1‖ ^ 2 := by
  have hw : ‖g w.down.1‖ ≤ 1 := (g.norm_map _).trans_le (mem_closedBall_zero_iff.1 w.down.2)
  exact (ψ.apply_morseCellMap_eq_sub_mul_norm_sq hball hf hk hε hw).trans_le
    (by rw [g.norm_map])

/-- **A homotopy of small Morse discs extends to the characteristic maps, given a deformation of
the band.** Let `ψ₀` and `ψ₁` be charts with values in `ℝⁿ` in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain the closed ball of radius `√ε`, with
characteristic maps `χ₀` and `χ₁`, and let `g` be a linear isometry of `ℝᵏ`. Let `0 < d ≤ 1`, and
let `R` be a homotopy from the identity of `M_{c-εd²}` to a self-map `r` with values in `M_{c-ε}`,
fixing `M_{c-ε}`. Suppose that `G` is a homotopy, on the disc `‖w‖ ≤ d`, from `w ↦ χ₁ w` to
`w ↦ χ₀ (g w)`, with values in `M_{c+ε}`, which keeps the sphere `‖w‖ = d` in `M_{c-εd²}`. Then
`χ₁` is homotopic to `χ₀ ∘ g` as a map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`: the homotopy
keeps the boundary sphere in `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel
    {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : k ≤ n) (hε : 0 ≤ ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) {d : I} (hd : 0 < d)
    {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
    (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε})
    (hr : ∀ x, f (r x).val ≤ c - ε)
    (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (hG₀ : ∀ w, G (0, w) = ψ₁.morseCellMap hk ε w)
    (hG₁ : ∀ w, G (1, w) = ψ₀.morseCellMap hk ε (g w))
    (hGf : ∀ t w, f (G (t, w)) ≤ c + ε)
    (hGd : ∀ t (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
        (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{u} k), f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  -- Apply the family version over a point.
  obtain ⟨K, hKf, hKb⟩ := exists_homotopy_morseCharacteristicFamily_of_innerDisc_of_homotopyRel
    hε (apply_chartFamily_le ψ₀ hk hε hball₀ hf₀ g)
    (apply_chartFamily_le ψ₁ hk hε hball₁ hf₁ (.refl ℝ _)) hd R hr
    (G.comp ⟨fun x ↦ (x.1, x.2.2), by fun_prop⟩) (fun _ w _ ↦ hG₀ _) (fun _ w _ ↦ hG₁ _)
    (fun q ↦ hGf _ _) (fun t _ w hw ↦ hGd t w hw)
  exact ⟨{ toFun x := ⟨K (x.1, PUnit.unit, x.2), hKf _⟩
           continuous_toFun := by fun_prop
           map_zero_left w := Subtype.ext <| (K.apply_zero _).trans <| by
             rw [chartFamily_apply, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
               LinearIsometryEquiv.coe_refl, id]
           map_one_left w := Subtype.ext <| (K.apply_one _).trans <| by
             rw [chartFamily_apply, TopCat.hom_comp, ContinuousMap.comp_apply,
               OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
               LinearIsometryEquiv.coe_diskMap_apply_down] },
    fun t s ↦ hKb t _ s⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]

/-- **A homotopy of small Morse discs extends to the characteristic maps.** Let `ψ₀` and `ψ₁` be
charts with values in `ℝⁿ` in which `f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain
the closed ball of radius `√ε`, with characteristic maps `χ₀` and `χ₁`, and let `g` be a linear
isometry of `ℝᵏ`. Let `0 < d ≤ 1` be such that the band `f⁻¹[c - ε, c - εd²]` is compact and free
of critical points. Suppose that `G` is a homotopy, on the disc `‖w‖ ≤ d`, from `w ↦ χ₁ w` to
`w ↦ χ₀ (g w)`, with values in `M_{c+ε}`, which keeps the sphere `‖w‖ = d` in `M_{c-εd²}`. Then
`χ₁` is homotopic to `χ₀ ∘ g` as a map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`: the homotopy
keeps the boundary sphere in `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_of_innerDisc (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : k ≤ n) (hε : 0 ≤ ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) {d : I} (hd : 0 < d)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (hG₀ : ∀ w, G (0, w) = ψ₁.morseCellMap hk ε w)
    (hG₁ : ∀ w, G (1, w) = ψ₀.morseCellMap hk ε (g w))
    (hGf : ∀ t w, f (G (t, w)) ≤ c + ε)
    (hGd : ∀ t (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
        (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{u} k), f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  obtain ⟨r, R, hr⟩ := exists_homotopyRel_of_band hf hε d hcompact hreg
  exact exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel hk hε hball₀ hball₁ hf₀
    hf₁ g hd R hr G hG₀ hG₁ hGf hGd

end Charts

end TauCeti
