/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.AdmissibleCharts
public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Geometry.Manifold.Morse.HandleRetraction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Cell attachment across a critical level

Let `f` be a smooth function on a boundaryless finite-dimensional manifold, and let `c` be a
critical value at which `f` has finitely many critical points, all nondegenerate. Milnor's
Theorem 3.2 says that passing the level `c` attaches one cell at each of these critical points:
for small `ε > 0`, the sublevel `M_{c+ε} = {f ≤ c + ε}` deformation retracts onto the lower
sublevel `M_{c-ε} = {f ≤ c - ε}` with one `λ`-cell attached at each critical point of index `λ`.

The cells are explicit. In a normalized Morse chart `ψ` at a critical point of index `λ`,

`f = c - Σ_{j < λ} yⱼ² + Σ_{j ≥ λ} yⱼ²`,

and the cell is the disc `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ λ}` of the negative coordinates, read in `M`.
Its boundary sphere lies on the level `f⁻¹(c - ε)`.

Following Milnor, write `u` for the negative and `v` for the positive coordinates of a chart. The
function `F = f - μ(‖u‖² + 2‖v‖²)` agrees with `f` outside the ellipsoids `‖u‖² + 2‖v‖² ≤ 2ε`,
where `μ` is a smooth nonincreasing cutoff with `μ = 2ε` on `[0, ε]` and `μ = 0` on `[2ε, ∞)`.
It has the same sublevel `{F ≤ c + ε} = M_{c+ε}`, and no critical points in the band
`F⁻¹[c - ε, c + ε]`: along the positive directions `F` strictly increases away from `v = 0`, and on
`v = 0` it lies below `c - ε`. So `M_{c+ε}` deformation retracts onto `{F ≤ c - ε}`
(`TauCeti.exists_sublevelDeformation`), which in turn retracts onto `M_{c-ε}` with the cells
attached (`TauCeti.exists_inter_sublevel_union_cells_deformation`), since lowering the positive
coordinates lowers `F`. The two retractions compose.

## Main results

* `TauCeti.exists_sublevel_union_cells_deformation`: for normal-form charts with disjoint sources
  around the critical points of a compact band `f⁻¹[c - ε, c + ε]`, the sublevel `M_{c+ε}`
  strong deformation retracts onto `M_{c-ε}` with the cells of the charts attached.
* `TauCeti.IsMorse.exists_sublevel_union_cells_deformation`: **Milnor's cell attachment
  theorem** for a Morse function with a compact band around a critical value, with the charts and
  the width `ε` supplied by `TauCeti.IsMorse.exists_admissible_morseCharts`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Filter Topology Metric
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {n : ℕ} {f : M → ℝ} {c ε : ℝ}

section MilnorFunction

variable
  {ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞}
  {k : ι → ℕ} {μ : ℝ → ℝ} {i : ι} {x : M}

/-- Milnor's function `f - μ(‖u‖² + 2‖v‖²)`, lowered in each chart `ψ i` and equal to `f` outside
the chart sources. Where `f` has the normal form `c - ‖u‖² + ‖v‖²` in the chart, the argument
`(3‖ψ i x‖² + (f x - c)) / 2` of `μ` is `‖u‖² + 2‖v‖²`. -/
private def milnorFunction [Fintype ι]
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (f : M → ℝ) (c : ℝ) (μ : ℝ → ℝ) (x : M) : ℝ :=
  f x - ∑ i, (ψ i).source.indicator (fun y ↦ μ ((3 * ‖ψ i y‖ ^ 2 + (f y - c)) / 2)) x

variable [Fintype ι]

private theorem milnorFunction_of_mem (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source))
    (hx : x ∈ (ψ i).source) :
    milnorFunction ψ f c μ x = f x - μ ((3 * ‖ψ i x‖ ^ 2 + (f x - c)) / 2) := by
  rw [milnorFunction, Finset.sum_eq_single i (fun j _ hji ↦ indicator_of_notMem
    (fun hj ↦ (hψ hji).ne_of_mem hj hx rfl) _) (by simp), indicator_of_mem hx]

private theorem milnorFunction_of_forall_notMem (hx : ∀ i, x ∉ (ψ i).source) :
    milnorFunction ψ f c μ x = f x := by
  simp [milnorFunction, indicator_of_notMem (hx _)]

private theorem milnorFunction_le (hμ : ∀ r, 0 ≤ μ r) (x : M) : milnorFunction ψ f c μ x ≤ f x :=
  sub_le_self _ (Finset.sum_nonneg fun _ _ ↦ indicator_nonneg (fun _ _ ↦ hμ _) _)

variable (k) in
/-- In the coordinates `(u, v)` of a chart in which `f` has the normal form, `f` is
`c - ‖u‖² + ‖v‖²` and Milnor's function is `c - ‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²)`. -/
private theorem milnorFunction_symm_apply (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source))
    (hf : ∀ y ∈ (ψ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i y j ^ 2)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ (ψ i).target) :
    f ((ψ i).toOpenPartialHomeomorph.symm z) =
        c + (-‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) z).1‖ ^ 2 +
          ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) z).2‖ ^ 2) ∧
      milnorFunction ψ f c μ ((ψ i).toOpenPartialHomeomorph.symm z) =
        c + (-‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) z).1‖ ^ 2 +
          ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) z).2‖ ^ 2) -
          μ (‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) z).1‖ ^ 2 +
            2 * ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) z).2‖ ^ 2) := by
  set φ := (ψ i).toOpenPartialHomeomorph
  have hx : φ.symm z ∈ (ψ i).source := φ.map_target hz
  have hψz : ψ i (φ.symm z) = z := φ.right_inv hz
  have hfz := hf _ hx
  rw [hψz, EuclideanSpace.sum_ite_neg_one_mul_sq_eq] at hfz
  refine ⟨hfz, ?_⟩
  rw [milnorFunction_of_mem hψ hx, hψz, hfz,
    ← EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq
      (p := fun j : Fin n ↦ j.val < k i)]
  ring_nf

variable (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source))
  (hf : ∀ i, ∀ y ∈ (ψ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i y j ^ 2)
include hψ hf

/-- Milnor's function at a chart point `x`, in the coordinates `(u, v) = e (ψ x)`. -/
private theorem milnorFunction_of_mem_source (hx : x ∈ (ψ i).source) :
    f x = c + (-‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).1‖ ^ 2 +
          ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).2‖ ^ 2) ∧
      milnorFunction ψ f c μ x =
        c + (-‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).1‖ ^ 2 +
          ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).2‖ ^ 2) -
          μ (‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).1‖ ^ 2 +
            2 * ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i)
              (ψ i x)).2‖ ^ 2) := by
  have h := milnorFunction_symm_apply k hψ (hf i) (μ := μ)
    ((ψ i).toOpenPartialHomeomorph.map_source hx)
  rwa [OpenPartialHomeomorph.left_inv _ hx] at h

/-- At a critical point `x` of Milnor's function in a chart, the positive coordinates `v` of `x`
vanish. Along the curve scaling `v` by `t`, Milnor's function is
`c - ‖u‖² + t²‖v‖² - μ(‖u‖² + 2t²‖v‖²)`, whose derivative `2‖v‖²(1 - 2μ')` at `t = 1` is
`0`, while `μ' ≤ 0`. -/
private theorem snd_eq_zero_of_mfderiv_milnorFunction_eq_zero (hμ : ContDiff ℝ ∞ μ)
    (hμa : Antitone μ) (hF : MDifferentiableAt I 𝓘(ℝ) (milnorFunction ψ f c μ) x)
    (hx : x ∈ (ψ i).source) (h0 : mfderiv I 𝓘(ℝ) (milnorFunction ψ f c μ) x = 0) :
    (EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).2 = 0 := by
  set φ := (ψ i).toOpenPartialHomeomorph
  set e := EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k i
  set a := ‖(e (ψ i x)).1‖ ^ 2
  set b := ‖(e (ψ i x)).2‖ ^ 2
  -- The curve `γ` scales the positive coordinates of `x` by `t`.
  set L : ℝ → EuclideanSpace ℝ (Fin n) := fun t ↦ e.symm ((e (ψ i x)).1, t • (e (ψ i x)).2)
  set γ : ℝ → M := fun t ↦ φ.symm (L t)
  have hL1 : L 1 = ψ i x := by simp [L]
  have hLt : L 1 ∈ (ψ i).target := hL1 ▸ φ.map_source hx
  have hγ1 : γ 1 = x := by
    simp only [γ, hL1]
    exact φ.left_inv hx
  -- `F ∘ γ` has derivative `0` at `1`, since `x` is a critical point of `F`.
  have hγ : MDifferentiableAt 𝓘(ℝ) I γ 1 :=
    -- The inverse of `φ` is the inverse function `(ψ i).invFun` of the partial diffeomorphism.
    (((ψ i).contMDiffOn_invFun.contMDiffAt
      ((ψ i).open_target.mem_nhds hLt)).mdifferentiableAt (by simp)).comp 1
      (mdifferentiableAt_iff_differentiableAt.2 (e.symm.differentiableAt.comp _
        ((differentiableAt_const _).prodMk (differentiableAt_id.smul_const _))))
  have h0' : mfderiv I 𝓘(ℝ) (milnorFunction ψ f c μ) (γ 1) = 0 := by
    rw [hγ1]
    exact h0
  have hd : HasDerivAt (milnorFunction ψ f c μ ∘ γ) 0 1 := by
    have hF' : MDifferentiableAt I 𝓘(ℝ) (milnorFunction ψ f c μ) (γ 1) := hγ1 ▸ hF
    have h := hF'.hasMFDerivAt.comp 1 hγ.hasMFDerivAt
    rw [h0', ContinuousLinearMap.zero_comp] at h
    have h2 : HasFDerivAt (milnorFunction ψ f c μ ∘ γ) (0 : ℝ →L[ℝ] ℝ) 1 :=
      hasMFDerivAt_iff_hasFDerivAt.1 h
    simpa using h2.hasDerivAt
  -- Explicitly, `F (γ t) = c - a + t² b - μ (a + 2 t² b)` near `t = 1`.
  have heq : milnorFunction ψ f c μ ∘ γ =ᶠ[𝓝 1]
      fun t ↦ c + (-a + t ^ 2 * b) - μ (a + 2 * (t ^ 2 * b)) := by
    have hLc : Continuous L :=
      e.symm.continuous.comp (continuous_const.prodMk (continuous_id.smul continuous_const))
    filter_upwards [hLc.continuousAt.preimage_mem_nhds ((ψ i).open_target.mem_nhds hLt)]
      with t ht
    rw [comp_apply, (milnorFunction_symm_apply k hψ (hf i) (μ := μ) ht).2]
    simp [L, e, a, b, norm_smul, mul_pow]
  have hq : HasDerivAt (fun t : ℝ ↦ t ^ 2 * b) (2 * b) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).mul_const b
  have hμd := ((hμ.differentiable (by simp)) (a + 2 * (1 ^ 2 * b))).hasDerivAt
  have hg : HasDerivAt (fun t : ℝ ↦ c + (-a + t ^ 2 * b) - μ (a + 2 * (t ^ 2 * b)))
      (2 * b - deriv μ (a + 2 * (1 ^ 2 * b)) * (2 * (2 * b))) 1 :=
    ((hq.const_add (-a)).const_add c).sub (hμd.comp 1 ((hq.const_mul 2).const_add a))
  have hval := (hg.congr_of_eventuallyEq heq).unique hd
  have hμ' : deriv μ (a + 2 * (1 ^ 2 * b)) ≤ 0 := by
    have := hμd.neg.nonneg_of_monotone hμa.neg
    linarith
  have hb : 0 ≤ b := sq_nonneg _
  have hb0 : b = 0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hμ' hb]
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hb0)

/-- **Milnor's function has no critical points at chart points of the band.** At a critical
point in a chart, the positive coordinates vanish, and there Milnor's function is
`c - ‖u‖² - μ(‖u‖²) < c - ε`. -/
private theorem mfderiv_milnorFunction_ne_zero (hε : 0 < ε) (hμ : ContDiff ℝ ∞ μ)
    (hμa : Antitone μ) (hμ_nonneg : ∀ r, 0 ≤ μ r) (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hF : MDifferentiableAt I 𝓘(ℝ) (milnorFunction ψ f c μ) x) (hx : x ∈ (ψ i).source)
    (hxε : c - ε ≤ milnorFunction ψ f c μ x) :
    mfderiv I 𝓘(ℝ) (milnorFunction ψ f c μ) x ≠ 0 := by
  intro h0
  have hv := snd_eq_zero_of_mfderiv_milnorFunction_eq_zero hψ hf hμ hμa hF hx h0
  rw [(milnorFunction_of_mem_source hψ hf (μ := μ) hx).2, hv, norm_zero] at hxε
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at hxε
  set a := ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).1‖ ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  rcases le_or_gt a ε with h | h
  · rw [hμ_eq a h] at hxε
    linarith
  · linarith [hμ_nonneg a]

/-- Scaling the positive coordinates of a chart point inside the ball of radius `√(2ε)` by a
factor in `[0, 1]` does not increase Milnor's function. -/
private theorem milnorFunction_symm_scale_le (hμa : Antitone μ)
    (hball : closedBall 0 √(2 * ε) ⊆ (ψ i).target) (hx : x ∈ (ψ i).source)
    (hxε : ‖ψ i x‖ ≤ √(2 * ε)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    milnorFunction ψ f c μ ((ψ i).toOpenPartialHomeomorph.symm
      (WithLp.toLp 2 fun j ↦ if j.val < k i then ψ i x j else s * ψ i x j)) ≤
      milnorFunction ψ f c μ x := by
  set e := EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k i
  rw [← EuclideanSpace.sumComplEquivProd_symm_smul_snd]
  have hw : e.symm ((e (ψ i x)).1, s • (e (ψ i x)).2) ∈ (ψ i).target :=
    hball (mem_closedBall_zero_iff.2 ((EuclideanSpace.norm_sumComplEquivProd_symm_smul_snd_le _
      ((Real.norm_of_nonneg hs.1).trans_le hs.2)).trans hxε))
  rw [(milnorFunction_symm_apply k hψ (hf i) (μ := μ) hw).2,
    (milnorFunction_of_mem_source hψ hf (μ := μ) hx).2]
  simp only [e, ContinuousLinearEquiv.apply_symm_apply, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
  have hb : 0 ≤ ‖(e (ψ i x)).2‖ ^ 2 := sq_nonneg _
  have hμle := hμa (show ‖(e (ψ i x)).1‖ ^ 2 + 2 * (s ^ 2 * ‖(e (ψ i x)).2‖ ^ 2) ≤
    ‖(e (ψ i x)).1‖ ^ 2 + 2 * ‖(e (ψ i x)).2‖ ^ 2 by nlinarith)
  nlinarith

/-- Milnor's function lies below `c - ε` on the cell `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ k i}` of a
chart. -/
private theorem milnorFunction_le_of_mem_cell (hε : 0 < ε) (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hx : x ∈ (ψ i).source) (hxε : ‖ψ i x‖ ^ 2 ≤ ε)
    (hxv : ∀ j : Fin n, k i ≤ j.val → ψ i x j = 0) :
    milnorFunction ψ f c μ x ≤ c - ε := by
  obtain ⟨hu, hv⟩ := EuclideanSpace.norm_fst_sumComplEquivProd_sq_le_and_snd_eq_zero_iff.2
    ⟨hxε, fun j hj ↦ hxv j (not_lt.1 hj)⟩
  rw [(milnorFunction_of_mem_source hψ hf (μ := μ) hx).2, hv, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  rw [hμ_eq _ hu]
  linarith [sq_nonneg ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i)
    (ψ i x)).1‖]

variable (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
include hμ₀

/-- Outside the ball of radius `√(2ε)` of a chart, Milnor's function agrees with `f`. -/
private theorem milnorFunction_eq_of_sqrt_lt (hx : x ∈ (ψ i).source) (hxε : √(2 * ε) < ‖ψ i x‖) :
    milnorFunction ψ f c μ x = f x := by
  obtain ⟨hfx, hFx⟩ := milnorFunction_of_mem_source hψ hf (μ := μ) hx
  -- Outside the ball, `‖u‖² + 2‖v‖² ≥ ‖u‖² + ‖v‖² = ‖ψ i x‖² > 2ε`.
  have h := EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq
    (p := fun j : Fin n ↦ j.val < k i) (ψ i x)
  have h2 : 2 * ε < ‖ψ i x‖ ^ 2 := Real.lt_sq_of_sqrt_lt hxε
  rw [hFx, hfx, hμ₀ _ (by nlinarith [sq_nonneg ‖(EuclideanSpace.sumComplEquivProd ℝ
    (fun j : Fin n ↦ j.val < k i) (ψ i x)).2‖]), sub_zero]

omit [Fintype ι] in
/-- Each lowering term of Milnor's function vanishes outside the image of the closed ball of
radius `√(2ε)` in its chart. -/
private theorem indicator_eq_zero_of_notMem_image [Finite ι] (i : ι) {y : M}
    (hy : y ∉ (ψ i).toOpenPartialHomeomorph.symm '' closedBall 0 √(2 * ε)) :
    (ψ i).source.indicator (fun y ↦ μ ((3 * ‖ψ i y‖ ^ 2 + (f y - c)) / 2)) y = 0 := by
  have := Fintype.ofFinite ι
  by_cases hys : y ∈ (ψ i).source
  · have hlt : √(2 * ε) < ‖ψ i y‖ := by
      by_contra h
      exact hy ⟨ψ i y, mem_closedBall_zero_iff.2 (not_lt.1 h),
        (ψ i).toOpenPartialHomeomorph.left_inv hys⟩
    have h := milnorFunction_of_mem (f := f) (c := c) (μ := μ) hψ hys
    rw [milnorFunction_eq_of_sqrt_lt hψ hf hμ₀ hys hlt, eq_comm, sub_eq_self] at h
    rwa [indicator_of_mem hys]
  · exact indicator_of_notMem hys _

variable (hball : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ i).target)
include hball

omit [Fintype ι] hψ hf hμ₀ in
private theorem isCompact_image_closedBall (i : ι) :
    IsCompact ((ψ i).toOpenPartialHomeomorph.symm '' closedBall 0 √(2 * ε)) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((ψ i).toOpenPartialHomeomorph.continuousOn_symm.mono (hball i))

variable [T2Space M]

/-- Away from the images of the closed balls of radius `√(2ε)`, Milnor's function agrees with `f`
on a neighbourhood. -/
private theorem milnorFunction_eventuallyEq [Finite ι]
    (hx : x ∉ ⋃ i, (ψ i).toOpenPartialHomeomorph.symm '' closedBall 0 √(2 * ε)) :
    milnorFunction ψ f c μ =ᶠ[𝓝 x] f := by
  have hclosed : IsClosed (⋃ i, (ψ i).toOpenPartialHomeomorph.symm '' closedBall 0 √(2 * ε)) :=
    isClosed_iUnion_of_finite fun i ↦ (isCompact_image_closedBall hball i).isClosed
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
  rw [milnorFunction, Finset.sum_eq_zero fun i _ ↦
    indicator_eq_zero_of_notMem_image hψ hf hμ₀ i fun h ↦ hy (mem_iUnion.2 ⟨i, h⟩), sub_zero]

/-- **Milnor's function is smooth.** -/
private theorem contMDiff_milnorFunction (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hμ : ContDiff ℝ ∞ μ) :
    ContMDiff I 𝓘(ℝ) ∞ (milnorFunction ψ f c μ) := by
  refine ContMDiff.sub hfs (ContMDiff.sum fun i _ ↦ contMDiff_of_tsupport fun y hy ↦ ?_)
  -- The lowering term is supported in the compact image of the ball, inside the chart source.
  have hK : tsupport ((ψ i).source.indicator fun y ↦ μ ((3 * ‖ψ i y‖ ^ 2 + (f y - c)) / 2)) ⊆
      (ψ i).toOpenPartialHomeomorph.symm '' closedBall 0 √(2 * ε) :=
    closure_minimal (fun y hy ↦ not_not.1 fun h ↦ hy
      (indicator_eq_zero_of_notMem_image hψ hf hμ₀ i h))
      (isCompact_image_closedBall hball i).isClosed
  obtain ⟨z, hz, rfl⟩ := hK hy
  have hs : (ψ i).toOpenPartialHomeomorph.symm z ∈ (ψ i).source :=
    (ψ i).toOpenPartialHomeomorph.map_target (hball i hz)
  have hψ' : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (ψ i)
      ((ψ i).toOpenPartialHomeomorph.symm z) :=
    (ψ i).contMDiffOn.contMDiffAt ((ψ i).open_source.mem_nhds hs)
  have hterm : ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ μ ((3 * ‖ψ i y‖ ^ 2 + (f y - c)) / 2))
      ((ψ i).toOpenPartialHomeomorph.symm z) :=
    -- `μ ((3 s + (t - c)) / 2)` is a smooth function of `(s, t) = (‖ψ i y‖², f y)`.
    have hg : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ μ ((3 * p.1 + (p.2 - c)) / 2) :=
      hμ.comp (by fun_prop)
    hg.contMDiff.contMDiffAt.comp _ (((contDiff_norm_sq ℝ).contMDiff.contMDiffAt.comp _
      hψ').prodMk_space (hfs _))
  exact hterm.congr_of_eventuallyEq
    (eventuallyEq_of_mem ((ψ i).open_source.mem_nhds hs) fun y hy ↦ indicator_of_mem hy _)

omit hball [T2Space M] in
/-- Milnor's function has the same sublevel `{F ≤ c + ε}` as `f`: inside Milnor's ellipsoid
`‖u‖² + 2‖v‖² < 2ε` of a chart, `f = c - ‖u‖² + ‖v‖² < c + ε`. -/
private theorem setOf_milnorFunction_le (hμ_nonneg : ∀ r, 0 ≤ μ r) :
    {x | milnorFunction ψ f c μ x ≤ c + ε} = {x | f x ≤ c + ε} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (milnorFunction_le hμ_nonneg x).trans hx⟩
  by_cases hxs : ∃ i, x ∈ (ψ i).source
  · obtain ⟨i, hi⟩ := hxs
    obtain ⟨hfx, hFx⟩ := milnorFunction_of_mem_source hψ hf (μ := μ) hi
    set a := ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).1‖ ^ 2
    set b := ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k i) (ψ i x)).2‖ ^ 2
    rcases le_or_gt (2 * ε) (a + 2 * b) with h | h
    · rw [mem_ofPred_eq, hFx, hμ₀ _ h, sub_zero, ← hfx] at hx
      exact hx
    · have ha : 0 ≤ a := sq_nonneg _
      rw [mem_ofPred_eq, hfx]
      linarith
  · rwa [mem_ofPred_eq, milnorFunction_of_forall_notMem (not_exists.1 hxs)] at hx

omit hball [T2Space M] in
/-- A point with `F ≤ c - ε` outside the balls of radius `√(2ε)` of the charts lies in the lower
sublevel `{f ≤ c - ε}`. -/
private theorem le_of_milnorFunction_le (hx : milnorFunction ψ f c μ x ≤ c - ε)
    (hxε : ∀ i, x ∈ (ψ i).source → √(2 * ε) < ‖ψ i x‖) : f x ≤ c - ε := by
  by_cases hxs : ∃ i, x ∈ (ψ i).source
  · obtain ⟨i, hi⟩ := hxs
    rwa [← milnorFunction_eq_of_sqrt_lt hψ hf hμ₀ hi (hxε i hi)]
  · rwa [← milnorFunction_of_forall_notMem (f := f) (c := c) (μ := μ) (not_exists.1 hxs)]

/-- Milnor's function has no critical points in the band `F⁻¹[c - ε, c + ε]`, provided the
critical points of `f` in the band `f⁻¹[c - ε, c + ε]` lie in the chart sources. -/
private theorem mfderiv_milnorFunction_ne_zero_of_mem_Icc [Finite ι]
    (hε : 0 < ε) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hμ : ContDiff ℝ ∞ μ) (hμa : Antitone μ)
    (hμ_nonneg : ∀ r, 0 ≤ μ r) (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ i).source)
    (h₁ : c - ε ≤ milnorFunction ψ f c μ x) (h₂ : milnorFunction ψ f c μ x ≤ c + ε) :
    mfderiv I 𝓘(ℝ) (milnorFunction ψ f c μ) x ≠ 0 := by
  by_cases hxs : ∃ i, x ∈ (ψ i).source
  · obtain ⟨i, hi⟩ := hxs
    exact mfderiv_milnorFunction_ne_zero hψ hf hε hμ hμa hμ_nonneg hμ_eq
      ((contMDiff_milnorFunction hψ hf hμ₀ hball hfs hμ).mdifferentiableAt (by simp)) hi h₁
  · replace hxs := not_exists.1 hxs
    have hK : x ∉ ⋃ i, (ψ i).toOpenPartialHomeomorph.symm '' closedBall 0 √(2 * ε) := by
      intro h
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 h
      exact hxs i ((ψ i).toOpenPartialHomeomorph.map_target (hball i hz))
    have hfx := milnorFunction_of_forall_notMem (f := f) (c := c) (μ := μ) hxs
    rw [(milnorFunction_eventuallyEq hψ hf hμ₀ hball hK).mfderiv_eq]
    intro h0
    obtain ⟨i, hi⟩ := mem_iUnion.1
      (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 h0, hfx ▸ h₁, hfx ▸ h₂⟩)
    exact hxs i hi

end MilnorFunction

section CellAttachment

/-- Milnor's cutoff: a smooth nonincreasing function equal to `2ε` on `(-∞, ε]` and to `0` on
`[2ε, ∞)`. Lowering `f` by it at `‖u‖² + 2‖v‖²` pushes the critical point below `c - ε` without
changing `f` outside Milnor's ellipsoid. -/
private theorem exists_milnorCutoff (hε : 0 < ε) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ Antitone μ ∧ (∀ r, 0 ≤ μ r) ∧ (∀ r, 2 * ε ≤ r → μ r = 0) ∧
      ∀ r ≤ ε, μ r = 2 * ε := by
  refine ⟨fun r ↦ 2 * ε * (1 - Real.smoothTransition ((r - ε) / ε)),
    contDiff_const.mul (contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))),
    fun r s hrs ↦ mul_le_mul_of_nonneg_left (sub_le_sub_left (Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (by linarith) hε.le)) _) (by positivity),
    fun r ↦ mul_nonneg (by positivity) (sub_nonneg.2 (Real.smoothTransition.le_one _)),
    fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · have h : 1 ≤ (r - ε) / ε := (one_le_div hε).2 (by linarith)
    simp only [Real.smoothTransition.one_of_one_le h, sub_self, mul_zero]
  · have h : (r - ε) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    simp only [Real.smoothTransition.zero_of_nonpos h, sub_zero, mul_one]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Cell attachment in disjoint Morse charts.** Let `f` be smooth, and let `ψ i` be charts of
`M` with pairwise disjoint sources, each containing the closed ball of radius `√(2ε)` about `0`
in its target, in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. Suppose the band
`f⁻¹[c - ε, c + ε]` is compact and its critical points lie in the chart sources. The cell of the
chart `ψ i` is the disc `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ k i}` of the first `k i` coordinates, read in
`M`.

Then the lower sublevel `{f ≤ c - ε}` with these cells attached is a strong deformation retract
of `{f ≤ c + ε}`: there is a retraction of `{f ≤ c + ε}` onto it, and a homotopy in
`{f ≤ c + ε}` from this retraction to the identity which fixes it pointwise. The cells lie in
`{f ≤ c}`, so intersecting with `{f ≤ c + ε}` does not change the retract. -/
theorem exists_sublevel_union_cells_deformation [Finite ι] (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ) (hε : 0 < ε)
    (hball : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ i).target)
    (hf : ∀ i, ∀ y ∈ (ψ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ i).source) :
    ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
        ⋃ i, (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
          ⋃ i, (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}}) := by
  have := Fintype.ofFinite ι
  obtain ⟨μ, hμ, hμa, hμ_nonneg, hμ₀, hμ_eq⟩ := exists_milnorCutoff hε
  set F := milnorFunction ψ f c μ
  set S := {x | f x ≤ c - ε} ∪
    ⋃ i, (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}
  have hFs : ContMDiff I 𝓘(ℝ) ∞ F := contMDiff_milnorFunction hψ hf hμ₀ hball hfs hμ
  have hX : {x | F x ≤ c + ε} = {x | f x ≤ c + ε} := setOf_milnorFunction_le hψ hf hμ₀ hμ_nonneg
  have hSY : S ⊆ {x | F x ≤ c - ε} := by
    rintro x (hx | hx)
    · exact (milnorFunction_le hμ_nonneg x).trans hx
    · obtain ⟨i, hxi, hxε, hxv⟩ := mem_iUnion.1 hx
      exact milnorFunction_le_of_mem_cell hψ hf hε hμ_eq hxi hxε hxv
  have hab : c - ε ≤ c + ε := by linarith
  -- First, `{F ≤ c + ε}` deformation retracts onto `{F ≤ c - ε}`, as `F` has no critical points
  -- in the compact band `F⁻¹[c - ε, c + ε]`.
  have hFcompact : IsCompact (F ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hFs.continuous) fun x hx ↦
      ⟨hx.1.trans (milnorFunction_le hμ_nonneg x), (Set.ext_iff.1 hX x).1 hx.2⟩
  obtain ⟨r₁, hr₁, ⟨H₁⟩⟩ := exists_sublevelDeformation hFs hab hFcompact fun x h₁ h₂ ↦
    mfderiv_milnorFunction_ne_zero_of_mem_Icc hψ hf hμ₀ hball hε hfs hμ hμa hμ_nonneg hμ_eq
      hcrit h₁ h₂
  -- Second, Milnor's handle retraction retracts `{F ≤ c - ε}` onto `S`, since lowering the
  -- positive coordinates of a chart lowers `F`.
  -- The charts enter through their underlying open partial homeomorphisms, which have the same
  -- source and forward map, so the retract is literally `S`.
  have hhandle : ∃ r : C(↥{x | F x ≤ c - ε}, ↥({x | F x ≤ c - ε} ∩ S)),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : M) ∈ S}) :=
    exists_inter_sublevel_union_cells_deformation
      (fun i ↦ (ψ i).toOpenPartialHomeomorph) hψ k hball hf (X := {x | F x ≤ c - ε})
      (fun x hx hxε ↦ le_of_milnorFunction_le hψ hf hμ₀ hx hxε)
      (fun i x hx hxε s hs ↦
        (milnorFunction_symm_scale_le hψ hf hμa (hball i) hx.2 hxε hs).trans hx.1)
  obtain ⟨r₂, hr₂, ⟨H₂⟩⟩ := hhandle
  -- Compose the two strong deformation retractions.
  have hrange₁ : range (sublevelInclusion F (c - ε) (c + ε) hab) =
      {x : ↥{x | F x ≤ c + ε} | F x ≤ c - ε} :=
    Set.ext fun x ↦ ⟨by rintro ⟨y, rfl⟩; simpa only [mem_ofPred_eq, coe_sublevelInclusion_apply]
      using y.2, fun hx ↦ ⟨⟨x, hx⟩, Subtype.ext (by simp)⟩⟩
  have hrange₂ : range (ContinuousMap.inclusion
      (inter_subset_left : {x | F x ≤ c - ε} ∩ S ⊆ {x | F x ≤ c - ε})) =
      {x : ↥{x | F x ≤ c - ε} | (x : M) ∈ S} :=
    Set.ext fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2.2, fun hx ↦ ⟨⟨x, x.2, hx⟩, rfl⟩⟩
  obtain ⟨H⟩ := ContinuousMap.HomotopicRel.comp_retractions
    (by rw [hrange₁]; exact ⟨H₁.symm⟩) (by rw [hrange₂]; exact ⟨H₂.symm⟩) hr₁
  have hYX : {x | F x ≤ c - ε} ∩ S ⊆ {x | F x ≤ c + ε} ∩ S :=
    inter_subset_inter_left _ fun _ hx ↦ le_trans hx hab
  have key : ∃ r : C({x | F x ≤ c + ε}, ↥({x | F x ≤ c + ε} ∩ S)),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : M) ∈ S}) := by
    refine ⟨(ContinuousMap.inclusion hYX).comp (r₂.comp r₁), fun x ↦ ?_, ⟨?_⟩⟩
    · have hx : (x : M) ∈ {x | F x ≤ c - ε} := hSY x.2.2
      have h₁ : r₁ (ContinuousMap.inclusion inter_subset_left x) = ⟨x, hx⟩ := by
        rw [show ContinuousMap.inclusion inter_subset_left x =
          sublevelInclusion F (c - ε) (c + ε) hab ⟨x, hx⟩ from Subtype.ext (by simp)]
        exact hr₁ _
      have h₂ : r₂ ⟨x, hx⟩ = ⟨x, hx, x.2.2⟩ := hr₂ ⟨x, hx, x.2.2⟩
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, h₁, h₂]
      exact Subtype.ext (by simp)
    · have hrange : range ((sublevelInclusion F (c - ε) (c + ε) hab).comp
          (ContinuousMap.inclusion inter_subset_left)) =
          {x : ↥{x | F x ≤ c + ε} | (x : M) ∈ S} :=
        Set.ext fun x ↦ ⟨by rintro ⟨y, rfl⟩; simpa using y.2.2,
          fun hx ↦ ⟨⟨x, hSY hx, hx⟩, Subtype.ext (by simp)⟩⟩
      have hmap : (ContinuousMap.inclusion inter_subset_left).comp
          ((ContinuousMap.inclusion hYX).comp (r₂.comp r₁)) =
          ((sublevelInclusion F (c - ε) (c + ε) hab).comp
            (ContinuousMap.inclusion inter_subset_left)).comp (r₂.comp r₁) :=
        ContinuousMap.ext fun x ↦ Subtype.ext (by simp)
      rw [hrange] at H
      rw [hmap]
      exact H.symm
  rwa [hX] at key

/-- **Milnor's cell attachment theorem.** Let `f` be a Morse function on a Hausdorff manifold whose
band `f⁻¹[c - δ, c + δ]` is compact, for some `0 < δ`. Then there are a width `0 < ε ≤ δ` and
normalized Morse charts `ψ p` with pairwise disjoint sources, indexed by the critical points `p`
on the level `f⁻¹(c)`, with `ψ p p = 0`, with the closed ball of radius `√(2ε)` in the target of
`ψ p`, and in which `f = c - Σ_{i < λ} yᵢ² + Σ_{i ≥ λ} yᵢ²`, where `λ` is the Morse index of `f`
at `p`. The cell at `p` is the disc `{‖y‖² ≤ ε, yᵢ = 0 for i ≥ λ}` of its negative coordinates,
read in `M` through `ψ p`.

The lower sublevel `{f ≤ c - ε}` with these cells attached is a strong deformation retract of
`{f ≤ c + ε}`: there is a retraction of `{f ≤ c + ε}` onto it, and a homotopy in `{f ≤ c + ε}`
from this retraction to the identity which fixes it pointwise. -/
theorem IsMorse.exists_sublevel_union_cells_deformation (hf : IsMorse I f) {δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧
      ∃ ψ : ↥(criticalPoints I f ∩ f ⁻¹' {c}) →
          PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
        Pairwise (Disjoint on fun p ↦ (ψ p).source) ∧
        (∀ p, ↑p ∈ (ψ p).source ∧ ψ p p = 0 ∧ closedBall 0 √(2 * ε) ⊆ (ψ p).target ∧
          ∀ y ∈ (ψ p).source,
            f y = c + ∑ i, (if i.val < manifoldMorseIndex I f p then -1 else 1) * ψ p y i ^ 2) ∧
        ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
            ⋃ p, (ψ p).source ∩ ψ p ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧
              ∀ i : Fin (Module.finrank ℝ E), manifoldMorseIndex I f p ≤ i.val → y i = 0}))),
          (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
              ⋃ p, (ψ p).source ∩ ψ p ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧
                ∀ i : Fin (Module.finrank ℝ E), manifoldMorseIndex I f p ≤ i.val → y i = 0}}) := by
  obtain ⟨ε, hε, hεδ, hband, ψ, hψ, hψp⟩ :=
    hf.exists_admissible_morseCharts hδ hcompact (U := fun _ ↦ univ) fun _ _ ↦ univ_mem
  have : Finite ↥(criticalPoints I f ∩ f ⁻¹' {c}) :=
    ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))).to_subtype
  refine ⟨ε, hε, hεδ, ψ, hψ, fun p ↦ ⟨(hψp p).1, (hψp p).2.2.1, (hψp p).2.2.2⟩,
    TauCeti.exists_sublevel_union_cells_deformation hf.contMDiff ψ hψ _ hε
      (fun p ↦ (hψp p).2.2.2.1) (fun p ↦ (hψp p).2.2.2.2)
      (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
        (preimage_mono (Icc_subset_Icc (by linarith) (by linarith))))
      fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx.1, hband hx⟩, (hψp _).1⟩⟩

end CellAttachment

end TauCeti
