/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCell.Attachment

/-!
# Composing fiberwise reattachment maps

Let `χ₀`, `χ₁`, `χ₂` be families over a parameter space `P` of characteristic maps of discs
`D^{k i}` in a space `Y`, with attaching maps `α₀`, `α₁`, `α₂` in a subspace `A`. A family of
self-maps `h₁₂ i` of `P × D^{k i}` over `P` and homotopies `K₁₂ i : χ₂ i ≃ χ₁ i ∘ (p, h₁₂ i)`
keeping the boundary spheres in `A` give the fiberwise reattachment map
`E₁₂ : (P × A) ∪_{α₂} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})`
(`TauCeti.fiberwiseCellReattachment`), and data `(h₀₁, K₀₁)` from `χ₁` to `χ₀` give `E₀₁`.
Composing the data gives data from `χ₂` to `χ₀`: the disc maps
`h₀₂ i (p, x) = h₀₁ i (p, h₁₂ i (p, x))` and the concatenated homotopies
`K₀₂ i = K₁₂ i * K₀₁ i ∘ (p, h₁₂ i)`, which first run along `K₁₂ i` and then along `K₀₁ i`
precomposed with `h₁₂ i`.

When each `h₁₂ i (p, ·)` is a linear isometry of the disc, as for the polar factors in Milnor's
comparison of two charts, the composite `E₀₁ ∘ E₁₂` is homotopic to the reattachment map `E₀₂` of
the composed data, relative to `P × A` and through maps over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_of_eq_trans`).
The maps `h₀₁ i` are arbitrary. Unlike
`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment`, this needs
no left inverse over `P` of a comparison map `(P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i}) → P × Y`.

On the `i`-th disc, `E₀₁ ∘ E₁₂` scales the disc of radius `1/4` onto the cells by `4`, runs along
`K₀₁` on the annulus `1/4 ≤ ‖x‖ ≤ 1/2` and along `K₁₂` on the annulus `1/2 ≤ ‖x‖ ≤ 1`, while `E₀₂`
does the same with the radii `1/2` and `3/4`. So the two agree after the radial reparametrization
of the disc sending the radii `1/4` and `1/2` to `1/2` and `3/4`, and the straight-line homotopy
from this reparametrization to the identity, which fixes the boundary sphere, gives the homotopy.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open CategoryTheory Set Metric unitInterval

universe u

namespace TauCeti

/-! ### The radial reparametrization -/

/-- The radial factor of the reparametrization of the disc used to compare a composite of two
reattachment maps with a single one: with `m = max r (1/4)`, it is `min (m + 1/4) ((m + 1)/2) / m`.
A vector of norm `r` is scaled by `2` when `r ≤ 1/4`, to norm `r + 1/4` when `1/4 ≤ r ≤ 1/2`, and
to norm `(r + 1)/2` when `1/2 ≤ r`. -/
private def composeRadialFactor (r : ℝ) : ℝ :=
  min (max r (1 / 4) + 1 / 4) ((max r (1 / 4) + 1) / 2) / max r (1 / 4)

private theorem quarter_le_max (r : ℝ) : (1 / 4 : ℝ) ≤ max r (1 / 4) :=
  le_max_right _ _

private theorem continuous_composeRadialFactor : Continuous composeRadialFactor := by
  have hm : Continuous fun r : ℝ ↦ max r (1 / 4) := continuous_id.max continuous_const
  exact (((hm.add continuous_const).min ((hm.add continuous_const).div_const _))).div hm
    fun r ↦ (lt_of_lt_of_le (by norm_num) (quarter_le_max r)).ne'

private theorem composeRadialFactor_nonneg (r : ℝ) : 0 ≤ composeRadialFactor r := by
  have := quarter_le_max r
  exact div_nonneg (le_min (by linarith) (by linarith)) (by linarith)

private theorem composeRadialFactor_of_le {r : ℝ} (hr : r ≤ 1 / 4) : composeRadialFactor r = 2 := by
  rw [composeRadialFactor, max_eq_right hr]
  norm_num

private theorem composeRadialFactor_mul_of_mem {r : ℝ} (h₁ : 1 / 4 ≤ r) (h₂ : r ≤ 1 / 2) :
    composeRadialFactor r * r = r + 1 / 4 := by
  rw [composeRadialFactor, max_eq_left h₁, min_eq_left (by linarith),
    div_mul_cancel₀ _ (by linarith : r ≠ 0)]

private theorem composeRadialFactor_mul_of_le {r : ℝ} (h : 1 / 2 ≤ r) :
    composeRadialFactor r * r = (r + 1) / 2 := by
  rw [composeRadialFactor, max_eq_left (by linarith), min_eq_right (by linarith),
    div_mul_cancel₀ _ (by linarith : r ≠ 0)]

private theorem composeRadialFactor_one : composeRadialFactor 1 = 1 := by
  have h := composeRadialFactor_mul_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)
  rw [mul_one] at h
  rw [h]
  norm_num

private theorem composeRadialFactor_mul_le_one {r : ℝ} (h₁ : r ≤ 1) :
    composeRadialFactor r * r ≤ 1 := by
  rcases le_total r (1 / 4) with h | h
  · rw [composeRadialFactor_of_le h]
    linarith
  rcases le_total r (1 / 2) with h' | h'
  · rw [composeRadialFactor_mul_of_mem h h']
    linarith
  · rw [composeRadialFactor_mul_of_le h']
    linarith

private theorem norm_composeRadialHomotopy_le {n : ℕ} (t : I) (x : TopCat.disk.{u} n) :
    ‖((1 - (t : ℝ)) * composeRadialFactor ‖x.down.1‖ + t) • x.down.1‖ ≤ 1 := by
  have hx : ‖x.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 x.down.2
  have hc := composeRadialFactor_nonneg ‖x.down.1‖
  have hcr := composeRadialFactor_mul_le_one hx
  have ht₀ := t.2.1
  have ht₁ := t.2.2
  rw [norm_smul, Real.norm_of_nonneg (by nlinarith)]
  nlinarith

/-- The straight-line homotopy `(t, x) ↦ ((1 - t) c(‖x‖) + t) • x` of the disc, for the radial
factor `c` of `composeRadialFactor`: it starts at the radial reparametrization sending the radii
`1/4` and `1/2` to `1/2` and `3/4`, ends at the identity, and fixes the boundary sphere. -/
private def composeRadialHomotopy (n : ℕ) : C(I × TopCat.disk.{u} n, TopCat.disk.{u} n) where
  toFun q := ULift.up ⟨((1 - (q.1 : ℝ)) * composeRadialFactor ‖q.2.down.1‖ + q.1) • q.2.down.1,
    mem_closedBall_zero_iff.2 (norm_composeRadialHomotopy_le q.1 q.2)⟩
  continuous_toFun := by
    have hx : Continuous fun q : I × TopCat.disk.{u} n ↦ (q.2.down.1 : EuclideanSpace ℝ (Fin n)) :=
      continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd)
    have ht : Continuous fun q : I × TopCat.disk.{u} n ↦ (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact continuous_uliftUp.comp ((((continuous_const.sub ht).mul
      (continuous_composeRadialFactor.comp hx.norm)).add ht).smul hx |>.subtype_mk _)

private theorem coe_composeRadialHomotopy_apply_down {n : ℕ} (t : I) (x : TopCat.disk.{u} n) :
    ((composeRadialHomotopy n (t, x)).down : EuclideanSpace ℝ (Fin n)) =
      ((1 - (t : ℝ)) * composeRadialFactor ‖x.down.1‖ + t) • x.down.1 :=
  (rfl)

private theorem coe_composeRadialHomotopy_zero_apply_down {n : ℕ} (x : TopCat.disk.{u} n) :
    ((composeRadialHomotopy n (0, x)).down : EuclideanSpace ℝ (Fin n)) =
      composeRadialFactor ‖x.down.1‖ • x.down.1 := by
  rw [coe_composeRadialHomotopy_apply_down]
  simp

private theorem composeRadialHomotopy_one {n : ℕ} (x : TopCat.disk.{u} n) :
    composeRadialHomotopy n (1, x) = x :=
  ULift.ext (Subtype.ext ((coe_composeRadialHomotopy_apply_down 1 x).trans (by simp)))

private theorem composeRadialHomotopy_diskBoundaryInclusion {n : ℕ} (t : I)
    (s : TopCat.diskBoundary.{u} n) :
    composeRadialHomotopy n (t, TopCat.diskBoundaryInclusion n s) =
      TopCat.diskBoundaryInclusion n s := by
  refine ULift.ext (Subtype.ext ((coe_composeRadialHomotopy_apply_down t _).trans ?_))
  rw [TopCat.norm_diskBoundaryInclusion, composeRadialFactor_one]
  simp

/-- The radial homotopy `composeRadialHomotopy` applied to the disc coordinate of
`P × D^n`. -/
private def composeRadialHomotopyProd (P : Type*) [TopologicalSpace P] (n : ℕ) :
    C(I × (P × TopCat.disk.{u} n), P × TopCat.disk.{u} n) :=
  ⟨fun q ↦ (q.2.1, composeRadialHomotopy n (q.1, q.2.2)),
    (continuous_fst.comp continuous_snd).prodMk ((composeRadialHomotopy n).continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩

/-- The norm of the radial reparametrization of a vector of norm `r` is `2r` for `r ≤ 1/4`. -/
private theorem norm_composeRadialHomotopy_zero_of_le {n : ℕ} {x : TopCat.disk.{u} n}
    (hx : ‖x.down.1‖ ≤ 1 / 4) :
    ‖(composeRadialHomotopy n (0, x)).down.1‖ = 2 * ‖x.down.1‖ := by
  rw [coe_composeRadialHomotopy_zero_apply_down, composeRadialFactor_of_le hx, norm_smul,
    Real.norm_two]

private theorem norm_composeRadialHomotopy_zero {n : ℕ} (x : TopCat.disk.{u} n) :
    ‖(composeRadialHomotopy n (0, x)).down.1‖ = composeRadialFactor ‖x.down.1‖ * ‖x.down.1‖ := by
  rw [coe_composeRadialHomotopy_zero_apply_down, norm_smul,
    Real.norm_of_nonneg (composeRadialFactor_nonneg _)]

/-! ### Composing two reattachment maps -/

variable {P Y : Type u} [TopologicalSpace P] [TopologicalSpace Y] {A : Set Y} {ι : Type u}
  {k : ι → ℕ}

section Composition

variable (α₀ α₁ α₂ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ χ₂ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (hχ₂ : ∀ i p s, χ₂ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₂ i (p, s))
  (h₀₁ h₁₂ h₀₂ : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh₀₁ : ∀ i p, MapsTo (fun w ↦ h₀₁ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh₁₂ : ∀ i p, MapsTo (fun w ↦ h₁₂ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh₀₂ : ∀ i p, MapsTo (fun w ↦ h₀₂ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K₀₁ : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h₀₁ i))))
  (hK₀₁ : ∀ i t p s, K₀₁ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (K₁₂ : ∀ i, (χ₂ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (h₁₂ i))))
  (hK₁₂ : ∀ i t p s, K₁₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (K₀₂ : ∀ i, (χ₂ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h₀₂ i))))
  (hK₀₂ : ∀ i t p s, K₀₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (e₁₂ : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (he₁₂ : ∀ i p w, ((h₁₂ i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = e₁₂ i p w.down)
  (hh : ∀ i x, h₀₂ i x = h₀₁ i (x.1, h₁₂ i x))
  (hK : ∀ i x, K₀₂ i x =
    ((K₁₂ i).trans ((K₀₁ i).compContinuousMap (ContinuousMap.fst.prodMk (h₁₂ i)))) x)

include hK in
/-- Up to time `1/2`, the concatenated homotopy `K₀₂ i` runs along `K₁₂ i` at double speed. -/
private theorem apply_of_le_half {i : ι} {t t' : I} (ht' : (t' : ℝ) ≤ 1 / 2)
    (ht : (t : ℝ) = 2 * t') (x : P × TopCat.disk.{u} (k i)) : K₀₂ i (t', x) = K₁₂ i (t, x) := by
  rw [hK, ContinuousMap.Homotopy.trans_apply]
  split_ifs with h
  · exact congrArg (fun t ↦ K₁₂ i (t, x)) (Subtype.ext ht.symm)
  · exact absurd ht' h

include hK in
/-- From time `1/2` on, the concatenated homotopy `K₀₂ i` runs along `K₀₁ i ∘ (p, h₁₂ i)` at
double speed. -/
private theorem apply_of_half_le {i : ι} {t t' : I} (ht' : 1 / 2 ≤ (t' : ℝ))
    (ht : (t : ℝ) = 2 * t' - 1) (x : P × TopCat.disk.{u} (k i)) :
    K₀₂ i (t', x) = K₀₁ i (t, (x.1, h₁₂ i x)) := by
  rw [hK, ContinuousMap.Homotopy.trans_apply]
  split_ifs with h
  · -- At the seam `t' = 1/2` both `K₁₂ i (1, x)` and `K₀₁ i (0, (x.1, h₁₂ i x))` are
    -- `χ₁ i (x.1, h₁₂ i x)`.
    have h₁ : ∀ hm, (⟨2 * (t' : ℝ), hm⟩ : I) = 1 := fun _ ↦
      Subtype.ext (by rw [Set.Icc.coe_one]; linarith)
    have h₀ : t = 0 := Subtype.ext (by rw [ht, Set.Icc.coe_zero]; linarith)
    rw [h₁, h₀, ContinuousMap.Homotopy.apply_one, ContinuousMap.Homotopy.apply_zero]
    rfl
  · rw [ContinuousMap.Homotopy.compContinuousMap_apply]
    exact congrArg (fun t ↦ K₀₁ i (t, (x.1, h₁₂ i x))) (Subtype.ext ht.symm)

include he₁₂ hh in
/-- On the disc of radius `1/4`, both the composite of two reattachment maps and the reattachment
map of the composed data after the radial reparametrization send `w` to `h₀₁ i (p, h₁₂ i (p, 4w))`
in the `i`-th cell. -/
private theorem comp_cell_of_norm_le_quarter (i : ι) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.1‖ ≤ 1 / 4) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, composeRadialHomotopy (k i) (0, w))) := by
  have hw₂ : ‖w.down.1‖ ≤ 1 / 2 := by linarith
  have hw'₂ : ‖(composeRadialHomotopy (k i) (0, w)).down.1‖ ≤ 1 / 2 := by
    rw [norm_composeRadialHomotopy_zero_of_le hw]
    linarith
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂
      K₁₂ hK₁₂ i p hw₂ (TopCat.coe_reattachmentRadial_of_norm_le hw₂),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂
      hh₀₂ K₀₂ hK₀₂ i p hw'₂ (TopCat.coe_reattachmentRadial_of_norm_le hw'₂), hh,
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁
      hh₀₁ K₀₁ hK₀₁ i p (by
        rw [he₁₂, LinearIsometryEquiv.norm_map, TopCat.coe_reattachmentRadial_of_norm_le hw₂,
          norm_smul, Real.norm_two]
        linarith)]
  rw [he₁₂, he₁₂, TopCat.coe_reattachmentRadial_of_norm_le hw'₂,
    TopCat.coe_reattachmentRadial_of_norm_le hw₂, coe_composeRadialHomotopy_zero_apply_down,
    composeRadialFactor_of_le hw, map_smul, map_smul]

include he₁₂ hK in
/-- On the annulus `1/4 ≤ ‖w‖ ≤ 1/2`, both the composite of two reattachment maps and the
reattachment map of the composed data after the radial reparametrization run along `K₀₁ i` at
the direction of `h₁₂ i (p, w)`. -/
private theorem comp_cell_of_quarter_le_of_le_half (i : ι) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw₄ : 1 / 4 ≤ ‖w.down.1‖) (hw₂ : ‖w.down.1‖ ≤ 1 / 2) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, composeRadialHomotopy (k i) (0, w))) := by
  set r := ‖w.down.1‖
  set w' := composeRadialHomotopy (k i) (0, w)
  set v := h₁₂ i (p, TopCat.reattachmentRadial w)
  have hw' : w'.down.1 = composeRadialFactor r • w.down.1 :=
    coe_composeRadialHomotopy_zero_apply_down w
  have hv : ‖v.down.1‖ = 2 * r := by
    rw [he₁₂, LinearIsometryEquiv.norm_map, TopCat.coe_reattachmentRadial_of_norm_le hw₂,
      norm_smul, Real.norm_two]
  have hv₂ : 1 / 2 ≤ ‖v.down.1‖ := by
    rw [hv]
    linarith
  have hw'n : ‖w'.down.1‖ = r + 1 / 4 := by
    rw [norm_composeRadialHomotopy_zero, composeRadialFactor_mul_of_mem hw₄ hw₂]
  have hw'₂ : 1 / 2 ≤ ‖w'.down.1‖ := by
    rw [hw'n]
    linarith
  -- `h₁₂ i (p, ·)` carries the direction of `w'` to the direction of `v`
  have hdir : h₁₂ i (p, TopCat.diskBoundaryInclusion (k i)
      (TopCat.annulusDir (by norm_num) ⟨w', hw'₂⟩)) =
      TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨v, hv₂⟩) := by
    refine ULift.ext (Subtype.ext ?_)
    rw [he₁₂, TopCat.coe_diskBoundaryInclusion_apply_down,
      TopCat.coe_diskBoundaryInclusion_apply_down, TopCat.coe_annulusDir, TopCat.coe_annulusDir,
      hw'n, hv, he₁₂, TopCat.coe_reattachmentRadial_of_norm_le hw₂, hw', map_smul, map_smul,
      map_smul, smul_smul, smul_smul]
    congr 1
    have hr₀ : r ≠ 0 := by linarith
    rw [eq_div_of_mul_eq hr₀ (composeRadialFactor_mul_of_mem hw₄ hw₂)]
    field_simp
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂
      K₁₂ hK₁₂ i p hw₂ (TopCat.coe_reattachmentRadial_of_norm_le hw₂),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁
      hh₀₁ K₀₁ hK₀₁ i p hv₂ (TopCat.coe_reattachmentTime_of_le_norm hv₂)
      (s := TopCat.annulusDir (by norm_num) ⟨v, hv₂⟩) (TopCat.coe_annulusDir _ _),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂
      hh₀₂ K₀₂ hK₀₂ i p hw'₂ (TopCat.coe_reattachmentTime_of_le_norm hw'₂)
      (s := TopCat.annulusDir (by norm_num) ⟨w', hw'₂⟩) (TopCat.coe_annulusDir _ _)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (p, a)) (Subtype.ext ?_)
  dsimp only
  have hK' := apply_of_half_le χ₀ χ₁ χ₂ h₀₁ h₁₂ h₀₂ K₀₁ K₁₂ K₀₂ hK
    (t := TopCat.reattachmentTime v) (t' := TopCat.reattachmentTime w')
    (by rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, hw'n]; linarith)
    (by rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, TopCat.coe_reattachmentTime_of_le_norm hv₂,
      hw'n, hv]; ring)
    (p, TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨w', hw'₂⟩))
  rw [hK', hdir]

include hK in
/-- On the annulus `1/2 ≤ ‖w‖`, both the composite of two reattachment maps and the reattachment
map of the composed data after the radial reparametrization run along `K₁₂ i` at the direction of
`w`. -/
private theorem comp_cell_of_half_le (i : ι) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw₂ : 1 / 2 ≤ ‖w.down.1‖) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, composeRadialHomotopy (k i) (0, w))) := by
  set r := ‖w.down.1‖ with hr
  set w' := composeRadialHomotopy (k i) (0, w)
  have hw' : w'.down.1 = composeRadialFactor r • w.down.1 :=
    coe_composeRadialHomotopy_zero_apply_down w
  have hw'n : ‖w'.down.1‖ = (r + 1) / 2 := by
    rw [norm_composeRadialHomotopy_zero, composeRadialFactor_mul_of_le hw₂]
  have hw'₂ : 1 / 2 ≤ ‖w'.down.1‖ := by
    rw [hw'n]
    linarith
  -- `w'` has the direction of `w`
  have hdir : TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w', hw'₂⟩ =
      TopCat.annulusDir (by norm_num) ⟨w, hw₂⟩ := by
    refine ULift.ext (Subtype.ext ?_)
    rw [TopCat.coe_annulusDir, TopCat.coe_annulusDir, hw'n, hw', smul_smul]
    congr 1
    have hr₀ : r ≠ 0 := by linarith
    have hr₁ : r + 1 ≠ 0 := by linarith
    simp only [← hr, eq_div_of_mul_eq hr₀ (composeRadialFactor_mul_of_le hw₂)]
    field_simp
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂
      hh₁₂ K₁₂ hK₁₂ i p hw₂ (TopCat.coe_reattachmentTime_of_le_norm hw₂)
      (s := TopCat.annulusDir (by norm_num) ⟨w, hw₂⟩) (TopCat.coe_annulusDir _ _),
    fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂
      hh₀₂ K₀₂ hK₀₂ i p hw'₂ (TopCat.coe_reattachmentTime_of_le_norm hw'₂)
      (s := TopCat.annulusDir (by norm_num) ⟨w', hw'₂⟩) (TopCat.coe_annulusDir _ _)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (p, a)) (Subtype.ext ?_)
  dsimp only
  have hK' := apply_of_le_half χ₀ χ₁ χ₂ h₀₁ h₁₂ h₀₂ K₀₁ K₁₂ K₀₂ hK
    (t := TopCat.reattachmentTime w) (t' := TopCat.reattachmentTime w')
    (by rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, hw'n]; linarith)
    (by rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, TopCat.coe_reattachmentTime_of_le_norm hw₂,
      hw'n]; ring)
    (p, TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨w', hw'₂⟩))
  rw [hK', hdir]

include he₁₂ hh hK in
/-- On the `i`-th cell, the composite of two reattachment maps is the reattachment map of the
composed data after the radial reparametrization `composeRadialHomotopy` at time `0`. -/
private theorem fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell
    (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, composeRadialHomotopy (k i) (0, w))) := by
  rcases le_total ‖w.down.1‖ (1 / 2) with hw₂ | hw₂
  · rcases le_total ‖w.down.1‖ (1 / 4) with hw₄ | hw₄
    · exact comp_cell_of_norm_le_quarter α₀ α₁ α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂ hh₀₂
        K₀₁ hK₀₁ K₁₂ hK₁₂ K₀₂ hK₀₂ e₁₂ he₁₂ hh i p hw₄
    · exact comp_cell_of_quarter_le_of_le_half α₀ α₁ α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂
        hh₀₂ K₀₁ hK₀₁ K₁₂ hK₁₂ K₀₂ hK₀₂ e₁₂ he₁₂ hK i p hw₄ hw₂
  · exact comp_cell_of_half_le α₀ α₁ α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂ hh₀₂ K₀₁ hK₀₁
      K₁₂ hK₁₂ K₀₂ hK₀₂ hK i p hw₂

/-- The composite of two reattachment maps is the identity on `P × A`. -/
private theorem comp_fiberwiseCellAttachmentIncl (x : P × A) :
    (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂ ≫
      fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁).hom
        (fiberwiseCellAttachmentIncl α₂ x) = fiberwiseCellAttachmentIncl α₀ x := by
  rw [TopCat.hom_comp, ContinuousMap.comp_apply,
    fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
    fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]

include he₁₂ hh hK in
/-- **Fiberwise reattachment maps compose to the reattachment map of the composed data.** Let
`E₁₂` be the fiberwise reattachment map of disc maps `h₁₂ i` and homotopies
`K₁₂ i : χ₂ i ≃ χ₁ i ∘ (p, h₁₂ i)`, and `E₀₁` that of `h₀₁ i` and
`K₀₁ i : χ₁ i ≃ χ₀ i ∘ (p, h₀₁ i)`.
If each `h₁₂ i (p, ·)` is a linear isometry `e₁₂ i p` of the disc, then `E₀₁ ∘ E₁₂` is homotopic,
relative to `P × A` and through maps over `P`, to the fiberwise reattachment map `E₀₂` of the
composed disc maps `h₀₂ i (p, x) = h₀₁ i (p, h₁₂ i (p, x))` and the concatenated homotopies
`K₀₂ i = K₁₂ i * K₀₁ i ∘ (p, h₁₂ i)`. No left inverse of a comparison map is needed. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_of_eq_trans :
    ∃ G : (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂ ≫
        fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁).hom.HomotopyRel
        (fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂).hom
        (range (fiberwiseCellAttachmentIncl α₂)),
      ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₂ y := by
  set E₀₂ := fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
  -- On the `i`-th cell the homotopy is `E₀₂` after the straight-line radial homotopy.
  let C : ∀ i, C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α₀) := fun i ↦
    (fiberwiseCellAttachmentCell α₂ i ≫ E₀₂).hom.comp (composeRadialHomotopyProd P (k i))
  have hC : ∀ i t x, C i (t, x) =
      E₀₂ (fiberwiseCellAttachmentCell α₂ i (x.1, composeRadialHomotopy (k i) (t, x.2))) :=
    fun _ _ _ ↦ rfl
  have hCb : ∀ i t p s, C i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      ((fiberwiseCellAttachmentIncl α₀).hom.comp ContinuousMap.snd) (t, (p, α₂ i (p, s))) :=
    fun i t p s ↦ by
      rw [hC, composeRadialHomotopy_diskBoundaryInclusion,
        fiberwiseCellAttachmentCell_diskBoundaryInclusion]
      exact fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..
  have hE := comp_fiberwiseCellAttachmentIncl α₀ α₁ α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ hh₀₁ hh₁₂ K₀₁
    hK₀₁ K₁₂ hK₁₂
  let D := fiberwiseCellAttachmentCylinderDesc α₂
    ((fiberwiseCellAttachmentIncl α₀).hom.comp ContinuousMap.snd) C hCb
  refine ⟨{ toFun := D
            continuous_toFun := D.continuous
            map_zero_left := fun y ↦ ?_
            map_one_left := fun y ↦ ?_
            prop' := ?_ }, fun t y ↦ ?_⟩
  · refine fiberwiseCellAttachment_induction α₂ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl ..).trans (hE x).symm
    · refine (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell ..).trans ?_
      rw [hC, TopCat.hom_comp, ContinuousMap.comp_apply]
      exact (fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell α₀ α₁
        α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂ hh₀₂ K₀₁ hK₀₁ K₁₂ hK₁₂ K₀₂ hK₀₂ e₁₂ he₁₂ hh
        hK i x.1 x.2).symm
  · refine fiberwiseCellAttachment_induction α₂ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl ..).trans
        (fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..).symm
    · refine (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell ..).trans ?_
      rw [hC, composeRadialHomotopy_one]
  · rintro t _ ⟨x, rfl⟩
    exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl ..).trans (hE x).symm
  · refine fiberwiseCellAttachment_induction α₂ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact (congrArg (fiberwiseCellAttachmentProj α₀)
        (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl ..)).trans
        ((fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl α₀ x).trans
          (fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl α₂ x).symm)
    · refine (congrArg (fiberwiseCellAttachmentProj α₀)
        (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell ..)).trans ?_
      rw [hC, fiberwiseCellAttachmentProj_fiberwiseCellReattachment,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]

end Composition

end TauCeti
