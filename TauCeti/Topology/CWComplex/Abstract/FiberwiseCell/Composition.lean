/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCell.Attachment
import TauCeti.Topology.Homotopy.Trans

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
The maps `h₀₁ i` are arbitrary, and the homotopies `K₀₂ i` only have to agree with the
concatenations on the boundary spheres `P × ∂D^{k i}`. Unlike
`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment`, this needs
no left homotopy inverse over `P` of a comparison map `(P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i}) → P × Y`.

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

private theorem composeRadialFactor_pos (r : ℝ) : 0 < composeRadialFactor r := by
  have := quarter_le_max r
  exact div_pos (lt_min (by linarith) (by linarith)) (by linarith)

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
    ‖((1 - (t : ℝ)) * composeRadialFactor ‖x.down.val‖ + t) • x.down.val‖ ≤ 1 := by
  have hx : ‖x.down.val‖ ≤ 1 := mem_closedBall_zero_iff.1 x.down.property
  have hc := (composeRadialFactor_pos ‖x.down.val‖).le
  have hcr := composeRadialFactor_mul_le_one hx
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  rw [norm_smul, Real.norm_of_nonneg (by nlinarith)]
  nlinarith

/-- The straight-line homotopy `(t, x) ↦ ((1 - t) c(‖x‖) + t) • x` of the disc, for the radial
factor `c` of `composeRadialFactor`: it starts at the radial reparametrization sending the radii
`1/4` and `1/2` to `1/2` and `3/4`, ends at the identity, and fixes the boundary sphere. -/
private def composeRadialHomotopy (n : ℕ) : C(I × TopCat.disk.{u} n, TopCat.disk.{u} n) where
  toFun q := ULift.up ⟨((1 - (q.1 : ℝ)) * composeRadialFactor ‖q.2.down.val‖ + q.1) • q.2.down.val,
    mem_closedBall_zero_iff.2 (norm_composeRadialHomotopy_le q.1 q.2)⟩
  continuous_toFun := by
    have hx : Continuous fun q : I × TopCat.disk.{u} n ↦
        (q.2.down.val : EuclideanSpace ℝ (Fin n)) :=
      continuous_subtypeVal.comp (continuous_uliftDown.comp continuous_snd)
    have ht : Continuous fun q : I × TopCat.disk.{u} n ↦ (q.1 : ℝ) :=
      continuous_subtypeVal.comp continuous_fst
    exact continuous_uliftUp.comp ((((continuous_const.sub ht).mul
      (continuous_composeRadialFactor.comp hx.norm)).add ht).smul hx |>.subtype_mk _)

private theorem coe_composeRadialHomotopy_apply_down {n : ℕ} (t : I) (x : TopCat.disk.{u} n) :
    ((composeRadialHomotopy n (t, x)).down : EuclideanSpace ℝ (Fin n)) =
      ((1 - (t : ℝ)) * composeRadialFactor ‖x.down.val‖ + t) • x.down.val :=
  (rfl)

private theorem coe_composeRadialHomotopy_zero_apply_down {n : ℕ} (x : TopCat.disk.{u} n) :
    ((composeRadialHomotopy n (0, x)).down : EuclideanSpace ℝ (Fin n)) =
      composeRadialFactor ‖x.down.val‖ • x.down.val := by
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

private theorem composeRadialHomotopyProd_apply (P : Type*) [TopologicalSpace P] (n : ℕ) (t : I)
    (x : P × TopCat.disk.{u} n) :
    composeRadialHomotopyProd P n (t, x) = (x.1, composeRadialHomotopy n (t, x.2)) :=
  rfl

private theorem norm_composeRadialHomotopy_zero {n : ℕ} (x : TopCat.disk.{u} n) :
    ‖(composeRadialHomotopy n (0, x)).down.val‖ =
      composeRadialFactor ‖x.down.val‖ * ‖x.down.val‖ := by
  rw [coe_composeRadialHomotopy_zero_apply_down, norm_smul,
    Real.norm_of_nonneg (composeRadialFactor_pos _).le]

/-- The radial reparametrization preserves the direction of every vector. -/
private theorem inv_norm_smul_composeRadialHomotopy_zero {n : ℕ} (x : TopCat.disk.{u} n) :
    ‖(composeRadialHomotopy n (0, x)).down.val‖⁻¹ • (composeRadialHomotopy n (0, x)).down.val =
      ‖x.down.val‖⁻¹ • x.down.val := by
  rw [norm_composeRadialHomotopy_zero, coe_composeRadialHomotopy_zero_apply_down, smul_smul,
    mul_inv_rev, mul_assoc, inv_mul_cancel₀ (composeRadialFactor_pos _).ne', mul_one]

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
  (hK : ∀ i t p s, K₀₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
    ((K₁₂ i).trans ((K₀₁ i).compContinuousMap (ContinuousMap.fst.prodMk (h₁₂ i))))
      (t, (p, TopCat.diskBoundaryInclusion (k i) s)))

include he₁₂ hh in
/-- On the disc of radius `1/4`, both the composite of two reattachment maps and the reattachment
map of the composed data after the radial reparametrization send `w` to `h₀₁ i (p, h₁₂ i (p, 4w))`
in the `i`-th cell. -/
private theorem comp_cell_of_norm_le_quarter (i : ι) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.val‖ ≤ 1 / 4) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, composeRadialHomotopy (k i) (0, w))) := by
  have hw₂ : ‖w.down.val‖ ≤ 1 / 2 := by linarith
  have hw'₂ : ‖(composeRadialHomotopy (k i) (0, w)).down.val‖ ≤ 1 / 2 := by
    rw [norm_composeRadialHomotopy_zero, composeRadialFactor_of_le hw]
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
  simp [he₁₂, TopCat.coe_reattachmentRadial_of_norm_le hw'₂,
    TopCat.coe_reattachmentRadial_of_norm_le hw₂, coe_composeRadialHomotopy_zero_apply_down,
    composeRadialFactor_of_le hw]

include he₁₂ hK in
/-- On the annulus `1/4 ≤ ‖w‖ ≤ 1/2`, both the composite of two reattachment maps and the
reattachment map of the composed data after the radial reparametrization run along `K₀₁ i` at
the direction of `h₁₂ i (p, w)`. -/
private theorem comp_cell_of_quarter_le_of_le_half (i : ι) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw₄ : 1 / 4 ≤ ‖w.down.val‖) (hw₂ : ‖w.down.val‖ ≤ 1 / 2) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, composeRadialHomotopy (k i) (0, w))) := by
  set r := ‖w.down.val‖
  set w' := composeRadialHomotopy (k i) (0, w)
  set v := h₁₂ i (p, TopCat.reattachmentRadial w)
  -- the direction of `w'`, which is that of `w`
  set s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 4) ⟨w, hw₄⟩
  have hv : ‖v.down.val‖ = 2 * r := by
    rw [he₁₂, LinearIsometryEquiv.norm_map, TopCat.coe_reattachmentRadial_of_norm_le hw₂,
      norm_smul, Real.norm_two]
  have hv₂ : 1 / 2 ≤ ‖v.down.val‖ := by
    rw [hv]
    linarith
  have hw'n : ‖w'.down.val‖ = r + 1 / 4 := by
    rw [norm_composeRadialHomotopy_zero, composeRadialFactor_mul_of_mem hw₄ hw₂]
  have hw'₂ : 1 / 2 ≤ ‖w'.down.val‖ := by
    rw [hw'n]
    linarith
  -- `h₁₂ i (p, ·)` carries the direction of `w` to the direction of `v`
  have hdir : h₁₂ i (p, TopCat.diskBoundaryInclusion (k i) s) =
      TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨v, hv₂⟩) := by
    refine ULift.ext (Subtype.ext ?_)
    rw [he₁₂, TopCat.coe_diskBoundaryInclusion_apply_down,
      TopCat.coe_diskBoundaryInclusion_apply_down, TopCat.coe_annulusDir, TopCat.coe_annulusDir,
      hv, he₁₂, TopCat.coe_reattachmentRadial_of_norm_le hw₂, map_smul, map_smul, smul_smul]
    congr 1
    field_simp
    exact div_self (by linarith : r ≠ 0)
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂
      K₁₂ hK₁₂ i p hw₂ (TopCat.coe_reattachmentRadial_of_norm_le hw₂),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁
      hh₀₁ K₀₁ hK₀₁ i p hv₂ (TopCat.coe_reattachmentTime_of_le_norm hv₂)
      (s := TopCat.annulusDir (by norm_num) ⟨v, hv₂⟩) (TopCat.coe_annulusDir _ _),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂
      hh₀₂ K₀₂ hK₀₂ i p hw'₂ (TopCat.coe_reattachmentTime_of_le_norm hw'₂) (s := s)
      ((TopCat.coe_annulusDir _ _).trans (inv_norm_smul_composeRadialHomotopy_zero w).symm)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (p, a)) (Subtype.ext ?_)
  dsimp only
  rw [hK, ContinuousMap.Homotopy.trans_apply_of_eq_two_mul_sub_one _ _
      (TopCat.reattachmentTime v) (by
        rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, TopCat.coe_reattachmentTime_of_le_norm hv₂,
          hw'n, hv]
        ring),
    ContinuousMap.Homotopy.compContinuousMap_apply, ContinuousMap.prod_eval, hdir]
  rfl

include hK in
/-- On the annulus `1/2 ≤ ‖w‖`, both the composite of two reattachment maps and the reattachment
map of the composed data after the radial reparametrization run along `K₁₂ i` at the direction of
`w`. -/
private theorem comp_cell_of_half_le (i : ι) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw₂ : 1 / 2 ≤ ‖w.down.val‖) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, composeRadialHomotopy (k i) (0, w))) := by
  set w' := composeRadialHomotopy (k i) (0, w)
  -- the direction of `w`, which is that of `w'`
  set s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw₂⟩
  have hw'n : ‖w'.down.val‖ = (‖w.down.val‖ + 1) / 2 := by
    rw [norm_composeRadialHomotopy_zero, composeRadialFactor_mul_of_le hw₂]
  have hw'₂ : 1 / 2 ≤ ‖w'.down.val‖ := by
    rw [hw'n]
    linarith
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂
      hh₁₂ K₁₂ hK₁₂ i p hw₂ (TopCat.coe_reattachmentTime_of_le_norm hw₂) (s := s)
      (TopCat.coe_annulusDir _ _),
    fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂
      hh₀₂ K₀₂ hK₀₂ i p hw'₂ (TopCat.coe_reattachmentTime_of_le_norm hw'₂) (s := s)
      ((TopCat.coe_annulusDir _ _).trans (inv_norm_smul_composeRadialHomotopy_zero w).symm)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (p, a)) (Subtype.ext ?_)
  dsimp only
  rw [hK, ContinuousMap.Homotopy.trans_apply_of_eq_two_mul _ _ (TopCat.reattachmentTime w) (by
    rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, TopCat.coe_reattachmentTime_of_le_norm hw₂,
      hw'n]
    ring)]

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
  rcases le_total ‖w.down.val‖ (1 / 2) with hw₂ | hw₂
  · rcases le_total ‖w.down.val‖ (1 / 4) with hw₄ | hw₄
    · exact comp_cell_of_norm_le_quarter α₀ α₁ α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂ hh₀₂
        K₀₁ hK₀₁ K₁₂ hK₁₂ K₀₂ hK₀₂ e₁₂ he₁₂ hh i p hw₄
    · exact comp_cell_of_quarter_le_of_le_half α₀ α₁ α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂
        hh₀₂ K₀₁ hK₀₁ K₁₂ hK₁₂ K₀₂ hK₀₂ e₁₂ he₁₂ hK i p hw₄ hw₂
  · exact comp_cell_of_half_le α₀ α₁ α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂ hh₀₂ K₀₁ hK₀₁
      K₁₂ hK₁₂ K₀₂ hK₀₂ hK i p hw₂

include he₁₂ hh hK in
/-- **Fiberwise reattachment maps compose to the reattachment map of the composed data.** Let
`E₁₂` be the fiberwise reattachment map of disc maps `h₁₂ i` and homotopies
`K₁₂ i : χ₂ i ≃ χ₁ i ∘ (p, h₁₂ i)`, and `E₀₁` that of `h₀₁ i` and
`K₀₁ i : χ₁ i ≃ χ₀ i ∘ (p, h₀₁ i)`.
If each `h₁₂ i (p, ·)` is a linear isometry `e₁₂ i p` of the disc, then `E₀₁ ∘ E₁₂` is homotopic,
relative to `P × A` and through maps over `P`, to the fiberwise reattachment map `E₀₂` of the
composed disc maps `h₀₂ i (p, x) = h₀₁ i (p, h₁₂ i (p, x))` and of any homotopies `K₀₂ i` that
agree on the boundary spheres `P × ∂D^{k i}` with the concatenations
`K₁₂ i * K₀₁ i ∘ (p, h₁₂ i)`. No left homotopy inverse of a comparison map is needed. -/
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
    fun i t x ↦ by simp [C, composeRadialHomotopyProd_apply]
  have hCb : ∀ i t p s, C i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      ((fiberwiseCellAttachmentIncl α₀).hom.comp ContinuousMap.snd) (t, (p, α₂ i (p, s))) :=
    fun i t p s ↦ by
      rw [hC, composeRadialHomotopy_diskBoundaryInclusion,
        fiberwiseCellAttachmentCell_diskBoundaryInclusion,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl, ContinuousMap.comp_apply,
        ContinuousMap.snd_apply]
  have hE : ∀ x, (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂ ≫
      fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁).hom
        (fiberwiseCellAttachmentIncl α₂ x) = fiberwiseCellAttachmentIncl α₀ x := fun x ↦ by
    rw [TopCat.hom_comp, ContinuousMap.comp_apply,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
  let D := fiberwiseCellAttachmentCylinderDesc α₂
    ((fiberwiseCellAttachmentIncl α₀).hom.comp ContinuousMap.snd) C hCb
  have hD : ∀ t x, D (t, fiberwiseCellAttachmentIncl α₂ x) = fiberwiseCellAttachmentIncl α₀ x :=
    fun t x ↦ by
      rw [fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl, ContinuousMap.comp_apply,
        ContinuousMap.snd_apply]
  refine ⟨{ toFun := D, continuous_toFun := D.continuous, map_zero_left := fun y ↦ ?_,
            map_one_left := fun y ↦ ?_, prop' := ?_ }, fun t y ↦ ?_⟩
  · refine fiberwiseCellAttachment_induction α₂ (fun x ↦ (hD 0 x).trans (hE x).symm)
      (fun i x ↦ ?_) y
    rw [fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell, hC, TopCat.hom_comp,
      ContinuousMap.comp_apply]
    exact (fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell α₀ α₁
      α₂ χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ h₀₁ h₁₂ h₀₂ hh₀₁ hh₁₂ hh₀₂ K₀₁ hK₀₁ K₁₂ hK₁₂ K₀₂ hK₀₂ e₁₂ he₁₂ hh
      hK i x.1 x.2).symm
  · refine fiberwiseCellAttachment_induction α₂ (fun x ↦ (hD 1 x).trans
      (fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..).symm) (fun i x ↦ ?_) y
    rw [fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell, hC,
      composeRadialHomotopy_one]
  · rintro t _ ⟨x, rfl⟩
    exact (hD t x).trans (hE x).symm
  · change fiberwiseCellAttachmentProj α₀ (D (t, y)) = _
    refine fiberwiseCellAttachment_induction α₂ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [hD, fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]
    · rw [fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell, hC,
        fiberwiseCellAttachmentProj_fiberwiseCellReattachment,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]

end Composition

end TauCeti
