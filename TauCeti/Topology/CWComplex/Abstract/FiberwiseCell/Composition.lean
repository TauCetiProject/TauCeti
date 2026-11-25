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

/-- The radial homotopy `TauCeti.TopCat.composeRadialHomotopy` applied to the disc coordinate of
`P × D^n`. -/
private def composeRadialHomotopyProd (P : Type*) [TopologicalSpace P] (n : ℕ) :
    C(I × (P × TopCat.disk.{u} n), P × TopCat.disk.{u} n) :=
  ⟨fun q ↦ (q.2.1, TopCat.composeRadialHomotopy n (q.1, q.2.2)),
    (continuous_fst.comp continuous_snd).prodMk ((TopCat.composeRadialHomotopy n).continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩

private theorem composeRadialHomotopyProd_apply (P : Type*) [TopologicalSpace P] (n : ℕ) (t : I)
    (x : P × TopCat.disk.{u} n) :
    composeRadialHomotopyProd P n (t, x) = (x.1, TopCat.composeRadialHomotopy n (t, x.2)) :=
  rfl

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

include he₁₂ in
/-- On the disc of radius `1/2`, `h₁₂ i (p, ·)` after the radial part of the reattachment map
doubles the norm. -/
private theorem norm_h₁₂_reattachmentRadial (i : ι) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.val‖ ≤ 1 / 2) :
    ‖(h₁₂ i (p, TopCat.reattachmentRadial w)).down.val‖ = 2 * ‖w.down.val‖ := by
  rw [he₁₂, LinearIsometryEquiv.norm_map, TopCat.coe_reattachmentRadial_of_norm_le hw, norm_smul,
    Real.norm_two]

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
        (fiberwiseCellAttachmentCell α₂ i (p, TopCat.composeRadialHomotopy (k i) (0, w))) := by
  have hw₂ : ‖w.down.val‖ ≤ 1 / 2 := by linarith
  have hw'₂ : ‖(TopCat.composeRadialHomotopy (k i) (0, w)).down.val‖ ≤ 1 / 2 := by
    rw [TopCat.norm_composeRadialHomotopy_zero, TopCat.composeRadialFactor_of_le_quarter hw]
    linarith
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂
      K₁₂ hK₁₂ i p hw₂ (TopCat.coe_reattachmentRadial_of_norm_le hw₂),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂
      hh₀₂ K₀₂ hK₀₂ i p hw'₂ (TopCat.coe_reattachmentRadial_of_norm_le hw'₂), hh,
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁
      hh₀₁ K₀₁ hK₀₁ i p (by
        rw [norm_h₁₂_reattachmentRadial h₁₂ e₁₂ he₁₂ i p hw₂]
        linarith)]
  simp [he₁₂, TopCat.coe_reattachmentRadial_of_norm_le hw'₂,
    TopCat.coe_reattachmentRadial_of_norm_le hw₂, TopCat.coe_composeRadialHomotopy_zero_apply_down,
    TopCat.composeRadialFactor_of_le_quarter hw]

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
        (fiberwiseCellAttachmentCell α₂ i (p, TopCat.composeRadialHomotopy (k i) (0, w))) := by
  set r := ‖w.down.val‖
  set w' := TopCat.composeRadialHomotopy (k i) (0, w)
  set v := h₁₂ i (p, TopCat.reattachmentRadial w)
  -- the direction of `w'`, which is that of `w`
  set s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 4) ⟨w, hw₄⟩
  have hv : ‖v.down.val‖ = 2 * r := norm_h₁₂_reattachmentRadial h₁₂ e₁₂ he₁₂ i p hw₂
  have hv₂ : 1 / 2 ≤ ‖v.down.val‖ := by
    rw [hv]
    linarith
  have hw'n : ‖w'.down.val‖ = r + 1 / 4 := by
    rw [TopCat.norm_composeRadialHomotopy_zero,
      TopCat.composeRadialFactor_mul_of_quarter_le_of_le_half hw₄ hw₂]
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
      ((TopCat.coe_annulusDir _ _).trans (TopCat.inv_norm_smul_composeRadialHomotopy_zero w).symm)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (p, a)) (Subtype.ext ?_)
  dsimp only
  rw [hK, ContinuousMap.Homotopy.trans_apply_of_eq_two_mul_sub_one _ _
      (TopCat.reattachmentTime v) (by
        rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, TopCat.coe_reattachmentTime_of_le_norm hv₂,
          hw'n, hv]
        ring),
    ContinuousMap.Homotopy.compContinuousMap_apply, ContinuousMap.prod_eval,
    ContinuousMap.fst_apply, hdir]

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
        (fiberwiseCellAttachmentCell α₂ i (p, TopCat.composeRadialHomotopy (k i) (0, w))) := by
  set w' := TopCat.composeRadialHomotopy (k i) (0, w)
  -- the direction of `w`, which is that of `w'`
  set s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw₂⟩
  have hw'n : ‖w'.down.val‖ = (‖w.down.val‖ + 1) / 2 := by
    rw [TopCat.norm_composeRadialHomotopy_zero, TopCat.composeRadialFactor_mul_of_half_le hw₂]
  have hw'₂ : 1 / 2 ≤ ‖w'.down.val‖ := by
    rw [hw'n]
    linarith
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂
      hh₁₂ K₁₂ hK₁₂ i p hw₂ (TopCat.coe_reattachmentTime_of_le_norm hw₂) (s := s)
      (TopCat.coe_annulusDir _ _),
    fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂
      hh₀₂ K₀₂ hK₀₂ i p hw'₂ (TopCat.coe_reattachmentTime_of_le_norm hw'₂) (s := s)
      ((TopCat.coe_annulusDir _ _).trans (TopCat.inv_norm_smul_composeRadialHomotopy_zero w).symm)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (p, a)) (Subtype.ext ?_)
  dsimp only
  rw [hK, ContinuousMap.Homotopy.trans_apply_of_eq_two_mul _ _ (TopCat.reattachmentTime w) (by
    rw [TopCat.coe_reattachmentTime_of_le_norm hw'₂, TopCat.coe_reattachmentTime_of_le_norm hw₂,
      hw'n]
    ring)]

include he₁₂ hh hK in
/-- On the `i`-th cell, the composite of two reattachment maps is the reattachment map of the
composed data after the radial reparametrization `TauCeti.TopCat.composeRadialHomotopy` at time
`0`. -/
private theorem fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell
    (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁
        (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
          (fiberwiseCellAttachmentCell α₂ i (p, w))) =
      fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂
        (fiberwiseCellAttachmentCell α₂ i (p, TopCat.composeRadialHomotopy (k i) (0, w))) := by
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
      E₀₂ (fiberwiseCellAttachmentCell α₂ i (x.1, TopCat.composeRadialHomotopy (k i) (t, x.2))) :=
    fun i t x ↦ by simp [C, composeRadialHomotopyProd_apply]
  have hCb : ∀ i t p s, C i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      ((fiberwiseCellAttachmentIncl α₀).hom.comp ContinuousMap.snd) (t, (p, α₂ i (p, s))) :=
    fun i t p s ↦ by rw [hC, TopCat.composeRadialHomotopy_diskBoundaryInclusion,
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
    fun t x ↦ by rw [fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl,
      ContinuousMap.comp_apply, ContinuousMap.snd_apply]
  have hDproj : ∀ t y, fiberwiseCellAttachmentProj α₀ (D (t, y)) =
      fiberwiseCellAttachmentProj α₂ y := fun t y ↦ by
    refine fiberwiseCellAttachment_induction α₂ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [hD, fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]
    · rw [fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell, hC,
        fiberwiseCellAttachmentProj_fiberwiseCellReattachment,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  -- The homotopy is the structure with underlying map `D`, so `hDproj` is its projection law.
  refine ⟨{ toFun := D, continuous_toFun := D.continuous, map_zero_left := fun y ↦ ?_,
            map_one_left := fun y ↦ ?_, prop' := ?_ }, hDproj⟩
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
      TopCat.composeRadialHomotopy_one]
  · rintro t _ ⟨x, rfl⟩
    exact (hD t x).trans (hE x).symm

end Composition

end TauCeti
