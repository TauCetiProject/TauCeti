/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.SpecialFunctions.Sigmoid
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Deriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod
import TauCeti.Geometry.Manifold.SmoothIsotopy.Arc

/-!
# Moving an arc of a concordance onto a straight line

Let `F : M × ℝ → Sⁿ × ℝ` be a smooth concordance (`TauCeti.SmoothEmbedding.Concordance`) from `f`
to `g`, two smooth embeddings into the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner
product space, and let `z₀` be a point of `M` with `f z₀ = g z₀`. Along the line `{z₀} × ℝ` the
concordance traces an arc `t ↦ F (z₀, t)` which is the straight line `t ↦ (f z₀, t)` near both ends.
In dimension `n ≥ 3` the arc can be straightened in the middle as well: some concordance `G` from
`f` to `g` has `G (z₀, t) = (f z₀, t)` for every `t`
(`TauCeti.SmoothEmbedding.Concordance.exists_apply_eq_line`). It is `Ψ ∘ F` for a diffeomorphism
`Ψ` of `Sⁿ × ℝ` which is the identity outside a compact subset of the open slab `Sⁿ × (0, 1)`.

The arc is read in one chart, where arcs are unknotted.

* **The chart.** A differentiable path in a sphere of dimension at least two omits a point `p`
  (`TauCeti.exists_notMem_range_real_sphere`); `p ≠ f z₀`, since the arc passes over `f z₀`. The
  map `χ : (y, s) ↦ (σ⁻¹_p y, Real.sigmoid s)`, from `ℝⁿ × ℝ` to `Sⁿ × ℝ`, where `σ⁻¹_p` is inverse
  stereographic projection from `p`, is an open embedding and a smooth local diffeomorphism onto
  `(Sⁿ \ {p}) × (0, 1)`, which contains the arc over the open interval `(0, 1)`.
* **The arc in the chart.** Run at the time `Real.sigmoid s`, the arc is `χ ∘ β` for a smooth
  injective immersion `β : ℝ → ℝⁿ × ℝ` which is the affine line `s ↦ (σ_p (f z₀), s)` for large
  `|s|`.
* **Unknotting.** In `ℝⁿ × ℝ`, of dimension at least four, a compactly supported diffeomorphism `Φ`
  carries `β` onto the line (`TauCeti.exists_diffeomorph_apply_eq_line_of_four_le_finrank`), and
  `Φ` extends along `χ` by the identity to the diffeomorphism `Ψ` of `Sⁿ × ℝ`
  (`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact`). It fixes everything outside the
  image under `χ` of a compact set off which `Φ` is the identity; that image is a compact subset of
  the open slab, so `Ψ ∘ F` is again a collared track from `f` to `g`
  (`TauCeti.IsCollaredTrack.comp_of_isCompact`).

For knots `f, g : S¹ → S³` in connected-sum position, joined by a concordance, this puts the arc of
the concordance over the base point `-i` of the circle onto the line of the standard strip
`(z, t) ↦ (ι z, t)`, a first step toward a concordance which agrees with the strip near that
line.

## Main results

* `TauCeti.SmoothEmbedding.Concordance.exists_diffeomorph_apply_eq_line`: a diffeomorphism of
  `Sⁿ × ℝ`, the identity outside a compact subset of the open slab, carrying the arc of a
  concordance onto the straight line.
* `TauCeti.SmoothEmbedding.Concordance.exists_apply_eq_line`: a concordance from `f` to `g` whose
  arc over `z₀` is the straight line.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, §1 (isotopy extension).
* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448.
-/

public section

noncomputable section

open Function Module Set Topology Filter Manifold Metric
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothEmbedding.Concordance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {f g : SmoothEmbedding I (𝓡 n) ∞ M (sphere (0 : E) 1)}

/-- The chart `(y, s) ↦ (σ⁻¹_p y, Real.sigmoid s)` of the product `Sⁿ × ℝ`, inverse stereographic
projection from `p` times the logistic sigmoid. -/
private def slabChart (p : sphere (0 : E) 1) :
    EuclideanSpace ℝ (Fin n) × ℝ → sphere (0 : E) 1 × ℝ :=
  Prod.map (stereographic' n p).symm Real.sigmoid

private theorem slabChart_apply (p : sphere (0 : E) 1) (y : EuclideanSpace ℝ (Fin n) × ℝ) :
    slabChart (n := n) p y = ((stereographic' n p).symm y.1, Real.sigmoid y.2) :=
  rfl

private theorem isOpenEmbedding_slabChart (p : sphere (0 : E) 1) :
    IsOpenEmbedding (slabChart (n := n) p) :=
  ((stereographic' n p).symm.isOpenEmbedding (by simp)).prodMap
    ⟨IsEmbedding.subtypeVal.comp Topology.isEmbedding_sigmoid, Real.range_sigmoid ▸ isOpen_Ioo⟩

private theorem isLocalDiffeomorph_slabChart (p : sphere (0 : E) 1) :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ((𝓡 n).prod 𝓘(ℝ)) ∞
      (slabChart (n := n) p) := by
  have hst : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (stereographic' n p).symm := fun y =>
    (stereographic' n p).isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
      (stereographic'_mem_maximalAtlas p) (by simp)
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hst.prodMap (isLocalDiffeomorph_sigmoid (by simp))

/-- The points of `Sⁿ × ℝ` in the image of the chart are those off `{p} × ℝ` in the open slab. -/
private theorem mem_range_slabChart {p : sphere (0 : E) 1} {q : sphere (0 : E) 1 × ℝ}
    (hq₁ : q.1 ≠ p) (hq₂ : q.2 ∈ Ioo (0 : ℝ) 1) : q ∈ range (slabChart (n := n) p) :=
  ⟨((stereographic' n p) q.1, Real.log (q.2 / (1 - q.2))), Prod.ext
    ((stereographic' n p).left_inv (by simpa using hq₁)) (Real.sigmoid_log_div_one_sub hq₂.1 hq₂.2)⟩

private theorem snd_mem_Ioo_of_mem_range_slabChart {p : sphere (0 : E) 1}
    {q : sphere (0 : E) 1 × ℝ} (hq : q ∈ range (slabChart (n := n) p)) :
    q.2 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨y, rfl⟩ := hq
  exact ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

/-- The chart carries the horizontal line through `(σ_p x, 0)` to the vertical line over `x`. -/
private theorem slabChart_line {p x : sphere (0 : E) 1} (hx : x ≠ p) (s : ℝ) :
    slabChart (n := n) p
        (((stereographic' n p) x, (0 : ℝ)) + s • ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))) =
      (x, Real.sigmoid s) := by
  simp only [slabChart_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero,
    add_zero, smul_eq_mul, mul_one, zero_add]
  rw [(stereographic' n p).left_inv (by simpa using hx)]

/-- The arc `s ↦ F (z₀, Real.sigmoid s)` of a concordance has injective differential: it is the
embedding `F` after `s ↦ (z₀, Real.sigmoid s)`, whose second component has nonzero derivative. -/
private theorem injective_mfderiv_arc (F : Concordance f g) (z₀ : M) (s : ℝ) :
    Injective (mfderiv 𝓘(ℝ) ((𝓡 n).prod 𝓘(ℝ)) (fun s : ℝ => F (z₀, Real.sigmoid s)) s) := by
  have hσ : Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) Real.sigmoid s) := by
    rw [← (isLocalDiffeomorph_sigmoid (n := ∞) (by simp) s).mfderivToContinuousLinearEquiv_coe
      (by simp)]
    exact ContinuousLinearEquiv.injective _
  have hjd : MDifferentiableAt 𝓘(ℝ) (I.prod 𝓘(ℝ)) (fun s : ℝ => (z₀, Real.sigmoid s)) s :=
    mdifferentiableAt_const.prodMk (contDiff_sigmoid.differentiable (by simp) s).mdifferentiableAt
  -- The differential of `s ↦ (z₀, Real.sigmoid s)` is injective, since its second component is.
  have hj : Injective (mfderiv 𝓘(ℝ) (I.prod 𝓘(ℝ)) (fun s : ℝ => (z₀, Real.sigmoid s)) s) := by
    have hsnd := mfderiv_comp s mdifferentiableAt_snd hjd
    have hcomp : (Prod.snd ∘ fun s : ℝ => (z₀, Real.sigmoid s)) = Real.sigmoid := rfl
    rw [hcomp] at hsnd
    rw [hsnd, ContinuousLinearMap.coe_comp] at hσ
    exact hσ.of_comp
  have hFd : MDifferentiableAt (I.prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) F (z₀, Real.sigmoid s) :=
    F.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)
  rw [show (fun s : ℝ => F (z₀, Real.sigmoid s)) = F ∘ fun s : ℝ => (z₀, Real.sigmoid s) from rfl,
    mfderiv_comp s hFd hjd, ContinuousLinearMap.coe_comp]
  refine Injective.comp ?_ hj
  rw [← coe_toSmoothEmbedding]
  exact F.toSmoothEmbedding.isImmersion.mfderiv_injective (by simp) _

/-- **The arc of a concordance in the chart.** If the arc `t ↦ F (z₀, t)` of a concordance stays off
`{p} × ℝ`, then, run at the time `Real.sigmoid s`, it is `χ ∘ β` for the chart `χ` at `p` and a
smooth injective immersion `β : ℝ → ℝⁿ × ℝ`. -/
private theorem exists_slabChart_comp_eq (F : Concordance f g) (z₀ : M) {p : sphere (0 : E) 1}
    (hp : ∀ t, (F (z₀, t)).1 ≠ p) :
    ∃ β : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ), EuclideanSpace ℝ (Fin n) × ℝ⟯,
      Injective β ∧ (∀ s, deriv β s ≠ 0) ∧
        ∀ s, slabChart (n := n) p (β s) = F (z₀, Real.sigmoid s) := by
  have hχo := isOpenEmbedding_slabChart (n := n) p
  have hχ := isLocalDiffeomorph_slabChart (n := n) p
  set χ := slabChart (n := n) p
  set γ : ℝ → sphere (0 : E) 1 × ℝ := fun s => F (z₀, Real.sigmoid s)
  have hγ : ContMDiff 𝓘(ℝ) ((𝓡 n).prod 𝓘(ℝ)) ∞ γ := F.toSmoothEmbedding.contMDiff.comp
    (contMDiff_const.prodMk (contDiff_sigmoid.of_le le_top).contMDiff)
  have hγχ : ∀ s, γ s ∈ range χ := fun s => mem_range_slabChart (hp _)
    (F.isCollaredTrack.snd_apply_mem_Ioo z₀ _ ⟨Real.sigmoid_pos s, Real.sigmoid_lt_one s⟩)
  -- `β` reads `γ` back through the homeomorphism of `ℝⁿ × ℝ` onto the image of the chart.
  set β : ℝ → EuclideanSpace ℝ (Fin n) × ℝ := fun s =>
    hχo.isEmbedding.toHomeomorph.symm ⟨γ s, hγχ s⟩
  have hχβ : ∀ s, χ (β s) = γ s := fun s => by
    rw [← hχo.isEmbedding.toHomeomorph_apply_coe]
    simp only [β, Homeomorph.apply_symm_apply]
  have hβ : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ β :=
    ContMDiff.of_comp_isLocalDiffeomorph hχ
      (hχo.isEmbedding.toHomeomorph.symm.continuous.comp (hγ.continuous.subtype_mk _))
      (by rwa [show χ ∘ β = γ from funext hχβ])
  have hFinj : Injective F := by
    rw [← coe_toSmoothEmbedding]
    exact F.toSmoothEmbedding.isEmbedding.injective
  have hβinj : Injective β := fun s s' h => Real.sigmoid_injective
    (congrArg Prod.snd (hFinj (show γ s = γ s' by rw [← hχβ s, ← hχβ s', h])) :)
  refine ⟨⟨β, hβ⟩, hβinj, fun s h0 => ?_, hχβ⟩
  -- The differential of `β` is injective, since that of `γ = χ ∘ β` is.
  have hβd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) β s :=
    hβ.mdifferentiableAt (by simp)
  have hinj : Injective (mfderiv 𝓘(ℝ) ((𝓡 n).prod 𝓘(ℝ)) γ s) := injective_mfderiv_arc F z₀ s
  rw [show γ = χ ∘ β from (funext hχβ).symm, mfderiv_comp s
    ((hχ (β s)).mdifferentiableAt (by simp)) hβd, ContinuousLinearMap.coe_comp] at hinj
  replace hinj := hinj.of_comp
  rw [(mdifferentiableAt_iff_differentiableAt.1 hβd).hasFDerivAt.hasMFDerivAt.mfderiv] at hinj
  have h10 : fderiv ℝ β s 1 = fderiv ℝ β s 0 := by
    rw [fderiv_apply_one_eq_deriv, map_zero]
    exact h0
  have h1 : (1 : ℝ) = 0 := hinj h10
  exact one_ne_zero h1

/-- **Moving the arc of a concordance onto a straight line.** Let `F` be a smooth concordance from
`f` to `g`, smooth embeddings into the unit sphere `Sⁿ`, `n ≥ 3`, and `z₀` a point with
`g z₀ = f z₀`. Some diffeomorphism `Ψ` of `Sⁿ × ℝ`, equal to the identity outside a compact subset
`C` of the open slab `Sⁿ × (0, 1)`, carries the arc `t ↦ F (z₀, t)` onto the straight line
`t ↦ (f z₀, t)`. -/
theorem exists_diffeomorph_apply_eq_line (hn : 3 ≤ n) (F : Concordance f g) {z₀ : M}
    (hz₀ : g z₀ = f z₀) :
    ∃ (Ψ : (sphere (0 : E) 1 × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ)⟯ (sphere (0 : E) 1 × ℝ))
      (C : Set (sphere (0 : E) 1 × ℝ)), IsCompact C ∧ (∀ q ∈ C, q.2 ∈ Ioo (0 : ℝ) 1) ∧
      (∀ q ∉ C, Ψ q = q) ∧ ∀ t, Ψ (F (z₀, t)) = (f z₀, t) := by
  -- Near both of its ends the arc is the straight line over `f z₀`.
  obtain ⟨ε₀, hε₀, hF₀⟩ := F.isCollaredTrack.exists_pos_apply_eq_left
  obtain ⟨ε₁, hε₁, hF₁⟩ := F.isCollaredTrack.exists_pos_apply_eq_right
  have hend : ∀ t, t ≤ ε₀ ∨ 1 - ε₁ ≤ t → F (z₀, t) = (f z₀, t) := by
    rintro t (ht | ht)
    · exact hF₀ z₀ t ht
    · rw [hF₁ z₀ t ht, hz₀]
  -- A point `p` of the sphere off the arc; the arc lies in the chart `χ` at `p`, as `χ ∘ β`.
  obtain ⟨p, hp⟩ := exists_notMem_range_real_sphere (f := fun t : ℝ => (F (z₀, t)).1)
    (by omega : 2 ≤ n) ((contMDiff_fst.comp (F.toSmoothEmbedding.contMDiff.comp
      (contMDiff_const.prodMk contMDiff_id))).mdifferentiable (by simp))
  have hp₀ : f z₀ ≠ p := fun h => hp ⟨0, by
    beta_reduce
    rw [hend 0 (Or.inl hε₀.le), h]⟩
  obtain ⟨β, hβinj, hβ', hχβ⟩ := exists_slabChart_comp_eq F z₀ (n := n) fun t h => hp ⟨t, h⟩
  have hχo := isOpenEmbedding_slabChart (n := n) p
  have hrange : ∀ y, (slabChart (n := n) p y).2 ∈ Ioo (0 : ℝ) 1 := fun y =>
    snd_mem_Ioo_of_mem_range_slabChart ⟨y, rfl⟩
  -- For large `|s|` the arc is the vertical line over `f z₀`, so `β` is a horizontal line.
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1
    (Real.tendsto_sigmoid_atTop.eventually (lt_mem_nhds (by linarith : 1 - ε₁ < 1)))
  obtain ⟨R₂, hR₂⟩ := Filter.eventually_atBot.1
    (Real.tendsto_sigmoid_atBot.eventually (gt_mem_nhds hε₀))
  have hline : ∀ s, max R₁ (-R₂) ≤ |s| → β s =
      ((stereographic' n p) (f z₀), (0 : ℝ)) + s • ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) := by
    intro s hs
    refine hχo.injective ?_
    rw [hχβ, slabChart_line hp₀]
    refine hend _ ?_
    rcases le_abs'.1 hs with h | h
    · exact Or.inl (hR₂ s (by linarith [le_max_right R₁ (-R₂)])).le
    · exact Or.inr (hR₁ s ((le_max_left _ _).trans h)).le
  -- Unknot `β` in `ℝⁿ × ℝ`, of dimension at least four, and extend along the chart.
  have hV : 4 ≤ finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  obtain ⟨Φ, K, hK, hΦK, hΦ⟩ := exists_diffeomorph_apply_eq_line_of_four_le_finrank
    (n := ⊤) (m := ⊤) le_top le_top hV β hβinj hβ' hline
  obtain ⟨Ψ, hΨχ, hΨK⟩ :=
    (isLocalDiffeomorph_slabChart p).exists_diffeomorph_extend_of_isCompact hχo Φ hK hΦK
  refine ⟨Ψ, slabChart p '' K, hK.image hχo.continuous, ?_, hΨK, fun t => ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact hrange y
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · -- Over `(0, 1)` the arc is `χ ∘ β`, which `Ψ` carries to `χ` of the line.
    obtain ⟨s, rfl⟩ : t ∈ range Real.sigmoid := Real.range_sigmoid ▸ ht
    rw [← hχβ, hΨχ, hΦ s, slabChart_line hp₀]
  · -- Outside `(0, 1)` the arc is already the line, which lies outside the chart.
    have ht' : t ≤ ε₀ ∨ 1 - ε₁ ≤ t := by
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
      exact ht.imp (fun h => h.trans hε₀.le) fun h => by linarith
    rw [hend t ht']
    refine hΨK _ ?_
    rintro ⟨y, -, hy⟩
    have hy' := hrange y
    rw [hy] at hy'
    exact ht hy'

/-- **A concordance whose arc over a point is a straight line.** Let `F` be a smooth concordance
from `f` to `g`, smooth embeddings into the unit sphere `Sⁿ`, `n ≥ 3`, and `z₀` a point with
`g z₀ = f z₀`. Then some concordance `G` from `f` to `g` is the straight line over `f z₀` along
`{z₀} × ℝ`: `G (z₀, t) = (f z₀, t)` for every `t`. -/
theorem exists_apply_eq_line (hn : 3 ≤ n) (F : Concordance f g) {z₀ : M}
    (hz₀ : g z₀ = f z₀) : ∃ G : Concordance f g, ∀ t, G (z₀, t) = (f z₀, t) := by
  obtain ⟨Ψ, C, hC, hCslab, hΨC, hΨF⟩ := exists_diffeomorph_apply_eq_line hn F hz₀
  refine ⟨⟨F.toSmoothEmbedding.transDiffeomorph Ψ, ?_⟩, fun t => ?_⟩
  · rw [SmoothEmbedding.coe_transDiffeomorph, coe_toSmoothEmbedding]
    exact F.isCollaredTrack.comp_of_isCompact Ψ.injective hC hCslab hΨC
  · rw [← hΨF t, ← coe_toSmoothEmbedding, SmoothEmbedding.transDiffeomorph_apply,
      coe_toSmoothEmbedding]

end SmoothEmbedding.Concordance

end TauCeti
