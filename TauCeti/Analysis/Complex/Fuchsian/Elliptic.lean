/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Descent
public import TauCeti.Analysis.Complex.UpperHalfPlane.Elliptic
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Local charts at elliptic orbits

Let `Γ ≤ PSL(2, ℝ)` be a subgroup and `z` a point of the upper half-plane with finite stabilizer
of order `m`. The orbit space of a small hyperbolic disc about `z` under that stabilizer maps to an
open subset of the coarse orbit quotient `Γ \ ℍ` as soon as the disc is precisely invariant
(`Subgroup.eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient`). This file packages the
local quotient coordinate on that open subset as a chart `Subgroup.stabilizerBallQuotientChart`,
an open partial homeomorphism from `Γ \ ℍ` to `ℂ` sending the orbit of a point `τ` of the disc to
`discCoordinate z τ ^ m` (`Subgroup.stabilizerBallQuotientChart_mk`). On the free locus `m = 1` and
the chart is the disc coordinate pushed forward along the orbit projection; at an elliptic point it
is the cyclic quotient model `u ↦ u ^ m`.

Near a point `τ` whose orbit lies in the source of the chart at `z`, the chart composed with the
orbit projection is `discCoordinate z (g • ·) ^ m` for a group element `g` moving `τ` into the
disc, hence holomorphic. Consequently the transition map between the charts at `z` and `z'` is the
descent through `u ↦ u ^ m` of a holomorphic function invariant under the `m`-th roots of unity,
and descent preserves holomorphy (`TauCeti.differentiableOn_descendPow`). These are the local
inputs that make the atlas of all such charts a holomorphic atlas on `Γ \ ℍ`.

The cyclic quotient model follows Farkas–Kra, *Riemann Surfaces*, Chapter I §§4–5, and Katok,
*Fuchsian Groups*, §2.4.

## Main declarations

* `Subgroup.stabilizerBallQuotientChart`: the chart at the orbit of `z`, with
  `Subgroup.stabilizerBallQuotientChart_mk` computing it on orbits,
  `Subgroup.mem_stabilizerBallQuotientChart_source_iff` describing its source, and
  `Subgroup.stabilizerBallQuotientChart_symm_pow` computing its inverse.
* `Subgroup.exists_stabilizerBallQuotientChart_quotientMk_eventuallyEq` and
  `Subgroup.mdifferentiableAt_stabilizerBallQuotientChart_comp_quotientMk`: the chart composed with
  the orbit projection is locally a power of a disc coordinate, hence holomorphic.
* `Subgroup.differentiableOn_stabilizerBallQuotientChart_symm_trans`: transition maps between two
  charts are holomorphic, being descents through `u ↦ u ^ m` of holomorphic pullbacks to the disc
  coordinate.

## References

* Hershel Farkas and Irwin Kra, *Riemann Surfaces*, Graduate Texts in Mathematics 71, Springer,
  second edition, 1992, Chapter I §§4–5.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.4.
-/

public noncomputable section

open Filter Metric MulAction Set TauCeti Topology UpperHalfPlane

open scoped ComplexConjugate ContDiff Manifold MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {z : ℍ} {ε : ℝ} [Finite (stabilizer Γ z)] (hε : 0 < ε)
  (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))

/-- **The chart at the orbit of `z`.** Its source is the image in `Γ \ ℍ` of the local orbit space
of the hyperbolic disc of radius `ε` about `z`, assumed to embed openly, and its target is the
Euclidean disc of radius `tanh (ε / 2) ^ m`, where `m` is the order of the stabilizer of `z`. It
sends the orbit of a point `τ` of the disc to `discCoordinate z τ ^ m`
(`Subgroup.stabilizerBallQuotientChart_mk`). -/
def stabilizerBallQuotientChart : OpenPartialHomeomorph (orbitRel.Quotient Γ ℍ) ℂ :=
  haveI : Nonempty (orbitRel.Quotient (stabilizer Γ z) (stabilizerBall Γ z ε)) :=
    ⟨Quotient.mk _ ⟨z, (mem_stabilizerBall Γ z ε).2 (by rwa [dist_self])⟩⟩
  haveI : Nonempty (ball (0 : ℂ) (Real.tanh (ε / 2) ^ Nat.card (stabilizer Γ z))) :=
    (nonempty_ball.2 (pow_pos (by
      rw [← Real.tanh_zero]
      exact Real.tanh_strictMono (by linarith)) _)).to_subtype
  ((hopen.toOpenPartialHomeomorph _).symm.transHomeomorph
      (stabilizerBallQuotientHomeomorph Γ z ε hε.le)).trans
    (isOpen_ball.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _)

@[simp]
theorem stabilizerBallQuotientChart_source :
    (stabilizerBallQuotientChart hε hopen).source =
      range (stabilizerBallQuotientToQuotient Γ z ε) := by
  simp [stabilizerBallQuotientChart]

@[simp]
theorem stabilizerBallQuotientChart_target :
    (stabilizerBallQuotientChart hε hopen).target =
      ball 0 (Real.tanh (ε / 2) ^ Nat.card (stabilizer Γ z)) := by
  simp [stabilizerBallQuotientChart, ← ball_zero_eq]

/-- In the chart at the orbit of `z`, the orbit of a point `τ` of the hyperbolic disc has
coordinate the `m`-th power of its disc coordinate, `m` the order of the stabilizer of `z`. -/
@[simp]
theorem stabilizerBallQuotientChart_mk {τ : ℍ} (hτ : dist τ z < ε) :
    stabilizerBallQuotientChart hε hopen (Quotient.mk _ τ) =
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  have : Nonempty (orbitRel.Quotient (stabilizer Γ z) (stabilizerBall Γ z ε)) :=
    ⟨Quotient.mk _ ⟨τ, (mem_stabilizerBall Γ z ε).2 hτ⟩⟩
  rw [← stabilizerBallQuotientToQuotient_mk Γ z ε ⟨τ, (mem_stabilizerBall Γ z ε).2 hτ⟩,
    stabilizerBallQuotientChart, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    hopen.toOpenPartialHomeomorph_left_inv, IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    coe_stabilizerBallQuotientHomeomorph_mk]

/-- The orbit of `τ` lies in the source of the chart at the orbit of `z` exactly when some element
of `Γ` moves `τ` into the hyperbolic disc of radius `ε` about `z`. -/
theorem mem_stabilizerBallQuotientChart_source_iff {τ : ℍ} :
    Quotient.mk _ τ ∈ (stabilizerBallQuotientChart hε hopen).source ↔
      ∃ g : Γ, dist (g • τ) z < ε := by
  rw [stabilizerBallQuotientChart_source]
  constructor
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h σ =>
      rw [stabilizerBallQuotientToQuotient_mk] at hq
      obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hq))
      refine ⟨g, ?_⟩
      rw [hg]
      exact (mem_stabilizerBall Γ z ε).1 σ.2
  · rintro ⟨g, hg⟩
    refine ⟨Quotient.mk _ ⟨g • τ, (mem_stabilizerBall Γ z ε).2 hg⟩, ?_⟩
    rw [stabilizerBallQuotientToQuotient_mk]
    exact Quotient.sound (orbitRel_apply.mpr (mem_orbit τ g))

/-- The inverse of the chart at the orbit of `z` sends the `m`-th power of a point `w` of the disc
of radius `tanh (ε / 2)` to the orbit of the point with disc coordinate `w`. -/
theorem stabilizerBallQuotientChart_symm_pow {w : ℂ} (hw : ‖w‖ < Real.tanh (ε / 2)) :
    (stabilizerBallQuotientChart hε hopen).symm (w ^ Nat.card (stabilizer Γ z)) =
      Quotient.mk _
        ((discCoordinateHomeomorph z).symm (.mk w (hw.trans (Real.tanh_lt_one _)))) := by
  set τ : ℍ := (discCoordinateHomeomorph z).symm (.mk w (hw.trans (Real.tanh_lt_one _))) with hτ
  have hw' : discCoordinate z τ = w := by simp [hτ]
  have hτε : dist τ z < ε := by
    rw [← mem_ball, mem_ball_iff_norm_discCoordinate_lt, hw']
    exact hw
  rw [← hw', ← stabilizerBallQuotientChart_mk hε hopen hτε]
  exact (stabilizerBallQuotientChart hε hopen).left_inv
    ((mem_stabilizerBallQuotientChart_source_iff hε hopen).2 ⟨(1 : Γ), by simpa using hτε⟩)

/-- Near a point `τ` whose orbit lies in the source of the chart at the orbit of `z`, the chart
composed with the orbit projection is `discCoordinate z (g • ·) ^ m`, where `g ∈ Γ` moves `τ` into
the hyperbolic disc about `z` and `m` is the order of the stabilizer of `z`. -/
theorem exists_stabilizerBallQuotientChart_quotientMk_eventuallyEq {τ : ℍ}
    (hτ : Quotient.mk _ τ ∈ (stabilizerBallQuotientChart hε hopen).source) :
    ∃ g : Γ, (fun σ : ℍ ↦ stabilizerBallQuotientChart hε hopen (Quotient.mk _ σ)) =ᶠ[𝓝 τ]
      fun σ ↦ discCoordinate z (g • σ) ^ Nat.card (stabilizer Γ z) := by
  obtain ⟨g, hg⟩ := (mem_stabilizerBallQuotientChart_source_iff hε hopen).1 hτ
  refine ⟨g, ?_⟩
  filter_upwards [(continuous_const_smul g).continuousAt.preimage_mem_nhds
    (isOpen_ball.mem_nhds (mem_ball.2 hg))] with σ hσ
  rw [← stabilizerBallQuotientChart_mk hε hopen (mem_ball.1 hσ)]
  exact congrArg _ (Quotient.sound (orbitRel_apply.mpr (mem_orbit σ g))).symm

/-- The chart at the orbit of `z` composed with the orbit projection is holomorphic at every point
whose orbit lies in the source of the chart. -/
theorem mdifferentiableAt_stabilizerBallQuotientChart_comp_quotientMk {τ : ℍ}
    (hτ : Quotient.mk _ τ ∈ (stabilizerBallQuotientChart hε hopen).source) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun σ : ℍ ↦ stabilizerBallQuotientChart hε hopen (Quotient.mk _ σ)) τ := by
  obtain ⟨g, hg⟩ := exists_stabilizerBallQuotientChart_quotientMk_eventuallyEq hε hopen hτ
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ hg
  exact (((mdifferentiable_discCoordinate z).comp
    ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) g).mdifferentiable (by simp))) τ).pow _

/-- The transition map between the charts at the orbits of `z` and `z'`, pulled back along
`w ↦ w ^ m` to the disc coordinate at `z`, is holomorphic at every point `w₀` of the disc of radius
`tanh (ε / 2)` whose orbit lies in the source of the second chart: near `w₀` it is the second chart
composed with the orbit projection and the inverse disc coordinate at `z`. -/
private theorem differentiableAt_stabilizerBallQuotientChart_symm_pow {z' : ℍ} {ε' : ℝ}
    [Finite (stabilizer Γ z')] (hε' : 0 < ε')
    (hopen' : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z' ε')) {w₀ : ℂ}
    (hw₀ : ‖w₀‖ < Real.tanh (ε / 2))
    (hw₀' : (stabilizerBallQuotientChart hε hopen).symm (w₀ ^ Nat.card (stabilizer Γ z)) ∈
      (stabilizerBallQuotientChart hε' hopen').source) :
    DifferentiableAt ℂ (fun w ↦ stabilizerBallQuotientChart hε' hopen'
      ((stabilizerBallQuotientChart hε hopen).symm (w ^ Nat.card (stabilizer Γ z)))) w₀ := by
  set e' := stabilizerBallQuotientChart hε' hopen' with he'
  -- The explicit inverse of the disc coordinate at `z`, as a function on `ℂ`.
  set ψ : ℂ → ℂ := fun w ↦ ((z : ℂ) - conj (z : ℂ) * w) / (1 - w) with hψ
  have hψτ : ∀ w (hw : ‖w‖ < Real.tanh (ε / 2)),
      (discCoordinateHomeomorph z).symm (.mk w (hw.trans (Real.tanh_lt_one _))) =
        ofComplex (ψ w) := fun w hw ↦ by
    rw [← ofComplex_apply ((discCoordinateHomeomorph z).symm _),
      coe_discCoordinateHomeomorph_symm_apply, Complex.UnitDisc.coe_mk]
  have heq : (fun w ↦ e' ((stabilizerBallQuotientChart hε hopen).symm
      (w ^ Nat.card (stabilizer Γ z)))) =ᶠ[𝓝 w₀] fun w ↦ e' (Quotient.mk _ (ofComplex (ψ w))) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hw₀)] with w hw
    rw [stabilizerBallQuotientChart_symm_pow hε hopen (mem_ball_zero_iff.1 hw),
      hψτ w (mem_ball_zero_iff.1 hw)]
  have hτ₀ : Quotient.mk _ (ofComplex (ψ w₀)) ∈ e'.source := by
    rwa [← hψτ w₀ hw₀, ← stabilizerBallQuotientChart_symm_pow hε hopen hw₀]
  have him : 0 < (ψ w₀).im := by
    have hcoe : (((discCoordinateHomeomorph z).symm
        (.mk w₀ (hw₀.trans (Real.tanh_lt_one _))) : ℍ) : ℂ) = ψ w₀ := by
      rw [coe_discCoordinateHomeomorph_symm_apply, Complex.UnitDisc.coe_mk]
    rw [← hcoe, coe_im]
    exact im_pos _
  have hψd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ w₀ :=
    mdifferentiableAt_iff_differentiableAt.2 ((analyticOnNhd_discCoordinateHomeomorph_symm z w₀
      (mem_ball_zero_iff.2 (hw₀.trans (Real.tanh_lt_one _)))).differentiableAt)
  exact (mdifferentiableAt_iff_differentiableAt.1
    (((mdifferentiableAt_stabilizerBallQuotientChart_comp_quotientMk hε' hopen' hτ₀).comp (ψ w₀)
      (mdifferentiableAt_ofComplex him)).comp w₀ hψd)).congr_of_eventuallyEq heq

/-- The transition map between the charts at the orbits of `z` and `z'` is holomorphic on its
domain: it is the descent through `u ↦ u ^ m` of its pullback to the disc coordinate at `z`. -/
theorem differentiableOn_stabilizerBallQuotientChart_symm_trans {z' : ℍ} {ε' : ℝ}
    [Finite (stabilizer Γ z')] (hε' : 0 < ε')
    (hopen' : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z' ε')) :
    DifferentiableOn ℂ
      ((stabilizerBallQuotientChart hε hopen).symm ≫ₕ stabilizerBallQuotientChart hε' hopen')
      ((stabilizerBallQuotientChart hε hopen).symm ≫ₕ
        stabilizerBallQuotientChart hε' hopen').source := by
  set e := stabilizerBallQuotientChart hε hopen with he
  set e' := stabilizerBallQuotientChart hε' hopen' with he'
  set m := Nat.card (stabilizer Γ z) with hm
  have : NeZero m := ⟨Nat.card_pos.ne'⟩
  have hr0 : 0 ≤ Real.tanh (ε / 2) := by
    rw [← Real.tanh_zero]
    exact Real.tanh_strictMono.monotone (by linarith)
  -- The transition map is the descent through `u ↦ u ^ m` of its pullback `F`.
  set F : ℂ → ℂ := fun w ↦ e' (e.symm (w ^ m)) with hF
  have hdesc : ⇑(e.symm ≫ₕ e') = descendPow m F := by
    funext u
    rw [OpenPartialHomeomorph.trans_apply]
    exact (congrFun (descendPow_comp_pow (m := m) fun v ↦ e' (e.symm v)) u).symm
  set s : Set ℂ := ball 0 (Real.tanh (ε / 2)) ∩ {w | e.symm (w ^ m) ∈ e'.source} with hs
  have hs_open : IsOpen s := by
    refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_ball e'.open_source
    refine e.continuousOn_symm.comp (continuous_pow m).continuousOn fun w hw ↦ ?_
    rw [he, stabilizerBallQuotientChart_target, ← image_pow_ball hr0]
    exact mem_image_of_mem _ hw
  have hsub : (e.symm ≫ₕ e').source ⊆ (· ^ m) '' s := by
    intro u hu
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, he,
      stabilizerBallQuotientChart_target, ← image_pow_ball hr0] at hu
    obtain ⟨⟨w, hw, rfl⟩, hu'⟩ := hu
    exact ⟨w, ⟨hw, hu'⟩, rfl⟩
  have hinv : ∀ u ∈ s, ∀ ζ : rootsOfUnity m ℂ, F (ζ • u) = F u := fun u _ ζ ↦ by
    simp only [hF, rootsOfUnity.smul_pow]
  have hFd : DifferentiableOn ℂ F s := fun w₀ ⟨hw₀, hw₀'⟩ ↦
    (differentiableAt_stabilizerBallQuotientChart_symm_pow hε hopen hε' hopen'
      (mem_ball_zero_iff.1 hw₀) hw₀').differentiableWithinAt
  rw [hdesc]
  exact (differentiableOn_descendPow hs_open hFd hinv).mono hsub

end Subgroup
