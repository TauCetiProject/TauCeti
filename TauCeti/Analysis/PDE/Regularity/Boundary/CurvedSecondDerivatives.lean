/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.SecondDerivatives
public import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Hessian
import TauCeti.Analysis.Holder.FDeriv
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.Sobolev.W1p.Convex
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Second derivatives up to a curved boundary

Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be open. Near a boundary point `x₀`, suppose that `∂Ω` is
straightened by a chart: changes of variables `Φ : U' → U` and `Ψ : U → U'` of order two, inverse
to each other on `U'` and `U`, with Jacobian determinant one and `D²Ψ` `α`-Hölder, such that `Φ`
maps the part of `U'` in an open half-space `H = {c₀ < ⟪y, ν⟫}` onto `Ω ∩ U` and `x₀ = Φ y₀` with
`y₀` on the boundary hyperplane. This is the situation at a boundary point of a domain with
`C^{2,α}` boundary. Let `a` be uniformly elliptic near `x₀` with entries of class `C^{1,α}` there,
let `f ∈ L²(Ω)` be `α`-Hölder up to the boundary near `x₀`, and let `u ∈ H¹(Ω)` be a weak solution
of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`

that vanishes on `∂Ω` near `x₀`. This file proves the Sobolev form of `C^{2,α}` regularity of `u`
up to the boundary near `x₀`: on `Ω ∩ V` for an open neighbourhood `V` of `x₀`, `u` is the
first-order part of an element of `W^{2,2}(Ω ∩ V)` whose weak gradient and weak Hessian agree
almost everywhere with fields that are `α`-Hölder on `closure Ω ∩ V`
(`exists_lowerOrder_eq_restrictL_and_holderOnWith_iteratedGradient_of_isChangeOfVariables`; this and
the other declarations named below are in the `TauCeti.PDE` namespace). No classical `C²`
representative of `u` is constructed here. With the interior regularity of
`exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_contDiffOn`, this is the local
regularity from which the `C^{2,α}` regularity of weak solutions of the Dirichlet problem on a
domain with `C^{2,α}` boundary is assembled (Gilbarg–Trudinger, Lemma 6.18 and Theorem 6.19, here
for divergence-form equations).

## The argument

* **Flattening.** The function `v = u ∘ Φ` lies in `H¹` of the flat half-ball `H ∩ B(y₀, r)`,
  vanishes on its flat boundary, and solves `-∂ᵢ(a'ⁱʲ ∂ⱼv) = f ∘ Φ` weakly there
  (`energyFormH1_compL_eq_setIntegral`), with the pulled-back coefficient
  `a' = DΨ(Φ ·) a(Φ ·) DΨ(Φ ·)ᵀ`. It is uniformly elliptic, and its entries are `C¹` with
  `α`-Hölder derivatives (`exists_holderOnWith_fderiv_pullbackPrincipal`). The datum `f ∘ Φ` is
  `α`-Hölder up to the flat boundary.
* **The flat case.** Every second derivative of `v` is `α`-Hölder up to the flat boundary
  (`exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq`). So
  `v ∈ W^{2,2}` on a smaller half-ball
  (`TauCeti.W1p.exists_lowerOrder_eq_and_iteratedGradient_ae_eq_of_forall_hasWeakLineDerivOn`), its
  weak Hessian agrees almost everywhere with an `α`-Hölder field, and so does its weak gradient,
  whose components have bounded gradients on the convex half-ball
  (`TauCeti.W1p.exists_holderOnWith_closure_ae_eq_of_gradient_ae_eq`).
* **Back to `Ω`.** On `Ω ∩ V` the function `u = v ∘ Ψ` lies in `W^{2,2}`
  (`TauCeti.Wkp.compL`), and the chain rule for the weak Hessian
  (`TauCeti.Wkp.inner_iteratedGradient_compL_ae`)

  `⟪D²u h, g⟫ = ⟪D²v(Ψ ·) (DΨ h), DΨ g⟫ + ⟪∇v(Ψ ·), D²Ψ h g⟫`

  expresses its entries through `α`-Hölder functions, since `Ψ` maps `closure Ω` near `x₀` into
  the closed half-space (`TauCeti.Wkp.exists_holderOnWith_iteratedGradient_compL`). The weak
  gradient `∇u = DΨ† ∇v(Ψ ·)` (`TauCeti.Wkp.gradient_firstOrder_compL_ae`) is `α`-Hölder in the
  same way.

## Main declarations

* `exists_lowerOrder_eq_restrictL_and_holderOnWith_iteratedGradient_of_isChangeOfVariables`:
  `W^{2,2}` regularity of weak solutions with `α`-Hölder weak gradient and weak Hessian up to a
  straightened boundary portion.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (flattening the boundary), Lemma 6.18 and Theorem 6.19.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2 (regularity up to the boundary
  by flattening).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### The flat boundary in Sobolev form -/

section Flat

/-- **`C^{2,α}` up to a flat boundary portion, in Sobolev form.** Under the hypotheses of
`exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq`, the restriction of `v` to
the half-ball `Ω' ∩ B(y₀, r / 16)` is the first-order part of an element of `W^{2,2}` there whose
weak Hessian and weak gradient agree almost everywhere with fields that are `α`-Hölder on the closed
half-ball `closure (H ∩ B(y₀, r / 16))`. -/
private theorem exists_wkp_and_holderOnWith_of_inter_ball_eq {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {H Ω' : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {y₀ : E}
    (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (hΩ' : (Ω' : Set E) ∩ ball y₀ r = (H : Set E) ∩ ball y₀ r)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hell : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω'))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {v : W1p volume Ω' 2}
    (hv : ∀ w : W1p0 volume Ω' 2, energyFormH1 a 0 0 v (w : W1p volume Ω' 2) =
      ∫ x in Ω', f x * W1p.value (w : W1p volume Ω' 2) x)
    (hv0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball y₀ r →
      ∃ w : W1p0 volume Ω' 2,
        W1p.value (w : W1p volume Ω' 2) =ᵐ[volume.restrict Ω'] fun x => ψ x * W1p.value v x) :
    ∃ V : Wkp volume (Ω' ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩ : Opens E) 2 2,
      Wkp.lowerOrder 1 V = W1p.restrictL inf_le_left v ∧
      ∃ (Gv : E → E →L[ℝ] E) (P : E → E),
        (∃ C : ℝ≥0, HolderOnWith C α Gv (closure ((H : Set E) ∩ ball y₀ (r / 16)))) ∧
        (∃ C : ℝ≥0, HolderOnWith C α P (closure ((H : Set E) ∩ ball y₀ (r / 16)))) ∧
        (Wkp.iteratedGradient 1 V : E → E →L[ℝ] E)
          =ᵐ[volume.restrict ((Ω' : Set E) ∩ ball y₀ (r / 16))] Gv ∧
        (W1p.gradient (W1p.restrictL (inf_le_left :
            (Ω' ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩ : Opens E) ≤ Ω') v) : E → E)
          =ᵐ[volume.restrict ((Ω' : Set E) ∩ ball y₀ (r / 16))] P := by
  let Ω'' : Opens E := Ω' ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩
  have hΩ''H : ((Ω'' : Opens E) : Set E) = (H : Set E) ∩ ball y₀ (r / 16) := by
    have hball : ball y₀ (r / 16) ⊆ ball y₀ r := ball_subset_ball (by linarith)
    -- Unfold the coercion of `Ω''` first, so that the rewrites do not reach inside the `Opens`.
    rw [show ((Ω'' : Opens E) : Set E) = (Ω' : Set E) ∩ ball y₀ (r / 16) from Opens.coe_inf _ _,
      ← inter_eq_right.2 hball, ← inter_assoc, hΩ', inter_assoc, inter_eq_right.2 hball]
  set S₀ := closure ((H : Set E) ∩ ball y₀ (r / 16))
  have hS₀ : S₀ ⊆ closedBall y₀ (r / 16) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ} :=
    closure_minimal (fun y hy => ⟨ball_subset_closedBall hy.2, ((hH y).1 hy.1).le⟩)
      (isClosed_closedBall.inter (isClosed_le continuous_const
        (continuous_id.inner continuous_const)))
  have hΩ''conv : Convex ℝ ((Ω'' : Opens E) : Set E) := by
    rw [hΩ''H, show (H : Set E) = {x | c₀ < ⟪x, ν⟫_ℝ} from Set.ext hH]
    exact (convex_halfSpace_gt (IsLinearMap.mk (fun x y => inner_add_left x y ν)
      (fun c x => real_inner_smul_left x ν c)) c₀).inter (convex_ball y₀ (r / 16))
  -- Second derivatives in every direction, from the flat theorem.
  have hflat := fun w : E => exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq
    hα hα1 hν hH hy₀ hr hΩ' ha hell hda hf hfH hv hv0 w
  choose d hd G hG hGd using hflat; choose CG hCG using hG
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hvv : W1p.value (W1p.restrictL (inf_le_left : Ω'' ≤ Ω') v)
      =ᵐ[volume.restrict (Ω'' : Set E)] W1p.value v := W1p.value_restrictL_ae inf_le_left v
  obtain ⟨V, hV, hhess⟩ :=
    W1p.exists_lowerOrder_eq_and_iteratedGradient_ae_eq_of_forall_hasWeakLineDerivOn _ d
      fun w => (hd w).congr_ae hvv.symm
  -- A Hölder representative of each component of `∇v` up to the flat boundary.
  have hP (j : Fin (n + 1)) : ∃ g : E → ℝ, (∃ C : ℝ≥0, HolderOnWith C α g S₀) ∧
      (fun x => ⟪W1p.gradient (W1p.restrictL (inf_le_left : Ω'' ≤ Ω') v) x, b j⟫_ℝ)
        =ᵐ[volume.restrict (Ω'' : Set E)] g := by
    obtain ⟨g, hgH, hg⟩ := W1p.exists_holderOnWith_closure_ae_eq_of_gradient_ae_eq hα hα1.le
      hΩ''conv (by rw [hΩ''H]; exact isBounded_ball.subset inter_subset_right) (d (b j))
      (by rw [hΩ''H]; exact (hCG (b j)).mono hS₀) (hGd (b j))
    exact ⟨g, by rwa [hΩ''H] at hgH, (((W1p.hasWeakLineDerivOn_inner_gradient _ (b j)).congr_ae
      hvv).ae_eq (hd (b j))).trans hg⟩
  choose g hgH hg using hP; choose Cg hCg using hgH
  refine ⟨V, hV, fun y => ∑ i, (innerSL ℝ (b i)).smulRight (G (b i) y),
    fun y => ∑ j, g j y • b j, ⟨_, HolderOnWith.sum fun i _ =>
      (ContinuousLinearMap.smulRightL ℝ ℝ ℝ E E (innerSL ℝ (b i))).lipschitzWith.comp_holderOnWith
        ((hCG (b i)).mono hS₀)⟩, ⟨_, HolderOnWith.sum fun j _ =>
      (ContinuousLinearMap.toSpanSingleton ℝ (b j)).lipschitzWith.comp_holderOnWith (hCg j)⟩,
    ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 fun i => (hhess (b i)).and (hGd (b i))] with x hx
    refine ContinuousLinearMap.ext fun h => ?_
    conv_lhs => rw [← b.sum_repr' h]
    simp only [map_sum, map_smul, sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [(hx i).1, (hx i).2]
  · filter_upwards [ae_all_iff.2 hg] with x hx
    conv_lhs => rw [← b.sum_repr' (W1p.gradient _ x)]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm, hx j]

end Flat

/-! ### Transport to a curved boundary -/

section Curved

/-- **The hypotheses of the flat theorem in a chart.** In the setting of
`exists_lowerOrder_eq_restrictL_and_holderOnWith_iteratedGradient_of_isChangeOfVariables`, on a
ball `B(y₀, r) ⊆ U'` that `Φ` maps into `W`, the pulled-back coefficient `a'` has `C¹` entries with
locally `α`-Hölder derivatives and is uniformly elliptic, and `f ∘ Φ` is `α`-Hölder up to the flat
boundary near each point of the ball in the closed half-space. -/
private theorem flat_hypotheses_of_isChangeOfVariables
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω W U' U : Opens E} {Φ Ψ : E → E} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) {ν : E} (hν : ν ≠ 0) {c₀ : ℝ}
    (himage : Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = (Ω : Set E) ∩ U)
    {KT : ℝ≥0} (hT : HolderOnWith KT α (fderiv ℝ (fderiv ℝ Ψ)) U)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) W)
    (hell : UniformlyEllipticOn W a lam Lam)
    (hda : ∀ x ∈ W, ∃ ρ > 0, ∃ C : ℝ≥0, ∀ i j,
      HolderOnWith C α (fderiv ℝ fun y => a y i j) (ball x ρ))
    {f : E → ℝ} (hfH : ∀ x ∈ (W : Set E) ∩ closure Ω, ∃ ρ > 0, ∃ C : ℝ≥0,
      HolderOnWith C α f (ball x ρ ∩ closure Ω))
    {y₀ : E} {r : ℝ} (hr : 0 < r) (hBU' : ball y₀ r ⊆ U') (hBW : MapsTo Φ (ball y₀ r) W) :
    (∀ i j, ContDiffOn ℝ 1 (fun x => pullbackPrincipal Φ a x i j) (ball y₀ r)) ∧
      (∃ lam' Lam' : ℝ, UniformlyEllipticOn (ball y₀ r) (pullbackPrincipal Φ a) lam' Lam') ∧
      (∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ C : ℝ≥0, ∀ i j,
        HolderOnWith C α (fderiv ℝ fun y => pullbackPrincipal Φ a y i j) (ball x ρ)) ∧
      ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ C : ℝ≥0,
        HolderOnWith C α (fun y => f (Φ y)) (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) := by
  have hΦ2 : ContDiffOn ℝ 2 Φ U' := by exact_mod_cast hΦ.contDiffOn
  have hΦc : ContinuousOn Φ U' := hΦ.contDiffOn.continuousOn
  -- Points of `U'` in the closed half-space are mapped into `closure Ω`.
  have hΦcl {y : E} (hy : y ∈ U') (hyν : c₀ ≤ ⟪y, ν⟫_ℝ) : Φ y ∈ closure (Ω : Set E) :=
    (hΦc.continuousAt (U'.isOpen.mem_nhds hy)).continuousWithinAt.mem_closure
      (mem_closure_setOf_lt_inner_inter hν hyν U'.isOpen hy)
      (fun z hz => (himage ▸ mem_image_of_mem Φ hz : Φ z ∈ (Ω : Set E) ∩ U).1)
  refine ⟨fun i j => contDiffOn_pullbackPrincipal_apply (hΦ.mono one_le_two) (hΨ.mono one_le_two)
      hΨΦ hΦΨ hBU' hBW ((hΦ2.mono hBU').of_le one_le_two)
      (by exact_mod_cast hΨ.contDiffOn) ha i j,
    exists_uniformlyEllipticOn_pullbackPrincipal (hΦ.mono one_le_two) (hΨ.mono one_le_two) hΨΦ
      hΦΨ hBU' ⟨y₀, mem_ball_self hr⟩ hBW hell,
    fun x hx => exists_holderOnWith_fderiv_pullbackPrincipal hα hα1.le hΦ hΨ hΨΦ hΦΨ hT ha hda
      (hBU' hx) (hBW hx), ?_⟩
  -- `f ∘ Φ` is Hölder near each point: `f` is near `Φ x`, and `Φ` is Lipschitz near `x`.
  rintro x ⟨hxB, hxν⟩
  obtain ⟨ρf, hρf, Cf, hCf⟩ := hfH (Φ x) ⟨hBW hxB, hΦcl (hBU' hxB) hxν⟩
  have hxO : x ∈ ball y₀ r ∩ Φ ⁻¹' ball (Φ x) ρf := by
    refine ⟨hxB, ?_⟩
    rw [mem_preimage]
    exact mem_ball_self hρf
  obtain ⟨ρ, hρ, hρs⟩ := nhds_basis_closedBall.mem_iff.1
    (((hΦc.mono hBU').isOpen_inter_preimage isOpen_ball isOpen_ball).mem_nhds hxO)
  obtain ⟨LΦ, hLΦ⟩ := ((hΦ2.mono ((hρs.trans inter_subset_left).trans hBU')).of_le
    one_le_two).exists_lipschitzOnWith one_ne_zero (convex_closedBall x ρ)
    (isCompact_closedBall x ρ)
  exact ⟨ρ, hρ, _, hCf.comp_lipschitzOnWith
    (hLΦ.mono (inter_subset_left.trans ball_subset_closedBall))
    fun y (hy : y ∈ ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) => ⟨(hρs (ball_subset_closedBall hy.1)).2,
      hΦcl (hBU' (hρs (ball_subset_closedBall hy.1)).1) hy.2⟩⟩

/-- **The flattened problem.** In the setting of
`exists_lowerOrder_eq_restrictL_and_holderOnWith_iteratedGradient_of_isChangeOfVariables`, on a
ball `B(y₀, r)` whose closure lies in `U'` and is mapped into `W` by `Φ`, the function `v = u ∘ Φ`
on `H ∩ B(y₀, r)` lies in `H¹`, vanishes on the flat boundary and solves
`-∂ᵢ(a'ⁱʲ ∂ⱼv) = f ∘ Φ` weakly, with `f ∘ Φ` square integrable. -/
private theorem exists_flattened_problem {Ω W U' U : Opens E} {Φ Ψ : E → E} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) {ν : E} {c₀ : ℝ} {H : Opens E}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (himage : Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = (Ω : Set E) ∩ U)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {f : E → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) {u : W1p volume Ω 2}
    (hu : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x)
    {y₀ : E} {r : ℝ} (hrB : closedBall y₀ r ⊆ (U' : Set E) ∩ Φ ⁻¹' W) :
    ∃ v : W1p volume (H ⊓ ⟨ball y₀ r, isOpen_ball⟩) 2,
      (W1p.value v : E → ℝ) =ᵐ[volume.restrict ((H : Set E) ∩ ball y₀ r)]
        (fun y => W1p.value u (Φ y)) ∧
      (∀ w : W1p0 volume (H ⊓ ⟨ball y₀ r, isOpen_ball⟩) 2,
        energyFormH1 (pullbackPrincipal Φ a) 0 0 v
            (w : W1p volume (H ⊓ ⟨ball y₀ r, isOpen_ball⟩) 2) =
          ∫ x in (H : Set E) ∩ ball y₀ r,
            f (Φ x) * W1p.value (w : W1p volume (H ⊓ ⟨ball y₀ r, isOpen_ball⟩) 2) x) ∧
      (∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball y₀ r →
        ∃ w : W1p0 volume (H ⊓ ⟨ball y₀ r, isOpen_ball⟩) 2,
          W1p.value (w : W1p volume (H ⊓ ⟨ball y₀ r, isOpen_ball⟩) 2)
            =ᵐ[volume.restrict ((H : Set E) ∩ ball y₀ r)] fun x => ψ x * W1p.value v x) ∧
      MemLp (fun y => f (Φ y)) 2 (volume.restrict ((H : Set E) ∩ ball y₀ r)) := by
  have hBU' : ball y₀ r ⊆ U' := ball_subset_closedBall.trans (hrB.trans inter_subset_left)
  -- The flat domain `Ω' = H ∩ B(y₀, r)` and the curved one `D = Ω ∩ U ∩ Ψ⁻¹ B(y₀, r)`.
  let Ω' : Opens E := H ⊓ ⟨ball y₀ r, isOpen_ball⟩
  let O : Opens E := ⟨U ∩ Ψ ⁻¹' ball y₀ r,
    hΨ.contDiffOn.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩
  let D : Opens E := Ω ⊓ O
  have hΦmaps : MapsTo Φ Ω' D := fun x hx => by
    have hmem : Φ x ∈ (Ω : Set E) ∩ U :=
      himage ▸ mem_image_of_mem _ ⟨(hH x).1 hx.1, hBU' hx.2⟩
    exact ⟨hmem.1, hmem.2, by rw [mem_preimage, hΨΦ (hBU' hx.2)]; exact hx.2⟩
  have hΨmaps : MapsTo Ψ D Ω' := fun y hy => by
    obtain ⟨x, ⟨hxH, hxU'⟩, rfl⟩ : y ∈ Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') :=
      himage ▸ ⟨hy.1, hy.2.1⟩
    exact ⟨(hH _).2 (by rw [hΨΦ hxU']; exact hxH), hy.2.2⟩
  have hΨΦ' : LeftInvOn Ψ Φ Ω' := hΨΦ.mono fun x hx => hBU' hx.2
  have hΦΨ' : RightInvOn Ψ Φ D := hΦΨ.mono fun y hy => hy.2.1
  have hΦ' : Wkp.IsChangeOfVariables 1 Ω' D Φ L 1 :=
    (hΦ.mono_set (fun x hx => hBU' hx.2 : Ω' ≤ U') hΦmaps).mono one_le_two
  have hΨ' : Wkp.IsChangeOfVariables 2 D Ω' Ψ L 1 := hΨ.mono_set (fun y hy => hy.2.1) hΨmaps
  have hdet (x : E) (hx : x ∈ (Ω' : Set E)) : pullbackDensity Φ f x = f (Φ x) := by
    rw [pullbackDensity_apply, hΦ'.abs_det_fderiv_eq_one hΨ' hΨΦ' hΦΨ' hx, one_mul]
  refine ⟨hΦ'.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL (inf_le_left : D ≤ Ω) u), ?_,
    fun w => ?_, hΦ'.exists_w1p0_value_ae_eq_mul_value_w1pCompL ENNReal.ofNat_ne_top
      (hΦ.contDiffOn.continuousOn.mono hBU') (hΨ.contDiffOn.continuousOn.mono fun y hy => hy.2.1)
      hΨmaps hΨΦ'
      (fun x hx => ⟨hΦ.mapsTo (hBU' hx), by rw [mem_preimage, hΨΦ (hBU' hx)]; exact hx⟩ :
        MapsTo Φ ((⟨ball y₀ r, isOpen_ball⟩ : Opens E) : Set E) O)
      (fun χ hχ hχc hχs => hu0 χ hχ hχc (hχs.trans fun y hy => by
        have h := (hrB (ball_subset_closedBall hy.2)).2
        rwa [mem_preimage, hΦΨ hy.1] at h)), ?_⟩
  · filter_upwards [hΦ'.value_w1pCompL_ae ENNReal.ofNat_ne_top
      (W1p.restrictL (inf_le_left : D ≤ Ω) u),
      hΦ'.ae_comp (W1p.value_restrictL_ae (inf_le_left : D ≤ Ω) u)] with x h1 h2
    rw [h1, h2]
  · -- The transformed equation, with `pullbackDensity Φ f = f ∘ Φ` since `|det DΦ| = 1`.
    have h := energyFormH1_compL_eq_setIntegral hΦ'.differentiableOn hΦ'.injOn hΦ'.mapsTo
      hΦ'.norm_fderiv_le hΦ'.pos hΦ'.le_abs_det hΨ'.differentiableOn hΨ'.mapsTo
      hΨ'.norm_fderiv_le hΨ'.pos hΨ'.le_abs_det hΨΦ' hΦΨ'
      (energyFormH1_restrictL_eq_setIntegral (inf_le_left : D ≤ Ω) hu) w
    rw [pullbackDrift_zero, pullbackDensity_zero] at h
    exact h.trans (setIntegral_congr_fun Ω'.isOpen.measurableSet fun x hx => by rw [hdet x hx])
  · exact (memLp_pullbackDensity hΦ'.differentiableOn hΦ'.injOn hΦ'.mapsTo
      hΦ'.norm_fderiv_le hΦ'.pos hΦ'.le_abs_det (hf.mono_measure
        (Measure.restrict_mono (fun x hx => hx.1 : (D : Set E) ⊆ Ω) le_rfl))).ae_eq
      (ae_restrict_of_forall_mem Ω'.isOpen.measurableSet hdet)

/-- **The flattened solution has a Hölder Hessian up to the flat boundary.** Under the hypotheses of
`exists_lowerOrder_eq_restrictL_and_holderOnWith_iteratedGradient_of_isChangeOfVariables`, there is
`r > 0` such that on the half-ball `H ∩ B(y₀, r / 16)` the function `u ∘ Φ`
is the value of an element of `W^{2,2}` whose weak Hessian and weak gradient agree almost
everywhere with fields that are `α`-Hölder on `closure (H ∩ B(y₀, r / 16))`. -/
private theorem exists_flat_of_isChangeOfVariables
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω W U' U : Opens E} {Φ Ψ : E → E} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) {ν : E} (hν : ν ≠ 0) {c₀ : ℝ}
    {H : Opens E} (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (himage : Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = (Ω : Set E) ∩ U)
    {KT : ℝ≥0} (hT : HolderOnWith KT α (fderiv ℝ (fderiv ℝ Ψ)) U)
    {y₀ : E} (hy₀ : y₀ ∈ U') (hy₀ν : ⟪y₀, ν⟫_ℝ = c₀) (hy₀W : Φ y₀ ∈ W)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) W)
    (hell : UniformlyEllipticOn W a lam Lam)
    (hda : ∀ x ∈ W, ∃ ρ > 0, ∃ C : ℝ≥0, ∀ i j,
      HolderOnWith C α (fderiv ℝ fun y => a y i j) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hfH : ∀ x ∈ (W : Set E) ∩ closure Ω, ∃ ρ > 0, ∃ C : ℝ≥0,
      HolderOnWith C α f (ball x ρ ∩ closure Ω))
    {u : W1p volume Ω 2}
    (hu : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x) :
    ∃ r > 0,
      ∃ V2 : Wkp volume ((H ⊓ ⟨ball y₀ r, isOpen_ball⟩) ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩ :
        Opens E) 2 2,
        (Wkp.value 2 V2 : E → ℝ) =ᵐ[volume.restrict ((H : Set E) ∩ ball y₀ r ∩ ball y₀ (r / 16))]
          (fun y => W1p.value u (Φ y)) ∧
        ∃ (Gv : E → E →L[ℝ] E) (P : E → E),
          (∃ C : ℝ≥0, HolderOnWith C α Gv (closure ((H : Set E) ∩ ball y₀ (r / 16)))) ∧
          (∃ C : ℝ≥0, HolderOnWith C α P (closure ((H : Set E) ∩ ball y₀ (r / 16)))) ∧
          (Wkp.iteratedGradient 1 V2 : E → E →L[ℝ] E)
            =ᵐ[volume.restrict ((H : Set E) ∩ ball y₀ r ∩ ball y₀ (r / 16))] Gv ∧
          (W1p.gradient (Wkp.lowerOrder 1 V2) : E → E)
            =ᵐ[volume.restrict ((H : Set E) ∩ ball y₀ r ∩ ball y₀ (r / 16))] P := by
  -- A closed ball about `y₀` in `U'` which `Φ` maps into `W`.
  obtain ⟨r, hr, hrB⟩ := nhds_basis_closedBall.mem_iff.1
    ((hΦ.contDiffOn.continuousOn.isOpen_inter_preimage U'.isOpen W.isOpen).mem_nhds ⟨hy₀, hy₀W⟩)
  have hBU' : ball y₀ r ⊆ U' := ball_subset_closedBall.trans (hrB.trans inter_subset_left)
  obtain ⟨ha', ⟨lam', Lam', hell'⟩, hda', hfH'⟩ := flat_hypotheses_of_isChangeOfVariables hα hα1
    hΦ hΨ hΨΦ hΦΨ hν himage hT ha hell hda hfH hr hBU'
    fun x hx => (hrB (ball_subset_closedBall hx)).2
  obtain ⟨v, hvu, hv, hv0, hf'⟩ :=
    exists_flattened_problem hΦ hΨ hΨΦ hΦΨ hH himage hf hu hu0 hrB
  have hΩ' : ((H ⊓ ⟨ball y₀ r, isOpen_ball⟩ : Opens E) : Set E) ∩ ball y₀ r =
      (H : Set E) ∩ ball y₀ r := by
    rw [Opens.coe_inf, inter_assoc]
    exact congrArg _ (inter_self _)
  -- Regularity near the flat boundary.
  obtain ⟨V2, hV2, Gv, P, hCG, hCP, hGvae, hPae⟩ :=
    exists_wkp_and_holderOnWith_of_inter_ball_eq hα hα1 hν hH hy₀ν hr hΩ' ha' hell' hda' hf' hfH'
      hv hv0
  refine ⟨r, hr, V2, ?_, Gv, P, hCG, hCP, hGvae, by rwa [hV2]⟩
  rw [← Wkp.value_lowerOrder_one, hV2]
  filter_upwards [W1p.value_restrictL_ae (inf_le_left :
      ((H ⊓ ⟨ball y₀ r, isOpen_ball⟩) ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩ : Opens E) ≤
        H ⊓ ⟨ball y₀ r, isOpen_ball⟩) v,
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hvu] with x h1 h2
  rw [h1, h2]

/-- **The gradient and the Hessian are `α`-Hölder up to the curved boundary.** In the setting of
`exists_lowerOrder_eq_restrictL_and_holderOnWith_iteratedGradient_of_isChangeOfVariables`, if
`V ∈ W^{2,2}` on the flat half-ball `Ω₂` has weak Hessian and weak gradient equal almost everywhere
to fields that are `α`-Hölder on `closure (H ∩ B(y₀, r / 16))`, then for `V ∘ Ψ` on `Ω₁` the weak
gradient and the weak Hessian agree almost everywhere with fields that are `α`-Hölder on
`closure Ω ∩ U ∩ Ψ⁻¹ B(y₀, r / 32) ∩ B(z, ρ)`, whenever `closedBall z ρ ⊆ U`. -/
private theorem exists_holderOnWith_gradient_and_iteratedGradient_compL_closure {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω U U' Ω₁ Ω₂ H : Opens E} {Ψ : E → E} {L : ℝ}
    (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L 1) (hΨ'' : Wkp.IsChangeOfVariables 2 Ω₁ Ω₂ Ψ L 1)
    {KT : ℝ≥0} (hT : HolderOnWith KT α (fderiv ℝ (fderiv ℝ Ψ)) U)
    (hΨcl : ∀ x ∈ U, x ∈ closure (Ω : Set E) → Ψ x ∈ closure (H : Set E))
    {y₀ z : E} {r ρ : ℝ} (hr : 0 < r) (hρU : closedBall z ρ ⊆ U) (V : Wkp volume Ω₂ 2 2)
    {Gv : E → E →L[ℝ] E} {P : E → E} {CG CP : ℝ≥0}
    (hCG : HolderOnWith CG α Gv (closure ((H : Set E) ∩ ball y₀ (r / 16))))
    (hCP : HolderOnWith CP α P (closure ((H : Set E) ∩ ball y₀ (r / 16))))
    (hGvae : (Wkp.iteratedGradient 1 V : E → E →L[ℝ] E) =ᵐ[volume.restrict (Ω₂ : Set E)] Gv)
    (hPae : (W1p.gradient (Wkp.lowerOrder 1 V) : E → E) =ᵐ[volume.restrict (Ω₂ : Set E)] P) :
    (∃ Q : E → E, (∃ C : ℝ≥0, HolderOnWith C α Q
        (closure (Ω : Set E) ∩ ((U : Set E) ∩ Ψ ⁻¹' ball y₀ (r / 32) ∩ ball z ρ))) ∧
      (W1p.gradient (Wkp.lowerOrder 1 (Wkp.compL hΨ'' V)) : E → E)
        =ᵐ[volume.restrict (Ω₁ : Set E)] Q) ∧
    ∃ G : E → E →L[ℝ] E, (∃ C : ℝ≥0, HolderOnWith C α G
        (closure (Ω : Set E) ∩ ((U : Set E) ∩ Ψ ⁻¹' ball y₀ (r / 32) ∩ ball z ρ))) ∧
      (Wkp.iteratedGradient 1 (Wkp.compL hΨ'' V) : E → E →L[ℝ] E)
        =ᵐ[volume.restrict (Ω₁ : Set E)] G := by
  -- A compact set `K` containing `closure Ω ∩ V`, mapped by `Ψ` into the closed half-ball.
  let K : Set E := closure (Ω : Set E) ∩ (closedBall z ρ ∩ Ψ ⁻¹' closedBall y₀ (r / 32))
  have hKc : IsCompact K := (isCompact_closedBall z ρ).of_isClosed_subset
    (isClosed_closure.inter ((hΨ.contDiffOn.continuousOn.mono hρU).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_closedBall)) fun x hx => hx.2.1
  have hKU : K ⊆ U := fun x hx => hρU hx.2.1
  have hSK : closure (Ω : Set E) ∩ ((U : Set E) ∩ Ψ ⁻¹' ball y₀ (r / 32) ∩ ball z ρ) ⊆ K := by
    rintro x ⟨hxΩ, ⟨-, hxb⟩, hxρ⟩
    exact ⟨hxΩ, ball_subset_closedBall hxρ,
      mem_preimage.2 (ball_subset_closedBall (mem_preimage.1 hxb))⟩
  have hΨK : MapsTo Ψ K (closure ((H : Set E) ∩ ball y₀ (r / 16))) := fun x hx => by
    have hb : Ψ x ∈ ball y₀ (r / 16) :=
      closedBall_subset_ball (by linarith) (mem_preimage.1 hx.2.2)
    have h := isOpen_ball.inter_closure ⟨hb, hΨcl x (hKU hx) hx.1⟩
    rwa [inter_comm] at h
  -- `Ψ` is Lipschitz and `DΨ` is `α`-Hölder on the compact convex `closedBall z ρ ⊇ K`.
  have hΨ2 : ContDiffOn ℝ 2 Ψ U := by exact_mod_cast hΨ.contDiffOn
  obtain ⟨LΨ, hLΨ⟩ := ((hΨ2.mono hρU).of_le one_le_two).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall z ρ) (isCompact_closedBall z ρ)
  have hLΨK : LipschitzOnWith LΨ Ψ K := hLΨ.mono fun x (hx : x ∈ K) => hx.2.1
  obtain ⟨CD, hCD⟩ := ((hΨ.contDiffOn_fderiv (k := 1)).mono hρU).exists_holderOnWith
    (convex_closedBall z ρ) (isCompact_closedBall z ρ) hα1.le
  have hDΨ (e : E) : ∃ C : ℝ≥0, HolderOnWith C α (fun x => fderiv ℝ Ψ x e) K := by
    obtain ⟨C, hC⟩ := (((hΨ.contDiffOn_fderiv (k := 1)).clm_apply contDiffOn_const).mono
      hρU).exists_holderOnWith (convex_closedBall z ρ) (isCompact_closedBall z ρ) hα1.le
    exact ⟨C, hC.mono fun x (hx : x ∈ K) => hx.2.1⟩
  -- The weak gradient of `V ∘ Ψ` is `DΨ† ∇V(Ψ ·)`.
  obtain ⟨CQ, hCQ⟩ := (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).exists_holderOnWith_comp₂_of_isCompact
    hKc hα ((ContinuousLinearMap.adjoint.isometry.comp_holderOnWith hCD).mono
      fun x (hx : x ∈ K) => hx.2.1) (hCP.comp_lipschitzOnWith hLΨK hΨK)
  refine ⟨⟨fun x => (fderiv ℝ Ψ x).adjoint (P (Ψ x)), ⟨CQ, hCQ.mono hSK⟩, ?_⟩, ?_⟩
  · rw [← Wkp.firstOrder_one]
    filter_upwards [Wkp.gradient_firstOrder_compL_ae hΨ'' V, hΨ''.ae_comp hPae] with x h1 h2
    rw [h1, Wkp.firstOrder_one, h2]
  obtain ⟨G, ⟨C, hC⟩, hG⟩ := Wkp.exists_holderOnWith_iteratedGradient_compL hα hΨ''
    ENNReal.ofNat_ne_top V hKc hΨK hLΨK hDΨ (hT.mono hKU) hCG hCP hGvae hPae
  exact ⟨G, ⟨C, hC.mono hSK⟩, hG⟩

/-- **Second derivatives up to a straightened boundary portion.** Let `Φ` and `Ψ` be changes of
variables of order two between open sets `U'` and `U`, inverse to each other there, with Jacobian
determinant one, such that `Φ` maps the part of `U'` in the half-space `H = {c₀ < ⟪x, ν⟫}` onto
`Ω ∩ U`, and suppose that `D²Ψ` is `α`-Hölder on `U`, `0 < α < 1`. Let `y₀ ∈ U'` lie on the
boundary hyperplane, so that `Φ y₀` is a boundary point of `Ω`, and let `W` be an open
neighbourhood of `Φ y₀`. Suppose that `a` is uniformly elliptic on `W`, that its entries are `C¹`
there with first derivatives `α`-Hölder near each point of `W`, and that `f ∈ L²(Ω)` is `α`-Hölder
on `closure Ω` near each point of `W ∩ closure Ω`. Let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, such that
`ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `W`: `u` vanishes on `∂Ω ∩ W`.

Then there is an open neighbourhood `V` of `Φ y₀` such that, on `Ω ∩ V`, `u` is the first-order
part of an element `w` of `W^{2,2}(Ω ∩ V)` whose weak gradient and weak Hessian agree almost
everywhere on `Ω ∩ V` with fields that are `α`-Hölder on `closure Ω ∩ V`. This is the Sobolev form
of `C^{2,α}` regularity up to the boundary near `Φ y₀`; no classical `C²` representative of `u` is
constructed here. -/
theorem exists_lowerOrder_eq_restrictL_and_holderOnWith_iteratedGradient_of_isChangeOfVariables
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω W U' U : Opens E} {Φ Ψ : E → E} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) {ν : E} (hν : ν ≠ 0) {c₀ : ℝ}
    (himage : Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = (Ω : Set E) ∩ U)
    {KT : ℝ≥0} (hT : HolderOnWith KT α (fderiv ℝ (fderiv ℝ Ψ)) U)
    {y₀ : E} (hy₀ : y₀ ∈ U') (hy₀ν : ⟪y₀, ν⟫_ℝ = c₀) (hy₀W : Φ y₀ ∈ W)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) W)
    (hell : UniformlyEllipticOn W a lam Lam)
    (hda : ∀ x ∈ W, ∃ ρ > 0, ∃ C : ℝ≥0, ∀ i j,
      HolderOnWith C α (fderiv ℝ fun y => a y i j) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hfH : ∀ x ∈ (W : Set E) ∩ closure Ω, ∃ ρ > 0, ∃ C : ℝ≥0,
      HolderOnWith C α f (ball x ρ ∩ closure Ω))
    {u : W1p volume Ω 2}
    (hu : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x) :
    ∃ V : Opens E, Φ y₀ ∈ V ∧ ∃ w : Wkp volume (Ω ⊓ V) 2 2,
      Wkp.lowerOrder 1 w = W1p.restrictL inf_le_left u ∧
      (∃ Q : E → E, (∃ C : ℝ≥0, HolderOnWith C α Q (closure (Ω : Set E) ∩ V)) ∧
        (W1p.gradient (Wkp.lowerOrder 1 w) : E → E) =ᵐ[volume.restrict ((Ω : Set E) ∩ V)] Q) ∧
      ∃ G : E → E →L[ℝ] E, (∃ C : ℝ≥0, HolderOnWith C α G (closure (Ω : Set E) ∩ V)) ∧
        (Wkp.iteratedGradient 1 w : E → E →L[ℝ] E) =ᵐ[volume.restrict ((Ω : Set E) ∩ V)] G := by
  let H : Opens E := ⟨{x | c₀ < ⟪x, ν⟫_ℝ}, isOpen_lt continuous_const
    (continuous_id.inner continuous_const)⟩
  have hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ := fun _ => Iff.rfl
  obtain ⟨r, hr, V2, hval, Gv, P, ⟨CG, hCG⟩, ⟨CP, hCP⟩, hGvae, hPae⟩ :=
    exists_flat_of_isChangeOfVariables hα hα1 hΦ hΨ hΨΦ hΦΨ hν hH himage hT hy₀ hy₀ν
      hy₀W ha hell hda hf hfH hu hu0
  -- `Ψ` maps `closure Ω ∩ U` into the closed half-space.
  have hΨcl (x : E) (hx : x ∈ U) (hxΩ : x ∈ closure (Ω : Set E)) :
      Ψ x ∈ closure (H : Set E) := by
    refine (hΨ.contDiffOn.continuousOn.continuousAt (U.isOpen.mem_nhds hx)).continuousWithinAt
      |>.mem_closure (U.isOpen.inter_closure ⟨hx, hxΩ⟩) fun z hz => ?_
    obtain ⟨y, hy, hyz⟩ : z ∈ Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') := himage ▸ ⟨hz.2, hz.1⟩
    rw [← hyz, hΨΦ hy.2]
    exact hy.1
  -- `V = U ∩ Ψ⁻¹ B(y₀, r / 32) ∩ B(Φ y₀, ρ)` with `closedBall (Φ y₀) ρ ⊆ U`.
  have hx₀U : Φ y₀ ∈ U := hΦ.mapsTo hy₀
  obtain ⟨ρ, hρ, hρU⟩ := nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds hx₀U)
  let V : Opens E := ⟨U ∩ Ψ ⁻¹' ball y₀ (r / 32) ∩ ball (Φ y₀) ρ,
    (hΨ.contDiffOn.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball).inter isOpen_ball⟩
  have hx₀V : Φ y₀ ∈ V :=
    ⟨⟨hx₀U, by rw [mem_preimage, hΨΦ hy₀]; exact mem_ball_self (by positivity)⟩,
      mem_ball_self hρ⟩
  have hΨV : MapsTo Ψ (Ω ⊓ V : Opens E)
      ((H ⊓ ⟨ball y₀ r, isOpen_ball⟩) ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩ : Opens E) :=
    fun y hy => by
      obtain ⟨x, ⟨hxH, hxU'⟩, rfl⟩ : y ∈ Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') :=
        himage ▸ ⟨hy.1, hy.2.1.1⟩
      have hb := hy.2.1.2
      rw [mem_preimage] at hb
      exact ⟨⟨(hH _).2 (by rw [hΨΦ hxU']; exact hxH), ball_subset_ball (by linarith) hb⟩,
        ball_subset_ball (by linarith) hb⟩
  have hΨ'' := hΨ.mono_set (fun y hy => hy.2.1.1 : Ω ⊓ V ≤ U) hΨV
  obtain ⟨hQ, hG⟩ := exists_holderOnWith_gradient_and_iteratedGradient_compL_closure hα hα1 hΨ
    hΨ'' hT hΨcl hr hρU V2 hCG hCP hGvae hPae
  refine ⟨V, hx₀V, Wkp.compL hΨ'' V2, ?_, hQ, hG⟩
  -- The first-order part of `V2 ∘ Ψ` is `u`.
  refine W1p.ext_value (Lp.ext ?_)
  rw [Wkp.value_lowerOrder_one]
  filter_upwards [Wkp.value_compL_ae hΨ'' V2, hΨ''.ae_comp hval,
    W1p.value_restrictL_ae (inf_le_left : Ω ⊓ V ≤ Ω) u,
    ae_restrict_mem (Ω ⊓ V).isOpen.measurableSet] with x h1 h2 h3 hx
  rw [h1, h2, hΦΨ hx.2.1.1, h3]

end Curved

end PDE

end TauCeti
