/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.SecondDerivatives
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Sobolev.W1p.LipschitzRepresentative
import TauCeti.Analysis.Sobolev.WeakDeriv.ContinuousRepresentative

/-!
# Classical `C^{2,α}` regularity up to a flat portion of the boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `y₀` lie on the boundary hyperplane, and let `Ω` be
an open set with `Ω ∩ B(y₀, r) = H ∩ B(y₀, r)`. Let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω` that vanishes on `∂Ω ∩ B(y₀, r)`, with `a` uniformly elliptic and of
class `C^{1,α}` on `B(y₀, r)` and `f` locally `α`-Hölder up to the boundary there, `0 < α < 1`.
By `TauCeti.PDE.exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq`, every weak
derivative `∂_w u` lies in `H¹` of the half-ball `Ω ∩ B(y₀, r / 16)`, with a gradient that agrees
almost everywhere with a field `α`-Hölder up to the flat boundary.

This file turns that statement into classical regularity. On the half-ball `Ω ∩ B(y₀, r / 16)`
the solution `u` agrees almost everywhere with a function `g` of class `C²` there, whose value,
first derivative and second derivative are bounded there and whose first and second derivatives
are `α`-Hölder there
(`TauCeti.PDE.exists_contDiffOn_two_ae_eq_and_holderOnWith_of_inter_ball_eq`). A function
Hölder on a set extends Hölder continuously to its closure, so `g` is of class `C^{2,α}` up to the
flat boundary portion `∂Ω ∩ B(y₀, r / 16)`, and `g` tends to `0` there: the boundary condition
holds pointwise. The last statement holds for any Sobolev function vanishing on the flat portion
with a `C¹` representative of bounded derivative
(`TauCeti.PDE.tendsto_nhdsWithin_zero_of_inter_ball_eq`).

This is the boundary counterpart of the interior statement
`TauCeti.PDE.exists_contDiffOn_two_ae_eq_and_neg_laplacian_eq_of_locally_holderOnWith`, and the
form in which flat-boundary regularity is transported to a curved boundary: classical first and
second derivatives compose with a flattening map by the chain rule, as in
`TauCeti.holderOnWith_fderiv_fderiv_comp_shearAlong`.

## The argument

The directional derivatives `∂ᵢu` along an orthonormal basis have weak gradients agreeing almost
everywhere with Hölder, hence continuous, fields `Gᵢ` on the half-ball. Then `u` has a `C²`
representative `g` with `D²g(x) h k = ∑ᵢ ⟪Gᵢ x, h⟫ ⟪eᵢ, k⟫`
(`TauCeti.exists_contDiffOn_two_ae_eq_and_fderiv_fderiv_eq`), which is Hölder with the sum of the
Hölder constants of the `Gᵢ`. The half-ball is bounded and convex, so `D²g` is bounded there, and
the mean value inequality (`Convex.holderOnWith_of_norm_fderiv_le`) makes `Dg`, and then `g`,
Hölder, hence bounded, there.

For the boundary values, a cutoff equal to one near `y₀` turns `u` into an element `v` of
`H¹₀(Ω)` equal to `g` near `y₀`, whose gradient is bounded there. Points just below the hyperplane
lie outside `closure Ω`, so the zero extension of `v` has a Lipschitz representative vanishing on
the flat portion (`TauCeti.W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le`). It agrees
with `g` on the open half-ball, both being continuous there, so `g` tends to `0` at the flat
portion.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 6.18 (the corresponding statement for classical solutions).
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **Zero boundary values on a flat portion of the boundary are attained.** Let
`H = {x | c₀ < ⟪x, ν⟫}`, let `Ω` be open with `Ω ∩ B(y₀, r) = H ∩ B(y₀, r)`, and let
`u ∈ H¹(Ω)` vanish on `∂Ω ∩ B(y₀, r)`, in the sense that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ`
compactly supported in `B(y₀, r)`. If, for some `ρ < r`, `u` agrees almost everywhere on
`Ω ∩ B(y₀, ρ)` with a function `g` that is `C¹` there with bounded derivative, then `g` tends to
`0` at every point `z ∈ B(y₀, ρ)` of the hyperplane `⟪z, ν⟫ = c₀`, within `Ω ∩ B(y₀, ρ)`. -/
theorem tendsto_nhdsWithin_zero_of_inter_ball_eq {H Ω : Opens E} {ν : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {y₀ : E} {r ρ : ℝ} (hρr : ρ < r)
    (hΩ : (Ω : Set E) ∩ ball y₀ r = (H : Set E) ∩ ball y₀ r) {u : W1p volume Ω 2}
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball y₀ r →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x)
    {g : E → ℝ} (hg : ContDiffOn ℝ 1 g ((Ω : Set E) ∩ ball y₀ ρ))
    (hug : W1p.value u =ᵐ[volume.restrict ((Ω : Set E) ∩ ball y₀ ρ)] g) {M : ℝ≥0}
    (hM : ∀ x ∈ (Ω : Set E) ∩ ball y₀ ρ, ‖fderiv ℝ g x‖ ≤ M) {z : E} (hz : z ∈ ball y₀ ρ)
    (hzν : ⟪z, ν⟫_ℝ = c₀) :
    Tendsto g (𝓝[(Ω : Set E) ∩ ball y₀ ρ] z) (𝓝 0) := by
  -- For `ν = 0` the half-ball is empty.
  rcases eq_or_ne ν 0 with rfl | hν
  · rw [inter_eq_inter_mono_right hΩ (ball_subset_ball hρr.le),
      show (H : Set E) = {x | c₀ < ⟪x, 0⟫_ℝ} from Set.ext hH]
    simp [← hzν]
  have hρ : 0 < ρ := pos_of_mem_ball hz
  -- A cutoff equal to one on `B(y₀, ρ)` localizes `u` to an element `v` of `H¹₀(Ω)`, equal to `g`
  -- on `T = Ω ∩ B(y₀, ρ)`.
  let ψ : ContDiffBump y₀ := ⟨ρ, (ρ + r) / 2, hρ, by linarith⟩
  obtain ⟨v, hv⟩ := hu0 ψ ψ.contDiff ψ.hasCompactSupport
    (ψ.tsupport_eq ▸ closedBall_subset_ball (by simp only [ψ]; linarith))
  set T : Opens E := Ω ⊓ ⟨ball y₀ ρ, isOpen_ball⟩
  have hTΩ : T ≤ Ω := inf_le_left
  have hvg : W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict T] g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTΩ hv, hug,
      ae_restrict_mem T.isOpen.measurableSet] with x hx hxg hxT
    rw [hx, ψ.one_of_mem_closedBall (ball_subset_closedBall hxT.2), one_mul, hxg]
  have hgrad : ∀ᵐ x ∂volume, x ∈ T → W1p.gradient (v : W1p volume Ω 2) x = ∇ g x :=
    (ae_restrict_iff' T.isOpen.measurableSet).1 ((W1p.gradient_restrictL_ae hTΩ _).symm.trans
      (W1p.gradient_ae_eq_of_contDiffOn _ hg ((W1p.value_restrictL_ae hTΩ _).trans hvg)))
  -- The zero extension of `v` has a Lipschitz representative vanishing at `z`.
  have hzF := mem_closure_compl_closure_of_inter_ball_eq hν hH hΩ
    (ball_subset_ball hρr.le hz) hzν
  have hρz : 0 < ρ - dist z y₀ := sub_pos.2 (mem_ball.1 hz)
  have hbz : ball z (ρ - dist z y₀) ⊆ ball y₀ ρ := ball_subset_ball' (by linarith)
  obtain ⟨u', hvu', hLip, hu'z⟩ := W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le
    isClosed_closure subset_closure v hzF hρz (M := M) (by
      filter_upwards [hgrad] with x hx hxz
      rw [hx ⟨hxz.1, hbz hxz.2⟩, norm_gradient_eq_norm_fderiv]
      exact hM x ⟨hxz.1, hbz hxz.2⟩)
  -- The Lipschitz representative is `g` near `z`, so `g` tends to its value `0` at `z`.
  have heq : EqOn u' g ((Ω : Set E) ∩ ball z (ρ - dist z y₀)) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (Ω.isOpen.inter isOpen_ball)
      (hLip.continuousOn.mono inter_subset_right)
      (hg.continuousOn.mono (inter_subset_inter_right _ hbz))
    have h1 : W1p.value (v : W1p volume Ω 2)
        =ᵐ[volume.restrict ((Ω : Set E) ∩ ball z (ρ - dist z y₀))] u' :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hvu'
    have h2 : W1p.value (v : W1p volume Ω 2)
        =ᵐ[volume.restrict ((Ω : Set E) ∩ ball z (ρ - dist z y₀))] g :=
      ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _ hbz) hvg
    exact h1.symm.trans h2
  refine (((hLip.continuousOn.continuousAt (ball_mem_nhds z hρz)).tendsto.mono_left
    nhdsWithin_le_nhds).congr' ?_).trans (by rw [hu'z])
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z hρz)] with x hxS hxb
  exact heq ⟨hxS.1, hxb⟩

/-- The `C²` representative near a flat boundary portion, with `α`-Hölder second derivative. -/
private theorem exists_contDiffOn_two_ae_eq_and_holderOnWith_fderiv_fderiv_of_inter_ball_eq
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {H Ω : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {y₀ : E} (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (hΩ : (Ω : Set E) ∩ ball y₀ r = (H : Set E) ∩ ball y₀ r)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hell : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {u : W1p volume Ω 2}
    (hu : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball y₀ r →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x) :
    ∃ g : E → ℝ, ContDiffOn ℝ 2 g ((Ω : Set E) ∩ ball y₀ (r / 16)) ∧
      W1p.value u =ᵐ[volume.restrict ((Ω : Set E) ∩ ball y₀ (r / 16))] g ∧
      ∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ (fderiv ℝ g)) ((Ω : Set E) ∩ ball y₀ (r / 16)) := by
  set S : Opens E := Ω ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩
  have hSH : (S : Set E) ⊆ closedBall y₀ (r / 16) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ} := fun x hx => by
    have hx' : x ∈ (H : Set E) ∩ ball y₀ (r / 16) :=
      (inter_eq_inter_mono_right hΩ (ball_subset_ball (by linarith))).subset hx
    exact ⟨ball_subset_closedBall hx'.2, ((hH x).1 hx'.1).le⟩
  -- The derivatives along the standard basis have weak gradients with Hölder representatives.
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hsecond := fun i => exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq
    hα hα1 hν hH hy₀ hr hΩ ha hell hda hf hfH hu hu0 (b i)
  choose d hd G hG hdG using hsecond
  choose K hK using hG
  obtain ⟨g, hg, hug, hD2⟩ := exists_contDiffOn_two_ae_eq_and_fderiv_fderiv_eq (Ω := S) (b := b)
    (hd 0).locallyIntegrableOn hd
    (fun i => (W1p.hasWeakFDerivOn (d i)).congr_ae_deriv ((hdG i).fun_comp (innerSL ℝ)))
    fun i => ((hK i).continuousOn hα).mono hSH
  -- `D²g` is Hölder with the sum of the Hölder constants of the fields `Gᵢ`.
  refine ⟨g, hg, hug, ∑ i, K i, (HolderOnWith.sum (s := Finset.univ)
      (f := fun i x => (innerSL ℝ (G i x)).smulRight (innerSL ℝ (b i)))
      fun i _ => HolderOnWith.of_dist_le fun x hx y hy => ?_).congr
    fun x hx => (hD2 x hx).symm⟩
  have hGd : ‖G i x - G i y‖ ≤ K i * dist x y ^ (α : ℝ) := by
    rw [← dist_eq_norm]
    exact (hK i).dist_le (hSH hx) (hSH hy)
  rw [dist_eq_norm]
  refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h => ?_) hGd
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ← sub_smul,
    ← inner_sub_left, norm_smul, innerSL_apply_norm, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

/-- **`C^{2,α}` regularity up to a flat portion of the boundary, in classical form.** Let
`0 < α < 1`, let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `y₀` lie on the boundary hyperplane, and
let `Ω` be open with `Ω ∩ B(y₀, r) = H ∩ B(y₀, r)`. Suppose that `a` is uniformly elliptic on
`B(y₀, r)`, that its entries are `C¹` there with first derivatives `α`-Hölder near each point of
the ball, and that `f ∈ L²(Ω)` is `α`-Hölder up to the boundary near each point of
`B(y₀, r) ∩ {c₀ ≤ ⟪y, ν⟫}`. Let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω` such
that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `B(y₀, r)`.

Then on the half-ball `Ω ∩ B(y₀, r / 16)` the solution `u` agrees almost everywhere with a function
`g` of class `C²` there, such that `g`, `Dg` and `D²g` are bounded there and `Dg` and `D²g` are
`α`-Hölder there, all with one constant `C`, and `g` tends to `0` at each point of the flat
boundary portion `B(y₀, r / 16) ∩ {⟪z, ν⟫ = c₀}`. -/
theorem exists_contDiffOn_two_ae_eq_and_holderOnWith_of_inter_ball_eq
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {H Ω : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {y₀ : E} (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (hΩ : (Ω : Set E) ∩ ball y₀ r = (H : Set E) ∩ ball y₀ r)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hell : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {u : W1p volume Ω 2}
    (hu : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball y₀ r →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x) :
    ∃ g : E → ℝ, ContDiffOn ℝ 2 g ((Ω : Set E) ∩ ball y₀ (r / 16)) ∧
      W1p.value u =ᵐ[volume.restrict ((Ω : Set E) ∩ ball y₀ (r / 16))] g ∧
      (∃ C : ℝ≥0, (∀ x ∈ (Ω : Set E) ∩ ball y₀ (r / 16),
          ‖g x‖ ≤ C ∧ ‖fderiv ℝ g x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C) ∧
        HolderOnWith C α (fderiv ℝ g) ((Ω : Set E) ∩ ball y₀ (r / 16)) ∧
        HolderOnWith C α (fderiv ℝ (fderiv ℝ g)) ((Ω : Set E) ∩ ball y₀ (r / 16))) ∧
      ∀ z ∈ ball y₀ (r / 16), ⟪z, ν⟫_ℝ = c₀ →
        Tendsto g (𝓝[(Ω : Set E) ∩ ball y₀ (r / 16)] z) (𝓝 0) := by
  obtain ⟨g, hg, hug, K₂, hhol2⟩ :=
    exists_contDiffOn_two_ae_eq_and_holderOnWith_fderiv_fderiv_of_inter_ball_eq hα hα1 hν hH hy₀
      hr hΩ ha hell hda hf hfH hu hu0
  have hconv : Convex ℝ ((Ω : Set E) ∩ ball y₀ (r / 16)) := by
    rw [inter_eq_inter_mono_right hΩ (ball_subset_ball (by linarith)),
      show (H : Set E) = {x | c₀ < ⟪x, ν⟫_ℝ} from Set.ext hH]
    exact (convex_halfSpace_gt ⟨fun x y => inner_add_left x y ν, fun c x => by
      rw [real_inner_smul_left, smul_eq_mul]⟩ c₀).inter (convex_ball y₀ (r / 16))
  set S := (Ω : Set E) ∩ ball y₀ (r / 16)
  have hSo : IsOpen S := Ω.isOpen.inter isOpen_ball
  -- The half-ball is bounded and convex, so `D²g`, then `Dg` and `g`, are bounded and Hölder.
  have hSb : Bornology.IsBounded S := isBounded_ball.subset inter_subset_right
  obtain ⟨M₂, hM₂⟩ := isBounded_iff_forall_norm_le.1 (hhol2.isBounded_image hSb)
  have hhol1 := hconv.holderOnWith_of_norm_fderiv_le hα1.le inter_subset_right
    (N := M₂.toNNReal) (fun x hx => ((hg.fderiv_of_isOpen hSo (by norm_num)).differentiableOn
      one_ne_zero).differentiableAt (hSo.mem_nhds hx))
    fun x hx => (hM₂ _ (mem_image_of_mem _ hx)).trans (Real.le_coe_toNNReal M₂)
  obtain ⟨M₁, hM₁⟩ := isBounded_iff_forall_norm_le.1 (hhol1.isBounded_image hSb)
  have hhol0 := hconv.holderOnWith_of_norm_fderiv_le hα1.le inter_subset_right
    (N := M₁.toNNReal)
    (fun x hx => (hg.differentiableOn (by norm_num)).differentiableAt (hSo.mem_nhds hx))
    fun x hx => (hM₁ _ (mem_image_of_mem _ hx)).trans (Real.le_coe_toNNReal M₁)
  obtain ⟨M₀, hM₀⟩ := isBounded_iff_forall_norm_le.1 (hhol0.isBounded_image hSb)
  set K₁ := M₂.toNNReal * (2 * (r / 16)).toNNReal ^ ((1 : ℝ) - α)
  refine ⟨g, hg, hug, ⟨max (max M₀.toNNReal M₁.toNNReal) (max M₂.toNNReal (max K₁ K₂)),
    fun x hx => ⟨?_, ?_, ?_⟩, hhol1.mono_const ?_, hhol2.mono_const ?_⟩,
    fun z hz hzν => tendsto_nhdsWithin_zero_of_inter_ball_eq hH (by linarith) hΩ hu0
      (hg.of_le (by norm_num)) hug (M := M₁.toNNReal)
      (fun x hx => (hM₁ _ (mem_image_of_mem _ hx)).trans (Real.le_coe_toNNReal M₁)) hz hzν⟩
  · exact (hM₀ _ (mem_image_of_mem _ hx)).trans ((Real.le_coe_toNNReal M₀).trans
      (by exact_mod_cast (le_max_left _ _).trans (le_max_left _ _)))
  · exact (hM₁ _ (mem_image_of_mem _ hx)).trans ((Real.le_coe_toNNReal M₁).trans
      (by exact_mod_cast (le_max_right _ _).trans (le_max_left _ _)))
  · exact (hM₂ _ (mem_image_of_mem _ hx)).trans ((Real.le_coe_toNNReal M₂).trans
      (by exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)))
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

end PDE

end TauCeti
