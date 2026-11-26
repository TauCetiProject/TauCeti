/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables

import TauCeti.Analysis.Holder.CompLinear
import TauCeti.Analysis.Holder.FaaDiBruno
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.Holder.Leibniz

/-!
# Hölder derivatives of the transformed principal coefficient

Let `Φ` and `Ψ` be mutually inverse changes of variables of order one with Jacobian determinants
of absolute value one, such as the shear that flattens the region above the graph of a function.
Under the change of variables `Φ`, a divergence-form operator with principal coefficient `a`
becomes one with the transformed coefficient `a' = TauCeti.PDE.pullbackPrincipal Φ a`, whose
entries are

`a'ᵢⱼ(x) = ∑ₖₗ (DΨ(Φ x) eₖ)ᵢ aₖₗ(Φ x) (DΨ(Φ x) eₗ)ⱼ`.

The entries of `a'` are `C¹` where `Φ` is `C¹`, `Ψ` is `C²` and the entries of `a` are `C¹`
(`TauCeti.PDE.contDiffOn_pullbackPrincipal_apply`). This file proves the Hölder half of the
`C^{1,α}` statement: if moreover `Φ` is `C²`, and the second derivative of `Ψ` and the first
derivatives of the entries of `a` are `α`-Hölder near `Φ x`, `α ≤ 1`, then the first derivatives
of the entries of `a'` are `α`-Hölder near `x`, with a common constant for all entries on a ball
around `x`
(`TauCeti.PDE.exists_holderOnWith_fderiv_pullbackPrincipal_apply`).

This is the coefficient regularity that the Schauder theory up to a curved boundary needs. A
`C^{2,α}` boundary is flattened by a shear `Φ` whose inverse `Ψ` has `α`-Hölder second
derivative, and the Laplacian becomes the divergence-form operator with coefficient
`pullbackPrincipal Φ 1`, whose entries are then `C^{1,α}`: this is the hypothesis of the
`C^{2,α}` regularity of divergence-form equations near a flat boundary portion, from which
Kellogg's theorem, the base case of the method of continuity for the Dirichlet problem on
`C^{2,α}` domains, is assembled.

## The argument

Every factor in the formula for `a'ᵢⱼ` is a composite with `Φ`: `(DΨ(·) eₖ)ᵢ` and `aₖₗ` are `C¹`
with locally `α`-Hölder derivative, and the Hölder chain rule
`TauCeti.exists_holderOnWith_iteratedFDerivWithin_comp` makes their composites with the `C²` map
`Φ` so. The Leibniz rule `ContinuousLinearMap.exists_holderOnWith_iteratedFDeriv_comp₂` handles
the products and `HolderOnWith.sum` the sums. Each step shrinks the ball; finitely many steps
leave a ball of positive radius.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §6.2 (flattening a boundary portion by a `C^{2,α}` change of variables).
-/

public section

noncomputable section

open Filter Metric Set TopologicalSpace
open scoped NNReal Topology

namespace TauCeti

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ≥0} {x : E}

/-- `f` is `C¹` with `α`-Hölder first derivative on every small enough ball `B(x, ρ)`. -/
private def IsC1HolderNear (α : ℝ≥0) (x : E) (f : E → ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 1 f (ball x ρ) ∧
    ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 1 f) (ball x ρ)

/-- It suffices to find one ball, since the property passes to smaller balls. -/
private theorem IsC1HolderNear.of_ball {f : E → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ 1 f (ball x ρ)) {K : ℝ≥0}
    (hK : HolderOnWith K α (iteratedFDeriv ℝ 1 f) (ball x ρ)) : IsC1HolderNear α x f := by
  filter_upwards [Ioc_mem_nhdsGT hρ] with ρ' hρ'
  exact ⟨hf.mono (ball_subset_ball hρ'.2), K, hK.mono (ball_subset_ball hρ'.2)⟩

/-- A function agreeing near `x` with one that is `C^{1,α}` near `x` is `C^{1,α}` near `x`. -/
private theorem IsC1HolderNear.congr {f g : E → ℝ} (hf : IsC1HolderNear α x f)
    (hfg : f =ᶠ[𝓝 x] g) : IsC1HolderNear α x g := by
  obtain ⟨ε, hε, hεfg⟩ := Metric.eventually_nhds_iff_ball.1 hfg
  filter_upwards [hf, Ioc_mem_nhdsGT hε] with ρ ⟨hc, K, hK⟩ hρ
  have heq : EqOn f g (ball x ρ) := fun y hy => hεfg y (ball_subset_ball hρ.2 hy)
  refine ⟨hc.congr fun y hy => (heq hy).symm, K, hK.congr fun y hy => ?_⟩
  have hev : f =ᶠ[𝓝 y] g := eventually_of_mem (isOpen_ball.mem_nhds hy) fun z hz => heq hz
  exact (hev.iteratedFDeriv ℝ 1).eq_of_nhds

/-- The product of two functions that are `C^{1,α}` near `x` is `C^{1,α}` near `x`, for
`α ≤ 1`. -/
private theorem IsC1HolderNear.mul (hα : α ≤ 1) {f g : E → ℝ} (hf : IsC1HolderNear α x f)
    (hg : IsC1HolderNear α x g) : IsC1HolderNear α x (fun y => f y * g y) := by
  obtain ⟨ρ, ⟨⟨hfc, C, hC⟩, ⟨hgc, D, hD⟩⟩, hρ⟩ := ((hf.and hg).and self_mem_nhdsWithin).exists
  obtain ⟨r, hr, -, hc, K, hK⟩ :=
    (ContinuousLinearMap.mul ℝ ℝ).exists_holderOnWith_iteratedFDeriv_comp₂
      (ball_mem_nhds x hρ) hα hfc hgc hC hD
  exact .of_ball hr hc hK

/-- A finite sum of functions that are `C^{1,α}` near `x` is `C^{1,α}` near `x`. -/
private theorem IsC1HolderNear.sum {β : Type*} [Fintype β] {f : β → E → ℝ}
    (hf : ∀ b, IsC1HolderNear α x (f b)) : IsC1HolderNear α x (fun y => ∑ b, f b y) := by
  filter_upwards [eventually_all.2 hf] with ρ hρ
  choose hc K hK using hρ
  refine ⟨ContDiffOn.sum fun b _ => hc b, ∑ b, K b,
    (HolderOnWith.sum (s := Finset.univ) fun b _ => hK b).congr fun y hy => ?_⟩
  have hat (b : β) : ContDiffAt ℝ 1 (f b) y := (hc b).contDiffAt (isOpen_ball.mem_nhds hy)
  exact (iteratedFDeriv_fun_sum_apply fun b _ => hat b).symm

/-- **The Hölder chain rule near a point.** Let `Φ` be `C²` on an open set `s` and map it into an
open set `t`, on which `g` is `C¹`. If the derivative of `g` is `α`-Hölder on `t ∩ B(Φ x, ρ)`,
`α ≤ 1`, then `g ∘ Φ` is `C^{1,α}` near `x ∈ s`. -/
private theorem isC1HolderNear_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E → F} {g : F → ℝ} {s : Set E} {t : Set F} (hα : α ≤ 1) (hs : IsOpen s) (ht : IsOpen t)
    (hΦ : ContDiffOn ℝ 2 Φ s) (hmaps : MapsTo Φ s t) (hg : ContDiffOn ℝ 1 g t) (hx : x ∈ s)
    {ρ : ℝ} (hρ : 0 < ρ) {C : ℝ≥0} (hgH : HolderOnWith C α (fderiv ℝ g) (t ∩ ball (Φ x) ρ)) :
    IsC1HolderNear α x (fun y => g (Φ y)) := by
  -- On the open set `t`, the derivative of `g` within `t` is its derivative.
  have hH : HolderOnWith C α (iteratedFDerivWithin ℝ 1 g t) (t ∩ ball (Φ x) ρ) :=
    (holderOnWith_iteratedFDeriv_one_iff.2 hgH).congr
      fun y hy => (iteratedFDerivWithin_of_isOpen 1 ht hy.1).symm
  obtain ⟨r, hr, K, hK⟩ := exists_holderOnWith_iteratedFDerivWithin_comp hα (hs.mem_nhds hx)
    ht.uniqueDiffOn (hΦ.of_le (by norm_num)) hg hmaps
    (inter_mem_nhdsWithin t (ball_mem_nhds _ hρ)) hH
  obtain ⟨r₀, hr₀, hr₀s⟩ := isOpen_iff.1 hs x hx
  have hsub : ball x (min r r₀) ⊆ s := (ball_subset_ball (min_le_right r r₀)).trans hr₀s
  refine .of_ball (lt_min hr hr₀) ((hg.comp (hΦ.of_le one_le_two) hmaps).mono hsub)
    ((hK.mono (ball_subset_ball (min_le_left r r₀))).congr fun y hy => ?_)
  exact iteratedFDerivWithin_of_isOpen 1 hs (hsub hy)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {U U' : Opens (EuclideanSpace ℝ ι)}
  {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L L' : ℝ}

/-- **Hölder derivatives of the transformed principal coefficient.** Let `Φ` and `Ψ` be mutually
inverse changes of variables of order one, with Jacobian determinants at least one in absolute
value, let `s ⊆ U'` be open and let `Φ` map `s` into an open set `t`. Suppose that `Φ` is `C²` on
`s`, that `Ψ` is `C²` on its domain and that the entries of `a` are `C¹` on `t`. Let `x ∈ s`, and
suppose that the second derivative of `Ψ` and the first derivatives of the entries of `a` are
`α`-Hölder, `α ≤ 1`, on a ball around `Φ x`, the latter with a common constant. Then the first
derivatives of the entries of the pulled-back principal coefficient are `α`-Hölder, with a common
constant, on a ball around `x`. -/
theorem exists_holderOnWith_fderiv_pullbackPrincipal_apply
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L' 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) (hα : α ≤ 1)
    {s t : Set (EuclideanSpace ℝ ι)} (hs : IsOpen s) (hsU : s ⊆ U') (ht : IsOpen t)
    (hmaps : MapsTo Φ s t) (hΦ2 : ContDiffOn ℝ 2 Φ s) (hΨ2 : ContDiffOn ℝ 2 Ψ U)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (ha : ∀ k l, ContDiffOn ℝ 1 (fun y => a y k l) t)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ s)
    (hΨH : ∃ ρ > 0, ∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ (fderiv ℝ Ψ)) (ball (Φ x) ρ))
    (haH : ∃ ρ > 0, ∃ K : ℝ≥0, ∀ k l,
      HolderOnWith K α (fderiv ℝ (fun z => a z k l)) (ball (Φ x) ρ)) :
    ∃ ρ > 0, ∃ K : ℝ≥0, ∀ i j,
      HolderOnWith K α (fderiv ℝ (fun y => pullbackPrincipal Φ a y i j)) (ball x ρ) := by
  -- The coordinate `(DΨ(·) eₖ)ₘ` is a continuous linear functional `ℓ` of `DΨ`.
  let ℓ (m k : ι) : (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) →L[ℝ] ℝ :=
    (EuclideanSpace.proj m).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ ι) (EuclideanSpace.single k 1))
  have hDΨ : ContDiffOn ℝ 1 (fderiv ℝ Ψ) U := hΨ2.fderiv_of_isOpen U.isOpen (by norm_num)
  -- The factors `(DΨ(Φ ·) eₖ)ₘ` are `C^{1,α}` near `x`.
  have hT (m k : ι) : IsC1HolderNear α x (fun y => ℓ m k (fderiv ℝ Ψ (Φ y))) := by
    obtain ⟨ρ, hρ, K, hK⟩ := hΨH
    have hU : IsOpen ((U : Set (EuclideanSpace ℝ ι)) ∩ ball (Φ x) ρ) := U.isOpen.inter isOpen_ball
    exact isC1HolderNear_comp (g := fun v => ℓ m k (fderiv ℝ Ψ v)) hα hs U.isOpen hΦ2
      (fun y hy => hΦ.mapsTo (hsU hy)) ((ℓ m k).contDiff.comp_contDiffOn hDΨ) hx hρ
      (holderOnWith_iteratedFDeriv_one_iff.1
        ((ℓ m k).holderOnWith_iteratedFDeriv_comp_left hU (hDΨ.mono inter_subset_left)
          (holderOnWith_iteratedFDeriv_one_iff.2 (hK.mono inter_subset_right))))
  -- The factors `aₖₗ ∘ Φ` are `C^{1,α}` near `x`.
  have hA (k l : ι) : IsC1HolderNear α x (fun y => a (Φ y) k l) := by
    obtain ⟨ρ, hρ, K, hK⟩ := haH
    exact isC1HolderNear_comp (g := fun v => a v k l) hα hs ht hΦ2 hmaps (ha k l) hx hρ
      ((hK k l).mono inter_subset_right)
  -- Near `x`, `a'ᵢⱼ = ∑ₖₗ (DΨ(Φ ·) eₖ)ᵢ aₖₗ(Φ ·) (DΨ(Φ ·) eₗ)ⱼ`, which is `C^{1,α}` near `x`.
  have hentry (i j : ι) : IsC1HolderNear α x (fun y => pullbackPrincipal Φ a y i j) := by
    refine (IsC1HolderNear.sum fun k => IsC1HolderNear.sum fun l =>
      ((hT i k).mul hα (hA k l)).mul hα (hT j l)).congr ?_
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [pullbackPrincipal_apply_apply_of_comp_eq_id a
      (hΦ.fderiv_comp_fderiv_eq_id hΨ hΨΦ hΦΨ (hsU hy)) i j,
      hΦ.abs_det_fderiv_eq_one hΨ hΨΦ hΦΨ (hsU hy), one_mul]
    simp [ℓ]
  -- A common ball for all entries, with the sum of their Hölder constants.
  obtain ⟨ρ, hρK, hρ⟩ :=
    ((eventually_all.2 fun i => eventually_all.2 (hentry i)).and self_mem_nhdsWithin).exists
  choose K hK using fun ij : ι × ι => (hρK ij.1 ij.2).2
  refine ⟨ρ, hρ, ∑ ij, K ij, fun i j => ?_⟩
  exact holderOnWith_iteratedFDeriv_one_iff.1 ((hK (i, j)).mono_const
    (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ _)))

end PDE

end TauCeti
