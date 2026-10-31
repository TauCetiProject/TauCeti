/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.BCH.Basic
public import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# The bracket term of the local Baker--Campbell--Hausdorff germ

For a finite-dimensional real Lie group `G` with Lie algebra `𝔤` of left-invariant derivations,
the local Baker--Campbell--Hausdorff germ `TauCeti.lieLocalBCH I G` is the germ at the origin of
`bch X Y = lieLog (lieExp X * lieExp Y)`. Its first-order law
`TauCeti.hasFDerivAt_lieLocalBCH_representative` says that `bch X Y = X + Y + o(‖(X, Y)‖)`. This
file proves the next term:

`bch X Y = X + Y + ½ ⁅X, Y⁆ + O(‖(X, Y)‖ ³)`,

so the local group law of `G` is determined to second order by the Lie bracket of `𝔤`. For the
units of a Banach algebra this is `NormedSpace.isBigO_log_exp_mul_exp_sub_firstOrder`, proved
from the exponential and logarithm series; for an abstract Lie group there is no series, and the
bracket enters through the adjoint representation instead.

## The proof

Write `f` for the representative of the germ and `S` for its second derivative at the origin, a
symmetric bilinear map on `𝔤 × 𝔤` since `f` is smooth. Along a curve `γ` through the origin the
second derivative of `f ∘ γ` at `0` is `S (γ' 0) (γ' 0) + f' (γ'' 0)`, with `f'` the first
derivative of `f` at the origin, which is addition. Four identities between curves pin down `S`:

* `bch (t • X) 0 = t • X` and `bch 0 (t • Y) = t • Y`, so `S` vanishes on each coordinate axis;
* `bch (t • X) (t • X) = t • (X + X)`, so the mixed part `β X Y = S (X, 0) (0, Y)` is alternating;
* conjugating `lieExp (t • Y)` by `lieExp (t • X)` gives `lieExp (t • Ad (lieExp (t • X)) Y)`, so
  `bch (t • X) (t • Y) = bch (t • Ad (lieExp (t • X)) Y) (t • X)`. By the adjoint-exponential
  formula `Ad (lieExp (t • X)) Y = exp (t • ad X) Y` (`LeftInvariantDerivation.Ad_lieExp_apply`),
  the second curve has velocity `(Y, X)` and acceleration `(2 ⁅X, Y⁆, 0)` at `0`, which gives
  `β X Y = β Y X + ⁅X, Y⁆`.

Hence `β X Y = ½ ⁅X, Y⁆` and `S p q = ½ (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆)`
(`TauCeti.fderiv_fderiv_lieLocalBCH_representative_apply`). The remainder estimate then follows
from Taylor's theorem in the form of two applications of the mean value inequality
(`isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero`): the remainder vanishes at the origin and
its derivative is `O(‖p‖ ²)`, because the derivative of that derivative is
`S' - S = O(‖p‖)`, with `S'` the second derivative of `f` at `p`.

## Main results

* `TauCeti.fderiv_fderiv_lieLocalBCH_representative_apply`: the second derivative of the local
  BCH germ at the origin is `(p, q) ↦ ½ (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆)`.
* `TauCeti.isBigO_lieLocalBCH_representative_sub_bracket`: **the bracket term**,
  `bch X Y = X + Y + ½ ⁅X, Y⁆ + O(‖(X, Y)‖ ³)`.
* `TauCeti.isBigO_sub_bracket_of_coe_eq_lieLocalBCH`: the same for an arbitrary representative
  of `TauCeti.lieLocalBCH I G`.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Chapter 3, where the commutator is introduced as the
  second-order term of the group law in exponential coordinates.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Chapter 5.
-/

public section

noncomputable section

open Asymptotics Filter
open scoped ContDiff Manifold Topology

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

namespace TauCeti

private local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

private local instance : CompleteSpace (LeftInvariantDerivation I G) :=
  FiniteDimensional.complete ℝ _

variable (I G) in
/-- The bounded bilinear map `(p, q) ↦ ½ (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆)` on pairs of left-invariant
derivations, the second derivative of the local BCH germ at the origin. -/
private def bchBracket :
    LeftInvariantDerivation I G × LeftInvariantDerivation I G →L[ℝ]
      LeftInvariantDerivation I G × LeftInvariantDerivation I G →L[ℝ]
        LeftInvariantDerivation I G :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun p q : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
          (2⁻¹ : ℝ) • (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆))
        (fun p p' q ↦ by simp only [Prod.fst_add, Prod.snd_add, add_lie, lie_add]; module)
        (fun c p q ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_lie, lie_smul]; module)
        (fun p q q' ↦ by simp only [Prod.fst_add, Prod.snd_add, add_lie, lie_add]; module)
        (fun c p q ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_lie, lie_smul]; module))

private theorem bchBracket_apply (p q : LeftInvariantDerivation I G × LeftInvariantDerivation I G) :
    bchBracket I G p q = (2⁻¹ : ℝ) • (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆) :=
  rfl

/-- The linear algebra closing the computation of the second derivative of the local BCH germ:
a symmetric bilinear map `S` on pairs of left-invariant derivations whose quadratic form vanishes
on both coordinate axes and on the diagonal, and satisfies
`S (X, Y) (X, Y) = S (Y, X) (Y, X) + 2 ⁅X, Y⁆`, is `(p, q) ↦ ½ (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆)`. -/
private theorem apply_eq_of_bch_identities
    (S : LeftInvariantDerivation I G × LeftInvariantDerivation I G →L[ℝ]
      LeftInvariantDerivation I G × LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G)
    (hsymm : ∀ v w, S v w = S w v) (hfst : ∀ X, S (X, 0) (X, 0) = 0)
    (hsnd : ∀ Y, S (0, Y) (0, Y) = 0) (hdiag : ∀ X, S (X, X) (X, X) = 0)
    (hAd : ∀ X Y, S (X, Y) (X, Y) = S (Y, X) (Y, X) + (⁅X, Y⁆ + ⁅X, Y⁆))
    (p q : LeftInvariantDerivation I G × LeftInvariantDerivation I G) :
    S p q = (2⁻¹ : ℝ) • (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆) := by
  let 𝔤 := LeftInvariantDerivation I G
  -- Polarization and the coordinate splitting of `S`.
  have hpol : ∀ a b, S (a + b) (a + b) = S a a + S b b + (S a b + S a b) := by
    intro a b
    simp only [map_add, add_apply]
    rw [hsymm b a]
    abel
  have htwo : ∀ a : 𝔤, a + a = 0 → a = 0 := fun a h ↦ by
    rw [← two_smul ℝ, smul_eq_zero] at h
    exact h.resolve_left two_ne_zero
  have hsplit : ∀ X Y : 𝔤, ((X, Y) : 𝔤 × 𝔤) = (X, 0) + (0, Y) := by simp
  have hfst' : ∀ X X' : 𝔤, S (X, 0) (X', 0) = 0 := fun X X' ↦ htwo _ <| by
    simpa [hfst] using (hpol (X, 0) (X', 0)).symm
  have hsnd' : ∀ Y Y' : 𝔤, S (0, Y) (0, Y') = 0 := fun Y Y' ↦ htwo _ <| by
    simpa [hsnd] using (hpol (0, Y) (0, Y')).symm
  -- The mixed part `β X Y = S (X, 0) (0, Y)` is half the bracket.
  have hβ : ∀ X Y : 𝔤, S (X, Y) (X, Y) = S (X, 0) (0, Y) + S (X, 0) (0, Y) := fun X Y ↦ by
    rw [hsplit, hpol, hfst, hsnd, zero_add, zero_add]
  have hanti : ∀ X Y : 𝔤, S (Y, 0) (0, X) = -S (X, 0) (0, Y) := by
    intro X Y
    have h := hdiag (X + Y)
    rw [hβ, show ((X + Y, 0) : 𝔤 × 𝔤) = (X, 0) + (Y, 0) by simp,
      show ((0, X + Y) : 𝔤 × 𝔤) = (0, X) + (0, Y) by simp] at h
    simp only [map_add, add_apply] at h
    have hX := htwo _ ((hβ X X).symm.trans (hdiag X))
    have hY := htwo _ ((hβ Y Y).symm.trans (hdiag Y))
    rw [hX, hY] at h
    exact eq_neg_of_add_eq_zero_left (htwo _ (by simpa only [zero_add, add_zero] using h))
  have hhalf : ∀ X Y : 𝔤, S (X, 0) (0, Y) = (2⁻¹ : ℝ) • ⁅X, Y⁆ := by
    intro X Y
    have e := hAd X Y
    rw [hβ, hβ, hanti X Y] at e
    linear_combination (norm := module) (4⁻¹ : ℝ) • e
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  rw [hsplit p₁ p₂, hsplit q₁ q₂]
  simp only [map_add, add_apply, hfst', hsnd', hhalf, hsymm (0, p₂) (q₁, 0), Prod.fst_add,
    Prod.snd_add, zero_add, add_zero, smul_add]
  abel

/-- **The second derivative of the local BCH germ.** At the origin, the second derivative of the
representative `(X, Y) ↦ lieLog (lieExp X * lieExp Y)` of `TauCeti.lieLocalBCH I G` is the
symmetric bilinear map `(p, q) ↦ ½ (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆)`. -/
theorem fderiv_fderiv_lieLocalBCH_representative_apply
    (p q : LeftInvariantDerivation I G × LeftInvariantDerivation I G) :
    fderiv ℝ (fderiv ℝ fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2)) (0, 0) p q =
      (2⁻¹ : ℝ) • (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆) := by
  let 𝔤 := LeftInvariantDerivation I G
  let f : 𝔤 × 𝔤 → 𝔤 := fun p ↦ lieLog (I := I) (lieExp p.1 * lieExp p.2)
  -- `S` abbreviates the second derivative at the origin; `change` names it in the goal.
  let S := fderiv ℝ (fderiv ℝ f) 0
  change S p q = _
  have hf : ContDiffAt ℝ 3 f (0, 0) :=
    contDiffAt_lieLocalBCH_representative.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdiff : ∀ᶠ p in 𝓝 ((0, 0) : 𝔤 × 𝔤), DifferentiableAt ℝ f p :=
    (hf.eventually (by simp)).mono fun p hp ↦ hp.differentiableAt (by norm_num)
  have hdiff' : DifferentiableAt ℝ (fderiv ℝ f) (0, 0) :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : ∀ v w, S v w = S w v :=
    (hf.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField])).eq
  have hDf : fderiv ℝ f 0 =
      ContinuousLinearMap.fst ℝ 𝔤 𝔤 + ContinuousLinearMap.snd ℝ 𝔤 𝔤 :=
    hasFDerivAt_lieLocalBCH_representative.fderiv
  -- The second derivative of `f` along a curve through the origin.
  have key : ∀ {γ γ' : ℝ → 𝔤 × 𝔤} {w : 𝔤 × 𝔤}, γ 0 = 0 →
      (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt γ (γ' t) t) → HasDerivAt γ' w 0 →
      HasDerivAt (deriv (f ∘ γ)) (S (γ' 0) (γ' 0) + (w.1 + w.2)) 0 := by
    intro γ γ' w h0 hγ hγ'
    have hγ0 : HasDerivAt γ (γ' 0) 0 := hγ.self_of_nhds
    have hcont : Tendsto γ (𝓝 0) (𝓝 0) := h0 ▸ hγ0.continuousAt.tendsto
    -- Near `0`, the derivative of `f ∘ γ` is `t ↦ f' (γ t) (γ' t)`, by the chain rule.
    have heq : deriv (f ∘ γ) =ᶠ[𝓝 0] fun t ↦ fderiv ℝ f (γ t) (γ' t) := by
      filter_upwards [hγ, hcont.eventually hdiff] with t ht hft
      exact (hft.hasFDerivAt.comp_hasDerivAt t ht).deriv
    have h := (hdiff'.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ0 h0.symm).clm_apply hγ'
    rw [Function.comp_apply, h0, hDf] at h
    exact h.congr_of_eventuallyEq heq
  -- A curve along which `f` is linear has zero second derivative.
  have hlin : ∀ {γ γ' : ℝ → 𝔤 × 𝔤} {w : 𝔤 × 𝔤} (Z : 𝔤), γ 0 = 0 →
      (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt γ (γ' t) t) → HasDerivAt γ' w 0 →
      f ∘ γ =ᶠ[𝓝 0] (fun t ↦ t • Z) → S (γ' 0) (γ' 0) + (w.1 + w.2) = 0 := by
    intro γ γ' w Z h0 hγ hγ' hfγ
    refine (key h0 hγ hγ').unique ((hasDerivAt_const (0 : ℝ) Z).congr_of_eventuallyEq ?_)
    filter_upwards [hfγ.deriv] with t ht
    rw [ht]
    simpa using ((hasDerivAt_id t).smul_const Z).deriv
  -- On a line through the origin, `f` is eventually the identity after `lieExp`.
  have hline : ∀ Z : 𝔤, ∀ᶠ t in 𝓝 (0 : ℝ), lieLog (I := I) (lieExp (t • Z)) = t • Z := by
    intro Z
    have ht : Tendsto (fun t : ℝ ↦ t • Z) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const Z
    exact ht.eventually (eventually_lieLog_lieExp (I := I) (G := G))
  have hsmul : ∀ (v : 𝔤 × 𝔤) (t : ℝ), HasDerivAt (fun t : ℝ ↦ t • v) v t := fun v t ↦ by
    simpa using (hasDerivAt_id t).smul_const v
  -- The quadratic form of `S` vanishes on both coordinate axes and on the diagonal.
  have hfst : ∀ X : 𝔤, S (X, 0) (X, 0) = 0 := by
    intro X
    have := hlin (γ := fun t ↦ t • ((X, 0) : 𝔤 × 𝔤)) (γ' := fun _ ↦ (X, 0)) (w := 0) X
      (by simp) (.of_forall (hsmul _)) (hasDerivAt_const _ _)
      (by filter_upwards [hline X] with t ht; simpa [f] using ht)
    simpa using this
  have hsnd : ∀ Y : 𝔤, S (0, Y) (0, Y) = 0 := by
    intro Y
    have := hlin (γ := fun t ↦ t • ((0, Y) : 𝔤 × 𝔤)) (γ' := fun _ ↦ (0, Y)) (w := 0) Y
      (by simp) (.of_forall (hsmul _)) (hasDerivAt_const _ _)
      (by filter_upwards [hline Y] with t ht; simpa [f] using ht)
    simpa using this
  have hdiag : ∀ X : 𝔤, S (X, X) (X, X) = 0 := by
    intro X
    have := hlin (γ := fun t ↦ t • ((X, X) : 𝔤 × 𝔤)) (γ' := fun _ ↦ (X, X)) (w := 0) (X + X)
      (by simp) (.of_forall (hsmul _)) (hasDerivAt_const _ _)
      (by
        filter_upwards [hline (X + X)] with t ht
        have h2 : lieExp (I := I) (t • X) * lieExp (t • X) = lieExp (t • (X + X)) := by
          rw [smul_add, ← add_smul, lieExp_add_smul]
        simp only [f, Function.comp_apply, Prod.smul_mk, h2]
        exact ht)
    simpa using this
  -- Conjugation by `lieExp (t • X)` moves the second factor across the first.
  have hAd : ∀ X Y : 𝔤, S (X, Y) (X, Y) = S (Y, X) (Y, X) + (⁅X, Y⁆ + ⁅X, Y⁆) := by
    intro X Y
    let A : 𝔤 →L[ℝ] 𝔤 := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ 𝔤 X)
    let B : ℝ → 𝔤 → 𝔤 := fun t Z ↦ NormedSpace.exp (t • A) Z
    have hB : ∀ Z t, HasDerivAt (fun t ↦ B t Z) (B t (A Z)) t := by
      intro Z t
      simpa [B] using (hasDerivAt_exp_smul_const A t).clm_apply (hasDerivAt_const t Z)
    have hB0 : ∀ Z, B 0 Z = Z := by simp [B]
    have hconj : ∀ t : ℝ, lieExp (I := I) (t • X) * lieExp (t • Y) =
        lieExp (t • B t Y) * lieExp (t • X) := by
      intro t
      have h := Lie.conj_lieExp (I := I) (lieExp (t • X)) (t • Y)
      rw [map_smul, LeftInvariantDerivation.Ad_lieExp_apply, map_smul, map_smul] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    have hγ : f ∘ (fun t : ℝ ↦ t • ((X, Y) : 𝔤 × 𝔤)) = f ∘ fun t ↦ (t • B t Y, t • X) := by
      funext t
      simp [f, hconj]
    have h₁ := key (γ := fun t ↦ t • ((X, Y) : 𝔤 × 𝔤)) (γ' := fun _ ↦ (X, Y)) (w := 0)
      (by simp) (.of_forall (hsmul _)) (hasDerivAt_const _ _)
    have h₂ := key (γ := fun t ↦ (t • B t Y, t • X)) (γ' := fun t ↦ (t • B t (A Y) + B t Y, X))
      (w := (A Y + A Y, 0)) (by simp)
      (.of_forall fun t ↦ by
        simpa using ((hasDerivAt_id t).smul (hB Y t)).prodMk ((hasDerivAt_id t).smul_const X))
      (by
        simpa [hB0] using
          (((hasDerivAt_id (0 : ℝ)).smul (hB (A Y) 0)).add (hB Y 0)).prodMk
            (hasDerivAt_const (0 : ℝ) X))
    rw [hγ] at h₁
    simpa [hB0, A] using h₁.unique h₂
  exact apply_eq_of_bch_identities S hsymm hfst hsnd hdiag hAd p q

/-- **The bracket term of the local Baker--Campbell--Hausdorff germ.** Near the origin,
`bch X Y = X + Y + ½ ⁅X, Y⁆ + O(‖(X, Y)‖ ³)`: to second order, the local group law of `G` read
in the exponential chart is determined by the Lie bracket of `𝔤`. -/
theorem isBigO_lieLocalBCH_representative_sub_bracket :
    (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2) - (p.1 + p.2 + (2⁻¹ : ℝ) • ⁅p.1, p.2⁆))
      =O[𝓝 (0, 0)] fun p ↦ ‖p‖ ^ 3 := by
  let 𝔤 := LeftInvariantDerivation I G
  let f : 𝔤 × 𝔤 → 𝔤 := fun p ↦ lieLog (I := I) (lieExp p.1 * lieExp p.2)
  let L : 𝔤 × 𝔤 →L[ℝ] 𝔤 := ContinuousLinearMap.fst ℝ 𝔤 𝔤 + ContinuousLinearMap.snd ℝ 𝔤 𝔤
  let B := bchBracket I G
  have hf : ContDiffAt ℝ 3 f 0 :=
    contDiffAt_lieLocalBCH_representative.of_le (WithTop.coe_le_coe.mpr le_top)
  have hev : ∀ᶠ p in 𝓝 (0 : 𝔤 × 𝔤), ContDiffAt ℝ 3 f p := hf.eventually (by simp)
  have hDf : fderiv ℝ f 0 = L := hasFDerivAt_lieLocalBCH_representative.fderiv
  have hS : fderiv ℝ (fderiv ℝ f) 0 = B :=
    ContinuousLinearMap.ext fun p ↦ ContinuousLinearMap.ext fun q ↦
      (fderiv_fderiv_lieLocalBCH_representative_apply p q).trans (bchBracket_apply p q).symm
  have hdf : ∀ {p}, ContDiffAt ℝ 3 f p → DifferentiableAt ℝ (fderiv ℝ f) p := fun hp ↦
    (hp.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  -- The derivative of the remainder, `f' - L - B`, is `O(‖p‖ ²)`.
  let h : 𝔤 × 𝔤 → 𝔤 × 𝔤 →L[ℝ] 𝔤 := fun p ↦ fderiv ℝ f p - L - B p
  have hh : h =O[𝓝 0] fun p ↦ ‖p - 0‖ ^ ((1 : ℝ) + 1) := by
    refine isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero zero_le_one ?_ ?_ ?_
    · filter_upwards [hev] with p hp
      exact ((hdf hp).sub_const L).sub B.differentiableAt
    · have hfd : ∀ᶠ p in 𝓝 (0 : 𝔤 × 𝔤), fderiv ℝ h p = fderiv ℝ (fderiv ℝ f) p - B := by
        filter_upwards [hev] with p hp
        exact (((hdf hp).hasFDerivAt.sub_const L).sub B.hasFDerivAt).fderiv
      have h2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) 0 :=
        ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
          (by norm_num)).differentiableAt (by norm_num)
      refine (h2.isBigO_sub.congr' ?_ EventuallyEq.rfl).trans ?_
      · filter_upwards [hfd] with p hp
        rw [hp, hS]
      · simpa using (isBigO_refl (fun p : 𝔤 × 𝔤 ↦ p) (𝓝 0)).norm_right
    · simp [h, hDf]
  -- The remainder vanishes at the origin and has derivative `h`.
  let g : 𝔤 × 𝔤 → 𝔤 := fun p ↦ f p - (p.1 + p.2 + (2⁻¹ : ℝ) • ⁅p.1, p.2⁆)
  have hg' : ∀ {p}, ContDiffAt ℝ 3 f p → HasFDerivAt g (h p) p := by
    intro p hp
    have hbr : HasFDerivAt (fun p : 𝔤 × 𝔤 ↦ (2⁻¹ : ℝ) • B p p) (B p) p := by
      refine ((B.hasFDerivAt_of_bilinear (hasFDerivAt_id p) (hasFDerivAt_id p)).const_smul
        (2⁻¹ : ℝ)).congr_fderiv (ContinuousLinearMap.ext fun q ↦ ?_)
      simp only [smul_apply, add_apply, ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_apply, id]
      rw [show B q p = B p q by simp only [B, bchBracket_apply]; module]
      module
    refine (((hp.differentiableAt (by norm_num)).hasFDerivAt.sub
      (L.hasFDerivAt.add hbr)).congr_of_eventuallyEq (.of_forall fun q ↦ ?_)).congr_fderiv
        (by simp only [h]; abel)
    simp only [g, B, L, bchBracket_apply, Pi.sub_apply, Pi.add_apply,
      FunLike.coe_add, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    module
  have hg : g =O[𝓝 0] fun p ↦ ‖p - 0‖ ^ ((1 : ℝ) + 1 + 1) := by
    refine isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (by norm_num) ?_ ?_ ?_
    · filter_upwards [hev] with p hp
      exact (hg' hp).differentiableAt
    · refine hh.congr' ?_ EventuallyEq.rfl
      filter_upwards [hev] with p hp
      exact (hg' hp).fderiv.symm
    · simp [g, f]
  refine hg.congr' EventuallyEq.rfl (.of_forall fun p ↦ ?_)
  norm_num

/-- **The bracket term for an arbitrary representative** of the local Baker--Campbell--Hausdorff
germ: `f X Y = X + Y + ½ ⁅X, Y⁆ + O(‖(X, Y)‖ ³)`. -/
theorem isBigO_sub_bracket_of_coe_eq_lieLocalBCH
    (f : LeftInvariantDerivation I G × LeftInvariantDerivation I G → LeftInvariantDerivation I G)
    (hf : (↑f : Germ (𝓝 ((0, 0) : LeftInvariantDerivation I G × LeftInvariantDerivation I G))
      (LeftInvariantDerivation I G)) = lieLocalBCH I G) :
    (fun p ↦ f p - (p.1 + p.2 + (2⁻¹ : ℝ) • ⁅p.1, p.2⁆)) =O[𝓝 (0, 0)] fun p ↦ ‖p‖ ^ 3 := by
  rw [lieLocalBCH_def, Germ.coe_eq] at hf
  exact isBigO_lieLocalBCH_representative_sub_bracket.congr' (hf.symm.sub EventuallyEq.rfl)
    EventuallyEq.rfl

end TauCeti
