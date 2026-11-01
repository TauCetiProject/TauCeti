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
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.SecondOrderExpansion
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

The second derivative of the germ at the origin is computed from four identities between curves
through the origin, the last of which comes from conjugation and the adjoint-exponential formula
`LeftInvariantDerivation.Ad_lieExp_apply`; the remainder estimate is then the second-order Taylor
expansion `ContDiffAt.isBigO_sub_taylor_two`.

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

/-- Conjugation by `lieExp (t • X)` moves `lieExp (t • Y)` across `lieExp (t • X)`, which relates
the quadratic form of the second derivative of the local BCH germ at `(X, Y)` and at `(Y, X)`:
`S (X, Y) (X, Y) = S (Y, X) (Y, X) + 2 ⁅X, Y⁆`. -/
private theorem fderiv_fderiv_lieLocalBCH_representative_apply_swap
    (X Y : LeftInvariantDerivation I G) :
    fderiv ℝ (fderiv ℝ fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2)) (0, 0) (X, Y) (X, Y) =
      fderiv ℝ (fderiv ℝ fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2)) (0, 0) (Y, X) (Y, X) + (⁅X, Y⁆ + ⁅X, Y⁆) := by
  -- Conjugating gives `bch (t • X) (t • Y) = bch (t • B t Y) (t • X)` with
  -- `B t = exp (t • ad X)`, by the adjoint-exponential formula. The curve
  -- `γ t = (t • B t Y, t • X)` has velocity `(Y, X)` and acceleration `(2 ⁅X, Y⁆, 0)` at `0`, and
  -- `iteratedDeriv_two_comp` compares the second derivatives of the two sides at `0`.
  let 𝔤 := LeftInvariantDerivation I G
  let f : 𝔤 × 𝔤 → 𝔤 := fun p ↦ lieLog (I := I) (lieExp p.1 * lieExp p.2)
  have hf : ContDiffAt ℝ 2 f (0, 0) :=
    contDiffAt_lieLocalBCH_representative.of_le (WithTop.coe_le_coe.mpr le_top)
  have hDf : fderiv ℝ f (0, 0) =
      ContinuousLinearMap.fst ℝ 𝔤 𝔤 + ContinuousLinearMap.snd ℝ 𝔤 𝔤 :=
    hasFDerivAt_lieLocalBCH_representative.fderiv
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
  let ρ : ℝ → 𝔤 × 𝔤 := fun t ↦ (0, 0) + t • (X, Y)
  let γ : ℝ → 𝔤 × 𝔤 := fun t ↦ (t • B t Y, t • X)
  have hργ : f ∘ ρ = f ∘ γ := by
    funext t
    simp [f, ρ, γ, hconj]
  have hρ0 : ρ 0 = (0, 0) := by simp [ρ]
  have hγ0 : γ 0 = (0, 0) := by simp [γ]
  have hρ' : deriv ρ 0 = (X, Y) := congrFun (deriv_const_add_smul _ _) 0
  have hρ'' : iteratedDeriv 2 ρ 0 = 0 := congrFun (iteratedDeriv_two_const_add_smul _ _) 0
  have hγ' : deriv γ = fun t ↦ (t • B t (A Y) + B t Y, X) := funext fun t ↦ by
    simpa using (((hasDerivAt_id t).smul (hB Y t)).prodMk ((hasDerivAt_id t).smul_const X)).deriv
  have hγ'' : iteratedDeriv 2 γ 0 = (A Y + A Y, 0) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hγ']
    simpa [hB0] using
      ((((hasDerivAt_id (0 : ℝ)).smul (hB (A Y) 0)).add (hB Y 0)).prodMk
        (hasDerivAt_const (0 : ℝ) X)).deriv
  have hγc : ContDiffAt ℝ 2 γ 0 :=
    (contDiffAt_id.smul (((NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt.comp 0
      (contDiffAt_id.smul_const A)).clm_apply contDiffAt_const)).prodMk
        (contDiffAt_id.smul contDiffAt_const)
  have h := iteratedDeriv_two_comp (f := f) (γ := ρ) (t := 0) (by rwa [hρ0])
    (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  rw [hργ, iteratedDeriv_two_comp (by rwa [hγ0]) hγc, hρ0, hγ0, hρ', hρ'', hγ', hγ'', hDf] at h
  simpa [hB0, A] using h.symm

/-- **The second derivative of the local BCH germ.** At the origin, the second derivative of the
representative `(X, Y) ↦ lieLog (lieExp X * lieExp Y)` of `TauCeti.lieLocalBCH I G` is the
symmetric bilinear map `(p, q) ↦ ½ (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆)`. -/
theorem fderiv_fderiv_lieLocalBCH_representative_apply
    (p q : LeftInvariantDerivation I G × LeftInvariantDerivation I G) :
    fderiv ℝ (fderiv ℝ fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2)) (0, 0) p q =
      (2⁻¹ : ℝ) • (⁅p.1, q.2⁆ + ⁅q.1, p.2⁆) := by
  -- Write `f` for the representative and `S` for its second derivative at the origin. Since
  -- `bch (t • X) 0 = t • X`, `bch 0 (t • Y) = t • Y` and `bch (t • X) (t • X) = t • (X + X)`,
  -- `f` is linear along both coordinate axes and the diagonal, so these are isotropic for `S`.
  -- Together with `fderiv_fderiv_lieLocalBCH_representative_apply_swap`, the linear algebra in
  -- `apply_eq_of_bch_identities` determines `S`.
  let 𝔤 := LeftInvariantDerivation I G
  let f : 𝔤 × 𝔤 → 𝔤 := fun p ↦ lieLog (I := I) (lieExp p.1 * lieExp p.2)
  have hf : ContDiffAt ℝ 2 f (0, 0) :=
    contDiffAt_lieLocalBCH_representative.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ f) (0, 0) v w = fderiv ℝ (fderiv ℝ f) (0, 0) w v :=
    (hf.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField])).eq
  -- On a line through the origin, `lieLog` inverts `lieExp`.
  have hline : ∀ Z : 𝔤, ∀ᶠ t in 𝓝 (0 : ℝ), lieLog (I := I) (lieExp (t • Z)) = t • Z := by
    intro Z
    have ht : Tendsto (fun t : ℝ ↦ t • Z) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const Z
    exact ht.eventually (eventually_lieLog_lieExp (I := I) (G := G))
  have hray : ∀ (v : 𝔤 × 𝔤) (Z : 𝔤), (∀ᶠ t in 𝓝 (0 : ℝ), f (t • v) = t • Z) →
      fderiv ℝ (fderiv ℝ f) (0, 0) v v = 0 := fun v Z hv ↦
    fderiv_fderiv_apply_self_eq_zero_of_eventually_eq_add_smul (z := Z) hf (by
      filter_upwards [hv] with t ht
      simpa [f] using ht)
  have hfst : ∀ X : 𝔤, fderiv ℝ (fderiv ℝ f) (0, 0) (X, 0) (X, 0) = 0 := fun X ↦
    hray _ X (by filter_upwards [hline X] with t ht; simpa [f] using ht)
  have hsnd : ∀ Y : 𝔤, fderiv ℝ (fderiv ℝ f) (0, 0) (0, Y) (0, Y) = 0 := fun Y ↦
    hray _ Y (by filter_upwards [hline Y] with t ht; simpa [f] using ht)
  have hdiag : ∀ X : 𝔤, fderiv ℝ (fderiv ℝ f) (0, 0) (X, X) (X, X) = 0 := fun X ↦
    hray _ (X + X) (by
      filter_upwards [hline (X + X)] with t ht
      have h2 : lieExp (I := I) (t • X) * lieExp (t • X) = lieExp (t • (X + X)) := by
        rw [smul_add, ← add_smul, lieExp_add_smul]
      simp only [f, Prod.smul_mk, h2]
      exact ht)
  exact apply_eq_of_bch_identities _ hsymm hfst hsnd hdiag
    fderiv_fderiv_lieLocalBCH_representative_apply_swap p q

/-- **The bracket term of the local Baker--Campbell--Hausdorff germ.** Near the origin,
`bch X Y = X + Y + ½ ⁅X, Y⁆ + O(‖(X, Y)‖ ³)`: to second order, the local group law of `G` read
in the exponential chart is determined by the Lie bracket of `𝔤`. -/
theorem isBigO_lieLocalBCH_representative_sub_bracket :
    (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2) - (p.1 + p.2 + (2⁻¹ : ℝ) • ⁅p.1, p.2⁆))
      =O[𝓝 (0, 0)] fun p ↦ ‖p‖ ^ 3 := by
  refine ((contDiffAt_lieLocalBCH_representative (I := I) (G := G)).of_le
    (WithTop.coe_le_coe.mpr le_top)).isBigO_sub_taylor_two.congr' (.of_forall fun p ↦ ?_)
      (.of_forall fun p ↦ by simp only [Prod.mk_zero_zero, sub_zero])
  dsimp only
  rw [hasFDerivAt_lieLocalBCH_representative.fderiv, fderiv_fderiv_lieLocalBCH_representative_apply]
  simp only [lieExp_zero, mul_one, lieLog_one, sub_zero, add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub]
  module

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
