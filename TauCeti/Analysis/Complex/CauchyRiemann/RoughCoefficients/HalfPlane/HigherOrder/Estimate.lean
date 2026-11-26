/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.HigherOrder.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.CauchyRiemann.NormalDerivative
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Estimate
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Bound
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Higher
import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Data.ENNReal.Mul
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic
import TauCeti.Topology.Sets.Opens

/-!
# Estimates of every order up to the real axis for rough Cauchy–Riemann equations

Let `Ω ⊆ ℂ` be an open set invariant under complex conjugation, write `z = s + i t` and
`Ω⁺ = Ω ∩ {0 ≤ t}`, and let `V` be a finite-dimensional real inner product space with an isometric
involution `R` whose fixed vectors lie in the boundary subspace `Λ` (for `V = ℂⁿ` with real
boundary values, coordinatewise conjugation and `Λ = ℝⁿ`). For a weak solution `ξ` up to the real
axis of

`∂_s ξ + J ∂_t ξ + S ξ = η`

with boundary subspace `Λ`, in the sense of `TauCeti.IsWeakCRSolutionHalf`, with `J² = -1`,
`p > 2`, `1/p + 1/q < 1` and `q ≤ p`, this file proves the estimate of every order `k` up to the
boundary: for `U` with compact closure in `Ω`, and `U⁺ = U ∩ {0 ≤ t}`,

`‖ξ‖_{W^{k+1,q}(U⁺)} ≤ C (‖η‖_{W^{k,q}(Ω⁺)} + ‖ξ‖_{L^q(Ω⁺)})`,

with one constant `C` for all coefficients `J`, `S` whose `W^{k,p}(Ω⁺)` norms, and the `W^{1,p}`
norm of `J` (or of its reflection), are at most a given bound `M`. This is McDuff–Salamon,
Proposition B.4.9, with a totally real boundary condition and a zeroth-order term, together with
the uniformity in the coefficients that compactness for sequences of solutions needs. At `k = 0` it
is the case `r = q` of `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_le`, and the
estimate accompanies the qualitative regularity `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_succ`.

## The argument

The estimate is proved for the twisted reflection of `ξ` solving the reflected equation on `Ω`,
by induction on `k`, following the qualitative induction
`TauCeti.IsWeakCRSolution.memWkpLoc_succ_of_crReflection`. For the step from `k` to `k + 1`, take
nested open sets `U ⋐ W₂ ⋐ W₁ ⋐ W ⋐ W' ⋐ Ω`, all but `W₂` invariant under conjugation
(`TauCeti.exists_mapsTo_conj_between_and_isCompact_closure`).

* The estimate of order `k` bounds `ξ` in `W^{k+1,q}(W'⁺)`.
* *Tangential derivative.* The reflection of `∂_s ξ` solves the reflected equation with zeroth-order
  coefficient `S + (∂_s J) J` and right side `∂_s η - (∂_s J) J (S ξ - η) - (∂_s S) ξ`
  (`TauCeti.IsWeakCRSolution.crReflection_partial_one`). The half-disc product bounds
  (`TauCeti.exists_eLpNormWkp_bilin_le_mul_eLpNormWkp_succ_halfPlane`) bound these data on `W₁⁺`,
  so the estimate of order `k` on `W₁` bounds `∂_s ξ` in `W^{k+1,q}(W₂⁺)`.
* *Normal derivative.* The equation gives `∂_t ξ = J (∂_s ξ + S ξ - η)`, which the product bound
  `TauCeti.exists_eLpNormWkp_succ_clm_apply_le_halfPlane` controls in `W^{k+1,q}(U⁺)`.

The two partial derivatives bound `ξ` in `W^{k+2,q}(U⁺)`
(`TauCeti.eLpNormWkp_succ_le_eLpNorm_add_apply_one_add_apply_I`). The order-zero case is the
interior estimate on `Ω` for the reflected equation, read back on `Ω⁺`
(`TauCeti.eLpNormWkp_inter_le_of_twistedReflection`).

## Main results

* `TauCeti.exists_eLpNormWkp_succ_le_of_isWeakCRSolutionHalf`: the estimate of every order up to
  the real axis, uniform over coefficients whose reflections are Sobolev coefficients with bounded
  norms.
* `TauCeti.exists_eLpNormWkp_succ_le_of_isWeakCRSolutionHalf_of_hasWeakFDerivOn`: the same with
  hypotheses on the half-plane coefficients: `J` continuous up to the axis with weak derivative
  `DJ`, anticommuting with `R` on the axis, and `‖J‖_{W^{max k 1, p}(Ω⁺)} ≤ M`,
  `‖S‖_{W^{k,p}(Ω⁺)} ≤ M`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemma B.4.6 and Proposition B.4.9.
-/

public section

open MeasureTheory TopologicalSpace Complex Set ContinuousLinearMap
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {R : V ≃ₗᵢ[ℝ] V}

variable (V) in
/-- The estimate of order `k` up to the real axis with constant `C`, for reflected solutions:
whenever the twisted reflection of `ξ` solves the reflected equation on `Ω`, the reflected
coefficients are Sobolev coefficients on `Ω`, `J² = -1` on `Ω⁺`, the reflection of `J` has
`W^{1,p}(Ω)` norm at most `M`, `J` and `S` have `W^{k,p}(Ω⁺)` norms at most `M`, and
`η ∈ W^{k,q}_loc(Ω⁺)`, then `‖ξ‖_{W^{k+1,q}(U⁺)} ≤ C (‖η‖_{W^{k,q}(Ω⁺)} + ‖ξ‖_{L^q(Ω⁺)})`. -/
private def CRReflectedBound (R : V ≃ₗᵢ[ℝ] V) (p q : ℝ≥0∞) (k : ℕ) (M : ℝ≥0) (Ω : Opens ℂ)
    (U : Set ℂ) (C : ℝ≥0) : Prop :=
  ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
    IsWeakCRSolution q Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S)
      (twistedReflection (R : V →L[ℝ] V) ξ) (twistedReflection (R : V →L[ℝ] V) η) →
    IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S) →
    (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) →
    eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤ M →
    eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k J ≤ M →
    eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k S ≤ M →
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η →
    eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) (k + 1) ξ ≤
      C * (eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η +
        eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})))

variable (V) in
/-- The uniform estimate of order `k` up to the real axis, for reflected solutions: some constant
satisfies `CRReflectedBound`. -/
private def CRReflectedEstimate (R : V ≃ₗᵢ[ℝ] V) (p q : ℝ≥0∞) (k : ℕ) (M : ℝ≥0) (Ω : Opens ℂ)
    (U : Set ℂ) : Prop :=
  ∃ C : ℝ≥0, CRReflectedBound V R p q k M Ω U C

/-- The estimate of order `0` for reflected solutions: the interior estimate on `Ω` for the
reflected equation, read back on `Ω⁺`. -/
private theorem crReflectedEstimate_zero [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {U : Set ℂ} (hUc : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) : CRReflectedEstimate V R p q 0 M Ω U := by
  have hq1 : (1 : ℝ≥0∞) < q := ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)
  have hp1 : (1 : ℝ≥0∞) ≤ p := hq1.le.trans (by exact_mod_cast hqp)
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le (V := V)
    (by exact_mod_cast hp) hpq hq1 ENNReal.coe_ne_top (by exact_mod_cast hqp) hUc hUΩ (2 * M)
  refine ⟨2 * C, fun J S DJ ξ η h hc hJ2 hJ1 _ hS hη => ?_⟩
  rw [eLpNormWkp_zero] at hS ⊢
  refine eLpNormWkp_inter_le_of_twistedReflection (R := R) hΩ hq1.le hq1.le
    (hC _ _ _ _ _ h hc (ae_crReflectionCoeff_mul_self hΩ hJ2) (hJ1.trans ?_)
      ((eLpNorm_crReflectionZeroth_le hΩ hp1 S).trans ?_)
      ((memWkpLoc_zero_iff.1 hη).twistedReflection hΩ _))
  · push_cast
    exact le_mul_of_one_le_left' one_le_two
  · push_cast
    gcongr

omit [CompleteSpace V] in
/-- The bound for the right side `∂_s η - M (S ξ - η) - (∂_s S) ξ` of the tangential step in
`W^{k,q}(W₁)`, from bounds for its factors on a larger set `W` through the product bound `hCp`. -/
private theorem eLpNormWkp_tangential_rhs_le {p q : ℝ≥0∞} (hq1 : 1 ≤ q) {k : ℕ} {W₁ W : Set ℂ}
    {S Mf : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    {Cp cM cσ M Ca : ℝ≥0} {A : ℝ≥0∞}
    (hCp : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V), eLpNormWkp q W₁ k (fun z => B z (u z)) ≤
      Cp * eLpNormWkp p W k B * eLpNormWkp q W (k + 1) u)
    (hDη : eLpNormWkp q W₁ k (fun z => Dη z 1) ≤ ↑(1 : ℝ≥0) * A)
    (hMf : eLpNormWkp p W k Mf ≤ cM)
    (hSξη : eLpNormWkp q W (k + 1) (fun z => S z (ξ z) - η z) ≤ ↑cσ * A)
    (hDS : eLpNormWkp p W k (fun z => DS z 1) ≤ M) (hX : eLpNormWkp q W (k + 1) ξ ≤ ↑Ca * A) :
    eLpNormWkp q W₁ k (fun z => Dη z 1 - Mf z (S z (ξ z) - η z) - DS z 1 (ξ z)) ≤
      ↑(1 + Cp * cM * cσ + Cp * M * Ca) * A := by
  refine (eLpNormWkp_sub_le (f := fun z => Dη z 1 - Mf z (S z (ξ z) - η z))
    (g := fun z => DS z 1 (ξ z)) hq1).trans (ENNReal.add_le_coe_mul ((eLpNormWkp_sub_le
      (f := fun z => Dη z 1) (g := fun z => Mf z (S z (ξ z) - η z)) hq1).trans
        (ENNReal.add_le_coe_mul hDη ?_)) ?_)
  · exact ENNReal.le_coe_mul_of_le_mul_mul (hCp Mf fun z => S z (ξ z) - η z) hMf hSξη
  · exact ENNReal.le_coe_mul_of_le_mul_mul (hCp (fun z => DS z 1) ξ) hDS hX

/-- **The tangential step, qualitatively.** Let the twisted reflection of `ξ` solve the reflected
equation on the conjugation-invariant `Ω`, with reflected Sobolev coefficients, `J² = -1` on
`Ω⁺`, `p > 2`, `1/p + 1/q < 1` and `q ≤ p`, and let `J, S ∈ W^{k+1,p}_loc(Ω⁺)` and
`ξ, η ∈ W^{k+1,q}_loc(Ω⁺)`, with weak derivatives `Dξ`, `DS`, `Dη` on the open upper part. Then
the reflection of `∂_s ξ` solves the reflected equation with zeroth-order coefficient
`S + (∂_s J) J`, whose reflection is again a Sobolev coefficient, and right side
`∂_s η - (∂_s J) J (S ξ - η) - (∂_s S) ξ ∈ W^{k,q}_loc(Ω⁺)`; and the normal derivative is
`∂_t ξ = J (∂_s ξ + S ξ - η)` almost everywhere on `Ω⁺`. -/
private theorem crReflection_tangential_step [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) {k : ℕ} {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V}
    (h : IsWeakCRSolution q Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S)
      (twistedReflection (R : V →L[ℝ] V) ξ) (twistedReflection (R : V →L[ℝ] V) η))
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S))
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hJk : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) J)
    (hSk : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) S)
    (hξ : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ)
    (hη : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) η)
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hDξ : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ξ Dξ)
    (hDξk : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k Dξ)
    (hDS : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) S DS)
    (hDSk : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k DS)
    (hDη : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) η Dη)
    (hDηk : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k Dη) :
    IsWeakCRSolution q Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv fun z => S z + (DJ z 1).comp (J z))
        (twistedReflection (R : V →L[ℝ] V) fun z => Dξ z 1)
        (twistedReflection (R : V →L[ℝ] V)
          fun z => Dη z 1 - DJ z 1 (J z (S z (ξ z) - η z)) - DS z 1 (ξ z)) ∧
      IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv fun z => S z + (DJ z 1).comp (J z)) ∧
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k
        (fun z => Dη z 1 - DJ z 1 (J z (S z (ξ z) - η z)) - DS z 1 (ξ z)) ∧
      ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
        Dξ z I = J z (Dξ z 1 + S z (ξ z) - η z) := by
  have hq : 1 < q := by
    exact_mod_cast (ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq) : (1 : ℝ≥0∞) < q)
  have hDJ := hasWeakFDerivOn_of_crReflectionCoeff hc
  have hw := memWkpLoc_one_twistedReflection hΩ hp hq hJ2 hpq hqp h hc hη.memLpLoc
  have hDJ1 := (hJk.memWkpLoc_of_hasWeakFDerivOn_inter_setOf_im_nonneg hDJ).clm_comp
    (apply ℝ (V →L[ℝ] V) 1)
  have hMf := hDJ1.bilin_of_memWkpLoc_succ_halfPlane (compL ℝ V V V) hp (hq.trans_le hqp) le_rfl hJk
  refine ⟨h.crReflection_partial_one hΩ hc hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hJ2
    hw hDξ (hDξk.memLpLoc.mono_exponent (by exact_mod_cast hq.le)) hDS hDSk.memLpLoc hDη
    (hDηk.memLpLoc.mono_exponent (by exact_mod_cast hq.le)) hMf.memLpLoc, ?_,
    ((hDηk.clm_comp (apply ℝ V 1)).sub
      (hDJ1.bilin_of_memWkpLoc_succ_halfPlane (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
        (hJk.clm_apply_succ_halfPlane hp hq hqp
          ((hSk.clm_apply_succ_halfPlane hp hq hqp hξ).sub hη)))).sub
      ((hDSk.clm_comp (apply ℝ (V →L[ℝ] V) 1)).bilin_of_memWkpLoc_succ_halfPlane
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp hξ),
    (ae_cauchyRiemann_iff_ae_apply_I_eq
      (hJ2.mono fun _ => mul_self_eq_neg_one_iff_comp_eq_neg_id.1)).1
      (ae_cauchyRiemann_of_crReflection hc h hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hw hDξ)⟩
  have := hc.add_zeroth ((memLpLoc_crReflectionZeroth_iff (R := R.toContinuousLinearEquiv)
    hΩ).2 hMf.memLpLoc)
  rwa [← Pi.add_def, ← crReflectionZeroth_add] at this

/-- **The bound for the tangential derivative.** In the induction step, with `W₂ ⋐ W₁ ⋐ W ⊆ Ω`,
the estimate `hCb` of order `k` on `W₁` applies to the tangential step of
`crReflection_tangential_step`: its zeroth-order coefficient `S + (∂_s J) J` and its right side are
bounded on `W₁⁺` through the product bounds `hCM` and `hCp`, so `∂_s ξ` is bounded in
`W^{k+1,q}(W₂⁺)` by a multiple of `A`. -/
private theorem eLpNormWkp_partial_s_le {p q : ℝ≥0} (hp : 2 < p) (hq : 1 < q) {k : ℕ}
    {Ω W W₁ W₂ : Opens ℂ} (hWΩ : W ≤ Ω) (hW₁le : W₁ ≤ W) {M CM Cp Cb Ca cσ : ℝ≥0} {A : ℝ≥0∞}
    (hCM : ∀ f g : ℂ → V →L[ℝ] V,
      eLpNormWkp p ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => (f z).comp (g z)) ≤
        CM * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k f *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) g)
    (hCp : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V),
      eLpNormWkp q ((W₁ : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => B z (u z)) ≤
        Cp * eLpNormWkp p ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) k B *
          eLpNormWkp q ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (hCb : CRReflectedBound V R p q k (M + CM * M * M) W₁ W₂ Cb)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hT : IsWeakCRSolution q Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv fun z => S z + (DJ z 1).comp (J z))
        (twistedReflection (R : V →L[ℝ] V) fun z => Dξ z 1)
        (twistedReflection (R : V →L[ℝ] V)
          fun z => Dη z 1 - DJ z 1 (J z (S z (ξ z) - η z)) - DS z 1 (ξ z)))
    (hc' : IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv fun z => S z + (DJ z 1).comp (J z)))
    (hη' : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k
        (fun z => Dη z 1 - DJ z 1 (J z (S z (ξ z) - η z)) - DS z 1 (ξ z)))
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hJ1 : eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤ M)
    (hJM : eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) J ≤ M)
    (hSM : eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) S ≤ M)
    (hDJ : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ)
    (hDS : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) S DS)
    (hDη : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) η Dη)
    (ha : eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) η ≤ ↑(1 : ℝ≥0) * A)
    (hSξη : eLpNormWkp q ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => S z (ξ z) - η z) ≤
      ↑cσ * A)
    (hX : eLpNormWkp q ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ ≤ ↑Ca * A)
    (hDξ1 : eLpNorm (fun z => Dξ z 1) q (volume.restrict ((W₁ : Set ℂ) ∩ {z | 0 ≤ z.im})) ≤
      ↑Ca * A) :
    eLpNormWkp q ((W₂ : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => Dξ z 1) ≤
      ↑(Cb * (1 + Cp * (CM * M * M) * cσ + Cp * M * Ca + Ca)) * A := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_le_two.trans hp.le
  have hH (X Y : Set ℂ) (hXY : X ⊆ Y) : X ∩ {z : ℂ | 0 ≤ z.im} ⊆ Y ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ hXY
  have hHΩ := inter_setOf_im_nonneg_ae_eq_interior Ω
  have hW₁Ω : W₁ ≤ Ω := hW₁le.trans hWΩ
  -- The data of the tangential step on `W₁⁺`.
  have hMfW : eLpNormWkp p ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => (DJ z 1).comp (J z)) ≤
      ↑(CM * M * M) := by
    refine (hCM (fun z => DJ z 1) J).trans ?_
    push_cast
    gcongr
    exact (eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn_interior hHΩ hDJ
      (by simp)).trans hJM
  have hη'W₁ := eLpNormWkp_tangential_rhs_le (by exact_mod_cast hq.le) hCp
    ((eLpNormWkp_mono_set (hH _ _ hW₁Ω)).trans
      ((eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn_interior hHΩ hDη (by simp)).trans
        ha)) hMfW hSξη
    ((eLpNormWkp_mono_set (hH _ _ hWΩ)).trans
      ((eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn_interior hHΩ hDS (by simp)).trans
        hSM)) hX
  -- The estimate of order `k` on `W₁`.
  refine (hCb J (fun z => S z + (DJ z 1).comp (J z)) DJ (fun z => Dξ z 1) _ (hT.mono hW₁Ω)
    (hc'.mono hW₁Ω) (ae_mono (Measure.restrict_mono (hH _ _ hW₁Ω) le_rfl) hJ2)
    ((eLpNormWkp_mono_set hW₁Ω).trans (hJ1.trans (by push_cast; exact le_self_add)))
    ((eLpNormWkp_mono_set (hH _ _ hW₁Ω)).trans ((eLpNormWkp_mono_order k.le_succ).trans
      (hJM.trans (by push_cast; exact le_self_add))))
    ((eLpNormWkp_add_le hp1).trans (by
      push_cast
      exact add_le_add ((eLpNormWkp_mono_set (hH _ _ hW₁Ω)).trans
        ((eLpNormWkp_mono_order k.le_succ).trans hSM))
        ((eLpNormWkp_mono_set (hH _ _ hW₁le)).trans hMfW)))
    (hη'.mono (hH _ _ hW₁Ω))).trans ?_
  rw [show (↑(Cb * (1 + Cp * (CM * M * M) * cσ + Cp * M * Ca + Ca)) : ℝ≥0∞) * A =
      Cb * (↑(1 + Cp * (CM * M * M) * cσ + Cp * M * Ca + Ca) * A) by push_cast; ring]
  exact mul_le_mul_right (ENNReal.add_le_coe_mul hη'W₁ hDξ1) _

/-- **Assembling the two partial derivatives.** If `‖ξ‖_{L^q(U)} ≤ Ca A`, the tangential
derivative is bounded by `cS A` and `S ξ - η` by `cσ A` in `W^{k+1,q}(W₂)` with `U ⊆ W₂`, and the
normal derivative is `∂_t ξ = J (∂_s ξ + S ξ - η)` on `U` with `‖J‖_{W^{k+1,p}(W₂)} ≤ M`, then the
product bound `hCq` bounds `∂_t ξ` and the two partial derivatives bound `ξ` in `W^{k+2,q}(U)`. -/
private theorem eLpNormWkp_succ_succ_le_of_partials {p q : ℝ≥0∞} (hq1 : 1 ≤ q) {k : ℕ}
    {U W₂ : Set ℂ} (hUW₂ : U ⊆ W₂) {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    {Cq M Ca cS cσ : ℝ≥0} {A : ℝ≥0∞}
    (hCq : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V), eLpNormWkp q U (k + 1) (fun z => B z (u z)) ≤
      Cq * eLpNormWkp p W₂ (k + 1) B * eLpNormWkp q W₂ (k + 1) u)
    (hDξ : HasWeakFDerivOn volume (Opens.interior U) ξ Dξ)
    (hI : ∀ᵐ z ∂volume.restrict U, Dξ z I = J z (Dξ z 1 + S z (ξ z) - η z))
    (hX : eLpNorm ξ q (volume.restrict U) ≤ ↑Ca * A) (hJ : eLpNormWkp p W₂ (k + 1) J ≤ M)
    (h1 : eLpNormWkp q W₂ (k + 1) (fun z => Dξ z 1) ≤ ↑cS * A)
    (hSξη : eLpNormWkp q W₂ (k + 1) (fun z => S z (ξ z) - η z) ≤ ↑cσ * A) :
    eLpNormWkp q U (k + 1 + 1) ξ ≤ ↑(Ca + (‖smulRightL ℝ ℝ ℝ ℂ V reCLM‖₊ * cS +
      ‖smulRightL ℝ ℝ ℝ ℂ V imCLM‖₊ * (Cq * M * (cS + cσ)))) * A := by
  have hT : eLpNormWkp q U (k + 1) (fun z => Dξ z I) ≤ ↑(Cq * M * (cS + cσ)) * A := by
    rw [eLpNormWkp_congr_ae hI]
    refine ENNReal.le_coe_mul_of_le_mul_mul (hCq J fun z => Dξ z 1 + S z (ξ z) - η z) hJ ?_
    rw [show (fun z => Dξ z 1 + S z (ξ z) - η z) =
        (fun z => Dξ z 1) + fun z => S z (ξ z) - η z from funext fun z => add_sub_assoc _ _ _]
    exact (eLpNormWkp_add_le hq1).trans (ENNReal.add_le_coe_mul h1 hSξη)
  have hdec := eLpNormWkp_succ_le_eLpNorm_add_apply_one_add_apply_I (k := k + 1) hq1 hDξ
  simp only [eNorm_eq_nnNorm] at hdec
  exact hdec.trans (ENNReal.add_le_coe_mul hX (ENNReal.add_le_coe_mul
    (ENNReal.coe_mul_le_coe_mul ((eLpNormWkp_mono_set hUW₂).trans h1))
    (ENNReal.coe_mul_le_coe_mul hT)))

/-- **The estimate of order `k + 1` for one solution.** Given nested open sets
`U ⊆ W₂ ≤ W₁ ≤ W ≤ W' ≤ Ω` and the constants of the estimates of order `k` (`hCa` on `W'`, `hCb` on
`W₁`) and of the product bounds (`hCσ`, `hCM`, `hCp`, `hCq`) on them, a reflected solution with
`J`, `S` bounded by `M` in `W^{k+1,p}(Ω⁺)` satisfies the estimate of order `k + 1` on `U⁺` with an
explicit constant. -/
private theorem eLpNormWkp_succ_succ_le_of_crReflection [FiniteDimensional ℝ V] {p q : ℝ≥0}
    (hp : 2 < p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) {k : ℕ}
    {Ω W' W W₁ W₂ : Opens ℂ} {U : Set ℂ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hW'le : W' ≤ Ω)
    (hWle : W ≤ W') (hW₁le : W₁ ≤ W) (hW₂le : W₂ ≤ W₁) (hUle : U ⊆ W₂)
    {M Ca Cσ CM Cp Cb Cq : ℝ≥0} (hCa : CRReflectedBound V R p q k M Ω W' Ca)
    (hCσ : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V),
      eLpNormWkp q ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => B z (u z)) ≤
        Cσ * eLpNormWkp p ((W' : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) B *
          eLpNormWkp q ((W' : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (hCM : ∀ f g : ℂ → V →L[ℝ] V,
      eLpNormWkp p ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => (f z).comp (g z)) ≤
        CM * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k f *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) g)
    (hCp : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V),
      eLpNormWkp q ((W₁ : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => B z (u z)) ≤
        Cp * eLpNormWkp p ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) k B *
          eLpNormWkp q ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (hCb : CRReflectedBound V R p q k (M + CM * M * M) W₁ W₂ Cb)
    (hCq : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V),
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => B z (u z)) ≤
        Cq * eLpNormWkp p ((W₂ : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) B *
          eLpNormWkp q ((W₂ : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u) :
    CRReflectedBound V R p q (k + 1) M Ω U
      (Ca + (‖smulRightL ℝ ℝ ℝ ℂ V reCLM‖₊ *
          (Cb * (1 + Cp * (CM * M * M) * (Cσ * M * Ca + 1) + Cp * M * Ca + Ca)) +
        ‖smulRightL ℝ ℝ ℝ ℂ V imCLM‖₊ * (Cq * M *
          (Cb * (1 + Cp * (CM * M * M) * (Cσ * M * Ca + 1) + Cp * M * Ca + Ca) +
            (Cσ * M * Ca + 1))))) := by
  intro J S DJ ξ η h hc hJ2 hJ1 hJM hSM hη
  have hq : 1 < q := by
    exact_mod_cast (ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq) : (1 : ℝ≥0∞) < q)
  have hH (X Y : Set ℂ) (hXY : X ⊆ Y) : X ∩ {z : ℂ | 0 ≤ z.im} ⊆ Y ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ hXY
  have hW₁W' : W₁ ≤ W' := hW₁le.trans hWle
  have hW₂Ω : W₂ ≤ Ω := hW₂le.trans (hW₁W'.trans hW'le)
  -- Qualitative regularity, weak derivatives up to the axis, and the tangential step.
  have hJk := memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top hJM)
  have hSk := memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top hSM)
  have hξ := h.memWkpLoc_succ_of_crReflection hΩ hc hp hJ2 hpq hqp hJk.of_succ hSk.of_succ
    hη.of_succ
  obtain ⟨Dξ, hDξ, hDξk⟩ := hξ.exists_weakFDeriv
  obtain ⟨DS, hDS, hDSk⟩ := hSk.exists_weakFDeriv
  obtain ⟨Dη, hDη, hDηk⟩ := hη.exists_weakFDeriv
  obtain ⟨hT, hc', hη', hI⟩ := crReflection_tangential_step hp hpq hqp hΩ h hc hJ2 hJk hSk hξ hη
    hDξ hDξk hDS hDSk hDη hDηk
  -- Bounds in terms of `A = ‖η‖_{W^{k+1,q}(Ω⁺)} + ‖ξ‖_{L^q(Ω⁺)}`.
  set A := eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) η +
    eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
  have ha : eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) η ≤ ↑(1 : ℝ≥0) * A := by simp [A]
  have hX : eLpNormWkp q ((W' : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ ≤ ↑Ca * A :=
    (hCa J S DJ ξ η h hc hJ2 hJ1 ((eLpNormWkp_mono_order k.le_succ).trans hJM)
      ((eLpNormWkp_mono_order k.le_succ).trans hSM) hη.of_succ).trans
      (mul_le_mul_right (add_le_add (eLpNormWkp_mono_order k.le_succ) le_rfl) _)
  have hSξη : eLpNormWkp q ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1)
      (fun z => S z (ξ z) - η z) ≤ ↑(Cσ * M * Ca + 1) * A :=
    (eLpNormWkp_sub_le (by exact_mod_cast hq.le)).trans (ENNReal.add_le_coe_mul
      (ENNReal.le_coe_mul_of_le_mul_mul (hCσ S ξ)
        ((eLpNormWkp_mono_set (hH _ _ hW'le)).trans hSM) hX)
      ((eLpNormWkp_mono_set (hH _ _ (hWle.trans hW'le))).trans ha))
  have hDξ1 : eLpNorm (fun z => Dξ z 1) q (volume.restrict ((W₁ : Set ℂ) ∩ {z | 0 ≤ z.im})) ≤
      ↑Ca * A := by
    rw [← eLpNormWkp_zero]
    exact (eLpNormWkp_mono_order (Nat.zero_le k)).trans ((eLpNormWkp_mono_set (hH _ _ hW₁W')).trans
      ((eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn_interior
        (inter_setOf_im_nonneg_ae_eq_interior W')
        (hDξ.mono fun z hz => interior_mono (hH _ _ hW'le) hz) (by simp)).trans hX))
  -- `∂_s ξ` on `W₂⁺`, then `∂_t ξ` and `ξ` on `U⁺`.
  have h1 := eLpNormWkp_partial_s_le hp hq (hWle.trans hW'le) hW₁le hCM hCp hCb hT hc' hη' hJ2
    hJ1 hJM hSM (hasWeakFDerivOn_of_crReflectionCoeff hc) hDS hDη ha hSξη
    ((eLpNormWkp_mono_set (hH _ _ hWle)).trans hX) hDξ1
  exact eLpNormWkp_succ_succ_le_of_partials (by exact_mod_cast hq.le) (hH _ _ hUle) hCq
    (hDξ.mono fun z hz => interior_mono (hH _ _ (hUle.trans hW₂Ω)) hz)
    (ae_restrict_of_ae_restrict_of_subset (hH _ _ (hUle.trans hW₂Ω)) hI)
    ((eLpNorm_le_eLpNormWkp.trans (eLpNormWkp_mono_set
      (hH _ _ (hUle.trans (hW₂le.trans hW₁W'))))).trans hX)
    ((eLpNormWkp_mono_set (hH _ _ hW₂Ω)).trans hJM) h1
    ((eLpNormWkp_mono_set (hH _ _ (hW₂le.trans hW₁le))).trans hSξη)

/-- **The induction step for reflected solutions.** If the estimate of order `k` holds for every
conjugation-invariant open set and every bound, so does the estimate of order `k + 1`. -/
private theorem crReflectedEstimate_succ [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ (Ω : Opens ℂ) (U : Set ℂ) (M : ℝ≥0), MapsTo (starRingEnd ℂ) Ω Ω →
      IsCompact (closure U) → closure U ⊆ Ω → CRReflectedEstimate V R p q k M Ω U)
    {Ω : Opens ℂ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {U : Set ℂ} (hUc : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) : CRReflectedEstimate V R p q (k + 1) M Ω U := by
  have hq : 1 < q := by
    exact_mod_cast (ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq) : (1 : ℝ≥0∞) < q)
  -- Nested open sets `U ⋐ W₂ ⋐ W₁ ⋐ W ⋐ W' ⋐ Ω`, all but `W₂` invariant under conjugation.
  obtain ⟨W', hW'c, hUW', hW'Ω, hW'cc⟩ :=
    exists_mapsTo_conj_between_and_isCompact_closure hUc hΩ hUΩ
  obtain ⟨W, hWc, hUW, hWW', hWcc⟩ :=
    exists_mapsTo_conj_between_and_isCompact_closure hUc hW'c hUW'
  obtain ⟨W₁, hW₁c, hUW₁, hW₁W, hW₁cc⟩ :=
    exists_mapsTo_conj_between_and_isCompact_closure hUc hWc hUW
  obtain ⟨W₂, hUW₂, hW₂W₁, hW₂cc⟩ := Opens.exists_between_and_isCompact_closure hUc hUW₁
  -- The constants of the estimates of order `k` and of the product bounds on these sets.
  obtain ⟨Ca, hCa⟩ := hk Ω W' M hΩ hW'cc hW'Ω
  obtain ⟨Cσ, hCσ⟩ := exists_eLpNormWkp_succ_clm_apply_le_halfPlane (F := V) (G := V) hp hq hqp k
    hWcc hWW'
  obtain ⟨CM, hCM⟩ := exists_eLpNormWkp_bilin_le_mul_eLpNormWkp_succ_halfPlane
    (F := V →L[ℝ] V) (G := V →L[ℝ] V) (H := V →L[ℝ] V) hp (one_lt_two.trans hp) le_rfl k hWcc
    (hWW'.trans (subset_closure.trans hW'Ω))
  replace hCM (f g : ℂ → V →L[ℝ] V) := by
    simpa only [compL_apply] using
      le_mul_mul_of_le_mul_eNorm_mul_mul (norm_compL_le ℝ V V V) (hCM (compL ℝ V V V) f g)
  obtain ⟨Cp, hCp⟩ := exists_eLpNormWkp_clm_apply_le_mul_eLpNormWkp_succ_halfPlane (F := V)
    (G := V) hp hq hqp k hW₁cc hW₁W
  obtain ⟨Cb, hCb⟩ := hk W₁ W₂ (M + CM * M * M) hW₁c hW₂cc hW₂W₁
  obtain ⟨Cq, hCq⟩ := exists_eLpNormWkp_succ_clm_apply_le_halfPlane (F := V) (G := V) hp hq hqp k
    hUc hUW₂
  exact ⟨_, eLpNormWkp_succ_succ_le_of_crReflection hp hpq hqp hΩ (subset_closure.trans hW'Ω)
    (subset_closure.trans hWW') (subset_closure.trans hW₁W) (subset_closure.trans hW₂W₁)
    (subset_closure.trans hUW₂) hCa hCσ hCM hCp hCb hCq⟩

/-- The estimate of every order for reflected solutions: induction on the order, from
`crReflectedEstimate_zero` and `crReflectedEstimate_succ`. -/
private theorem crReflectedEstimate [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) (k : ℕ) {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {U : Set ℂ} (hUc : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) : CRReflectedEstimate V R p q k M Ω U := by
  induction k generalizing Ω U M with
  | zero => exact crReflectedEstimate_zero hp hpq hqp hΩ hUc hUΩ M
  | succ k ih =>
    exact crReflectedEstimate_succ hp hpq hqp (fun _ _ M hΩ hUc hUΩ => ih hΩ hUc hUΩ M) hΩ hUc
      hUΩ M

variable [FiniteDimensional ℝ V] (hR : Function.Involutive R)
include hR

/-- **The estimates of every order up to the real axis** (McDuff–Salamon, Lemma B.4.6 and
Proposition B.4.9 with a totally real boundary condition). Let `Ω` be invariant under conjugation,
`R` an isometric involution of the finite-dimensional space `V` whose fixed vectors lie in `Λ`,
`p > 2`, `1/p + 1/q < 1` and `q ≤ p`, let `U` have compact closure in `Ω`, and let `M ≥ 0`. For
every `k` there is a constant `C` such that for all coefficients `J`, `S` with `J² = -1` almost
everywhere on `Ω ∩ {0 ≤ t}` whose reflections are Sobolev coefficients on `Ω`, with
`‖crReflectionCoeff R J‖_{W^{1,p}(Ω)} ≤ M`, `‖J‖_{W^{k,p}(Ω ∩ {0 ≤ t})} ≤ M` and
`‖S‖_{W^{k,p}(Ω ∩ {0 ≤ t})} ≤ M`, every weak solution `ξ ∈ L^q_loc` up to the real axis of
`∂_s ξ + J ∂_t ξ + S ξ = η` with boundary subspace `Λ` and `η ∈ W^{k,q}_loc` up to the axis
satisfies
`‖ξ‖_{W^{k+1,q}(U ∩ {0 ≤ t})} ≤ C (‖η‖_{W^{k,q}(Ω ∩ {0 ≤ t})} + ‖ξ‖_{L^q(Ω ∩ {0 ≤ t})})`. -/
theorem exists_eLpNormWkp_succ_le_of_isWeakCRSolutionHalf {Ω : Opens ℂ} {Λ : Submodule ℝ V}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΛ : ∀ v, R v = v → v ∈ Λ) {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) (k : ℕ) {U : Set ℂ}
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η →
      IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv S) →
      (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) →
      eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤ M →
      eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k J ≤ M →
      eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k S ≤ M →
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η →
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) (k + 1) ξ ≤
        C * (eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η +
          eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  obtain ⟨C, hC⟩ := crReflectedEstimate (R := R) hp hpq hqp k hΩ hUc hUΩ M
  exact ⟨C, fun J S DJ ξ η h hc => hC J S DJ ξ η (h.isWeakCRSolution_crReflection hR hΩ hΛ
    ((memLpLoc_crReflectionCoeff_iff hΩ).1 hc.memLpLoc_coeff)
    ((memLpLoc_crReflectionDeriv_iff hΩ).1 hc.memLpLoc_deriv)
    ((memLpLoc_crReflectionZeroth_iff hΩ).1 hc.memLpLoc_zeroth) hpq.le) hc⟩

/-- **The estimates of every order up to the real axis for Sobolev coefficients** (McDuff–Salamon,
Lemma B.4.6 and Proposition B.4.9 with a totally real boundary condition). Under the hypotheses of
`TauCeti.exists_eLpNormWkp_succ_le_of_isWeakCRSolutionHalf`, the constant `C` applies to all
coefficients `J`, `S` such that `J` is continuous on `Ω ∩ {0 ≤ t}` with weak derivative `DJ` on
the open upper part and anticommutes with `R` on `Ω ∩ ℝ`, `J² = -1` almost everywhere on
`Ω ∩ {0 ≤ t}`, `‖J‖_{W^{max k 1, p}(Ω ∩ {0 ≤ t})} ≤ M` and `‖S‖_{W^{k,p}(Ω ∩ {0 ≤ t})} ≤ M`: every
weak solution `ξ ∈ L^q_loc` up to the real axis with `η ∈ W^{k,q}_loc` up to the axis satisfies
`‖ξ‖_{W^{k+1,q}(U ∩ {0 ≤ t})} ≤ C (‖η‖_{W^{k,q}(Ω ∩ {0 ≤ t})} + ‖ξ‖_{L^q(Ω ∩ {0 ≤ t})})`. -/
theorem exists_eLpNormWkp_succ_le_of_isWeakCRSolutionHalf_of_hasWeakFDerivOn {Ω : Opens ℂ}
    {Λ : Submodule ℝ V} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΛ : ∀ v, R v = v → v ∈ Λ)
    {p q : ℝ≥0} (hp : 2 < p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) (k : ℕ)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η →
      HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ →
      ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) →
      (∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v)) →
      (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) →
      eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (max k 1) J ≤ M →
      eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k S ≤ M →
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η →
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) (k + 1) ξ ≤
        C * (eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η +
          eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_le_of_isWeakCRSolutionHalf hR hΩ hΛ hp hpq hqp k hUc
    hUΩ (2 * M)
  refine ⟨C, fun J S DJ ξ η h hJW hJc hJR hJ2 hJM hSM hη => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_le_two.trans hp.le
  have hM : (M : ℝ≥0∞) ≤ ↑(2 * M) := by exact_mod_cast le_mul_of_one_le_left' one_le_two
  -- `DJ` and `S` are locally `Lᵖ` up to the axis because their norms are finite.
  have hJ1 := (eLpNormWkp_mono_order (le_max_right k 1)).trans hJM
  have hDJ := (memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top
    hJ1)).memLpLoc_of_hasWeakFDerivOn_inter_setOf_im_nonneg hJW
  have hS0 := (eLpNormWkp_mono_order (Nat.zero_le k)).trans hSM
  rw [eLpNormWkp_zero] at hS0
  obtain ⟨hc, hJM', -⟩ := isSobolevCRCoefficients_crReflection_of_le hΩ hp1 hJW hJc hJR hDJ
    (memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top hSM)).memLpLoc hJ1 hS0
  exact hC J S DJ ξ η h hc hJ2 hJM' ((eLpNormWkp_mono_order (le_max_left k 1)).trans (hJM.trans hM))
    (hSM.trans hM) hη

end TauCeti
