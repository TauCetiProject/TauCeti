/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.Local.Norm
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder.Estimate
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Calculus.ContDiff.Compactness
import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Analysis.Sobolev.Local.ChainRule.Bound.Higher
import TauCeti.Analysis.Sobolev.Local.Compactness.ContDiff
import TauCeti.Analysis.Sobolev.Local.Wkp.Norm
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Uniform estimates and compactness for the nonlinear Cauchy–Riemann equation in the plane

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real normed space.
This file proves the planar interior case of McDuff–Salamon, Theorem B.4.2 with Remark B.4.3, for
domain-dependent structures and inhomogeneous terms. Let `p > 2` and `ℓ : ℕ`, and let
`u n : ℂ → V` be weak solutions `TauCeti.IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n)` of

`∂ₛu + J n (z, u) ∂ₜu = η n (z, u)`,

where `J n` and `η n` are of class `C^ℓ` jointly in `(z, x)`, with `J n (z, u n z)² = -1`.
Suppose that the images under the `u n` of every compact `K ⊆ Ω` lie in one compact set, and that
their weak derivatives are bounded in `Lᵖ(W)` on every open `W` with compact closure in `Ω`.

* *Uniform estimates.* If `p < ∞` and the derivatives of orders at most `ℓ` of the data are
  bounded on compact sets uniformly in `n`, then the `u n` are bounded in `W^{ℓ+1,p}(U)` for
  every `U` with compact closure in `Ω` (`TauCeti.exists_eLpNormWkp_le_of_isWeakCauchyRiemannOn`).
* *Compactness.* If `ℓ ≥ 1` and the data converge in `C^ℓ` on compact sets to `J` and `η`, a
  subsequence of the `u n` converges in `C^ℓ` on compact subsets of `Ω` to a solution `v` of the
  limiting equation `TauCeti.IsWeakCauchyRiemannOn p Ω J η v`
  (`TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn`). Here `p = ∞` is
  allowed: the hypotheses for `p` give those for the finite exponent `min p 3`.
* *Smooth data.* If the data are smooth and converge in `C^∞` on compact sets, a subsequence
  converges in `C^∞` on compact subsets of `Ω` to a smooth solution of the limiting equation
  (`TauCeti.exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn`).
* *Gradient bounds* (McDuff–Salamon, Theorem 4.1.1). In the compactness theorem for `ℓ ≥ 1` and
  data converging in `C^ℓ`, and in the one for smooth data converging in `C^∞` (in particular fixed
  smooth data), a bound on `‖du n‖` on each compact subset of `Ω`, uniform in `n`, may replace the
  `Lᵖ` bound on the weak derivatives
  (`exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_of_norm_fderiv_le` and
  `exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_of_norm_fderiv_le`).

## The argument

The estimate is proved by induction on the order, as in the qualitative bootstrapping
`TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn`. If the `u n` are bounded in `W^{m+1,p}` on a set `W`
with compact closure in `Ω`, with `m + 1 ≤ ℓ`, then so are the graphs `z ↦ (z, u n z)`, whose
values over `W` lie in a fixed compact set, on which the derivatives of the data are bounded
uniformly in `n`. The composition bound `TauCeti.exists_eLpNormWkp_succ_comp_le_of_norm_le`, whose
constant depends on the composed map only through such a bound, bounds the frozen coefficients
`A n z = J n z (u n z)` and `f n z = η n z (u n z)` in `W^{m+1,p}` on a smaller set `W₁`. The
interior estimate of order `m + 1` for `∂ₛu + A ∂ₜu = f`
(`TauCeti.exists_eLpNormWkp_succ_le_of_isWeakCauchyRiemannOn`, which is
`TauCeti.crInteriorEstimate` with `S = 0` and `q = p`, read on a Euclidean model of `V`), whose
constant depends on the coefficient only through a bound for its norm, then bounds the `u n` in
`W^{m+2,p}` on every `U` with compact closure in `W₁`.

For compactness, `C^ℓ` convergence of the data bounds their derivatives on compact sets uniformly
in `n` (`TauCeti.exists_forall_norm_iteratedFDeriv_le_of_tendstoLocallyUniformly`), so the
uniform estimate applies.
The bounds in `W^{ℓ+1,p}` are bounds in the spaces `TauCeti.Wkp`
(`TauCeti.exists_wkp_norm_le_eLpNormWkp`), and Rellich's theorem with classical derivatives
(`Module.Basis.exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn_iteratedFDeriv`) gives a
subsequence converging in `C^ℓ` on compact subsets. Each `u n` is `C^ℓ` by
`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn` and solves its equation pointwise
(`TauCeti.isWeakCauchyRiemannOn_iff_of_contDiffOn`); for `ℓ ≥ 1` the pointwise equations pass to
the limit.

For smooth data, every subsequence has, for each `ℓ`, a further subsequence converging in `C^ℓ`,
so a diagonal extraction
(`IsOpen.exists_strictMono_forall_tendstoLocallyUniformlyOn_iteratedFDeriv`) gives one subsequence
converging in every order to a smooth map. It solves the limiting equation because it agrees on
`Ω` with the limit given by the case `ℓ = 1` along a further subsequence.

Under gradient bounds each `u n` is `C¹` on `Ω`, so its classical derivative is a weak
derivative, and a pointwise bound on compact sets bounds it in `Lᵖ` on sets of finite measure.

## Main results

* `TauCeti.exists_eLpNormWkp_succ_le_of_isWeakCauchyRiemannOn`: the interior estimates for the
  linear equation `∂ₛu + A ∂ₜu = f` on a finite-dimensional normed space, uniform in bounded sets
  of coefficients.
* `TauCeti.exists_eLpNormWkp_le_of_isWeakCauchyRiemannOn`: uniform `W^{ℓ+1,p}` estimates for
  sequences of solutions with `C^ℓ`-bounded data.
* `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn`: a subsequence
  converges in `C^ℓ` on compact subsets to a solution of the limiting equation.
* `TauCeti.exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn`: for smooth
  data converging in `C^∞`, a subsequence converges in `C^∞` on compact subsets to a smooth
  solution of the limiting equation.
* `exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_of_norm_fderiv_le` and
  `exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_of_norm_fderiv_le`:
  the same conclusions under pointwise gradient bounds on compact sets.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 4.1.1 and Appendix B.4 (Theorems B.4.1 and B.4.2 and Remark B.4.3).
-/

public section

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ}

/-! ### The linear equation -/

/-- **Interior estimates for `∂ₛu + A ∂ₜu = f`.** Let `V` be a finite-dimensional real normed
space, `p > 2` finite and `k : ℕ`, and let `U` have compact closure contained in `Ω`. For every `M`
there is a constant `C` such that every weak solution `u` on `Ω` of `∂ₛu + A ∂ₜu = f` with
`A² = -1`, `‖A‖_{W^{max k 1, p}(Ω)} ≤ M` and `f ∈ W^{k,p}_loc(Ω)` satisfies
`‖u‖_{W^{k+1,p}(U)} ≤ C (‖f‖_{W^{k,p}(Ω)} + ‖u‖_{Lᵖ(Ω)})`. This is `TauCeti.crInteriorEstimate`
with `S = 0` and `q = p`, applied on a Euclidean model of `V`. -/
theorem exists_eLpNormWkp_succ_le_of_isWeakCauchyRiemannOn {p : ℝ≥0} (hp : 2 < p) (k : ℕ)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → V →L[ℝ] V) (f u : ℂ → V),
      IsWeakCauchyRiemannOn p Ω (fun z _ => A z) (fun z _ => f z) u →
      (∀ᵐ z ∂volume.restrict Ω, A z * A z = -1) → eLpNormWkp p Ω (max k 1) A ≤ M →
      MemWkpLoc p Ω k f →
      eLpNormWkp p U (k + 1) u ≤ C * (eLpNormWkp p Ω k f + eLpNorm u p (volume.restrict Ω)) := by
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let e : V ≃L[ℝ] E := toEuclidean
  let c : (V →L[ℝ] V) →L[ℝ] (E →L[ℝ] E) :=
    (e.conjContinuousAlgEquiv.toContinuousLinearEquiv :
      (V →L[ℝ] V) ≃L[ℝ] (E →L[ℝ] E)).toContinuousLinearMap
  obtain ⟨C, hC⟩ := crInteriorEstimate_iff.1 (crInteriorEstimate (V := E) hp
    (ENNReal.inv_add_inv_lt_one_of_two_lt (by exact_mod_cast hp)) le_rfl k hUc hUΩ (‖c‖₊ * M))
  refine ⟨‖(e.symm : E →L[ℝ] V)‖₊ * C * ‖(e : V →L[ℝ] E)‖₊, fun A f u h hA2 hA hf => ?_⟩
  -- Transport the equation to `E`, where the linear theory applies.
  have hcA (z : ℂ) : c (A z) = (e : V →L[ℝ] E) ∘L A z ∘L (e.symm : E →L[ℝ] V) := by
    simp [c, ← ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  have hA' : eLpNormWkp p Ω (max k 1) (fun z => c (A z)) ≤ ↑(‖c‖₊ * M) :=
    (eLpNormWkp_clm_comp_le c).trans (by rw [eNorm_eq_nnNorm, ENNReal.coe_mul]; gcongr)
  have hA1 : MemWkpLoc p Ω 1 (fun z => c (A z)) :=
    (memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top hA')).of_le
      (le_max_right k 1)
  obtain ⟨DA, hDA, hDAk⟩ := hA1.exists_weakFDeriv_of_isOpen
  have hc : IsSobolevCRCoefficients p Ω (fun z => c (A z)) DA 0 :=
    ⟨hDA, hA1.memLpLoc, hDAk.memLpLoc, memLpLoc_zero⟩
  have h' : IsWeakCauchyRiemannOn p Ω (fun z _ => c (A z)) (fun z _ => e (f z))
      (fun z => e (u z)) := by
    simpa only [hcA, ContinuousLinearEquiv.symm_apply_apply] using h.continuousLinearEquiv_comp e
  have hA2' : ∀ᵐ z ∂volume.restrict Ω, c (A z) * c (A z) = -1 := by
    filter_upwards [hA2] with z hz
    -- `c` is the algebra equivalence `e.conjContinuousAlgEquiv`, read as a linear map.
    have h := congrArg e.conjContinuousAlgEquiv hz
    rwa [map_mul, map_neg, map_one] at h
  have hest := hC _ 0 DA _ _ (h'.isWeakCRSolution hp.le hc (hf.clm_comp (e : V →L[ℝ] E)).memLpLoc)
    hc hA2' hA' (by simp [eLpNormWkp_zero_fun])
    (hf.clm_comp (e : V →L[ℝ] E))
  -- Transport the estimate back to `V`.
  have hf' := eLpNormWkp_clm_comp_le (p := p) (U := Ω) (k := k) (e : V →L[ℝ] E) (f := f)
  have hu' := eLpNormWkp_clm_comp_le (p := p) (U := Ω) (k := 0) (e : V →L[ℝ] E) (f := u)
  rw [eLpNormWkp_zero, eLpNormWkp_zero] at hu'
  calc
    _ = eLpNormWkp p U (k + 1) (fun z => (e.symm : E →L[ℝ] V) (e (u z))) := by simp
    _ ≤ ‖(e.symm : E →L[ℝ] V)‖ₑ * eLpNormWkp p U (k + 1) (fun z => e (u z)) :=
      eLpNormWkp_clm_comp_le _
    _ ≤ ‖(e.symm : E →L[ℝ] V)‖ₑ * (C * (‖(e : V →L[ℝ] E)‖ₑ * eLpNormWkp p Ω k f +
        ‖(e : V →L[ℝ] E)‖ₑ * eLpNorm u p (volume.restrict Ω))) := by
      gcongr
      exact hest.trans (by gcongr <;> assumption)
    _ = _ := by simp only [eNorm_eq_nnNorm, ENNReal.coe_mul]; ring

/-! ### Uniform estimates -/

omit [FiniteDimensional ℝ V] in
/-- Bounds for the `u n` in `W^{k,p}(W)`, for `W` with compact closure, bound the graphs
`z ↦ (z, u n z)` in `W^{k,p}(W)`: their norms are at most that of `z ↦ (z, 0)` plus that of
`u n`. -/
private theorem exists_eLpNormWkp_graph_le [CompleteSpace V] {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ)
    {W : Set ℂ} (hWc : IsCompact (closure W)) {u : ℕ → ℂ → V} {R : ℝ≥0}
    (hR : ∀ n, eLpNormWkp p W k (u n) ≤ R) :
    ∃ X : ℝ≥0, ∀ n, 1 + eLpNormWkp p W k (fun z => ((z, u n z) : ℂ × V)) ≤ X := by
  set G₀ := eLpNormWkp p W k (fun z => ((z, 0) : ℂ × V))
  have hG₀ : G₀ ≠ ∞ := ((contDiff_id.prodMk contDiff_const).memWkpLoc (U := univ) (k := k)
    (p := p)).eLpNormWkp_ne_top_of_isCompact (subset_univ _) hWc |> ne_top_of_le_ne_top <|
      eLpNormWkp_mono_set subset_closure
  refine ⟨1 + G₀.toNNReal + R, fun n => ?_⟩
  have h : (fun z => ((z, u n z) : ℂ × V)) =
      (fun z => ((z, 0) : ℂ × V)) + fun z => ContinuousLinearMap.inr ℝ ℂ V (u n z) := by
    funext z; simp
  rw [h, ENNReal.coe_add, ENNReal.coe_add, ENNReal.coe_toNNReal hG₀, add_assoc]
  exact add_le_add le_rfl ((eLpNormWkp_add_le hp).trans (add_le_add le_rfl
    ((eLpNormWkp_clm_comp_le_of_norm_le_one _ (ContinuousLinearMap.norm_inr_le_one ℝ ℂ V)).trans
      (hR n))))

/-- **The frozen coefficients along a family of graphs.** For `W₁` with compact closure in `W`,
`B` and `X`, one constant `C` bounds `‖g (z, u z)‖_{W^{m+1,p}(W₁)}` for every `g : ℂ × V → G` of
class `C^{m+1}` whose derivatives of orders at most `m + 1` are bounded by `B` on a set `L`, and
every `u` continuous on `W` whose graph over `W` lies in `L` and has `W^{m+1,p}(W)` size at most
`X - 1`. This is `TauCeti.exists_eLpNormWkp_succ_comp_le_of_norm_le` along graphs. -/
private theorem exists_eLpNormWkp_comp_graph_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] {p : ℝ≥0} (hp : 2 < p) (m : ℕ) {W : Opens ℂ}
    {W₁ : Set ℂ} (hW₁c : IsCompact (closure W₁)) (hW₁W : closure W₁ ⊆ W) (L : Set (ℂ × V))
    (B : ℝ) (X : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (g : ℂ × V → G) (u : ℂ → V), ContDiff ℝ (m + 1) g → ContinuousOn u W →
      (∀ z ∈ W, (z, u z) ∈ L) → (∀ i ≤ m + 1, ∀ x ∈ L, ‖iteratedFDeriv ℝ i g x‖ ≤ B) →
      1 + eLpNormWkp p W (m + 1) (fun z => ((z, u z) : ℂ × V)) ≤ X →
      eLpNormWkp p W₁ (m + 1) (fun z => g (z, u z)) ≤ C := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_comp_le_of_norm_le (F := ℂ × V) (G := G) (Ω := W) hp
    m B.toNNReal hW₁c hW₁W
  refine ⟨C * X ^ (m + 1), fun g u hg hu hL hgB hX => (hC g univ _ isOpen_univ hg.contDiffOn
    (continuousOn_id.prodMk hu) (mapsTo_univ _ _) fun z hz i hi =>
      (hgB i hi _ (hL z hz)).trans (Real.le_coe_toNNReal B)).trans ?_⟩
  push_cast
  gcongr
  exact hX

/-- The step of the uniform estimates: bounds for the `u n` in `W^{m+1,p}` on every set with
compact closure in `Ω` give bounds in `W^{m+2,p}`, for data of class `C^{m+1}` whose derivatives
of orders at most `m + 1` are bounded on compact sets uniformly in `n`. -/
private theorem exists_eLpNormWkp_add_two_le {p : ℝ≥0} (hp : 2 < p) {m : ℕ}
    {J : ℕ → ℂ → V → V →L[ℝ] V} {η : ℕ → ℂ → V → V} {u : ℕ → ℂ → V}
    (hJ : ∀ n, ContDiff ℝ (m + 1) (fun x : ℂ × V => J n x.1 x.2))
    (hη : ∀ n, ContDiff ℝ (m + 1) (fun x : ℂ × V => η n x.1 x.2))
    (hBJ : ∀ L : Set (ℂ × V), IsCompact L → ∃ B : ℝ, ∀ n, ∀ i ≤ m + 1, ∀ x ∈ L,
      ‖iteratedFDeriv ℝ i (fun x : ℂ × V => J n x.1 x.2) x‖ ≤ B)
    (hBη : ∀ L : Set (ℂ × V), IsCompact L → ∃ B : ℝ, ∀ n, ∀ i ≤ m + 1, ∀ x ∈ L,
      ‖iteratedFDeriv ℝ i (fun x : ℂ × V => η n x.1 x.2) x‖ ≤ B)
    (hJ2 : ∀ n, ∀ᵐ z ∂volume.restrict Ω, J n z (u n z) * J n z (u n z) = -1)
    (hu : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (ih : ∀ U : Set ℂ, IsCompact (closure U) → closure U ⊆ Ω →
      ∃ R : ℝ≥0, ∀ n, eLpNormWkp p U (m + 1) (u n) ≤ R)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ R : ℝ≥0, ∀ n, eLpNormWkp p U (m + 2) (u n) ≤ R := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  obtain ⟨W, hUW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hUc hUΩ
  obtain ⟨W₁, hUW₁, hW₁W, hW₁c⟩ := Opens.exists_between_and_isCompact_closure hUc hUW
  have hW₁le : (W₁ : Set ℂ) ⊆ W := subset_closure.trans hW₁W
  have hWle : (W : Set ℂ) ⊆ Ω := subset_closure.trans hWΩ
  obtain ⟨R, hR⟩ := ih W hWc hWΩ
  obtain ⟨K', hK', hK'u⟩ := hK _ hWΩ hWc
  obtain ⟨BJ, hBJ⟩ := hBJ _ (hWc.prod hK')
  obtain ⟨Bη, hBη⟩ := hBη _ (hWc.prod hK')
  -- The graphs `z ↦ (z, u n z)` are bounded in `W^{m+1,p}(W)` and take values in
  -- `closure W ×ˢ K'`, where the derivatives of the data are bounded.
  obtain ⟨X, hX⟩ := exists_eLpNormWkp_graph_le (by exact_mod_cast (one_lt_two.trans hp).le)
    (m + 1) hWc hR
  have hgB (n : ℕ) (z : ℂ) (hz : z ∈ W) : (z, u n z) ∈ closure (W : Set ℂ) ×ˢ K' :=
    ⟨subset_closure hz, hK'u n (subset_closure hz)⟩
  obtain ⟨CJ, hCJ⟩ := exists_eLpNormWkp_comp_graph_le (V := V) (G := V →L[ℝ] V) hp m hW₁c hW₁W _
    BJ X
  obtain ⟨Cη, hCη⟩ := exists_eLpNormWkp_comp_graph_le (V := V) (G := V) hp m hW₁c hW₁W _ Bη X
  set M : ℝ≥0 := CJ + Cη
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_le_of_isWeakCauchyRiemannOn (V := V) hp (m + 1) hUc
    hUW₁ M
  refine ⟨C * (M + R), fun n => ?_⟩
  -- The frozen coefficients are bounded in `W^{m+1,p}(W₁)` by `M`.
  have huW := (hu n).continuousOn.mono hWle
  have hA : eLpNormWkp p W₁ (m + 1) (fun z => J n z (u n z)) ≤ M :=
    (hCJ _ _ (hJ n) huW (hgB n) (hBJ n) (hX n)).trans (by simp [M])
  have hf : eLpNormWkp p W₁ (m + 1) (fun z => η n z (u n z)) ≤ M :=
    (hCη _ _ (hη n) huW (hgB n) (hBη n) (hX n)).trans (by simp [M])
  have hsol : IsWeakCauchyRiemannOn p W₁ (fun z _ => J n z (u n z)) (fun z _ => η n z (u n z))
      (u n) := (isWeakCauchyRiemannOn_congr_ae (J' := fun z _ => J n z (u n z))
        (η' := fun z _ => η n z (u n z)) (.of_forall fun _ => rfl)
        (.of_forall fun _ => rfl)).1 ((hu n).mono (hW₁le.trans hWle))
  refine (hC _ _ _ hsol (ae_mono (Measure.restrict_mono (hW₁le.trans hWle) le_rfl) (hJ2 n))
    (by rwa [max_eq_left (by omega)])
    (memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top hf))).trans ?_
  push_cast
  gcongr
  exact eLpNorm_le_eLpNormWkp.trans ((eLpNormWkp_mono_set hW₁le).trans (hR n))

/-- On a set `W` of finite measure, one constant bounds the `Lᵖ(W)` norms of all maps whose norm
is at most `r` almost everywhere on `W`: `volume W ^ (1 / p) * r` will do. -/
private theorem exists_eLpNorm_le_of_ae_norm_le {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    {W : Set ℂ} (hW : volume W ≠ ∞) (r : ℝ) :
    ∃ c : ℝ≥0, ∀ f : ℂ → E, AEStronglyMeasurable f (volume.restrict W) →
      (∀ᵐ z ∂volume.restrict W, ‖f z‖ ≤ r) → eLpNorm f p (volume.restrict W) ≤ c := by
  have hA : volume W ^ p.toReal⁻¹ * ENNReal.ofReal r ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hW) ENNReal.ofReal_ne_top
  refine ⟨(volume W ^ p.toReal⁻¹ * ENNReal.ofReal r).toNNReal, fun f hf hfr => ?_⟩
  rw [ENNReal.coe_toNNReal hA]
  simpa [Measure.restrict_apply_univ] using eLpNorm_le_of_ae_bound (p := p) hf hfr

omit [FiniteDimensional ℝ V] in
/-- The base of the uniform estimates: images of compact sets in one compact set and bounds for
the weak derivatives in `Lᵖ` give bounds in `W^{1,p}(U)` for `U` with compact closure in `Ω`. -/
private theorem exists_eLpNormWkp_one_le {p : ℝ≥0∞} {u : ℕ → ℂ → V}
    (hu : ∀ n, ContinuousOn (u n) Ω)
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (hd : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ c : ℝ≥0, ∀ n, ∃ D, HasWeakFDerivOn volume W (u n) D ∧ eLpNorm D p (volume.restrict W) ≤ c)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ R : ℝ≥0, ∀ n, eLpNormWkp p U 1 (u n) ≤ R := by
  obtain ⟨W, hUW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hUc hUΩ
  obtain ⟨K', hK', hK'u⟩ := hK _ hWΩ hWc
  obtain ⟨r, hr⟩ := hK'.isBounded.exists_norm_le
  obtain ⟨c, hc⟩ := hd W hWc hWΩ
  obtain ⟨c₀, hc₀⟩ := exists_eLpNorm_le_of_ae_norm_le (E := V) (p := p)
    ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne r
  refine ⟨c₀ + c, fun n => ?_⟩
  obtain ⟨D, hD, hDc⟩ := hc n
  refine (eLpNormWkp_mono_set (subset_closure.trans hUW)).trans
    ((eLpNormWkp_succ_le (k := 0) (by rwa [Opens.interior_coe])).trans ?_)
  rw [eLpNormWkp_zero, ENNReal.coe_add]
  exact add_le_add (hc₀ _
    (((hu n).mono (subset_closure.trans hWΩ)).aestronglyMeasurable W.isOpen.measurableSet)
    ((ae_restrict_mem W.isOpen.measurableSet).mono
      fun z hz => hr _ (hK'u n (subset_closure hz)))) hDc

/-- **Uniform estimates for the nonlinear Cauchy–Riemann equation** (McDuff–Salamon,
Theorem B.4.2 and Remark B.4.3, planar interior case). Let `2 < p < ∞` and `ℓ : ℕ`. Let
`J n : ℂ → V → End V` and `η n : ℂ → V → V` be of class `C^ℓ` jointly in `(z, x)`, with
derivatives of orders at most `ℓ` bounded on each compact set uniformly in `n`, and let `u n` be
weak solutions of `∂ₛu + J n (z, u) ∂ₜu = η n (z, u)` on `Ω` with `J n (z, u n z)² = -1` almost
everywhere. Suppose that the images under the `u n` of each compact `K ⊆ Ω` lie in one compact
set, and that on each open `W` with compact closure in `Ω` the weak derivatives of the `u n` are
bounded in `Lᵖ(W)`. Then on every `U` with compact closure in `Ω` the `u n` are bounded in
`W^{ℓ+1,p}(U)`. -/
theorem exists_eLpNormWkp_le_of_isWeakCauchyRiemannOn {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤)
    {ℓ : ℕ} {J : ℕ → ℂ → V → V →L[ℝ] V} {η : ℕ → ℂ → V → V} {u : ℕ → ℂ → V}
    (hJ : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => J n x.1 x.2))
    (hη : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => η n x.1 x.2))
    (hBJ : ∀ L : Set (ℂ × V), IsCompact L → ∃ B : ℝ, ∀ n, ∀ i ≤ ℓ, ∀ x ∈ L,
      ‖iteratedFDeriv ℝ i (fun x : ℂ × V => J n x.1 x.2) x‖ ≤ B)
    (hBη : ∀ L : Set (ℂ × V), IsCompact L → ∃ B : ℝ, ∀ n, ∀ i ≤ ℓ, ∀ x ∈ L,
      ‖iteratedFDeriv ℝ i (fun x : ℂ × V => η n x.1 x.2) x‖ ≤ B)
    (hJ2 : ∀ n, ∀ᵐ z ∂volume.restrict Ω, J n z (u n z) * J n z (u n z) = -1)
    (hu : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (hd : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ c : ℝ≥0, ∀ n, ∃ D, HasWeakFDerivOn volume W (u n) D ∧ eLpNorm D p (volume.restrict W) ≤ c)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ R : ℝ≥0, ∀ n, eLpNormWkp p U (ℓ + 1) (u n) ≤ R := by
  lift p to ℝ≥0 using hp'
  have hp2 : 2 < p := by exact_mod_cast hp
  suffices ∀ m ≤ ℓ, ∀ U : Set ℂ, IsCompact (closure U) → closure U ⊆ Ω →
      ∃ R : ℝ≥0, ∀ n, eLpNormWkp p U (m + 1) (u n) ≤ R from this ℓ le_rfl U hUc hUΩ
  intro m hm
  induction m with
  | zero =>
    exact fun U hUc hUΩ => exists_eLpNormWkp_one_le (fun n => (hu n).continuousOn) hK hd hUc hUΩ
  | succ m ih =>
    have hmℓ : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hm
    intro U hUc hUΩ
    exact exists_eLpNormWkp_add_two_le hp2 (fun n => by exact_mod_cast (hJ n).of_le hmℓ)
      (fun n => by exact_mod_cast (hη n).of_le hmℓ)
      (fun L hL => (hBJ L hL).imp fun B hB n i hi => hB n i (by omega))
      (fun L hL => (hBη L hL).imp fun B hB n i hi => hB n i (by omega)) hJ2 hu hK
      (ih (by omega)) hUc hUΩ

/-! ### Compactness -/

/-- Bounds for the `u n` in `W^{k,p}(W)` bound their coordinates in a basis in the space
`Wkp volume W p k`, uniformly in `n`. -/
private theorem exists_forall_wkp_repr_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ} {W : Opens ℂ}
    {ι : Type*} (b : Module.Basis ι ℝ V) (i : ι) {u : ℕ → ℂ → V} {R : ℝ≥0}
    (hR : ∀ n, eLpNormWkp p W k (u n) ≤ R) :
    ∃ R' : ℝ, ∀ n, ∃ y : Wkp volume W p k,
      ‖y‖ ≤ R' ∧ Wkp.value k y =ᵐ[volume.restrict W] fun z => b.repr (u n z) i := by
  let c : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  have hcR : ‖c‖ₑ * (R : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top eNorm_ne_top ENNReal.coe_ne_top
  refine ⟨(‖c‖ₑ * R).toReal, fun n => ?_⟩
  have hcn : eLpNormWkp p W k (fun z => c (u n z)) ≤ ‖c‖ₑ * R :=
    (eLpNormWkp_clm_comp_le c).trans (by gcongr; exact hR n)
  obtain ⟨y, hy, hyn⟩ := exists_wkp_norm_le_eLpNormWkp (ne_top_of_le_ne_top hcR hcn)
  exact ⟨y, (ENNReal.ofReal_le_iff_le_toReal hcR).1 (hyn.trans hcn), by simpa [c] using hy⟩

omit [FiniteDimensional ℝ V] in
/-- If the derivatives of order `0` of continuous maps `g n` converge locally uniformly to those
of `g₀`, then `g₀` is continuous and `g (φ n) → g₀` locally uniformly along every `φ → ∞`. -/
private theorem continuous_and_tendstoLocallyUniformly_comp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : ℕ → ℂ × V → G} {g₀ : ℂ × V → G} (hg : ∀ n, Continuous (g n))
    (h : TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ 0 (g n)) (iteratedFDeriv ℝ 0 g₀)
      atTop) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    Continuous g₀ ∧ TendstoLocallyUniformly (fun n => g (φ n)) g₀ atTop := by
  have h0 := tendstoLocallyUniformlyOn_univ.1 (tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1
    (tendstoLocallyUniformlyOn_univ.2 h))
  exact ⟨h0.continuous (.of_forall hg), h0.comp_tendsto hφ⟩

/-- **Passage to the limit in the equation.** If `C¹` solutions `u n` of the equations for
`(J n, η n)` converge pointwise on `Ω` with their derivatives to a `C¹` map `v`, and the frozen
coefficients converge pointwise to those of `(J, η)` along `v`, then `v` solves the equation for
`(J, η)`. -/
private theorem isWeakCauchyRiemannOn_of_tendsto {p : ℝ≥0∞} {J : ℕ → ℂ → V → V →L[ℝ] V}
    {η : ℕ → ℂ → V → V} {J₀ : ℂ → V → V →L[ℝ] V} {η₀ : ℂ → V → V} {u : ℕ → ℂ → V}
    {v : ℂ → V} (hu : ∀ n, ContDiffOn ℝ 1 (u n) Ω)
    (hJu : ∀ n, ContinuousOn (fun z => J n z (u n z)) Ω)
    (hηu : ∀ n, ContinuousOn (fun z => η n z (u n z)) Ω)
    (hsol : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n)) (hv : ContDiffOn ℝ 1 v Ω)
    (hJv : ContinuousOn (fun z => J₀ z (v z)) Ω) (hηv : ContinuousOn (fun z => η₀ z (v z)) Ω)
    (hJ : ∀ z ∈ Ω, Tendsto (fun n => J n z (u n z)) atTop (𝓝 (J₀ z (v z))))
    (hη : ∀ z ∈ Ω, Tendsto (fun n => η n z (u n z)) atTop (𝓝 (η₀ z (v z))))
    (hD : ∀ z ∈ Ω, ∀ w, Tendsto (fun n => fderiv ℝ (u n) z w) atTop (𝓝 (fderiv ℝ v z w))) :
    IsWeakCauchyRiemannOn p Ω J₀ η₀ v := by
  refine (isWeakCauchyRiemannOn_iff_of_contDiffOn hv hJv hηv).2 fun z hz => ?_
  have heq (n : ℕ) := (isWeakCauchyRiemannOn_iff_of_contDiffOn (hu n) (hJu n) (hηu n)).1
    (hsol n) z hz
  refine tendsto_nhds_unique (((hD z hz 1).add ((isBoundedBilinearMap_apply.continuous.tendsto
    _).comp ((hJ z hz).prodMk_nhds (hD z hz I)))).congr fun n => ?_) (hη z hz)
  exact heq n

/-- The compactness part for a finite exponent: under the hypotheses of the uniform estimates,
with data bounded in `C^ℓ` on compact sets, a subsequence of the `u n` converges in `C^ℓ` on
compact subsets of `Ω` to a map of class `C^ℓ` on `Ω`, by Rellich's theorem. -/
private theorem exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv {p : ℝ≥0∞} (hp : 2 < p)
    (hp' : p ≠ ⊤) {ℓ : ℕ} {J : ℕ → ℂ → V → V →L[ℝ] V} {η : ℕ → ℂ → V → V} {u : ℕ → ℂ → V}
    (hJ : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => J n x.1 x.2))
    (hη : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => η n x.1 x.2))
    (hBJ : ∀ L : Set (ℂ × V), IsCompact L → ∃ B : ℝ, ∀ n, ∀ i ≤ ℓ, ∀ x ∈ L,
      ‖iteratedFDeriv ℝ i (fun x : ℂ × V => J n x.1 x.2) x‖ ≤ B)
    (hBη : ∀ L : Set (ℂ × V), IsCompact L → ∃ B : ℝ, ∀ n, ∀ i ≤ ℓ, ∀ x ∈ L,
      ‖iteratedFDeriv ℝ i (fun x : ℂ × V => η n x.1 x.2) x‖ ≤ B)
    (hJ2 : ∀ n, ∀ᵐ z ∂volume.restrict Ω, J n z (u n z) * J n z (u n z) = -1)
    (hu : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (hd : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ c : ℝ≥0, ∀ n, ∃ D, HasWeakFDerivOn volume W (u n) D ∧ eLpNorm D p (volume.restrict W) ≤ c) :
    ∃ (φ : ℕ → ℕ) (v : ℂ → V), StrictMono φ ∧ ContDiffOn ℝ ℓ v Ω ∧ ∀ i ≤ ℓ,
      TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (u (φ n))) (iteratedFDeriv ℝ i v)
        atTop Ω := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  obtain ⟨φ, hφ, v, -, hv, hconv⟩ :=
    (Module.finBasis ℝ V).exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn_iteratedFDeriv hp
      fun W hWc hWΩ i => (exists_eLpNormWkp_le_of_isWeakCauchyRiemannOn hp hp' hJ hη hBJ hBη hJ2 hu
        hK hd hWc hWΩ).elim fun _ hR => exists_forall_wkp_repr_le _ i hR
  exact ⟨φ, v, hφ, hv, hconv u (fun n => (hu n).continuousOn) fun n => .rfl⟩

/-- **Compactness for the nonlinear Cauchy–Riemann equation** (McDuff–Salamon, Theorem B.4.2
and Remark B.4.3, planar interior case). Let `p > 2`, possibly `p = ∞`, and `ℓ ≥ 1`. Let `J n`
and `η n` be of class `C^ℓ` jointly in `(z, x)`, converging to `J₀` and `η₀` in `C^ℓ` on compact
subsets of `ℂ × V`: their derivatives of orders at most `ℓ` converge locally uniformly. Let `u n`
be weak solutions on `Ω` of `∂ₛu + J n (z, u) ∂ₜu = η n (z, u)` with `J n (z, u n z)² = -1`
almost everywhere, such that the images under the `u n` of each compact `K ⊆ Ω` lie in one
compact set and, on each open `W` with compact closure in `Ω`, their weak derivatives are bounded
in `Lᵖ(W)`. Then a subsequence `u (φ n)` converges in `C^ℓ` on compact subsets of `Ω` to a map
`v`, of class `C^ℓ` on `Ω`, that solves the limiting equation `∂ₛv + J₀ (z, v) ∂ₜv = η₀ (z, v)`.
-/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn {p : ℝ≥0∞}
    (hp : 2 < p) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {J : ℕ → ℂ → V → V →L[ℝ] V}
    {η : ℕ → ℂ → V → V} {J₀ : ℂ → V → V →L[ℝ] V} {η₀ : ℂ → V → V} {u : ℕ → ℂ → V}
    (hJ : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => J n x.1 x.2))
    (hη : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => η n x.1 x.2))
    (hJt : ∀ i ≤ ℓ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => J n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => J₀ x.1 x.2)) atTop)
    (hηt : ∀ i ≤ ℓ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => η n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => η₀ x.1 x.2)) atTop)
    (hJ2 : ∀ n, ∀ᵐ z ∂volume.restrict Ω, J n z (u n z) * J n z (u n z) = -1)
    (hu : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (hd : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ c : ℝ≥0, ∀ n, ∃ D, HasWeakFDerivOn volume W (u n) D ∧ eLpNorm D p (volume.restrict W) ≤ c) :
    ∃ (φ : ℕ → ℕ) (v : ℂ → V), StrictMono φ ∧ ContDiffOn ℝ ℓ v Ω ∧
      IsWeakCauchyRiemannOn p Ω J₀ η₀ v ∧ ∀ i ≤ ℓ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (u (φ n))) (iteratedFDeriv ℝ i v) atTop Ω := by
  -- Pass to the finite exponent `q = min p 3 > 2` for the estimates.
  have hq : 2 < min p 3 := lt_min hp (by norm_num)
  have hq' : min p 3 ≠ ⊤ := ((min_le_right _ _).trans_lt (by norm_num)).ne
  -- The data are bounded in `C^ℓ` on compact sets, so the uniform estimates apply; read in the
  -- coordinates of a basis, they are bounds in the spaces `Wkp`.
  have hdq (W : Opens ℂ) (hWc : IsCompact (closure (W : Set ℂ)))
      (hWΩ : closure (W : Set ℂ) ⊆ Ω) : ∃ c : ℝ≥0, ∀ n, ∃ D, HasWeakFDerivOn volume W (u n) D ∧
        eLpNorm D (min p 3) (volume.restrict W) ≤ c := by
    obtain ⟨c, hc⟩ := hd W hWc hWΩ
    have : IsFiniteMeasure (volume.restrict (W : Set ℂ)) := isFiniteMeasure_restrict.2
      ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne
    obtain ⟨c', hc'⟩ := MeasureTheory.exists_eLpNorm_le_mul_eLpNorm_of_le
      (μ := volume.restrict (W : Set ℂ)) (E := ℂ →L[ℝ] V) (min_le_left p 3)
    refine ⟨c' * c, fun n => ?_⟩
    obtain ⟨D, hD, hDc⟩ := hc n
    exact ⟨D, hD, (hc' D).trans (by push_cast; gcongr)⟩
  obtain ⟨φ, v, hφ, hv, hconv⟩ := exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv hq hq'
    hJ hη (fun _ => exists_forall_norm_iteratedFDeriv_le_of_tendstoLocallyUniformly hJ hJt)
    (fun _ => exists_forall_norm_iteratedFDeriv_le_of_tendstoLocallyUniformly hη hηt) hJ2
    (fun n => (hu n).mono_exponent (min_le_left _ _)) hK hdq
  refine ⟨φ, v, hφ, hv, ?_, hconv⟩
  -- Each `u n` is `C^ℓ`, and its pointwise equation passes to the limit.
  have hℓ1 : (1 : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hℓ
  have hun (n : ℕ) : ContDiffOn ℝ 1 (u n) Ω :=
    (contDiffOn_of_isWeakCauchyRiemannOn hp isOpen_univ (hJ n).contDiffOn (hη n).contDiffOn
      (fun _ _ => mem_univ _) (hJ2 n) (hu n)).of_le (by exact_mod_cast hℓ1)
  have hgraph (n : ℕ) : ContinuousOn (fun z => ((z, u n z) : ℂ × V)) Ω :=
    continuousOn_id.prodMk (hu n).continuousOn
  have hval (z : ℂ) (hz : z ∈ Ω) : Tendsto (fun n => u (φ n) z) atTop (𝓝 (v z)) :=
    (tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hconv 0 (Nat.zero_le ℓ))).tendsto_at hz
  have hvg : ContinuousOn (fun z => ((z, v z) : ℂ × V)) Ω := continuousOn_id.prodMk hv.continuousOn
  -- The data converge locally uniformly along the subsequence, to continuous limits.
  obtain ⟨hJc, hφJ⟩ := continuous_and_tendstoLocallyUniformly_comp (fun n => (hJ n).continuous)
    (hJt 0 (Nat.zero_le ℓ)) hφ.tendsto_atTop
  obtain ⟨hηc, hφη⟩ := continuous_and_tendstoLocallyUniformly_comp (fun n => (hη n).continuous)
    (hηt 0 (Nat.zero_le ℓ)) hφ.tendsto_atTop
  refine isWeakCauchyRiemannOn_of_tendsto (fun n => hun (φ n))
    (fun n => (hJ (φ n)).continuous.comp_continuousOn (hgraph (φ n)))
    (fun n => (hη (φ n)).continuous.comp_continuousOn (hgraph (φ n))) (fun n => hu (φ n))
    (hv.of_le (by exact_mod_cast hℓ1)) (hJc.comp_continuousOn hvg) (hηc.comp_continuousOn hvg)
    (fun z hz => hφJ.tendsto_comp hJc.continuousAt (tendsto_const_nhds.prodMk_nhds (hval z hz)))
    (fun z hz => hφη.tendsto_comp hηc.continuousAt (tendsto_const_nhds.prodMk_nhds (hval z hz)))
    fun z hz w => ?_
  simpa [Function.comp_def, iteratedFDeriv_one_apply] using
    ((continuous_eval_const (fun _ : Fin 1 => w)).tendsto _).comp ((hconv 1 hℓ).tendsto_at hz)

/-- **Smooth compactness for the nonlinear Cauchy–Riemann equation** (McDuff–Salamon, Theorem
B.4.2 and Remark B.4.3, planar interior case, for smooth data). Let `p > 2`, possibly `p = ∞`. Let
`J n` and `η n` be smooth jointly in `(z, x)`, converging to `J₀` and `η₀` in `C^∞` on compact
subsets of `ℂ × V`: their derivatives of every order converge locally uniformly. Let `u n` be weak
solutions on `Ω` of `∂ₛu + J n (z, u) ∂ₜu = η n (z, u)` with `J n (z, u n z)² = -1` almost
everywhere, such that the images under the `u n` of each compact `K ⊆ Ω` lie in one compact set
and, on each open `W` with compact closure in `Ω`, their weak derivatives are bounded in `Lᵖ(W)`.
Then a subsequence `u (φ n)` converges in `C^∞` on compact subsets of `Ω` to a map `v`, smooth on
`Ω`, that solves the limiting equation `∂ₛv + J₀ (z, v) ∂ₜv = η₀ (z, v)`. -/
theorem exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn {p : ℝ≥0∞}
    (hp : 2 < p) {J : ℕ → ℂ → V → V →L[ℝ] V} {η : ℕ → ℂ → V → V} {J₀ : ℂ → V → V →L[ℝ] V}
    {η₀ : ℂ → V → V} {u : ℕ → ℂ → V}
    (hJ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ × V => J n x.1 x.2))
    (hη : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ × V => η n x.1 x.2))
    (hJt : ∀ i : ℕ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => J n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => J₀ x.1 x.2)) atTop)
    (hηt : ∀ i : ℕ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => η n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => η₀ x.1 x.2)) atTop)
    (hJ2 : ∀ n, ∀ᵐ z ∂volume.restrict Ω, J n z (u n z) * J n z (u n z) = -1)
    (hu : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (hd : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ c : ℝ≥0, ∀ n, ∃ D, HasWeakFDerivOn volume W (u n) D ∧ eLpNorm D p (volume.restrict W) ≤ c) :
    ∃ (φ : ℕ → ℕ) (v : ℂ → V), StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧
      IsWeakCauchyRiemannOn p Ω J₀ η₀ v ∧ ∀ k : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ k (u (φ n))) (iteratedFDeriv ℝ k v) atTop Ω := by
  have hℓ (ℓ : ℕ) : (ℓ : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := by exact_mod_cast le_top
  -- Along every subsequence, the compactness theorem of each order `ℓ ≥ 1` applies.
  have hsub (ℓ : ℕ) (h1 : 1 ≤ ℓ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :=
    exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn hp h1
      (u := fun n => u (ψ n)) (fun n => (hJ (ψ n)).of_le (hℓ ℓ))
      (fun n => (hη (ψ n)).of_le (hℓ ℓ)) (fun i _ => (hJt i).comp_tendsto hψ.tendsto_atTop)
      (fun i _ => (hηt i).comp_tendsto hψ.tendsto_atTop) (fun n => hJ2 (ψ n)) (fun n => hu (ψ n))
      (fun K hKΩ hKc => (hK K hKΩ hKc).imp fun _ h => ⟨h.1, fun n => h.2 (ψ n)⟩)
      fun W hWc hWΩ => (hd W hWc hWΩ).imp fun _ h n => h (ψ n)
  -- A diagonal subsequence converges in every order to a smooth map `v`.
  obtain ⟨σ, hσ, v, hv, hconv⟩ :=
    Ω.isOpen.exists_strictMono_forall_tendstoLocallyUniformlyOn_iteratedFDeriv
      (fun n => contDiffOn_of_isWeakCauchyRiemannOn hp (ℓ := ⊤) isOpen_univ (hJ n).contDiffOn
        (hη n).contDiffOn (fun _ _ => mem_univ _) (hJ2 n) (hu n)) fun k ψ hψ => by
      obtain ⟨ψ', w, hψ', -, -, hw⟩ := hsub (k + 1) (Nat.le_add_left 1 k) ψ hψ
      exact ⟨ψ', hψ', _, hw k (Nat.le_succ k)⟩
  -- The case `ℓ = 1` along a further subsequence gives a solution, which agrees with `v` on `Ω`.
  obtain ⟨ψ', w, hψ', -, hw, hconv'⟩ := hsub 1 le_rfl σ hσ
  have hvw : EqOn w v Ω := fun z hz => tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hconv' 0 (Nat.zero_le 1))).tendsto_at hz)
    (((tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hconv 0)).comp_tendsto
      hψ'.tendsto_atTop).tendsto_at hz)
  exact ⟨σ, v, hσ, hv, hw.congr hvw, hconv⟩

/-! ### Gradient bounds -/

omit [FiniteDimensional ℝ V] in
/-- **Gradient bounds bound the weak derivatives in `Lᵖ`.** If the maps `u n` are `C¹` on `Ω` and
their classical derivatives are bounded on each compact subset of `Ω` uniformly in `n`, then on each
open `W` with compact closure in `Ω` the `u n` have weak derivatives bounded in `Lᵖ(W)` uniformly
in `n`, namely their classical derivatives. This is the derivative hypothesis of the compactness
theorems above. -/
theorem exists_forall_hasWeakFDerivOn_eLpNorm_le_of_norm_fderiv_le [CompleteSpace V] {p : ℝ≥0∞}
    {u : ℕ → ℂ → V}
    (hu : ∀ n, ContDiffOn ℝ 1 (u n) Ω)
    (hC : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C : ℝ, ∀ n, ∀ z ∈ K, ‖fderiv ℝ (u n) z‖ ≤ C)
    (W : Opens ℂ) (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ c : ℝ≥0, ∀ n, ∃ D, HasWeakFDerivOn volume W (u n) D ∧
      eLpNorm D p (volume.restrict W) ≤ c := by
  obtain ⟨C, hC⟩ := hC _ hWΩ hWc
  obtain ⟨c, hc⟩ := exists_eLpNorm_le_of_ae_norm_le (E := ℂ →L[ℝ] V) (p := p)
    ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne C
  have huW (n : ℕ) : ContDiffOn ℝ 1 (u n) W := (hu n).mono (subset_closure.trans hWΩ)
  exact ⟨c, fun n => ⟨fderiv ℝ (u n), (huW n).hasWeakFDerivOn_fderiv, hc _
    (((huW n).continuousOn_fderiv_of_isOpen W.isOpen le_rfl).aestronglyMeasurable
      W.isOpen.measurableSet)
    ((ae_restrict_mem W.isOpen.measurableSet).mono fun z hz => hC n z (subset_closure hz))⟩⟩

/-- **`C^ℓ` compactness under gradient bounds.** The compactness theorem
`TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn` for `ℓ ≥ 1` and data
converging in `C^ℓ`, with the `Lᵖ` bound on the weak derivatives replaced by a bound on `‖du n‖` on
each compact `K ⊆ Ω`, uniform in `n`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_of_norm_fderiv_le
    {p : ℝ≥0∞} (hp : 2 < p) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {J : ℕ → ℂ → V → V →L[ℝ] V}
    {η : ℕ → ℂ → V → V} {J₀ : ℂ → V → V →L[ℝ] V} {η₀ : ℂ → V → V} {u : ℕ → ℂ → V}
    (hJ : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => J n x.1 x.2))
    (hη : ∀ n, ContDiff ℝ ℓ (fun x : ℂ × V => η n x.1 x.2))
    (hJt : ∀ i ≤ ℓ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => J n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => J₀ x.1 x.2)) atTop)
    (hηt : ∀ i ≤ ℓ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => η n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => η₀ x.1 x.2)) atTop)
    (hJ2 : ∀ n, ∀ᵐ z ∂volume.restrict Ω, J n z (u n z) * J n z (u n z) = -1)
    (hu : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (hC : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C : ℝ, ∀ n, ∀ z ∈ K, ‖fderiv ℝ (u n) z‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (v : ℂ → V), StrictMono φ ∧ ContDiffOn ℝ ℓ v Ω ∧
      IsWeakCauchyRiemannOn p Ω J₀ η₀ v ∧ ∀ i ≤ ℓ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (u (φ n))) (iteratedFDeriv ℝ i v) atTop Ω := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  exact exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn hp hℓ hJ hη hJt hηt hJ2
    hu hK (exists_forall_hasWeakFDerivOn_eLpNorm_le_of_norm_fderiv_le (fun n =>
      (contDiffOn_of_isWeakCauchyRiemannOn hp (ℓ := ℓ) isOpen_univ (hJ n).contDiffOn
        (hη n).contDiffOn (fun _ _ => mem_univ _) (hJ2 n) (hu n)).of_le
        (by exact_mod_cast hℓ)) hC)

/-- **Compactness under gradient bounds** (McDuff–Salamon, Theorem 4.1.1, planar case). Let
`p > 2`, possibly `p = ∞`. Let `J n` and `η n` be smooth jointly in `(z, x)`, converging to `J₀`
and `η₀` in `C^∞` on compact subsets of `ℂ × V`; fixed data `J` and `η` are the constant sequences,
by `TauCeti.tendstoLocallyUniformly_const`. Let `u n` be weak solutions on `Ω` of
`∂ₛu + J n (z, u) ∂ₜu = η n (z, u)` with `J n (z, u n z)² = -1` almost everywhere, such that the
images under the `u n` of each compact `K ⊆ Ω` lie in one compact set and `‖du n‖` is bounded on
each compact `K ⊆ Ω` uniformly in `n`. Then a subsequence `u (φ n)` converges in `C^∞` on compact
subsets of `Ω` to a map `v`, smooth on `Ω`, that solves the limiting equation
`∂ₛv + J₀ (z, v) ∂ₜv = η₀ (z, v)`.

The image bound is needed: for `J = i` and `η = 0` on the unit disc, the constant solutions `m`
satisfy the gradient bound, but their images lie in no fixed compact set
(`TauCeti.Analysis.Complex.CauchyRiemann.Weak.Compactness.Checks`). The maps `z ↦ z / m` satisfy
both bounds and converge with every derivative to the solution `0`. -/
theorem
    exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_of_norm_fderiv_le
    {p : ℝ≥0∞} (hp : 2 < p) {J : ℕ → ℂ → V → V →L[ℝ] V} {η : ℕ → ℂ → V → V}
    {J₀ : ℂ → V → V →L[ℝ] V} {η₀ : ℂ → V → V} {u : ℕ → ℂ → V}
    (hJ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ × V => J n x.1 x.2))
    (hη : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ × V => η n x.1 x.2))
    (hJt : ∀ i : ℕ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => J n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => J₀ x.1 x.2)) atTop)
    (hηt : ∀ i : ℕ, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ i (fun x : ℂ × V => η n x.1 x.2))
      (iteratedFDeriv ℝ i (fun x : ℂ × V => η₀ x.1 x.2)) atTop)
    (hJ2 : ∀ n, ∀ᵐ z ∂volume.restrict Ω, J n z (u n z) * J n z (u n z) = -1)
    (hu : ∀ n, IsWeakCauchyRiemannOn p Ω (J n) (η n) (u n))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set V, IsCompact K' ∧ ∀ n, MapsTo (u n) K K')
    (hC : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C : ℝ, ∀ n, ∀ z ∈ K, ‖fderiv ℝ (u n) z‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (v : ℂ → V), StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧
      IsWeakCauchyRiemannOn p Ω J₀ η₀ v ∧ ∀ k : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ k (u (φ n))) (iteratedFDeriv ℝ k v) atTop Ω := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  exact exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn hp hJ hη hJt hηt
    hJ2 hu hK (exists_forall_hasWeakFDerivOn_eLpNorm_le_of_norm_fderiv_le (fun n =>
      (contDiffOn_of_isWeakCauchyRiemannOn hp (ℓ := ⊤) isOpen_univ (hJ n).contDiffOn
        (hη n).contDiffOn (fun _ _ => mem_univ _) (hJ2 n) (hu n)).of_le
        (by exact_mod_cast le_top)) hC)

end TauCeti
