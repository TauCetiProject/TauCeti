/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.BumpFunction.HolderApproximation
import TauCeti.Analysis.Holder.JetBounds
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Laplacian
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Newtonian potential of Hölder continuous data

Let `n ≥ 3` and let `f : ℝⁿ → ℝ` have compact support and be `α`-Hölder, `0 < α ≤ 1`. The
Newtonian potential `w = Gₙ ⋆ f` was known to solve Poisson's equation for `C²` data
(`TauCeti.laplacian_newtonianKernel_convolution`). This file extends it to Hölder data, which is
the setting of the classical Schauder theory:

* `w` is `C²` (`TauCeti.contDiff_newtonianKernel_convolution_of_holderWith`) and solves `-Δw = f` at
  every point (`TauCeti.laplacian_newtonianKernel_convolution_of_holderWith`), as in
  Gilbarg–Trudinger, Lemma 4.2;
* for `0 < α < 1` its Hessian is globally `α`-Hölder with `[D²w]_α ≤ C [f]_α`, where `C` depends
  only on `n` and `α` (`TauCeti.exists_holderWith_iteratedFDeriv_two_newtonianKernel_convolution`),
  the whole-space form of Gilbarg–Trudinger, Lemma 4.4.

Continuity of `f` alone does not suffice: there is continuous data for which Poisson's equation
has no `C²` solution near the origin
(`TauCeti.PDE.not_exists_contDiffOn_laplacian_eq_laplacianQuadraticSqrtNegLog`). The argument uses
that the potential of bounded data vanishing outside a ball is bounded
(`TauCeti.exists_norm_newtonianKernel_convolution_le`); this is where `n ≥ 3` enters. The plane,
with the logarithmic kernel `TauCeti.planarNewtonianKernel`, is not treated here.

## The argument

Mollification gives smooth `g k`, supported in one ball, `α`-Hölder with the constant of `f` and
converging to `f` uniformly (`TauCeti.exists_contDiff_support_subset_holderWith_tendstoUniformly`).
Their potentials `w k = Gₙ ⋆ g k` are smooth, and their derivatives, which are potentials of the
derivatives of `g k`, are bounded. So they lie in the Banach space `C_b^{2,β}` for `β = α / 2`. The
global Schauder estimate (`TauCeti.PDE.exists_norm_le_of_sum_smul_fderiv_fderiv`) bounds the
`C_b^{2,β}` norm of `w k - w l` by `[g k - g l]_β + sup |w k - w l|`. The second term is at most
a constant times `sup |g k - g l|`. The first tends to zero by interpolating between the
common `α`-Hölder bound and uniform convergence. So the `w k` form a Cauchy sequence. Its limit
is `w`, which is therefore `C²`, and `Δw = -f` follows from `Δ(w k) = -g k` in the limit. The
global estimate at the exponent `α` gives one Hölder constant for all `D²(w k)`, which passes to
`D²w`. The scale-invariant estimate for the Laplacian
(`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_holderWith_laplacian`) then removes the
dependence on the size of `w`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.2, Lemmas 4.2 and 4.4.
-/

public section

noncomputable section

open ContinuousLinearMap Filter InnerProductSpace Laplacian MeasureTheory Metric Set Topology
open scoped Convolution NNReal ContDiff

namespace TauCeti

variable {n : ℕ}

/-- The scalar case of `TauCeti.exists_norm_newtonianKernel_convolution_le`: the potential of a
function bounded by `D` and vanishing outside `closedBall 0 R` is bounded by `D C`. -/
private theorem exists_norm_newtonianKernel_convolution_le_mul (hn : 3 ≤ n) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : EuclideanSpace ℝ (Fin n) → ℝ} {D : ℝ},
      (∀ y, ‖g y‖ ≤ D) → Function.support g ⊆ closedBall 0 R →
      ∀ x, ‖(newtonianKernel n ⋆ g) x‖ ≤ D * C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_newtonianKernel_convolution_le (G := ℝ) (H := ℝ) hn R
  refine ⟨C, hC0, fun {g D} hD hs x ↦ (hC _ hD hs x).trans ?_⟩
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  calc ‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * D * C ≤ 1 * D * C := by
        gcongr; exact opNorm_lsmul_le
    _ = D * C := by ring

section Smooth

variable {g : EuclideanSpace ℝ (Fin n) → ℝ}

/-- For `n ≥ 3`, the Hessian of the Newtonian potential of a smooth function with compact support
is bounded and Lipschitz, so it is `β`-Hölder for every `β ≤ 1`. -/
private theorem memHolder_iteratedFDeriv_two_newtonianKernel_convolution (hn : 3 ≤ n)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {β : ℝ≥0} (hβ : β ≤ 1) :
    MemHolder β (iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ g)) := by
  obtain ⟨C₂, hC₂⟩ := exists_norm_iteratedFDeriv_newtonianKernel_convolution_le hn 2
    (hg.of_le (by norm_cast)) hc
  obtain ⟨C₃, hC₃⟩ := exists_norm_iteratedFDeriv_newtonianKernel_convolution_le hn 3
    (hg.of_le (by norm_cast)) hc
  have hw : ContDiff ℝ 3 (newtonianKernel n ⋆ g) :=
    (contDiff_newtonianKernel_convolution hg hc).of_le (by norm_cast)
  exact ⟨_, holderOnWith_univ.1 ((hw.contDiffOn (s := univ)).holderOnWith_iteratedFDeriv_of_lt
    (j := 2) isOpen_univ convex_univ (by norm_num) hβ (M := C₂.toNNReal) (L := C₃.toNNReal)
    (fun x _ ↦ (hC₂ x).trans (Real.le_coe_toNNReal C₂))
    (fun x _ ↦ (hC₃ x).trans (Real.le_coe_toNNReal C₃)))⟩

end Smooth

section Approximation

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m + 1))

/-- **The Schauder estimate for potentials of smooth data, by interpolation.** For `n = m + 1 ≥ 3`,
`R`, and exponents `0 < β < α`, `β < 1`, there is a constant `C` such that the potential of every
smooth `g` vanishing outside `closedBall 0 R`, `α`-Hölder with constant `K` and bounded by `D`, lies
in `C_b^{2,β}` with norm at most `C (K δ^(α - β) + D δ^(-β) + D)` for every `δ > 0`. -/
private theorem exists_norm_le_of_newtonianKernel_convolution (hn : 3 ≤ m + 1) (R : ℝ)
    {α β : ℝ≥0} (hβ : 0 < β) (hβα : β < α) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : E → ℝ} {K : ℝ≥0} {D δ : ℝ}, ContDiff ℝ ∞ g →
      Function.support g ⊆ closedBall 0 R → HolderWith K α g → (∀ x, ‖g x‖ ≤ D) → 0 < δ →
      ∃ W : CkHolderSpace 2 β E ℝ, ⇑W = newtonianKernel (m + 1) ⋆ g ∧
        ‖W‖ ≤ C * (K * δ ^ ((α : ℝ) - β) + D * δ ^ (-(β : ℝ)) + D) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_newtonianKernel_convolution_le_mul hn R
  obtain ⟨C₁, hC₁⟩ := PDE.exists_norm_le_of_sum_smul_fderiv_fderiv (n := m) hβ hβ1 1 1 0
  refine ⟨C₁ * (2 + C₀), by positivity, fun {g K D δ} hg hs hgK hD hδ ↦ ?_⟩
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hc : HasCompactSupport g := .of_support_subset_isCompact (isCompact_closedBall _ _) hs
  let W : CkHolderSpace 2 β E ℝ :=
    CkHolderSpace.ofContDiff _ ((contDiff_newtonianKernel_convolution hg hc).of_le (by norm_cast))
      (fun i _ ↦ exists_norm_iteratedFDeriv_newtonianKernel_convolution_le hn i
        (hg.of_le (mod_cast le_top)) hc)
      (memHolder_iteratedFDeriv_two_newtonianKernel_convolution hn hg hc hβ1.le)
  refine ⟨W, CkHolderSpace.coe_ofContDiff _ _ _ _, ?_⟩
  -- The potential is bounded by `D C₀`.
  have hN : ∀ x, |W x| ≤ (D * C₀).toNNReal := fun x ↦ by
    rw [CkHolderSpace.coe_ofContDiff, Real.coe_toNNReal _ (mul_nonneg hD0 hC₀0)]
    exact hC₀ hD hs x
  -- Its Laplacian `-g` is `β`-Hölder: use `K` below the scale `δ` and the bound `D` above it.
  have hK : HolderWith (K * δ.toNNReal ^ ((α : ℝ) - β) + 2 * D.toNNReal * δ.toNNReal ^ (-(β : ℝ)))
      β (fun x ↦ ∑ i, ∑ j, (fun _ ↦ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) x i j •
        fderiv ℝ (fderiv ℝ ⇑W) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    simp only [PDE.sum_one_smul_fderiv_fderiv_eq_laplacian, W, CkHolderSpace.coe_ofContDiff,
      laplacian_newtonianKernel_convolution (by omega) (by omega) (hg.of_le (by norm_cast)) hc]
    exact hgK.neg.of_le_of_norm_le (fun x ↦ by
      simpa only [Pi.neg_apply, norm_neg] using (hD x).trans (Real.le_coe_toNNReal D)) hβα.le
      (Real.toNNReal_pos.2 hδ)
  have hle := hC₁ (PDE.uniformlyEllipticOn_const_one_one univ) (fun _ _ ↦ HolderWith.const)
    W hN hK
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ hδ.le,
    Real.coe_toNNReal _ hD0, Real.coe_toNNReal _ (mul_nonneg hD0 hC₀0), NNReal.coe_ofNat] at hle
  have hx : 0 ≤ (K : ℝ) * δ ^ ((α : ℝ) - β) := by positivity
  have hy : 0 ≤ D * δ ^ (-(β : ℝ)) := by positivity
  -- Compare the three terms one at a time against `2 + C₀` times the corresponding term.
  calc ‖W‖ ≤ C₁ * (K * δ ^ ((α : ℝ) - β) + 2 * D * δ ^ (-(β : ℝ)) + D * C₀) := hle
    _ ≤ C₁ * ((2 + C₀) * (K * δ ^ ((α : ℝ) - β)) + (2 + C₀) * (D * δ ^ (-(β : ℝ))) +
          (2 + C₀) * D) := by
        gcongr C₁ * (?_ + ?_ + ?_)
        · exact le_mul_of_one_le_left hx (by linarith)
        · rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) hy
        · rw [mul_comm D]
          exact mul_le_mul_of_nonneg_right (by linarith) hD0
    _ = C₁ * (2 + C₀) * (K * δ ^ ((α : ℝ) - β) + D * δ ^ (-(β : ℝ)) + D) := by ring

/-- **The potentials of convergent smooth data form a Cauchy sequence in `C_b^{2,β}`.** Let `g k`
be smooth, vanish outside one ball, be `α`-Hölder with one constant `H`, and converge uniformly.
Then their potentials, as elements of `C_b^{2,β}` for `0 < β < α` and `β < 1`, form a Cauchy
sequence. -/
private theorem exists_cauchySeq_newtonianKernel_convolution (hn : 3 ≤ m + 1) {R : ℝ}
    {α β H : ℝ≥0} {M : ℝ} (hβ : 0 < β) (hβα : β < α) (hβ1 : β < 1) {g : ℕ → E → ℝ}
    {f : E → ℝ} (hgs : ∀ k, ContDiff ℝ ∞ (g k))
    (hgsupp : ∀ k, Function.support (g k) ⊆ closedBall 0 R) (hgH : ∀ k, HolderWith H α (g k))
    (hgM : ∀ k x, ‖g k x‖ ≤ M) (hglim : TendstoUniformly g f atTop) :
    ∃ W : ℕ → CkHolderSpace 2 β E ℝ, (∀ k, ⇑(W k) = newtonianKernel (m + 1) ⋆ g k) ∧
      CauchySeq W := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_of_newtonianKernel_convolution hn R hβ hβα hβ1
  have hgc : ∀ k, HasCompactSupport (g k) := fun k ↦
    .of_support_subset_isCompact (isCompact_closedBall _ _) (hgsupp k)
  choose W hW using fun k ↦ hC (hgs k) (hgsupp k) (hgH k) (hgM k) one_pos
  refine ⟨W, fun k ↦ (hW k).1, Metric.cauchySeq_iff.2 fun ε hε ↦ ?_⟩
  -- The difference of two potentials is the potential of the difference of the data.
  have hdist : ∀ k l {D δ : ℝ}, (∀ x, ‖g k x - g l x‖ ≤ D) → 0 < δ →
      dist (W k) (W l) ≤ C * ((H + H : ℝ≥0) * δ ^ ((α : ℝ) - β) + D * δ ^ (-(β : ℝ)) + D) := by
    intro k l D δ hD hδ
    obtain ⟨V, hV, hVle⟩ := hC (g := g k - g l) ((hgs k).sub (hgs l))
      ((Function.support_sub _ _).trans (union_subset (hgsupp k) (hgsupp l)))
      (holderOnWith_univ.1 (((hgH k).holderOnWith univ).sub ((hgH l).holderOnWith univ))) hD hδ
    have hVkl : V = W k - W l := by
      ext x
      rw [hV, CkHolderSpace.coe_sub, (hW k).1, (hW l).1, newtonianKernel_convolution_sub
        (hgs k).continuous (hgc k) (hgs l).continuous (hgc l)]
    rw [dist_eq_norm, ← hVkl]
    exact hVle
  -- Choose the scale `δ`, then the uniform closeness `η` of the data.
  have hαβ : (0 : ℝ) < (α : ℝ) - β := sub_pos.2 (by exact_mod_cast hβα)
  obtain ⟨δ, hδ, -, hδε⟩ := Real.exists_pos_le_one_mul_rpow_le (C * (2 * H)) hαβ (half_pos hε)
  set A : ℝ := C * (2 * δ ^ (-(β : ℝ)) + 2)
  have hA : 0 ≤ A := by positivity
  set η : ℝ := ε / (4 * (A + 1))
  have hη : 0 < η := by positivity
  have hAη : A * η < ε / 2 := by
    calc A * η = ε / 2 * (A / (2 * (A + 1))) := by simp only [η]; field_simp; ring
      _ < ε / 2 * 1 := by gcongr; rw [div_lt_one (by positivity)]; linarith
      _ = ε / 2 := mul_one _
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformly_iff.1 hglim) η hη)
  refine ⟨N, fun k hk l hl ↦ ?_⟩
  have hD : ∀ x, ‖g k x - g l x‖ ≤ 2 * η := fun x ↦ by
    have h1 := hN k hk x
    have h2 := hN l hl x
    rw [dist_eq_norm] at h1 h2
    calc ‖g k x - g l x‖ = ‖(f x - g l x) - (f x - g k x)‖ := by congr 1; ring
      _ ≤ ‖f x - g l x‖ + ‖f x - g k x‖ := norm_sub_le _ _
      _ ≤ 2 * η := by linarith
  calc dist (W k) (W l)
      ≤ C * ((H + H : ℝ≥0) * δ ^ ((α : ℝ) - β) + 2 * η * δ ^ (-(β : ℝ)) + 2 * η) :=
        hdist k l hD hδ
    _ = C * (2 * H) * δ ^ ((α : ℝ) - β) + A * η := by push_cast; ring
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hδε hAη
    _ = ε := add_halves ε

/-- **The limit of the potentials is the potential of the limit.** If the potentials of data
`g k` converge in `C_b^{2,β}` and the data converge uniformly to a continuous `f`, all vanishing
outside one ball, then the limit is `Gₙ ⋆ f`, the Hessians converge pointwise, and
`Δ(Gₙ ⋆ g k) = -g k` passes to `Δ(Gₙ ⋆ f) = -f`. -/
private theorem coe_eq_and_tendsto_iteratedFDeriv_two_of_tendsto (hn : 3 ≤ m + 1) {R : ℝ}
    {β : ℝ≥0} {g : ℕ → E → ℝ} {f : E → ℝ} (hgcont : ∀ k, Continuous (g k))
    (hgsupp : ∀ k, Function.support (g k) ⊆ closedBall 0 R) (hfcont : Continuous f)
    (hfsupp : Function.support f ⊆ closedBall 0 R) (hglim : TendstoUniformly g f atTop)
    {W : ℕ → CkHolderSpace 2 β E ℝ} {V : CkHolderSpace 2 β E ℝ}
    (hW : ∀ k, ⇑(W k) = newtonianKernel (m + 1) ⋆ g k) (hV : Tendsto W atTop (𝓝 V))
    (hΔg : ∀ k, Δ (newtonianKernel (m + 1) ⋆ g k) = -g k) :
    ⇑V = newtonianKernel (m + 1) ⋆ f ∧ (∀ x, Tendsto (fun k ↦ iteratedFDeriv ℝ 2 (W k) x) atTop
      (𝓝 (iteratedFDeriv ℝ 2 (newtonianKernel (m + 1) ⋆ f) x))) ∧
      Δ (newtonianKernel (m + 1) ⋆ f) = -f := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_newtonianKernel_convolution_le_mul hn R
  have hV0 : Tendsto (fun k ↦ ‖W k - V‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hV
  -- The values converge both to those of `V` and to those of `Gₙ ⋆ f`.
  have hlimV : ∀ x, Tendsto (fun k ↦ W k x) atTop (𝓝 (V x)) := fun x ↦
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun k ↦ by simpa only [CkHolderSpace.coe_sub, Pi.sub_apply] using (W k - V).norm_apply_le x)
      hV0)
  have hlimf : ∀ x, Tendsto (fun k ↦ W k x) atTop (𝓝 ((newtonianKernel (m + 1) ⋆ f) x)) := by
    intro x
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((Metric.tendstoUniformly_iff.1 hglim) (ε / (C₀ + 1)) (by positivity))
    refine ⟨N, fun k hk ↦ ?_⟩
    have hD : ∀ y, ‖(g k - f) y‖ ≤ ε / (C₀ + 1) := fun y ↦ by
      rw [Pi.sub_apply, norm_sub_rev, ← dist_eq_norm]
      exact (hN k hk y).le
    rw [dist_eq_norm, hW, ← Pi.sub_apply (newtonianKernel (m + 1) ⋆ g k),
      ← newtonianKernel_convolution_sub (hgcont k)
        (.of_support_subset_isCompact (isCompact_closedBall _ _) (hgsupp k)) hfcont
        (.of_support_subset_isCompact (isCompact_closedBall _ _) hfsupp)]
    calc ‖(newtonianKernel (m + 1) ⋆ (g k - f)) x‖ ≤ ε / (C₀ + 1) * C₀ :=
          hC₀ hD ((Function.support_sub _ _).trans (union_subset (hgsupp k) hfsupp)) x
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have hVf : ⇑V = newtonianKernel (m + 1) ⋆ f :=
    funext fun x ↦ tendsto_nhds_unique (hlimV x) (hlimf x)
  -- The Hessians converge to that of `V`, and with them the Laplacians.
  have hlimD : ∀ x, Tendsto (fun k ↦ iteratedFDeriv ℝ 2 (W k) x) atTop
      (𝓝 (iteratedFDeriv ℝ 2 (newtonianKernel (m + 1) ⋆ f) x)) := fun x ↦
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ by
      rw [← hVf, ← iteratedFDeriv_sub_apply (W k).contDiff.contDiffAt V.contDiff.contDiffAt,
        ← CkHolderSpace.coe_sub]
      exact (W k - V).norm_iteratedFDeriv_apply_le le_rfl x) hV0)
  refine ⟨hVf, hlimD, funext fun x ↦ tendsto_nhds_unique (l := atTop)
    (f := fun k ↦ Δ (newtonianKernel (m + 1) ⋆ g k) x) ?_ ?_⟩
  · simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ), ← hW]
    exact tendsto_finsetSum _ fun i _ ↦ ((continuous_eval_const _).tendsto _).comp (hlimD x)
  · simp only [hΔg, Pi.neg_apply]
    exact (hglim.tendsto_at x).neg

end Approximation

/-- **The Newtonian potential of Hölder data.** For `n ≥ 3`, `0 < α < 1` and `f` `α`-Hölder with
compact support, `Gₙ ⋆ f` is `C²` and bounded, solves `-Δ(Gₙ ⋆ f) = f`, and has a globally
`α`-Hölder Hessian. -/
private theorem newtonianKernel_convolution_of_holderWith_aux (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {H α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hf : HolderWith H α f) (hc : HasCompactSupport f) :
    ContDiff ℝ 2 (newtonianKernel n ⋆ f) ∧ Δ (newtonianKernel n ⋆ f) = -f ∧
      (∃ N : ℝ≥0, ∀ x, |(newtonianKernel n ⋆ f) x| ≤ N) ∧
      MemHolder α (iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ f)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Approximate `f` by smooth functions with the same Hölder constant and one support ball.
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨M₀, hM₀⟩ := (hf.continuous hα).bounded_above_of_compact_support hc
  have hM : ∀ x, ‖f x‖ ≤ M₀.toNNReal := fun x ↦ (hM₀ x).trans (Real.le_coe_toNNReal M₀)
  have hsupp : Function.support f ⊆ closedBall 0 R := (subset_tsupport f).trans hR
  obtain ⟨g, hgs, hgsupp, hgH, hgM, hglim⟩ :=
    exists_contDiff_support_subset_holderWith_tendstoUniformly hα hf hM hsupp
  have hgc : ∀ k, HasCompactSupport (g k) := fun k ↦
    .of_support_subset_isCompact (isCompact_closedBall _ _) (hgsupp k)
  have hfsupp : Function.support f ⊆ closedBall 0 (R + 1) :=
    hsupp.trans (closedBall_subset_closedBall (by linarith))
  -- Their potentials converge in `C_b^{2,α/2}` to the potential of `f`.
  have hβ : 0 < α / 2 := div_pos hα two_pos
  have hβα : α / 2 < α := NNReal.half_lt_self hα.ne'
  obtain ⟨W, hW, hcauchy⟩ := exists_cauchySeq_newtonianKernel_convolution hn hβ hβα
    (hβα.trans hα1) hgs hgsupp hgH hgM hglim
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hΔu : ∀ k, Δ (newtonianKernel (m + 1) ⋆ g k) = -g k := fun k ↦
    laplacian_newtonianKernel_convolution (by omega) (by omega) ((hgs k).of_le (by norm_cast))
      (hgc k)
  obtain ⟨hVf, hlimD, hΔ⟩ := coe_eq_and_tendsto_iteratedFDeriv_two_of_tendsto hn
    (fun k ↦ (hgs k).continuous) hgsupp (hf.continuous hα) hfsupp hglim hW hV hΔu
  simp only [hW] at hlimD
  -- The potentials are bounded uniformly, so the whole-space estimate gives one Hölder constant
  -- for the Hessians of the approximants, which passes to the limit.
  obtain ⟨C₀, -, hC₀⟩ := exists_norm_newtonianKernel_convolution_le_mul hn (R + 1)
  set N : ℝ≥0 := ((M₀.toNNReal : ℝ) * C₀).toNNReal
  have hNu : ∀ {a : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}, (∀ y, ‖a y‖ ≤ M₀.toNNReal) →
      Function.support a ⊆ closedBall 0 (R + 1) → ∀ x, |(newtonianKernel (m + 1) ⋆ a) x| ≤ N :=
    fun ha hs x ↦ (hC₀ ha hs x).trans (Real.le_coe_toNNReal _)
  obtain ⟨C₂, hC₂⟩ :=
    PDE.exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv (n := m) hα
      hα1 1 1 0
  have hHk : ∀ k, HolderWith (C₂ * (H + N)) α
      (iteratedFDeriv ℝ 2 (newtonianKernel (m + 1) ⋆ g k)) := fun k ↦ by
    refine (hC₂ (PDE.uniformlyEllipticOn_const_one_one univ) (fun _ _ ↦ HolderWith.const)
      ((contDiff_newtonianKernel_convolution (hgs k) (hgc k)).of_le (by norm_cast))
      (hNu (hgM k) (hgsupp k))
      (memHolder_iteratedFDeriv_two_newtonianKernel_convolution hn (hgs k) (hgc k) hα1.le)
      ?_).1
    simp only [PDE.sum_one_smul_fderiv_fderiv_eq_laplacian, hΔu]
    exact (hgH k).neg
  exact ⟨hVf ▸ V.contDiff, hΔ, ⟨N, hNu hM hfsupp⟩, ⟨_, HolderWith.of_tendsto hlimD
    (Eventually.of_forall hHk)⟩⟩

/-- The `C²` regularity and Poisson's equation for `α ≤ 1`, from the case of the exponent
`α / 2 < 1`: a bounded `α`-Hölder function is `α / 2`-Hölder. -/
private theorem contDiff_and_laplacian_newtonianKernel_convolution_of_holderWith (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {H α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : HolderWith H α f) (hc : HasCompactSupport f) :
    ContDiff ℝ 2 (newtonianKernel n ⋆ f) ∧ Δ (newtonianKernel n ⋆ f) = -f := by
  obtain ⟨M, hM⟩ := (hf.continuous hα).bounded_above_of_compact_support hc
  have hβ : 0 < α / 2 := div_pos hα two_pos
  have hβα : α / 2 < α := NNReal.half_lt_self hα.ne'
  have hf' := hf.of_le_of_norm_le (fun x ↦ (hM x).trans (Real.le_coe_toNNReal M)) hβα.le one_pos
  obtain ⟨h1, h2, -, -⟩ :=
    newtonianKernel_convolution_of_holderWith_aux hn hβ (hβα.trans_le hα1) hf' hc
  exact ⟨h1, h2⟩

/-- **The Newtonian potential of Hölder data is `C²`.** For `n ≥ 3` and `f` `α`-Hölder with
compact support, `0 < α ≤ 1`, the Newtonian potential `Gₙ ⋆ f` is of class `C²`. -/
theorem contDiff_newtonianKernel_convolution_of_holderWith (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {H α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : HolderWith H α f) (hc : HasCompactSupport f) :
    ContDiff ℝ 2 (newtonianKernel n ⋆ f) :=
  (contDiff_and_laplacian_newtonianKernel_convolution_of_holderWith hn hα hα1 hf hc).1

/-- **The Newtonian potential of Hölder data solves Poisson's equation.** For `n ≥ 3` and `f`
`α`-Hölder with compact support, `0 < α ≤ 1`, the Newtonian potential `u = Gₙ ⋆ f` satisfies
`-Δu = f` at every point. -/
theorem laplacian_newtonianKernel_convolution_of_holderWith (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {H α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : HolderWith H α f) (hc : HasCompactSupport f) :
    Δ (newtonianKernel n ⋆ f) = -f :=
  (contDiff_and_laplacian_newtonianKernel_convolution_of_holderWith hn hα hα1 hf hc).2

/-- **The Schauder estimate for the Newtonian potential.** For `n ≥ 3` and `0 < α < 1` there is
a constant `C`, depending only on `n` and `α`, such that for every `f` with compact support that
is `α`-Hölder with constant `H`, the Hessian of the Newtonian potential `Gₙ ⋆ f` is `α`-Hölder
on all of `ℝⁿ` with constant `C H`. -/
theorem exists_holderWith_iteratedFDeriv_two_newtonianKernel_convolution (hn : 3 ≤ n)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ} {H : ℝ≥0}, HolderWith H α f →
      HasCompactSupport f →
      HolderWith (C * H) α (iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ f)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨C, hC⟩ := PDE.exists_holderWith_iteratedFDeriv_two_of_holderWith_laplacian (n := m) hα hα1
  refine ⟨C, fun {f H} hf hc ↦ ?_⟩
  obtain ⟨hw2, hΔ, ⟨N, hN⟩, hw⟩ := newtonianKernel_convolution_of_holderWith_aux hn hα hα1 hf hc
  refine hC hw2 hN hw ?_
  rw [hΔ]
  exact hf.neg

end TauCeti
