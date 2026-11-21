/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Topology.FilledIn
import TauCeti.Analysis.Distribution.JetSpace
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.PDE.FundamentalSolution.CutoffPotential

/-!
# Harmonic Runge approximation on filled-in compact sets

Let `E` be a finite-dimensional real inner product space, `Ω ⊆ E` an open set, and `K ⊆ Ω` a
compact subset that is filled-in within `Ω` (`IsFilledIn K Ω`, i.e., `Ω \ K` has no nonempty
relatively compact connected component in `Ω`). This file proves the harmonic Runge approximation
theorem of Walsh (for uniform convergence) and Lax–Malgrange (in `C^m` by duality and fundamental
solutions): every function `f : E → F` (with `F` finite-dimensional) harmonic on a neighbourhood of
`K` can be approximated in `C^m` norm on `K` by functions harmonic on all of `Ω`.

## Proof strategy

For scalar-valued functions on `E`, we work in the Banach space `TauCeti.JetSpace E ℝ K m` of
continuous `m`-jets on `K` and the submodule `S` of `m`-jets of functions harmonic on `Ω`. By the
Hahn–Banach separation criterion (`Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero`),
`Jf ∈ S.topologicalClosure` reduces to showing that any continuous linear functional `ℓ` on
`TauCeti.JetSpace E ℝ K m` vanishing on `S` also vanishes on `Jf`. Pulling `ℓ` back along the
continuous `m`-jet restriction map `TestFunction.jetRestrictionCLM` produces a compactly supported
distribution `T ∈ 𝓓'(Ω, ℝ)` with `dsupport T ⊆ K`
(`Distribution.dsupport_comp_jetRestrictionCLM_subset`) that annihilates every test function
agreeing near `K` with a global harmonic function on `Ω`. By the Lax–Malgrange harmonic
orthogonality theorem (`Distribution.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd`), `T` also
annihilates a smooth cutoff `TestFunction.smulOfContDiffOn` of `f` equal to `f` near `K`, whence
`ℓ Jf = 0`. A basis of `F` upgrades scalar approximation to finite-dimensional vector values.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt`: harmonic Runge
  approximation in `C^m` on `K` for functions with values in a finite-dimensional real normed space.
* `InnerProductSpace.HarmonicOnNhd.exists_harmonicOnNhd_norm_sub_lt`: uniform (`C^0`) harmonic Runge
  approximation on `K`.

## References

* P. D. Lax, *A stability theorem for solutions of abstract differential equations, and its
  application to the study of the local behavior of solutions of elliptic equations*, Comm. Pure
  Appl. Math. 9 (1956), 747–766.
* B. Malgrange, *Existence et approximation des solutions des équations aux dérivées partielles et
  des équations de convolution*, Ann. Inst. Fourier (Grenoble) 6 (1955–1956), 271–355.
* J. L. Walsh, *The approximation of harmonic functions by harmonic polynomials and by harmonic
  rational functions*, Bull. Amer. Math. Soc. 35 (1929), 499–544.
* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer, 2001.
-/

public section

noncomputable section

open ContDiff Distribution Filter Metric Set TauCeti TopologicalSpace Topology
open scoped ContDiff Distributions

namespace InnerProductSpace

section Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Submodule of `TauCeti.JetSpace E ℝ K m` consisting of `m`-jets on `K` of real-valued functions
harmonic on the open set `Ω`. -/
private def harmonicJetSubmodule {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (m : ℕ) : Submodule ℝ (JetSpace E ℝ K m) where
  carrier := {J | ∃ H : E → ℝ, ∃ hH : HarmonicOnNhd H Ω,
    J = JetSpace.ofContDiffOn hK hΩ hKΩ m
      ((hH.analyticOnNhd.contDiffOn hΩ.uniqueDiffOn).of_le (mod_cast le_top))}
  zero_mem' := ⟨0, harmonicOnNhd_const 0, (JetSpace.ofContDiffOn_zero hK hΩ hKΩ m).symm⟩
  add_mem' := by
    rintro _ _ ⟨H₁, hH₁, rfl⟩ ⟨H₂, hH₂, rfl⟩
    exact ⟨H₁ + H₂, hH₁.add hH₂, (JetSpace.ofContDiffOn_add hK hΩ hKΩ m _ _).symm⟩
  smul_mem' := by
    rintro c _ ⟨H, hH, rfl⟩
    exact ⟨c • H, hH.const_smul, (JetSpace.ofContDiffOn_smul hK hΩ hKΩ m c _).symm⟩

end Submodule

section Approximation

/-- The `m`-jet on a compact set `K` of a scalar function harmonic on a neighbourhood of `K`. -/
private def harmonicJetOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : HarmonicOnNhd f K) (m : ℕ) :
    JetSpace E ℝ K m :=
  JetSpace.ofContDiffOn hK (isOpen_setOfPred_harmonicAt (f := f)) (fun _ hy ↦ hf _ hy) m
    (((HarmonicOnNhd.analyticOnNhd (f := f) fun _ hy ↦ hy).contDiffOn
      (isOpen_setOfPred_harmonicAt (f := f)).uniqueDiffOn).of_le (mod_cast le_top))

@[simp]
private theorem eval_harmonicJetOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : HarmonicOnNhd f K) (m : ℕ)
    (k : Fin (m + 1)) (x : K) :
    (harmonicJetOn hK hf m).eval k x = iteratedFDeriv ℝ (k : ℕ) f x.val :=
  JetSpace.eval_ofContDiffOn ..

/-- A continuous linear functional on `TauCeti.JetSpace E ℝ K m` vanishing on all harmonic `m`-jets
from `Ω` also vanishes on the `m`-jet of any function harmonic on a neighbourhood of `K`, provided
`K` is filled-in within `Ω`. -/
private theorem mem_topologicalClosure_harmonicJetSubmodule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K Ω : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω)
    {f : E → ℝ} (hf : HarmonicOnNhd f K) (m : ℕ) :
    harmonicJetOn hK hf m ∈ (harmonicJetSubmodule hK hΩ hKΩ m).topologicalClosure := by
  set Uf : Set E := {y | HarmonicAt f y}
  have hUf : IsOpen Uf := isOpen_setOfPred_harmonicAt (f := f)
  have hfU : HarmonicOnNhd f Uf := fun _ hy ↦ hy
  have hfU_cd : ContDiffOn ℝ ∞ f Uf := hfU.analyticOnNhd.contDiffOn hUf.uniqueDiffOn
  refine (Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero _ _).2 fun ℓ hℓ ↦ ?_
  let Ωo : Opens E := ⟨Ω, hΩ⟩
  set T := ℓ ∘L TestFunction.jetRestrictionCLM Ωo K m (by exact_mod_cast le_top) with hT_def
  have hTK : dsupport T ⊆ K :=
    Distribution.dsupport_comp_jetRestrictionCLM_subset hK.isClosed m (by exact_mod_cast le_top) ℓ
  have hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ωo, ℝ)),
      HarmonicOnNhd H Ωo → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0 := fun H ψ hH hψ ↦ by
    rw [hT_def, ContinuousLinearMap.comp_apply]
    exact hℓ _ ⟨H, hH, TestFunction.jetRestrictionCLM_eq_ofContDiffOn hK hΩ hKΩ m _
      ((hH.analyticOnNhd.contDiffOn hΩ.uniqueDiffOn).of_le (mod_cast le_top)) hψ⟩
  obtain ⟨η, -, hη1, hηU⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ωo) (n := ⊤)
    hK (hΩ.inter hUf) (subset_inter hKΩ hf) inter_subset_left
  let ψf : 𝓓(Ωo, ℝ) := η.smulOfContDiffOn hUf (hηU.trans inter_subset_right) hfU_cd
  have hψf : (ψf : E → ℝ) =ᶠ[𝓝ˢ K] f := hη1.mono fun y hy ↦ by simp [ψf, hy]
  have hT0 : T ψf = 0 :=
    Distribution.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd (T := T) hK hKΩ hfill hTK hT hf hψf
  rw [hT_def, ContinuousLinearMap.comp_apply,
    TestFunction.jetRestrictionCLM_eq_ofContDiffOn hK hUf (fun _ hy ↦ hf _ hy) m _
      (hfU_cd.of_le (mod_cast le_top)) hψf] at hT0
  exact hT0

/-- Scalar harmonic Runge approximation on any finite-dimensional real inner product space. -/
private theorem exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt_real
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K Ω : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω)
    {f : E → ℝ} (hf : HarmonicOnNhd f K) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, HarmonicOnNhd H Ω ∧ ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (H - f) x‖ < ε := by
  set Jf := harmonicJetOn hK hf m
  have hclos : Jf ∈ closure (harmonicJetSubmodule hK hΩ hKΩ m : Set (JetSpace E ℝ K m)) :=
    Submodule.topologicalClosure_coe (harmonicJetSubmodule hK hΩ hKΩ m) ▸
      mem_topologicalClosure_harmonicJetSubmodule hΩ hK hKΩ hfill hf m
  obtain ⟨_, ⟨H, hH, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hclos ε hε
  refine ⟨H, hH, fun k hk x hx ↦ ?_⟩
  set j : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  set JH := JetSpace.ofContDiffOn hK hΩ hKΩ m
    ((hH.analyticOnNhd.contDiffOn hΩ.uniqueDiffOn).of_le (mod_cast le_top))
  have hsub : iteratedFDeriv ℝ k (H - f) x = (JH - Jf).eval j ⟨x, hx⟩ := by
    simp only [JH, Jf, JetSpace.eval_sub, FunLike.coe_sub, Pi.sub_apply,
      JetSpace.eval_ofContDiffOn, eval_harmonicJetOn]
    exact iteratedFDeriv_sub_apply
      ((hH x (hKΩ hx)).analyticAt.contDiffAt.of_le (mod_cast le_top))
      ((hf x hx).analyticAt.contDiffAt.of_le (mod_cast le_top))
  rw [hsub]
  exact ((JH - Jf).norm_eval_apply_le j ⟨x, hx⟩).trans_lt
    ((dist_eq_norm' Jf JH).symm.trans_lt hdist)

/-- **Harmonic Runge approximation in `C^m`** (Walsh; Lax–Malgrange). Let `E` be a
finite-dimensional real inner product space, `Ω ⊆ E` an open set, and `K ⊆ Ω` a compact set that is
filled-in within `Ω` (`IsFilledIn K Ω`). Every function `f : E → F` with values in a
finite-dimensional real normed space that is harmonic on a neighbourhood of `K` can be approximated
uniformly up to order `m` on `K` by functions harmonic on `Ω`. -/
theorem HarmonicOnNhd.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K Ω : Set E} {f : E → F} (hf : HarmonicOnNhd f K)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → F, HarmonicOnNhd H Ω ∧
      ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (H - f) x‖ < ε := by
  classical
  let b := Module.finBasis ℝ F
  let M : ℝ := (∑ i, ‖b i‖) + 1
  have hM : 0 < M :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) zero_lt_one
  have hδ : 0 < ε / M := div_pos hε hM
  let coord (i : _) : F →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  let spanB (i : _) : ℝ →L[ℝ] F := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hi : ∀ i, ∃ H : E → ℝ, HarmonicOnNhd H Ω ∧
      ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (H - coord i ∘ f) x‖ < ε / M := fun i ↦
    exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt_real hΩ hK hKΩ hfill
      (hf.comp_CLM (coord i)) m hδ
  choose H hH hbound using hi
  refine ⟨fun x ↦ ∑ i, spanB i (H i x),
    HarmonicOnNhd.sum fun i _ ↦ (hH i).comp_CLM (spanB i), fun k hk x hx ↦ ?_⟩
  have hsub : (fun y ↦ ∑ i, spanB i (H i y)) - f =
      ∑ i : _, (spanB i ∘ (H i - coord i ∘ f)) := by
    ext y
    simp only [Pi.sub_apply, Finset.sum_apply, Function.comp_apply, spanB, coord,
      ContinuousLinearMap.toSpanSingleton_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, sub_smul, Finset.sum_sub_distrib, b.sum_repr (f y)]
  have hcd_diff : ∀ i, ContDiffAt ℝ ∞ (H i - coord i ∘ f) x := fun i ↦
    ((hH i x (hKΩ hx)).analyticAt.sub ((hf.comp_CLM (coord i) x hx).analyticAt)).contDiffAt
  have hcd : ∀ i ∈ (Finset.univ : Finset _),
      ContDiffAt ℝ (k : ℕ∞ω) (spanB i ∘ (H i - coord i ∘ f)) x := fun i _ ↦
    ((spanB i).contDiff.contDiffAt.comp x (hcd_diff i)).of_le (mod_cast le_top)
  rw [hsub, iteratedFDeriv_sum_apply hcd]
  calc ‖∑ i, iteratedFDeriv ℝ k (spanB i ∘ (H i - coord i ∘ f)) x‖
      ≤ ∑ i, ‖iteratedFDeriv ℝ k (spanB i ∘ (H i - coord i ∘ f)) x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖spanB i‖ * ‖iteratedFDeriv ℝ k (H i - coord i ∘ f) x‖ :=
        Finset.sum_le_sum fun i _ ↦
          (spanB i).norm_iteratedFDeriv_comp_left (hcd_diff i) (mod_cast le_top)
    _ ≤ ∑ i, ‖b i‖ * (ε / M) := Finset.sum_le_sum fun i _ ↦ by
        rw [ContinuousLinearMap.norm_toSpanSingleton]
        exact mul_le_mul_of_nonneg_left (hbound i k hk x hx).le (norm_nonneg _)
    _ = (∑ i, ‖b i‖) * (ε / M) := (Finset.sum_mul _ _ _).symm
    _ < M * (ε / M) := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := mul_div_cancel₀ ε hM.ne'

/-- **Uniform harmonic Runge approximation** (Walsh; Lax–Malgrange). Under the same hypotheses as
`HarmonicOnNhd.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt`, any function harmonic on a
neighbourhood of the filled-in compact set `K ⊆ Ω` can be approximated uniformly on `K` by
functions harmonic on `Ω`. -/
theorem HarmonicOnNhd.exists_harmonicOnNhd_norm_sub_lt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K Ω : Set E} {f : E → F} (hf : HarmonicOnNhd f K)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → F, HarmonicOnNhd H Ω ∧ ∀ x ∈ K, ‖H x - f x‖ < ε := by
  obtain ⟨H, hH, hbound⟩ :=
    hf.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt hΩ hK hKΩ hfill 0 hε
  exact ⟨H, hH, fun x hx ↦ by simpa [norm_iteratedFDeriv_zero] using hbound 0 le_rfl x hx⟩

end Approximation

end InnerProductSpace
