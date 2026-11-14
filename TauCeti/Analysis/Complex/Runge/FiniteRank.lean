/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Runge.CauchyRepresentation
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# Finite-rank Runge approximation operators

Given an open subset `Ω ⊆ ℂ`, a compact set `K ⊆ Ω` filled in `Ω` (`TauCeti.IsFilledIn K Ω`), a
compact collar `L ⊆ ℂ` with `K ⊆ interior L`, and a tolerance `ε > 0`, we construct a single
finite-rank point-evaluation operator
`A f z = ∑ j : Fin N, (w j * g j z) • f (ζ j)`
whose evaluation nodes `ζ j ∈ interior L \ K`, weights `w j : ℂ`, and holomorphic output functions
`g j : ℂ → ℂ` on `Ω` depend **only** on `Ω`, `K`, `L`, and `ε` — and not on the target space `F`,
the open neighbourhood `U ⊇ L`, or the holomorphic map `f : ℂ → F` — such that
`‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * sSup ((fun x ↦ ‖f x‖) '' L)`
for all `z ∈ K` and every `f : ℂ → F` holomorphic on an open set `U ⊇ L`.

Because the spatial nodes `ζ j`, weights `w j`, and kernels `g j` are independent of external
parameters, applying this operator slicewise to a family `H : P → ℂ → F` preserves spatial
holomorphy on `Ω`, preserves joint `C^n` smoothness on `s ×ˢ Ω`, commutes with arbitrary-order real
Fréchet derivatives `iteratedFDeriv ℝ k` and conjugate Wirtinger derivatives in external parameters,
preserves holomorphic dependence on complex parameters, and satisfies the same relative `ε`-bound on
every parameter derivative `iteratedFDeriv ℝ k (fun q ↦ H q ·) p`.

We also establish sharpness of both the rank and the `IsFilledIn K Ω` hypothesis: for `K` nonempty
and `ε < 1` any such operator has positive rank, and on a concentric closed annulus
`closedBall c R \ ball c r` inside `ball c R'` (`0 < r₁ < r ≤ R < R₂ < R'`) no finite-rank
holomorphic operator on `ball c R'` can achieve relative collar error `ε < r₁ / r`.

## Main results

* `TauCeti.IsFilledIn.exists_fin_differentiableOn_norm_sub_sum_mul_le`: scalar finite-rank Runge
  approximation operator on a filled-in compact set.
* `TauCeti.IsFilledIn.exists_fin_differentiableOn_norm_sub_sum_smul_le`: normed-space version for an
  arbitrary complex normed space `F` (with no completeness assumption).
* `TauCeti.differentiableOn_sum_mul_smul`, `TauCeti.conjWirtingerDeriv_sum_mul_smul_eq_zero`:
  holomorphy and vanishing `\bar∂` of the finite-rank output on `Ω`.
* `TauCeti.contDiffOn_sum_mul_smul_with_param`, `TauCeti.hasFDerivAt_sum_mul_smul_with_param`,
  `TauCeti.iteratedFDeriv_sum_mul_smul_with_param`,
  `TauCeti.norm_iteratedFDeriv_sub_sum_mul_smul_le_with_param`: joint smoothness, commutation with
  parameter Fréchet derivatives, and uniform derivative approximation bounds.
* `TauCeti.conjWirtingerDeriv_sum_mul_smul_with_param`,
  `TauCeti.differentiableAt_sum_mul_smul_with_param`: commutation with `\bar∂` and preservation of
  holomorphy in external complex parameters.
* `TauCeti.pos_of_forall_differentiableOn_norm_sub_sum_mul_le` and
  `TauCeti.not_exists_fin_differentiableOn_ball_norm_sub_sum_mul_le`: positive-rank necessity and
  failure of finite-rank Runge approximation when `K` is not filled in `Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.3.
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped ContDiff Real Topology

namespace TauCeti

/-! ### Finite-rank Runge approximation -/

section FiniteRankRunge

/-- **Finite-rank Runge approximation operator (scalar form).** Let `Ω ⊆ ℂ` be open, `K ⊆ Ω` be
compact and filled in `Ω`, and `L ⊆ ℂ` be compact with `K ⊆ interior L`. For every `ε > 0` there
exist `N : ℕ`, evaluation points `ζ : Fin N → ℂ` in `interior L \ K`, weights `w : Fin N → ℂ`, and
functions `g : Fin N → ℂ → ℂ` holomorphic on `Ω`, depending only on `Ω`, `K`, `L`, and `ε`, such
that every function `f : ℂ → ℂ` holomorphic on an open set `U ⊇ L` satisfies
`‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * sSup ((fun x ↦ ‖f x‖) '' L)` for all `z ∈ K`. -/
theorem IsFilledIn.exists_fin_differentiableOn_norm_sub_sum_mul_le {K L Ω : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hL : IsCompact L) (hKL : K ⊆ interior L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ j, ζ j ∈ interior L \ K) ∧
      (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
      ∀ ⦃U : Set ℂ⦄, IsOpen U → L ⊆ U → ∀ ⦃f : ℂ → ℂ⦄, DifferentiableOn ℂ f U →
        ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * sSup ((fun x ↦ ‖f x‖) '' L) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0,
      fun _ _ _ _ _ _ hz ↦ hz.elim⟩
  have hLne : L.Nonempty := hKne.mono (hKL.trans interior_subset)
  obtain ⟨N, ζ, w, hζ, hrat⟩ :=
    hK.exists_fin_mem_sdiff_norm_sub_sum_mul_inv_le hL hKL (half_pos hε)
  set S : ℝ := ∑ j : Fin N, ‖w j‖
  have : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  set δ : ℝ := (ε / 2) / (S + 1)
  have hδ : 0 < δ := by positivity
  choose g hgΩ hgK using fun j ↦
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ j).2 hδ
  refine ⟨N, ζ, w, g, hζ, hgΩ, fun U hU hLU f hf z hz ↦ ?_⟩
  set Mf := sSup ((fun x ↦ ‖f x‖) '' L)
  have hbdd : BddAbove ((fun x ↦ ‖f x‖) '' L) :=
    (hL.image_of_continuousOn
      (continuous_norm.comp_continuousOn (hf.continuousOn.mono hLU))).bddAbove
  have hML : ∀ x ∈ L, ‖f x‖ ≤ Mf := fun x hx ↦ le_csSup hbdd ⟨x, hx, rfl⟩
  have hMf : 0 ≤ Mf := (norm_nonneg _).trans (hML hLne.some hLne.some_mem)
  have hsplit : f z - ∑ j, w j * f (ζ j) * g j z =
      (f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) +
        ∑ j, w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; abel
  have htail : ‖∑ j, w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z)‖ ≤ (ε / 2) * Mf := by
    have hSδ : S * δ ≤ ε / 2 := by
      calc S * ((ε / 2) / (S + 1)) ≤ (S + 1) * ((ε / 2) / (S + 1)) := by gcongr; linarith
        _ = ε / 2 := mul_div_cancel₀ _ (by positivity)
    calc ‖∑ j, w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z)‖
        ≤ ∑ j, ‖w j‖ * Mf * δ := (norm_sum_le _ _).trans <| Finset.sum_le_sum fun j _ ↦ by
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hML _ (interior_subset (hζ j).1))
            (norm_nonneg _)) (hgK j z hz).le (norm_nonneg _) (by positivity)
      _ = (S * δ) * Mf := by simp [S, ← Finset.sum_mul]; ring
      _ ≤ (ε / 2) * Mf := by gcongr
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add (hrat hU hLU hf z hz) htail).trans_eq (by ring))

/-- **Finite-rank Runge approximation operator (normed-space form).** The evaluation points,
weights, and holomorphic kernels from `IsFilledIn.exists_fin_differentiableOn_norm_sub_sum_mul_le`
simultaneously approximate holomorphic maps into any complex normed space `F`, with no completeness
assumption on `F`. -/
theorem IsFilledIn.exists_fin_differentiableOn_norm_sub_sum_smul_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {K L Ω : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hL : IsCompact L) (hKL : K ⊆ interior L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ j, ζ j ∈ interior L \ K) ∧
      (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
      ∀ ⦃U : Set ℂ⦄, IsOpen U → L ⊆ U → ∀ ⦃f : ℂ → F⦄, DifferentiableOn ℂ f U →
        ∀ z ∈ K, ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤
          ε * sSup ((fun x ↦ ‖f x‖) '' L) := by
  obtain ⟨N, ζ, w, g, hζ, hg, happrox⟩ :=
    hfill.exists_fin_differentiableOn_norm_sub_sum_mul_le hΩ hK hKΩ hL hKL hε
  refine ⟨N, ζ, w, g, hζ, hg, fun U hU hLU f hf z hz ↦ ?_⟩
  exact hf.norm_sub_sum_mul_smul_le_of_forall_differentiableOn hL hLU hε.le
    fun φ hφ ↦ happrox hU hLU hφ z hz

end FiniteRankRunge

/-! ### Spatial holomorphy and dependence on external parameters -/

section ParameterLaws

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Every finite-rank combination `z ↦ ∑ j, (w j * g j z) • v j` with kernels `g j` holomorphic on
`Ω` is holomorphic on `Ω`. -/
theorem differentiableOn_sum_mul_smul {Ω : Set ℂ} {w : ι → ℂ} {g : ι → ℂ → ℂ}
    (hg : ∀ j, DifferentiableOn ℂ (g j) Ω) (v : ι → F) :
    DifferentiableOn ℂ (fun z ↦ ∑ j, (w j * g j z) • v j) Ω :=
  DifferentiableOn.fun_sum fun j _ ↦ ((hg j).const_mul (w j)).smul_const (v j)

/-- The conjugate Wirtinger derivative of `z ↦ ∑ j, (w j * g j z) • v j` vanishes on any open set
`Ω` on which each `g j` is holomorphic. -/
theorem conjWirtingerDeriv_sum_mul_smul_eq_zero {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {w : ι → ℂ} {g : ι → ℂ → ℂ} (hg : ∀ j, DifferentiableOn ℂ (g j) Ω) (v : ι → F)
    {z : ℂ} (hz : z ∈ Ω) :
    conjWirtingerDeriv (fun y ↦ ∑ j, (w j * g j y) • v j) z = 0 :=
  ((differentiableOn_sum_mul_smul hg v).differentiableAt
    (hΩ.mem_nhds hz)).conjWirtingerDeriv_eq_zero

section SmoothParameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Joint smoothness of a finite-rank operator in external parameters.** If each kernel `g j` is
holomorphic on an open set `Ω ⊆ ℂ` and each evaluation trace `p ↦ H p (ζ j)` is `C^n` over `ℝ` on
`s ⊆ P`, then `(p, z) ↦ ∑ j, (w j * g j z) • H p (ζ j)` is jointly `C^n` on `s ×ˢ Ω`. -/
theorem contDiffOn_sum_mul_smul_with_param {n : WithTop ℕ∞} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {w : ι → ℂ} {g : ι → ℂ → ℂ} (hg : ∀ j, DifferentiableOn ℂ (g j) Ω)
    {ζ : ι → ℂ} {H : P → ℂ → F} {s : Set P}
    (hH : ∀ j, ContDiffOn ℝ n (fun p ↦ H p (ζ j)) s) :
    ContDiffOn ℝ n (fun q : P × ℂ ↦ ∑ j, (w j * g j q.2) • H q.1 (ζ j)) (s ×ˢ Ω) := by
  refine ContDiffOn.sum fun j _ ↦ ?_
  have hg_snd : ContDiffOn ℝ n (fun q : P × ℂ ↦ w j * g j q.2) (s ×ˢ Ω) :=
    contDiffOn_const.mul
      ((((hg j).contDiffOn hΩ).restrict_scalars ℝ).comp contDiff_snd.contDiffOn fun _ hq ↦ hq.2)
  have hH_fst : ContDiffOn ℝ n (fun q : P × ℂ ↦ H q.1 (ζ j)) (s ×ˢ Ω) :=
    (hH j).comp contDiff_fst.contDiffOn fun _ hq ↦ hq.1
  exact hg_snd.fun_smul hH_fst

/-- Joint `C^n` smoothness on `s ×ˢ Ω` when `H` is jointly `C^n` on `s ×ˢ U` and every node `ζ j`
lies in `U`. -/
theorem contDiffOn_sum_mul_smul_of_uncurry {n : WithTop ℕ∞} {Ω U : Set ℂ} (hΩ : IsOpen Ω)
    {w : ι → ℂ} {g : ι → ℂ → ℂ} (hg : ∀ j, DifferentiableOn ℂ (g j) Ω)
    {ζ : ι → ℂ} (hζ : ∀ j, ζ j ∈ U) {H : P → ℂ → F} {s : Set P}
    (hH : ContDiffOn ℝ n ↿H (s ×ˢ U)) :
    ContDiffOn ℝ n (fun q : P × ℂ ↦ ∑ j, (w j * g j q.2) • H q.1 (ζ j)) (s ×ˢ Ω) :=
  contDiffOn_sum_mul_smul_with_param hΩ hg fun j ↦
    hH.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hp ↦ ⟨hp, hζ j⟩

/-- **First-order parameter derivatives commute with a finite-rank operator.** -/
theorem hasFDerivAt_sum_mul_smul_with_param {w : ι → ℂ} {g : ι → ℂ → ℂ} {ζ : ι → ℂ}
    {H : P → ℂ → F} {H' : ι → P →L[ℝ] F} {p : P} (z : ℂ)
    (hH : ∀ j, HasFDerivAt (fun q ↦ H q (ζ j)) (H' j) p) :
    HasFDerivAt (fun q ↦ ∑ j, (w j * g j z) • H q (ζ j))
      (∑ j, (w j * g j z) • H' j) p :=
  HasFDerivAt.fun_sum fun j _ ↦ (hH j).const_smul (w j * g j z)

/-- `fderiv` form of `hasFDerivAt_sum_mul_smul_with_param`. -/
theorem fderiv_sum_mul_smul_with_param {w : ι → ℂ} {g : ι → ℂ → ℂ} {ζ : ι → ℂ}
    {H : P → ℂ → F} {p : P} (z : ℂ)
    (hH : ∀ j, DifferentiableAt ℝ (fun q ↦ H q (ζ j)) p) :
    fderiv ℝ (fun q ↦ ∑ j, (w j * g j z) • H q (ζ j)) p =
      ∑ j, (w j * g j z) • fderiv ℝ (fun q ↦ H q (ζ j)) p :=
  (hasFDerivAt_sum_mul_smul_with_param z fun j ↦ (hH j).hasFDerivAt).fderiv

/-- **Iterated parameter Fréchet derivatives commute with a finite-rank operator.** -/
theorem iteratedFDeriv_sum_mul_smul_with_param (k : ℕ) {w : ι → ℂ} {g : ι → ℂ → ℂ} {ζ : ι → ℂ}
    {H : P → ℂ → F} {p : P} (z : ℂ)
    (hH : ∀ j, ContDiffAt ℝ k (fun q ↦ H q (ζ j)) p) :
    iteratedFDeriv ℝ k (fun q ↦ ∑ j, (w j * g j z) • H q (ζ j)) p =
      ∑ j, (w j * g j z) • iteratedFDeriv ℝ k (fun q ↦ H q (ζ j)) p := by
  rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦ (hH j).const_smul (w j * g j z))]
  exact Finset.sum_congr rfl fun j _ ↦ iteratedFDeriv_const_smul_apply' (hH j)

/-- **Uniform approximation of parameter derivatives.** For a jointly `C^n` family `H : P → ℂ → F`
on `s ×ˢ U` whose slices `H p` are holomorphic on `U`, any scalar finite-rank approximation bound at
`z ∈ U` with nodes in `U` transfers to the `k`-th parameter Fréchet derivative whenever
`(k + 1 : ℕ) ≤ n`. -/
theorem norm_iteratedFDeriv_sub_sum_mul_smul_le_with_param (k : ℕ) {n : WithTop ℕ∞}
    (hk : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) {s : Set P} {U L : Set ℂ}
    (hs : IsOpen s) (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U)
    {ζ : ι → ℂ} (hζ : ∀ j, ζ j ∈ U) {w : ι → ℂ} {g : ι → ℂ → ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : z ∈ U)
    (hscalar : ∀ ⦃φ : ℂ → ℂ⦄, DifferentiableOn ℂ φ U →
      ‖φ z - ∑ j, w j * φ (ζ j) * g j z‖ ≤ ε * sSup ((fun x ↦ ‖φ x‖) '' L))
    {H : P → ℂ → F} (hH : ContDiffOn ℝ n ↿H (s ×ˢ U))
    (hHol : ∀ p ∈ s, DifferentiableOn ℂ (H p) U) {p : P} (hp : p ∈ s) :
    ‖iteratedFDeriv ℝ k (fun q ↦ H q z - ∑ j, (w j * g j z) • H q (ζ j)) p‖ ≤
      ε * sSup ((fun x ↦ ‖iteratedFDeriv ℝ k (fun q ↦ H q x) p‖) '' L) := by
  have hk_succ : (k : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ k
  have hk0 : (k : WithTop ℕ∞) ≤ n := hk_succ.trans hk
  have hslice : ∀ {y : ℂ}, y ∈ U → ContDiffAt ℝ k (fun q ↦ H q y) p := fun hy ↦
    ((hH.of_le hk0).contDiffAt ((hs.prod hU).mem_nhds ⟨hp, hy⟩)).comp p
      (contDiffAt_id.prodMk contDiffAt_const)
  have hsum : ContDiffAt ℝ k (fun q ↦ ∑ j, (w j * g j z) • H q (ζ j)) p :=
    ContDiffAt.sum fun j _ ↦ (hslice (hζ j)).const_smul (w j * g j z)
  rw [fun_iteratedFDeriv_sub_apply (hslice hz) hsum,
    iteratedFDeriv_sum_mul_smul_with_param k z fun j ↦ hslice (hζ j)]
  exact (differentiableOn_iteratedFDeriv_partial k hs hU hk hH hHol
    hp).norm_sub_sum_mul_smul_le_of_forall_differentiableOn hL hLU hε hscalar

end SmoothParameter

section HolomorphicParameter

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- **The conjugate Wirtinger derivative in a complex parameter commutes with a finite-rank
operator.** -/
theorem conjWirtingerDeriv_sum_mul_smul_with_param {w : ι → ℂ} {g : ι → ℂ → ℂ} {ζ : ι → ℂ}
    {H : Q → ℂ → F} {q : Q} (z : ℂ)
    (hH : ∀ j, DifferentiableAt ℝ (fun r ↦ H r (ζ j)) q) :
    conjWirtingerDeriv (fun r ↦ ∑ j, (w j * g j z) • H r (ζ j)) q =
      ∑ j, (w j * g j z) • conjWirtingerDeriv (fun r ↦ H r (ζ j)) q := by
  rw [conjWirtingerDeriv_fun_sum (g := fun j r ↦ (w j * g j z) • H r (ζ j))
    fun j _ ↦ (hH j).const_smul (w j * g j z)]
  exact Finset.sum_congr rfl fun j _ ↦ conjWirtingerDeriv_const_smul (w j * g j z)

/-- **A finite-rank operator preserves pointwise holomorphy in complex parameters.** -/
theorem differentiableAt_sum_mul_smul_with_param {w : ι → ℂ} {g : ι → ℂ → ℂ} {ζ : ι → ℂ}
    {H : Q → ℂ → F} {q : Q} (z : ℂ)
    (hH : ∀ j, DifferentiableAt ℂ (fun r ↦ H r (ζ j)) q) :
    DifferentiableAt ℂ (fun r ↦ ∑ j, (w j * g j z) • H r (ζ j)) q :=
  DifferentiableAt.fun_sum fun j _ ↦ (hH j).const_smul (w j * g j z)

/-- `DifferentiableOn` form of `differentiableAt_sum_mul_smul_with_param`. -/
theorem differentiableOn_sum_mul_smul_with_param {w : ι → ℂ} {g : ι → ℂ → ℂ} {ζ : ι → ℂ}
    {H : Q → ℂ → F} {s : Set Q} (z : ℂ)
    (hH : ∀ j, DifferentiableOn ℂ (fun r ↦ H r (ζ j)) s) :
    DifferentiableOn ℂ (fun r ↦ ∑ j, (w j * g j z) • H r (ζ j)) s :=
  DifferentiableOn.fun_sum fun j _ ↦ (hH j).const_smul (w j * g j z)

end HolomorphicParameter

end ParameterLaws

/-! ### Rank positivity and failure without `IsFilledIn` -/

section Sharpness

/-- **Positive-rank necessity.** On a nonempty compact set `K ⊆ L`, any finite-rank approximation
operator achieving relative error `ε < 1` on constant functions must have positive rank `0 < N`. -/
theorem pos_of_forall_differentiableOn_norm_sub_sum_mul_le {N : ℕ} {K L : Set ℂ}
    (hK : K.Nonempty) (hKL : K ⊆ L) {ζ : Fin N → ℂ} {w : Fin N → ℂ} {g : Fin N → ℂ → ℂ}
    {ε : ℝ} (hε : ε < 1)
    (h : ∀ ⦃U : Set ℂ⦄, IsOpen U → L ⊆ U → ∀ ⦃f : ℂ → ℂ⦄, DifferentiableOn ℂ f U →
      ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * sSup ((fun x ↦ ‖f x‖) '' L)) :
    0 < N := by
  by_contra hN
  obtain rfl : N = 0 := Nat.eq_zero_of_not_pos hN
  obtain ⟨z₀, hz₀⟩ := hK
  have hLne : L.Nonempty := ⟨z₀, hKL hz₀⟩
  have hle := h isOpen_univ (subset_univ L) (differentiableOn_const (1 : ℂ)) z₀ hz₀
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, norm_one, hLne.image_const,
    csSup_singleton, mul_one] at hle
  linarith

/-- **Uniform distance from a simple fraction to holomorphic functions on a disc.** If `h : ℂ → ℂ`
is holomorphic on `ball c R'` and `0 < r < R'`, then at some point `z ∈ sphere c r` the simple
fraction `(z - c)⁻¹` has distance at least `r⁻¹` from `h z`. -/
theorem _root_.DifferentiableOn.exists_mem_sphere_inv_le_norm_sub_inv {c : ℂ} {r R' : ℝ}
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball c R')) (hr : 0 < r) (hrR' : r < R') :
    ∃ z ∈ sphere c r, r⁻¹ ≤ ‖(z - c)⁻¹ - h z‖ := by
  have hs_sub : sphere c r ⊆ ball c R' :=
    sphere_subset_closedBall.trans (closedBall_subset_ball hrR')
  have hne : (sphere c r).Nonempty := ⟨c + r, by simp [abs_of_pos hr]⟩
  have hinv_cont : ContinuousOn (fun z : ℂ ↦ (z - c)⁻¹) (sphere c r) :=
    (continuous_id'.continuousOn.sub continuousOn_const).inv₀ fun z hz ↦
      sub_ne_zero.mpr fun hzc ↦ hr.ne (by simpa [hzc] using mem_sphere.mp hz)
  have hh_cont : ContinuousOn h (sphere c r) := hh.continuousOn.mono hs_sub
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_sphere c r).exists_isMaxOn hne
    (continuous_norm.comp_continuousOn (hinv_cont.sub hh_cont))
  refine ⟨z₀, hz₀, ?_⟩
  set M := ‖(z₀ - c)⁻¹ - h z₀‖
  have hM : ∀ z ∈ sphere c r, ‖(z - c)⁻¹ - h z‖ ≤ M := fun z hz ↦ hmax hz
  have hdcc : DiffContOnCl ℂ h (ball c r) :=
    ⟨hh.mono (ball_subset_ball hrR'.le),
      hh.continuousOn.mono ((closure_ball c hr.ne').subset.trans (closedBall_subset_ball hrR'))⟩
  have hint : (∮ z in C(c, r), ((z - c)⁻¹ - h z)) = 2 * π * I := by
    rw [circleIntegral.integral_sub (hinv_cont.circleIntegrable hr.le)
        (hh_cont.circleIntegrable hr.le),
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr),
      hdcc.circleIntegral_eq_zero hr.le, sub_zero]
  have h2pi : 2 * π ≤ 2 * π * r * M := by
    have hnorm : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      rw [norm_mul, norm_I, mul_one, norm_mul, norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    have hle := circleIntegral.norm_integral_le_of_norm_le_const hr.le hM
    rwa [hint, hnorm] at hle
  have hpi_pos : 0 < 2 * π := by positivity
  exact (inv_le_iff_one_le_mul₀' hr).mpr ((mul_le_mul_iff_right₀ hpi_pos).mp (by linarith))

/-- **Sharpness of `IsFilledIn` on concentric annuli.** For `0 < r₁ < r ≤ R < R₂ < R'`, the closed
annulus `K = closedBall c R \ ball c r` is compact inside `Ω = ball c R'` with compact collar
`L = closedBall c R₂ \ ball c r₁` satisfying `K ⊆ interior L`, yet `¬ IsFilledIn K Ω`
(`TauCeti.not_isFilledIn_closedBall_sdiff_ball_ball`), and for every `ε < r₁ / r` (in particular
`ε < 3 / 4` when `r₁ = 3 / 2`, `r = 2`, `R = 3`, `R₂ = 7 / 2`, `R' = 4`) no finite-rank operator
with kernels holomorphic on `ball c R'` can satisfy the Runge collar estimate. -/
theorem not_exists_fin_differentiableOn_ball_norm_sub_sum_mul_le {c : ℂ} {r₁ r R R₂ R' : ℝ}
    (hr₁ : 0 < r₁) (hr₁r : r₁ < r) (hrR : r ≤ R) (hRR₂ : R < R₂) (hR₂R' : R₂ < R')
    {ε : ℝ} (hε : ε < r₁ / r) :
    ¬ ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ j, DifferentiableOn ℂ (g j) (ball c R')) ∧
      ∀ ⦃U : Set ℂ⦄, IsOpen U → closedBall c R₂ \ ball c r₁ ⊆ U →
        ∀ ⦃f : ℂ → ℂ⦄, DifferentiableOn ℂ f U →
          ∀ z ∈ closedBall c R \ ball c r,
            ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤
              ε * sSup ((fun x ↦ ‖f x‖) '' (closedBall c R₂ \ ball c r₁)) := by
  rintro ⟨N, ζ, w, g, hg, happrox⟩
  have hr : 0 < r := hr₁.trans hr₁r
  set L := closedBall c R₂ \ ball c r₁
  set U := ball c R' \ {c}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hLU : L ⊆ U := fun x hx ↦
    ⟨closedBall_subset_ball hR₂R' hx.1, fun hxc ↦ hx.2 (hxc ▸ mem_ball_self hr₁)⟩
  let f : ℂ → ℂ := fun z ↦ (z - c)⁻¹
  have hf : DifferentiableOn ℂ f U :=
    (differentiableOn_id.sub (differentiableOn_const c)).inv fun _ hz ↦ sub_ne_zero.mpr hz.2
  have hcr : c + r ∈ closedBall c R \ ball c r :=
    ⟨by simp [abs_of_pos hr, hrR], by simp [abs_of_pos hr]⟩
  have hLne : L.Nonempty :=
    ⟨c + r, closedBall_subset_closedBall hRR₂.le hcr.1,
      fun h ↦ hcr.2 (ball_subset_ball hr₁r.le h)⟩
  set S := sSup ((fun x ↦ ‖f x‖) '' L)
  have hS_pos : 0 < S := by
    have hbdd : BddAbove ((fun x ↦ ‖f x‖) '' L) :=
      (((isCompact_closedBall c R₂).diff isOpen_ball).image_of_continuousOn
        (continuous_norm.comp_continuousOn (hf.continuousOn.mono hLU))).bddAbove
    have hpos : 0 < ‖f (c + r)‖ := by simp [f, hr.ne']
    exact hpos.trans_le (le_csSup hbdd ⟨c + r, ⟨closedBall_subset_closedBall hRR₂.le hcr.1,
      fun h ↦ hcr.2 (ball_subset_ball hr₁r.le h)⟩, rfl⟩)
  have hS_le : S ≤ r₁⁻¹ := by
    refine csSup_le (hLne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have hdist : r₁ ≤ ‖x - c‖ := by simpa [mem_ball, dist_eq_norm] using hx.2
    simpa [f] using inv_anti₀ hr₁ hdist
  have hh : DifferentiableOn ℂ (fun z ↦ ∑ j, w j * f (ζ j) * g j z) (ball c R') :=
    DifferentiableOn.fun_sum fun j _ ↦ (hg j).const_mul (w j * f (ζ j))
  obtain ⟨z₀, hz₀, hlow⟩ :=
    hh.exists_mem_sphere_inv_le_norm_sub_inv hr (hrR.trans_lt (hRR₂.trans hR₂R'))
  have hz₀K : z₀ ∈ closedBall c R \ ball c r :=
    ⟨closedBall_subset_closedBall hrR (sphere_subset_closedBall hz₀),
      fun h ↦ (mem_ball.mp h).ne (mem_sphere.mp hz₀)⟩
  have hup : r⁻¹ ≤ ε * S := hlow.trans (happrox hU hLU hf z₀ hz₀K)
  rcases lt_or_ge ε 0 with hε_neg | hε_nonneg
  · linarith [mul_neg_of_neg_of_pos hε_neg hS_pos, inv_pos.mpr hr]
  · have hlt : ε * S < r⁻¹ :=
      calc ε * S ≤ ε * r₁⁻¹ := mul_le_mul_of_nonneg_left hS_le hε_nonneg
        _ < (r₁ / r) * r₁⁻¹ := mul_lt_mul_of_pos_right hε (inv_pos.mpr hr₁)
        _ = r⁻¹ := by field_simp [hr₁.ne', hr.ne']
    linarith

end Sharpness

end TauCeti
