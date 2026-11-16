/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Sets.Compacts
public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The topology of homogeneous symbols

A homogeneous symbol `a` of degree `m` (`TauCeti.HomogeneousSymbol`) is smooth away from the zero
frequency and positively homogeneous of degree `m` in the frequency, so it is determined by its
values on the cosphere bundle `X × {‖ξ‖ = 1}`. For a compact set `K` of positions and `k : ℕ`, the
seminorm `TauCeti.HomogeneousSymbol.seminorm K k a` is the best constant `C` in the estimate

`‖Dᵏ a (x, ξ)‖ ≤ C` for `x ∈ K` and `‖ξ‖ = 1`,

where `Dᵏ a` is the `k`-th Fréchet derivative of `(x, ξ) ↦ a (x, ξ)` on `X × E`. For a proper
(for instance finite-dimensional) frequency space these seminorms are finite, and they make
`TauCeti.HomogeneousSymbol X E V W m` a Hausdorff locally convex topological vector space over
`ℂ`: the `C^∞` topology on compact subsets of the cosphere bundle, read through homogeneity. A
parameter family `t ↦ a_t` of homogeneous symbols is continuous at `t₀` in this topology exactly
when, for every compact `K` and every `k`, the `k`-th derivatives of `a_t` converge to those of
`a_{t₀}` uniformly on `K × {‖ξ‖ = 1}`; this is the sense in which principal symbols vary
continuously along symbol homotopies.

Homogeneity transports the estimates on the sphere to every nonzero frequency:

* `TauCeti.HomogeneousSymbol.norm_iteratedFDeriv_coefficient_le_seminorm`: for `‖ξ‖ ≥ 1` the
  whole derivative is bounded by `‖ξ‖ ^ m` times the seminorm;
* `TauCeti.HomogeneousSymbol.norm_iteratedFDeriv_append_le_seminorm`: at every nonzero frequency,
  the derivative in `j` position directions and `l` frequency directions is bounded by
  `‖ξ‖ ^ (m - l)` times the seminorm.

These are the estimates that make the cut-off terms of homogeneous symbols depend continuously on
them in the symbol classes `S^m_{1,0}`: for a frequency cutoff `χ`, the derivatives of the cut-off
term `χ(ξ) a(x, ξ)` in `j` position and `l` frequency directions are bounded by a constant,
independent of `a`, times `⟨ξ⟩ ^ (m - l)` and the seminorms `p_{K,i}(a)`, `i ≤ j + l`
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_smul_coefficient_le_seminorm`). For a
single symbol this gives its symbol estimates of order `m`
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_smul_coefficient_le`).

The seminorms are set up following `TauCeti.Symbol.seminorm`
(`TauCeti/Analysis/Pseudodifferential/Symbol/Topology.lean`) and Mathlib's seminorms of the
Schwartz space (`SchwartzMap.seminorm`).

## Main declarations

* `TauCeti.HomogeneousSymbol.seminorm`: the seminorm `p_{K,k}`, with `le_seminorm`,
  `seminorm_le_bound` and `seminorm_le_iff`.
* `TauCeti.HomogeneousSymbol.seminormFamily`, `TauCeti.HomogeneousSymbol.withSeminorms`: the
  locally convex topology of homogeneous symbols.
* `TauCeti.HomogeneousSymbol.instT1Space`: the seminorms separate homogeneous symbols.
* `TauCeti.HomogeneousSymbol.coefficientCLM`: evaluation at a point is a continuous linear
  functional.
* `TauCeti.HomogeneousSymbol.spatialDerivCLM`, `TauCeti.HomogeneousSymbol.frequencyDerivCLM`: the
  spatial and frequency derivatives are continuous linear maps, with the seminorm bounds
  `seminorm_spatialDeriv_le` and `seminorm_frequencyDeriv_le`.

## References

* R. B. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2, (5.35)–(5.36):
  the `C^∞` topology on homogeneous symbols, in which the quantization of principal symbols is
  continuous.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Set Metric Filter Topology
open TopologicalSpace (Compacts)
open scoped ContDiff

namespace TauCeti

namespace HomogeneousSymbol

variable {X E V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Seminorm

/-- The `k`-th derivative of a homogeneous symbol is continuous away from the zero frequency. -/
private theorem continuousOn_iteratedFDeriv_coefficient (a : HomogeneousSymbol X E V W m)
    (k : ℕ) : ContinuousOn (iteratedFDeriv ℝ k a.coefficient) {p | p.2 ≠ 0} :=
  ContinuousOn.continuousOn_iteratedFDeriv a.contDiffOn_coefficient
    (isOpen_ne_fun continuous_snd continuous_const) (mod_cast le_top)

/-- The admissible constants in the estimate of the `k`-th derivative of `a` on `K × sphere 0 1`. -/
private def bounds (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ x ∈ K, ∀ ξ : E, ‖ξ‖ = 1 → ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ c}

private theorem bounds_nonempty [ProperSpace E] (K : Compacts X) (k : ℕ)
    (a : HomogeneousSymbol X E V W m) : (bounds K k a).Nonempty := by
  obtain ⟨C, hC⟩ := (K.isCompact.prod (isCompact_sphere (0 : E) 1)).exists_bound_of_continuousOn
    ((a.continuousOn_iteratedFDeriv_coefficient k).mono fun p hp h ↦ by
      simpa [h] using (mem_prod.1 hp).2)
  exact ⟨max C 0, le_max_right _ _, fun x hx ξ hξ ↦
    (hC (x, ξ) (mk_mem_prod hx (by simpa using hξ))).trans (le_max_left _ _)⟩

private theorem bounds_bddBelow (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m) :
    BddBelow (bounds K k a) :=
  ⟨0, fun _ hc ↦ hc.1⟩

/-- The best constant in the estimate of the `k`-th derivative of `a` on `K × sphere 0 1`. -/
private def seminormAux (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m) : ℝ :=
  sInf (bounds K k a)

private theorem seminormAux_nonneg [ProperSpace E] (K : Compacts X) (k : ℕ)
    (a : HomogeneousSymbol X E V W m) :
    0 ≤ seminormAux K k a :=
  le_csInf (bounds_nonempty K k a) fun _ hc ↦ hc.1

private theorem le_seminormAux [ProperSpace E] (K : Compacts X) (k : ℕ)
    (a : HomogeneousSymbol X E V W m)
    {x : X} (hx : x ∈ K) {ξ : E} (hξ : ‖ξ‖ = 1) :
    ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ seminormAux K k a :=
  le_csInf (bounds_nonempty K k a) fun _ hc ↦ hc.2 x hx ξ hξ

private theorem seminormAux_le_bound (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ : E, ‖ξ‖ = 1 → ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ C) :
    seminormAux K k a ≤ C :=
  csInf_le (bounds_bddBelow K k a) ⟨hC, h⟩

/-- Away from the zero frequency the derivatives of a sum are the sums of the derivatives. -/
private theorem iteratedFDeriv_coefficient_add (a b : HomogeneousSymbol X E V W m) (k : ℕ)
    {p : X × E} (hp : p.2 ≠ 0) :
    iteratedFDeriv ℝ k (a + b).coefficient p =
      iteratedFDeriv ℝ k a.coefficient p + iteratedFDeriv ℝ k b.coefficient p := by
  rw [coefficient_add]
  exact iteratedFDeriv_add_apply ((a.contDiffAt_coefficient hp).of_le (mod_cast le_top))
    ((b.contDiffAt_coefficient hp).of_le (mod_cast le_top))

private theorem iteratedFDeriv_coefficient_smul (c : ℂ) (a : HomogeneousSymbol X E V W m) (k : ℕ)
    {p : X × E} (hp : p.2 ≠ 0) :
    iteratedFDeriv ℝ k (c • a).coefficient p = c • iteratedFDeriv ℝ k a.coefficient p := by
  rw [coefficient_smul]
  exact iteratedFDeriv_const_smul_apply ((a.contDiffAt_coefficient hp).of_le (mod_cast le_top))

/-- Away from the zero frequency, a derivative of `a` in a fixed direction `q`, given by
`b (p) = Da (p) q`, has its `k`-th derivative bounded by `‖q‖` times the `(k + 1)`-st derivative
of `a`. -/
private theorem norm_iteratedFDeriv_le_of_eq_fderiv {m' : ℝ} (a : HomogeneousSymbol X E V W m)
    (b : HomogeneousSymbol X E V W m') (q : X × E)
    (hb : ∀ p : X × E, p.2 ≠ 0 → b.coefficient p = fderiv ℝ a.coefficient p q) (k : ℕ)
    {p : X × E} (hp : p.2 ≠ 0) :
    ‖iteratedFDeriv ℝ k b.coefficient p‖ ≤ ‖q‖ * ‖iteratedFDeriv ℝ (k + 1) a.coefficient p‖ := by
  have hS : IsOpen {p : X × E | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have heq : b.coefficient =ᶠ[𝓝 p]
      (ContinuousLinearMap.apply ℝ (V →L[ℂ] W) q) ∘ fderiv ℝ a.coefficient := by
    filter_upwards [hS.mem_nhds hp] with p' hp'
    rw [Function.comp_apply, ContinuousLinearMap.apply_apply]
    exact hb p' hp'
  rw [heq.iteratedFDeriv ℝ k |>.eq_of_nhds]
  have hd : ContDiffAt ℝ k (fderiv ℝ a.coefficient) p :=
    (a.contDiffAt_coefficient hp).fderiv_right (by norm_cast; exact le_top)
  have h1 := (ContinuousLinearMap.apply ℝ (V →L[ℂ] W) q).norm_iteratedFDeriv_comp_left hd le_rfl
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg q) fun L ↦ ?_
  simpa only [ContinuousLinearMap.apply_apply, mul_comm] using L.le_opNorm q

variable [ProperSpace E]

private theorem seminormAux_zero (K : Compacts X) (k : ℕ) :
    seminormAux K k (0 : HomogeneousSymbol X E V W m) = 0 :=
  le_antisymm (seminormAux_le_bound K k 0 le_rfl fun _ _ _ _ ↦ by
      rw [coefficient_zero, iteratedFDeriv_zero, Pi.zero_apply, norm_zero])
    (seminormAux_nonneg K k 0)

private theorem seminormAux_add_le (K : Compacts X) (k : ℕ) (a b : HomogeneousSymbol X E V W m) :
    seminormAux K k (a + b) ≤ seminormAux K k a + seminormAux K k b :=
  seminormAux_le_bound K k _ (add_nonneg (seminormAux_nonneg K k a) (seminormAux_nonneg K k b))
    fun x hx ξ hξ ↦ by
      rw [iteratedFDeriv_coefficient_add a b k (p := (x, ξ))
        (ne_zero_of_norm_ne_zero (hξ ▸ one_ne_zero))]
      exact (norm_add_le _ _).trans
        (add_le_add (le_seminormAux K k a hx hξ) (le_seminormAux K k b hx hξ))

private theorem seminormAux_smul_le (K : Compacts X) (k : ℕ) (c : ℂ)
    (a : HomogeneousSymbol X E V W m) : seminormAux K k (c • a) ≤ ‖c‖ * seminormAux K k a :=
  seminormAux_le_bound K k _ (mul_nonneg (norm_nonneg c) (seminormAux_nonneg K k a))
    fun x hx ξ hξ ↦ by
      rw [iteratedFDeriv_coefficient_smul c a k (p := (x, ξ))
        (ne_zero_of_norm_ne_zero (hξ ▸ one_ne_zero)), norm_smul]
      exact mul_le_mul_of_nonneg_left (le_seminormAux K k a hx hξ) (norm_nonneg c)

/-- The seminorm `p_{K,k}` on the homogeneous symbols of degree `m`: the best constant `C` in the
estimate `‖Dᵏ a (x, ξ)‖ ≤ C` for all positions `x ∈ K` and all unit frequencies `‖ξ‖ = 1`,
where `Dᵏ a` is the `k`-th Fréchet derivative of the coefficient on `X × E`. -/
protected def seminorm (K : Compacts X) (k : ℕ) : Seminorm ℂ (HomogeneousSymbol X E V W m) :=
  Seminorm.ofSMulLE (seminormAux K k) (seminormAux_zero K k) (seminormAux_add_le K k)
    (seminormAux_smul_le K k)

/-- The seminorm `p_{K,k}(a)` bounds the `k`-th derivative of `a` at unit frequencies over `K`. -/
theorem le_seminorm (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m) {x : X}
    (hx : x ∈ K) {ξ : E} (hξ : ‖ξ‖ = 1) :
    ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ HomogeneousSymbol.seminorm K k a :=
  le_seminormAux K k a hx hξ

/-- A bound for the `k`-th derivative of `a` at unit frequencies over `K` bounds the seminorm. -/
theorem seminorm_le_bound (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ : E, ‖ξ‖ = 1 → ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ C) :
    HomogeneousSymbol.seminorm K k a ≤ C :=
  seminormAux_le_bound K k a hC h

/-- The seminorm `p_{K,k}(a)` is at most `C ≥ 0` exactly when `C` bounds the `k`-th derivative of
`a` at unit frequencies over `K`. -/
theorem seminorm_le_iff {K : Compacts X} {k : ℕ} {a : HomogeneousSymbol X E V W m} {C : ℝ}
    (hC : 0 ≤ C) :
    HomogeneousSymbol.seminorm K k a ≤ C ↔
      ∀ x ∈ K, ∀ ξ : E, ‖ξ‖ = 1 → ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ C :=
  ⟨fun h _ hx _ hξ ↦ (le_seminorm K k a hx hξ).trans h, seminorm_le_bound K k a hC⟩

/-- The seminorms are monotone in the compact set. -/
theorem seminorm_mono {K L : Compacts X} (hKL : K ≤ L) (k : ℕ) (a : HomogeneousSymbol X E V W m) :
    HomogeneousSymbol.seminorm K k a ≤ HomogeneousSymbol.seminorm L k a :=
  seminorm_le_bound K k a (apply_nonneg _ _) fun _ hx _ hξ ↦ le_seminorm L k a (hKL hx) hξ

/-- **The seminorms bound all frequencies of norm at least `1`.** For `‖ξ‖ ≥ 1` and `x ∈ K`, the
`k`-th derivative of a homogeneous symbol of degree `m` satisfies
`‖Dᵏ a (x, ξ)‖ ≤ ‖ξ‖ ^ m p_{K,k}(a)`. -/
theorem norm_iteratedFDeriv_coefficient_le_seminorm (K : Compacts X) (k : ℕ)
    (a : HomogeneousSymbol X E V W m) {x : X} (hx : x ∈ K) {ξ : E} (hξ : 1 ≤ ‖ξ‖) :
    ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ ‖ξ‖ ^ m * HomogeneousSymbol.seminorm K k a := by
  set t := ‖ξ‖
  have ht : 0 < t := one_pos.trans_le hξ
  have hη : ‖t⁻¹ • ξ‖ = 1 := by simp [t, norm_smul, ht.ne']
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  -- Rescale the frequency components of the directions by `t⁻¹`.
  set v' : Fin k → X × E := fun i ↦ ((v i).1, t⁻¹ • (v i).2)
  have hv : (fun i ↦ ((v' i).1, t • (v' i).2)) = v := by
    funext i
    simp [v', smul_inv_smul₀ ht.ne']
  have heq := a.iteratedFDeriv_coefficient_smul_frequency (x := x)
    (ne_zero_of_norm_ne_zero (hη ▸ one_ne_zero)) ht k v'
  rw [smul_inv_smul₀ ht.ne', hv] at heq
  rw [heq, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine ((iteratedFDeriv ℝ k a.coefficient (x, t⁻¹ • ξ)).le_opNorm v').trans ?_
  refine mul_le_mul (le_seminorm K k a hx hη) (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    fun i _ ↦ ?_) (by positivity) (apply_nonneg _ _)
  -- The rescaled direction is no longer than the original one, since `t ≥ 1`.
  simp only [v', Prod.norm_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
  exact max_le_max le_rfl (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hξ))

/-- **Homogeneity of the mixed derivatives.** At every nonzero frequency `ξ` and position `x ∈ K`,
the derivative of a homogeneous symbol of degree `m` in `j` position directions `u` and `l`
frequency directions `w` is bounded by `‖ξ‖ ^ (m - l) p_{K,j+l}(a) ∏ ‖uᵢ‖ ∏ ‖wᵢ‖`. -/
theorem norm_iteratedFDeriv_append_le_seminorm (K : Compacts X) (a : HomogeneousSymbol X E V W m)
    {x : X} (hx : x ∈ K) {ξ : E} (hξ : ξ ≠ 0) {j l : ℕ} (u : Fin j → X) (w : Fin l → E) :
    ‖iteratedFDeriv ℝ (j + l) a.coefficient (x, ξ)
        (Fin.append (fun i ↦ (u i, 0)) (fun i ↦ (0, w i)))‖ ≤
      ‖ξ‖ ^ (m - l) * HomogeneousSymbol.seminorm K (j + l) a * ((∏ i, ‖u i‖) * ∏ i, ‖w i‖) := by
  set t := ‖ξ‖
  have ht : 0 < t := norm_pos_iff.2 hξ
  have hη : ‖t⁻¹ • ξ‖ = 1 := by simp [t, norm_smul, ht.ne']
  have heq := a.iteratedFDeriv_coefficient_smul_frequency_append (x := x)
    (ne_zero_of_norm_ne_zero (hη ▸ one_ne_zero)) ht u w
  rw [smul_inv_smul₀ ht.ne'] at heq
  rw [heq, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left (((iteratedFDeriv ℝ (j + l) a.coefficient
    (x, t⁻¹ • ξ)).norm_apply_append_prod_le u w).trans ?_) (by positivity)
  exact mul_le_mul_of_nonneg_right (le_seminorm K _ a hx hη) (by positivity)

/-- The seminorms of the spatial derivative `∂_v a` are bounded by `‖v‖` times seminorms of `a`
with one more derivative. -/
theorem seminorm_spatialDeriv_le (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m)
    (v : X) :
    HomogeneousSymbol.seminorm K k (a.spatialDeriv v) ≤
      ‖v‖ * HomogeneousSymbol.seminorm K (k + 1) a := by
  refine seminorm_le_bound K k _ (by positivity) fun x hx ξ hξ ↦ ?_
  refine (norm_iteratedFDeriv_le_of_eq_fderiv a _ (v, 0)
    (fun p _ ↦ a.coefficient_spatialDeriv_eq_fderiv v) k (p := (x, ξ))
    (ne_zero_of_norm_ne_zero (hξ ▸ one_ne_zero))).trans ?_
  rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg v)]
  exact mul_le_mul_of_nonneg_left (le_seminorm K (k + 1) a hx hξ) (norm_nonneg v)

/-- The seminorms of the frequency derivative `∂_w a` are bounded by `‖w‖` times seminorms of `a`
with one more derivative. -/
theorem seminorm_frequencyDeriv_le (K : Compacts X) (k : ℕ) (a : HomogeneousSymbol X E V W m)
    (w : E) :
    HomogeneousSymbol.seminorm K k (a.frequencyDeriv w) ≤
      ‖w‖ * HomogeneousSymbol.seminorm K (k + 1) a := by
  refine seminorm_le_bound K k _ (by positivity) fun x hx ξ hξ ↦ ?_
  refine (norm_iteratedFDeriv_le_of_eq_fderiv a _ (0, w)
    (fun _ hp ↦ a.coefficient_frequencyDeriv_eq_fderiv w hp) k (p := (x, ξ))
    (ne_zero_of_norm_ne_zero (hξ ▸ one_ne_zero))).trans ?_
  rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg w)]
  exact mul_le_mul_of_nonneg_left (le_seminorm K (k + 1) a hx hξ) (norm_nonneg w)

/-- At a nonzero frequency `ξ` and a position `x ∈ K`, the value of a homogeneous symbol of degree
`m` is bounded by `‖ξ‖ ^ m p_{K,0}(a)`. -/
theorem norm_coefficient_le_rpow_mul_seminorm (K : Compacts X) (a : HomogeneousSymbol X E V W m)
    {x : X} (hx : x ∈ K) {ξ : E} (hξ : ξ ≠ 0) :
    ‖a.coefficient (x, ξ)‖ ≤ ‖ξ‖ ^ m * HomogeneousSymbol.seminorm K 0 a := by
  simpa using a.norm_iteratedFDeriv_append_le_seminorm K hx hξ (j := 0) (l := 0) Fin.elim0
    Fin.elim0

omit [ProperSpace E] in
/-- The cut-off term `χ(ξ) a(x, ξ)` vanishes near the zero frequency, so all its derivatives vanish
there. -/
private theorem iteratedFDeriv_smul_coefficient_zero_frequency (χ : FrequencyCutoff E)
    (a : HomogeneousSymbol X E V W m) (k : ℕ) (x : X) :
    iteratedFDeriv ℝ k (fun p : X × E ↦ χ p.2 • a.coefficient p) (x, 0) = 0 := by
  have h0 : (fun p : X × E ↦ χ p.2 • a.coefficient p) =ᶠ[𝓝 (x, 0)] 0 := by
    simpa using χ.comp_inv_smul_snd_smul_eventuallyEq_zero 1 a.coefficient
      (p := (x, (0 : E))) (by simp)
  rw [h0.iteratedFDeriv ℝ k |>.eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply]

/-- At frequencies `‖ξ‖ ≤ 2`, the derivatives of the cut-off term `χ(ξ) a(x, ξ)` are
bounded by a constant, depending only on `χ`, `m` and the order `k`, times the homogeneous
seminorms `p_{K,i}(a)`, `i ≤ k`. -/
private theorem exists_norm_iteratedFDeriv_smul_coefficient_le_of_norm_le_two
    (χ : FrequencyCutoff E) (K : Compacts X) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ a : HomogeneousSymbol X E V W m, ∀ x ∈ K, ∀ ξ : E, ‖ξ‖ ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p : X × E ↦ χ p.2 • a.coefficient p) (x, ξ)‖ ≤
        C * ((Finset.range (k + 1)).sup fun i ↦ HomogeneousSymbol.seminorm K i) a := by
  choose B hB using fun i ↦ χ.exists_bound_iteratedFDeriv i
  set L := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * max (B i) 0
  refine ⟨L * 2 ^ |m|, by positivity, fun a x hx ξ hξ2 ↦ ?_⟩
  set P := ((Finset.range (k + 1)).sup fun i ↦ HomogeneousSymbol.seminorm K i) a
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [iteratedFDeriv_smul_coefficient_zero_frequency, norm_zero]
    positivity
  -- Away from the zero frequency, apply the Leibniz rule on the open set `ξ ≠ 0`.
  set S : Set (X × E) := {p | p.2 ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun continuous_snd continuous_const
  have hxξ : (x, ξ) ∈ S := hξ
  have hχ : ContDiff ℝ ∞ fun p : X × E ↦ χ p.2 := χ.contDiff.comp contDiff_snd
  have hleib := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn a.contDiffOn_coefficient
    hS.uniqueDiffOn hxξ (n := k) (mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hS hxξ] at hleib
  refine hleib.trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [iteratedFDerivWithin_of_isOpen i hS hxξ, iteratedFDerivWithin_of_isOpen (k - i) hS hxξ,
    mul_assoc (k.choose i : ℝ), mul_assoc (k.choose i : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  -- The derivatives of `ξ ↦ χ ξ` on the product are bounded by those of `χ`.
  have hχi : ‖iteratedFDeriv ℝ i (fun p : X × E ↦ χ p.2) (x, ξ)‖ ≤ ‖iteratedFDeriv ℝ i χ ξ‖ :=
    norm_iteratedFDeriv_comp_snd_le (f := χ) (x, ξ)
  rcases le_or_gt ‖ξ‖ 1 with hξ1 | hξ1
  · -- Inside the closed unit ball every derivative of `χ` vanishes.
    rw [χ.iteratedFDeriv_eq_zero_of_norm_le_one i hξ1, norm_zero] at hχi
    rw [norm_le_zero_iff.1 hχi, norm_zero, zero_mul]
    positivity
  · -- On `1 < ‖ξ‖ ≤ 2` both factors are bounded.
    have hik : k - i ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
    have ha : ‖iteratedFDeriv ℝ (k - i) a.coefficient (x, ξ)‖ ≤ 2 ^ |m| * P := by
      refine (a.norm_iteratedFDeriv_coefficient_le_seminorm K (k - i) hx hξ1.le).trans ?_
      refine mul_le_mul ?_ (Seminorm.le_finset_sup_apply hik) (apply_nonneg _ _) (by positivity)
      calc ‖ξ‖ ^ m ≤ ‖ξ‖ ^ |m| := Real.rpow_le_rpow_of_exponent_le hξ1.le (le_abs_self m)
        _ ≤ 2 ^ |m| := Real.rpow_le_rpow (norm_nonneg _) hξ2 (abs_nonneg m)
    calc ‖iteratedFDeriv ℝ i (fun p : X × E ↦ χ p.2) (x, ξ)‖ *
          ‖iteratedFDeriv ℝ (k - i) a.coefficient (x, ξ)‖
        ≤ max (B i) 0 * (2 ^ |m| * P) :=
          mul_le_mul (hχi.trans ((hB i ξ).trans (le_max_left _ _))) ha (norm_nonneg _)
            (le_max_right _ _)

/-- **Uniform symbol estimates for the cut-off term.** For positions in `K`, the derivative of the
cut-off term `χ(ξ) a(x, ξ)` in `j` position directions `u` and `l` frequency directions `w` is
bounded by `C p(a) ⟨ξ⟩ ^ (m - l) ∏ ‖uᵢ‖ ∏ ‖wᵢ‖`, where `p(a)` is the largest of the homogeneous
seminorms `p_{K,i}(a)`, `i ≤ j + l`, and the constant `C` depends only on `χ`, `m`, `K`, `j` and
`l`. -/
theorem exists_norm_iteratedFDeriv_smul_coefficient_le_seminorm (χ : FrequencyCutoff E)
    (K : Compacts X) (j l : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ a : HomogeneousSymbol X E V W m, ∀ x ∈ K, ∀ (ξ : E) (u : Fin j → X)
      (w : Fin l → E),
      ‖iteratedFDeriv ℝ (j + l) (fun p : X × E ↦ χ p.2 • a.coefficient p) (x, ξ)
          (Fin.append (fun i ↦ (u i, 0)) (fun i ↦ (0, w i)))‖ ≤
        C * ((Finset.range (j + l + 1)).sup fun i ↦ HomogeneousSymbol.seminorm K i) a *
          (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) * ((∏ i, ‖u i‖) * ∏ i, ‖w i‖) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_iteratedFDeriv_smul_coefficient_le_of_norm_le_two
    (V := V) (W := W) (m := m) χ K (j + l)
  refine ⟨C₁ * 5 ^ (|m - l| / 2) + 2 ^ (|m - l| / 2), by positivity, fun a x hx ξ u w ↦ ?_⟩
  set P := ((Finset.range (j + l + 1)).sup fun i ↦ HomogeneousSymbol.seminorm K i) a
  have hP : 0 ≤ P := apply_nonneg _ _
  have hw : 0 < (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by positivity
  have hprod : 0 ≤ (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by positivity
  rcases le_or_gt ‖ξ‖ 2 with hξ2 | hξ2
  · -- Near the zero frequency use the bound of the Leibniz rule.
    refine ((iteratedFDeriv ℝ (j + l) (fun p : X × E ↦ χ p.2 • a.coefficient p)
      (x, ξ)).norm_apply_append_prod_le u w).trans
      (mul_le_mul_of_nonneg_right ((h₁ a x hx ξ hξ2).trans ?_) hprod)
    have h5 := Real.one_le_five_rpow_mul_one_add_sq_rpow (t := ‖ξ‖) (by rwa [abs_norm]) (m - l)
    calc C₁ * P ≤ C₁ * P * (5 ^ (|m - l| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2)) :=
          le_mul_of_one_le_right (by positivity) h5
      _ ≤ (C₁ * 5 ^ (|m - l| / 2) + 2 ^ (|m - l| / 2)) * P * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by
          nlinarith [mul_nonneg (mul_nonneg hP hw.le)
            (Real.rpow_nonneg zero_le_two (|m - l| / 2))]
  · -- At large frequencies the cut-off term is the homogeneous symbol itself.
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (two_pos.trans hξ2)
    rw [a.iteratedFDeriv_smul_coefficient_of_two_lt_norm χ hξ2]
    refine (a.norm_iteratedFDeriv_append_le_seminorm K hx hξ0 u w).trans
      (mul_le_mul_of_nonneg_right ?_ hprod)
    have hk : j + l ∈ Finset.range (j + l + 1) := Finset.self_mem_range_succ _
    have hpk : HomogeneousSymbol.seminorm K (j + l) a ≤ P := Seminorm.le_finset_sup_apply hk
    have hξw := norm_rpow_le_one_add_norm_sq_rpow (one_le_two.trans hξ2.le) (m - l)
    calc ‖ξ‖ ^ (m - l) * HomogeneousSymbol.seminorm K (j + l) a
        ≤ 2 ^ (|m - l| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) * P :=
          mul_le_mul hξw hpk (apply_nonneg _ _) (by positivity)
      _ ≤ (C₁ * 5 ^ (|m - l| / 2) + 2 ^ (|m - l| / 2)) * P * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by
          nlinarith [mul_nonneg (mul_nonneg hP hw.le)
            (mul_nonneg hC₁ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (|m - l| / 2)))]

/-- On a proper frequency space, the cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol of
degree `m` satisfies the symbol estimates of order `m`: its derivatives in `j` position
directions and `l` frequency directions are bounded by `C ⟨ξ⟩ ^ (m - l)` for positions in a
compact set and every frequency. -/
theorem exists_norm_iteratedFDeriv_smul_coefficient_le (a : HomogeneousSymbol X E V W m)
    (χ : FrequencyCutoff E) {K : Set X} (hK : IsCompact K) (j l : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ (ξ : E) (u : Fin j → X) (w : Fin l → E),
      ‖iteratedFDeriv ℝ (j + l) (fun p : X × E ↦ χ p.2 • a.coefficient p) (x, ξ)
          (Fin.append (fun i ↦ (u i, 0)) (fun i ↦ (0, w i)))‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) * (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_smul_coefficient_le_seminorm
    (V := V) (W := W) (m := m) χ ⟨K, hK⟩ j l
  set P := ((Finset.range (j + l + 1)).sup fun i ↦ HomogeneousSymbol.seminorm ⟨K, hK⟩ i) a
  refine ⟨C * P, mul_nonneg hC (apply_nonneg _ _), fun x hx ξ u w ↦ ?_⟩
  rw [mul_assoc _ (∏ i, ‖u i‖)]
  exact h a x (SetLike.mem_coe.1 (by rwa [Compacts.coe_mk])) ξ u w

end Seminorm

section Topology

variable [ProperSpace E]

variable (X E V W m) in
/-- The family of all seminorms `p_{K,k}` on the homogeneous symbols of degree `m`, indexed by the
compact sets `K` of positions and the orders `k` of differentiation. -/
def seminormFamily : SeminormFamily ℂ (HomogeneousSymbol X E V W m) (Compacts X × ℕ) :=
  fun i ↦ HomogeneousSymbol.seminorm i.1 i.2

@[simp]
theorem seminormFamily_apply (K : Compacts X) (k : ℕ) :
    seminormFamily X E V W m (K, k) = HomogeneousSymbol.seminorm K k := (rfl)

/-- The topology of homogeneous symbols: the locally convex topology of the seminorms
`p_{K,k}`, that of uniform convergence of all derivatives on compact subsets of the cosphere
bundle. -/
instance instTopologicalSpace : TopologicalSpace (HomogeneousSymbol X E V W m) :=
  (seminormFamily X E V W m).moduleFilterBasis.topology'

/-- The topology of homogeneous symbols is induced by the seminorms `p_{K,k}`. -/
theorem withSeminorms : WithSeminorms (seminormFamily X E V W m) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (HomogeneousSymbol X E V W m) :=
  (seminormFamily X E V W m).addGroupFilterBasis.isTopologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℂ (HomogeneousSymbol X E V W m) :=
  withSeminorms.continuousSMul

instance instUniformSpace : UniformSpace (HomogeneousSymbol X E V W m) :=
  fast_instance% (seminormFamily X E V W m).addGroupFilterBasis.uniformSpace

instance instIsUniformAddGroup : IsUniformAddGroup (HomogeneousSymbol X E V W m) :=
  (seminormFamily X E V W m).addGroupFilterBasis.isUniformAddGroup

instance instPolynormableSpace : PolynormableSpace ℂ (HomogeneousSymbol X E V W m) :=
  withSeminorms.toPolynormableSpace

instance instLocallyConvexSpace : LocallyConvexSpace ℝ (HomogeneousSymbol X E V W m) :=
  withSeminorms.toLocallyConvexSpace

/-- Homogeneous symbols form a T1, hence Hausdorff, space: the seminorms `p_{{x},0}` separate them,
since a homogeneous symbol is determined by its values at unit frequencies. -/
instance instT1Space : T1Space (HomogeneousSymbol X E V W m) := by
  refine withSeminorms.T1_of_separating fun a ha ↦ ?_
  obtain ⟨⟨x, ξ⟩, hxξ⟩ : ∃ p, a.coefficient p ≠ 0 := by
    by_contra! h
    exact ha (HomogeneousSymbol.ext (funext h))
  have hξ : ξ ≠ 0 := by
    rintro rfl
    exact hxξ (a.zero_covector x)
  refine ⟨(({x} : Compacts X), 0), fun h0 ↦ hxξ (norm_le_zero_iff.1 ?_)⟩
  have h := a.norm_coefficient_le_rpow_mul_seminorm {x} ((Compacts.mem_singleton _ _).2 rfl) hξ
  rwa [← seminormFamily_apply, h0, mul_zero] at h

variable (X E V W m) in
/-- Evaluation of homogeneous symbols at a point `p = (x, ξ)`, as a continuous linear map. -/
def coefficientCLM (p : X × E) : HomogeneousSymbol X E V W m →L[ℂ] V →L[ℂ] W :=
  let f : HomogeneousSymbol X E V W m →ₗ[ℂ] V →L[ℂ] W :=
    { toFun a := a.coefficient p
      map_add' _ _ := by simp
      map_smul' _ _ := by simp }
  { f with
    cont := WithSeminorms.continuous_of_isBounded withSeminorms (norm_withSeminorms ℂ _) f
      (Seminorm.IsBounded.of_real fun _ ↦ ⟨{(({p.1} : Compacts X), 0)}, ‖p.2‖ ^ m,
        fun a ↦ by
          obtain ⟨x, ξ⟩ := p
          simp only [f, LinearMap.coe_mk, AddHom.coe_mk, coe_normSeminorm, Finset.sup_singleton,
            seminormFamily_apply]
          rcases eq_or_ne ξ 0 with rfl | hξ
          · rw [zero_covector, norm_zero]
            exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) m) (apply_nonneg _ a)
          · exact a.norm_coefficient_le_rpow_mul_seminorm _ ((Compacts.mem_singleton _ _).2 rfl)
              hξ⟩) }

@[simp]
theorem coefficientCLM_apply (p : X × E) (a : HomogeneousSymbol X E V W m) :
    coefficientCLM X E V W m p a = a.coefficient p := (rfl)

/-- Evaluation of homogeneous symbols at a point `(x, ξ)` is continuous. -/
theorem continuous_coefficient_apply (p : X × E) :
    Continuous fun a : HomogeneousSymbol X E V W m ↦ a.coefficient p :=
  (coefficientCLM X E V W m p).continuous

variable (X E V W m) in
/-- The spatial derivative `a ↦ ∂_v a` as a continuous linear map. -/
def spatialDerivCLM (v : X) :
    HomogeneousSymbol X E V W m →L[ℂ] HomogeneousSymbol X E V W m :=
  let f : HomogeneousSymbol X E V W m →ₗ[ℂ] HomogeneousSymbol X E V W m :=
    { toFun a := a.spatialDeriv v
      map_add' a b := add_spatialDeriv a b v
      map_smul' c a := smul_spatialDeriv a c v }
  { f with
    cont := WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms f
      (Seminorm.IsBounded.of_real fun (⟨K, k⟩ : Compacts X × ℕ) ↦ ⟨{(K, k + 1)}, ‖v‖,
        fun a ↦ by simpa [f] using seminorm_spatialDeriv_le K k a v⟩) }

@[simp]
theorem spatialDerivCLM_apply (v : X) (a : HomogeneousSymbol X E V W m) :
    spatialDerivCLM X E V W m v a = a.spatialDeriv v := (rfl)

variable (X E V W m) in
/-- The frequency derivative `a ↦ ∂_w a`, lowering the degree by one, as a continuous linear
map. -/
def frequencyDerivCLM (w : E) :
    HomogeneousSymbol X E V W m →L[ℂ] HomogeneousSymbol X E V W (m - 1) :=
  let f : HomogeneousSymbol X E V W m →ₗ[ℂ] HomogeneousSymbol X E V W (m - 1) :=
    { toFun a := a.frequencyDeriv w
      map_add' a b := add_frequencyDeriv a b w
      map_smul' c a := smul_frequencyDeriv a c w }
  { f with
    cont := WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms f
      (Seminorm.IsBounded.of_real fun (⟨K, k⟩ : Compacts X × ℕ) ↦ ⟨{(K, k + 1)}, ‖w‖,
        fun a ↦ by simpa [f] using seminorm_frequencyDeriv_le K k a w⟩) }

@[simp]
theorem frequencyDerivCLM_apply (w : E) (a : HomogeneousSymbol X E V W m) :
    frequencyDerivCLM X E V W m w a = a.frequencyDeriv w := (rfl)

end Topology

end HomogeneousSymbol

end TauCeti
