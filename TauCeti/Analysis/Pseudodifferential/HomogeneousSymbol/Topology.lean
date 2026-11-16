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
import TauCeti.Analysis.Normed.Module.Multilinear.Basic

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
them in the symbol classes `S^m_{1,0}`.

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

private theorem ne_zero_of_norm_eq_one {F : Type*} [NormedAddCommGroup F] {ξ : F} (hξ : ‖ξ‖ = 1) :
    ξ ≠ 0 :=
  norm_ne_zero_iff.1 (hξ ▸ one_ne_zero)

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
      rw [iteratedFDeriv_coefficient_add a b k (p := (x, ξ)) (ne_zero_of_norm_eq_one hξ)]
      exact (norm_add_le _ _).trans
        (add_le_add (le_seminormAux K k a hx hξ) (le_seminormAux K k b hx hξ))

private theorem seminormAux_smul_le (K : Compacts X) (k : ℕ) (c : ℂ)
    (a : HomogeneousSymbol X E V W m) : seminormAux K k (c • a) ≤ ‖c‖ * seminormAux K k a :=
  seminormAux_le_bound K k _ (mul_nonneg (norm_nonneg c) (seminormAux_nonneg K k a))
    fun x hx ξ hξ ↦ by
      rw [iteratedFDeriv_coefficient_smul c a k (p := (x, ξ)) (ne_zero_of_norm_eq_one hξ),
        norm_smul]
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
  have heq := a.iteratedFDeriv_coefficient_smul_frequency (x := x) (ne_zero_of_norm_eq_one hη)
    ht k v'
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
    (ne_zero_of_norm_eq_one hη) ht u w
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
    (ne_zero_of_norm_eq_one hξ)).trans ?_
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
    (ne_zero_of_norm_eq_one hξ)).trans ?_
  rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg w)]
  exact mul_le_mul_of_nonneg_left (le_seminorm K (k + 1) a hx hξ) (norm_nonneg w)

/-- At a nonzero frequency `ξ` and a position `x ∈ K`, the value of a homogeneous symbol of degree
`m` is bounded by `‖ξ‖ ^ m p_{K,0}(a)`. -/
theorem norm_coefficient_le_rpow_mul_seminorm (K : Compacts X) (a : HomogeneousSymbol X E V W m)
    {x : X} (hx : x ∈ K) {ξ : E} (hξ : ξ ≠ 0) :
    ‖a.coefficient (x, ξ)‖ ≤ ‖ξ‖ ^ m * HomogeneousSymbol.seminorm K 0 a := by
  simpa using a.norm_iteratedFDeriv_append_le_seminorm K hx hξ (j := 0) (l := 0) Fin.elim0
    Fin.elim0

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
  refine ⟨(⟨{x}, isCompact_singleton⟩, 0), fun h0 ↦ hxξ (norm_le_zero_iff.1 ?_)⟩
  have h := a.norm_coefficient_le_rpow_mul_seminorm ⟨{x}, isCompact_singleton⟩ rfl hξ
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
      (Seminorm.IsBounded.of_real fun _ ↦ ⟨{(⟨{p.1}, isCompact_singleton⟩, 0)}, ‖p.2‖ ^ m,
        fun a ↦ by
          obtain ⟨x, ξ⟩ := p
          simp only [f, LinearMap.coe_mk, AddHom.coe_mk, coe_normSeminorm, Finset.sup_singleton,
            seminormFamily_apply]
          rcases eq_or_ne ξ 0 with rfl | hξ
          · rw [zero_covector, norm_zero]
            exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) m) (apply_nonneg _ a)
          · exact a.norm_coefficient_le_rpow_mul_seminorm _ rfl hξ⟩) }

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
