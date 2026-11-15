/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# The graph norm of a partial linear map

For a partial linear map `A : E →ₗ.[R] F` between normed spaces, the *graph norm* of a vector `x`
in the domain of `A` is

  `‖x‖_A = √(‖x‖² + ‖A x‖²)`,

the norm of `(x, A x)` in the `L²` product `WithLp 2 (E × F)`. It controls the vector and its image
at once: `max ‖x‖ ‖A x‖ ≤ ‖x‖_A ≤ ‖x‖ + ‖A x‖`. It is a norm on the domain, and convergence in it
is convergence of the vectors together with their images. Domains of unbounded operators are
compared in this norm; for instance, the cores of a closed operator are the subspaces of its domain
that are dense for the graph norm.

The main result says that a partial linear map between Banach spaces is closed exactly when its
domain is complete for the graph norm. The proof transports graph-norm Cauchy sequences along the
isometric embedding `x ↦ (x, A x)` of the domain into `WithLp 2 (E × F)`, and uses the sequential
closed-graph criterion `LinearPMap.isClosed_iff_forall_tendsto`. For an everywhere defined bounded
operator `T`, the graph norm is equivalent to the ambient norm, with
`‖x‖ ≤ ‖x‖_T ≤ √(1 + ‖T‖²) ‖x‖`.

## Main definitions

* `LinearPMap.graphNorm`: the graph norm `√(‖x‖² + ‖A x‖²)` on the domain of `A`.

## Main results

* `LinearPMap.graphNorm_sq`, `LinearPMap.norm_le_graphNorm`,
  `LinearPMap.norm_apply_le_graphNorm`: the square identity and the two lower bounds.
* `LinearPMap.graphNorm_add_le`, `LinearPMap.graphNorm_smul`, `LinearPMap.graphNorm_eq_zero`: the
  graph norm is a norm on the domain.
* `LinearPMap.graphNorm_le_sqrt_one_add_sq_mul_norm`: a relatively bounded `A` has graph norm at
  most `√(1 + C²) ‖x‖`; `LinearPMap.graphNorm_toPMap_le` is the case of a bounded operator.
* `LinearPMap.isClosed_iff_forall_exists_tendsto_graphNorm_sub`: on Banach spaces, `A` is closed
  if and only if its domain is complete for the graph norm.

## References

* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer (2012), Section 1.1.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Section III.5.2.
-/

public section

open Filter Topology WithLp

namespace LinearPMap

section Ring

variable {R E F : Type*} [Ring R] [SeminormedAddCommGroup E] [Module R E]
  [SeminormedAddCommGroup F] [Module R F]

/-- The graph norm `‖x‖_A = √(‖x‖² + ‖A x‖²)` of a vector `x` in the domain of a partial linear
map `A`. It is the norm of `(x, A x)` in the `L²` product `WithLp 2 (E × F)`
(`LinearPMap.graphNorm_eq_norm_toLp`). -/
noncomputable def graphNorm (A : E →ₗ.[R] F) (x : A.domain) : ℝ :=
  √(‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2)

variable (A : E →ₗ.[R] F) (x y : A.domain)

theorem graphNorm_def : A.graphNorm x = √(‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2) :=
  (rfl)

/-- The graph norm of `x` is the norm of `(x, A x)` in the `L²` product `WithLp 2 (E × F)`. -/
theorem graphNorm_eq_norm_toLp : A.graphNorm x = ‖toLp 2 ((x : E), A x)‖ := by
  rw [graphNorm_def, prod_norm_eq_of_L2, toLp_fst, toLp_snd]

/-- The graph-norm distance between two domain vectors is the distance between the corresponding
points of the graph in the `L²` product. -/
theorem graphNorm_sub_eq_dist : A.graphNorm (x - y) =
    dist (toLp 2 ((x : E), A x)) (toLp 2 ((y : E), A y)) := by
  rw [graphNorm_eq_norm_toLp, dist_eq_norm, ← toLp_sub, Submodule.coe_sub, map_sub,
    Prod.mk_sub_mk]

theorem graphNorm_nonneg : 0 ≤ A.graphNorm x :=
  Real.sqrt_nonneg _

theorem graphNorm_sq : A.graphNorm x ^ 2 = ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The ambient norm is bounded by the graph norm. -/
theorem norm_le_graphNorm : ‖(x : E)‖ ≤ A.graphNorm x :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (by positivity))

/-- The norm of the image is bounded by the graph norm. -/
theorem norm_apply_le_graphNorm : ‖A x‖ ≤ A.graphNorm x :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (by positivity))

/-- The graph norm dominates the max-norm `max ‖x‖ ‖A x‖` of `(x, A x)`. -/
theorem max_norm_le_graphNorm : max ‖(x : E)‖ ‖A x‖ ≤ A.graphNorm x :=
  max_le (A.norm_le_graphNorm x) (A.norm_apply_le_graphNorm x)

theorem graphNorm_le_norm_add_norm : A.graphNorm x ≤ ‖(x : E)‖ + ‖A x‖ :=
  Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [norm_nonneg (x : E), norm_nonneg (A x)]⟩

@[simp]
theorem graphNorm_zero : A.graphNorm 0 = 0 := by
  simp [graphNorm_def]

@[simp]
theorem graphNorm_neg : A.graphNorm (-x) = A.graphNorm x := by
  simp [graphNorm_def, LinearPMap.map_neg]

theorem graphNorm_sub_rev : A.graphNorm (x - y) = A.graphNorm (y - x) := by
  rw [← neg_sub, graphNorm_neg]

/-- The triangle inequality for the graph norm. -/
theorem graphNorm_add_le : A.graphNorm (x + y) ≤ A.graphNorm x + A.graphNorm y := by
  simp only [graphNorm_eq_norm_toLp, Submodule.coe_add, map_add, ← Prod.mk_add_mk, toLp_add]
  exact norm_add_le _ _

variable {A} in
/-- If `‖A x‖ ≤ C ‖x‖` on the domain, then the graph norm is at most `√(1 + C²) ‖x‖`, so it is
equivalent to the ambient norm on the domain. -/
theorem graphNorm_le_sqrt_one_add_sq_mul_norm {C : ℝ} (h : ∀ x : A.domain, ‖A x‖ ≤ C * ‖(x : E)‖)
    (x : A.domain) : A.graphNorm x ≤ √(1 + C ^ 2) * ‖(x : E)‖ := by
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) (h x) 2]

end Ring

section Normed

variable {R E F : Type*} [Ring R] [NormedAddCommGroup E] [Module R E]
  [NormedAddCommGroup F] [Module R F]

/-- On normed spaces the graph norm is definite. -/
@[simp]
theorem graphNorm_eq_zero (A : E →ₗ.[R] F) (x : A.domain) : A.graphNorm x = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (norm_le_zero_iff.mp (h ▸ A.norm_le_graphNorm x)),
    fun h => h ▸ A.graphNorm_zero⟩

end Normed

section NormedSpace

variable {𝕜 E F : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The graph norm is homogeneous. -/
theorem graphNorm_smul (A : E →ₗ.[𝕜] F) (c : 𝕜) (x : A.domain) :
    A.graphNorm (c • x) = ‖c‖ * A.graphNorm x := by
  simp only [graphNorm_eq_norm_toLp, Submodule.coe_smul, map_smul, ← Prod.smul_mk, toLp_smul,
    norm_smul]

end NormedSpace

section Bounded

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Graph norm of a bounded operator.** For an everywhere defined bounded operator `T`, the graph
norm satisfies `‖x‖_T ≤ √(1 + ‖T‖²) ‖x‖`; together with `LinearPMap.norm_le_graphNorm` this makes
it equivalent to the ambient norm. -/
theorem graphNorm_toPMap_le (T : E →L[𝕜] F) (x : (T.toLinearMap.toPMap ⊤).domain) :
    (T.toLinearMap.toPMap ⊤).graphNorm x ≤ √(1 + ‖T‖ ^ 2) * ‖(x : E)‖ :=
  graphNorm_le_sqrt_one_add_sq_mul_norm (fun y =>
    (congrArg norm ((T : E →ₗ[𝕜] F).toPMap_apply ⊤ y)).trans_le (T.le_opNorm y)) x

end Bounded

section Complete

variable {R E F : Type*} [CommRing R] [NormedAddCommGroup E] [Module R E]
  [NormedAddCommGroup F] [Module R F] {A : E →ₗ.[R] F}

/-- **The domain of a closed operator is complete in the graph norm.** If `A` is a closed partial
linear map between Banach spaces, every sequence in its domain that is Cauchy for the graph norm
converges in the graph norm to a vector of the domain. -/
theorem IsClosed.exists_tendsto_graphNorm_sub [CompleteSpace E] [CompleteSpace F]
    (hA : A.IsClosed) {u : ℕ → A.domain}
    (hu : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, A.graphNorm (u m - u n) < ε) :
    ∃ x : A.domain, Tendsto (fun n => A.graphNorm (u n - x)) atTop (𝓝 0) := by
  -- Along `x ↦ (x, A x)` the sequence becomes Cauchy in the complete space `WithLp 2 (E × F)`.
  have hc : CauchySeq fun n => toLp 2 ((u n : E), A (u n)) :=
    Metric.cauchySeq_iff.mpr fun ε hε => (hu ε hε).imp fun _ hN m hm n hn => by
      simpa only [graphNorm_sub_eq_dist] using hN m hm n hn
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  have hz' := (prod_continuous_ofLp 2 E F).continuousAt.tendsto.comp hz
  -- Its limit lies on the graph since `A` is closed.
  obtain ⟨hz₁, hz₂⟩ := hA.mem_domain_of_tendsto (fun n => (u n).2) hz'.fst_nhds hz'.snd_nhds
  refine ⟨⟨(ofLp z).1, hz₁⟩, ?_⟩
  have hzx : toLp 2 ((ofLp z).1, A ⟨(ofLp z).1, hz₁⟩) = z := by rw [hz₂, toLp_ofLp]
  simpa only [graphNorm_sub_eq_dist, hzx] using tendsto_iff_dist_tendsto_zero.mp hz

/-- A partial linear map whose domain is complete for the graph norm is closed. -/
theorem isClosed_of_forall_exists_tendsto_graphNorm_sub
    (h : ∀ u : ℕ → A.domain, (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, A.graphNorm (u m - u n) < ε) →
      ∃ x : A.domain, Tendsto (fun n => A.graphNorm (u n - x)) atTop (𝓝 0)) :
    A.IsClosed := by
  refine isClosed_iff_forall_tendsto.mpr fun u x y hx hy => ?_
  -- The points `(u n, A (u n))` converge to `(x, y)`, so `u` is Cauchy for the graph norm.
  have hz : Tendsto (fun n => toLp 2 ((u n : E), A (u n))) atTop (𝓝 (toLp 2 (x, y))) :=
    (prod_continuous_toLp 2 E F).continuousAt.tendsto.comp (hx.prodMk_nhds hy)
  obtain ⟨x', hx'⟩ := h u fun ε hε => (Metric.cauchySeq_iff.mp hz.cauchySeq ε hε).imp
    fun _ hN m hm n hn => by simpa only [graphNorm_sub_eq_dist] using hN m hm n hn
  -- Its graph-norm limit `x'` gives a second limit `(x', A x')` of the same points.
  have hz' : Tendsto (fun n => toLp 2 ((u n : E), A (u n))) atTop
      (𝓝 (toLp 2 ((x' : E), A x'))) :=
    tendsto_iff_dist_tendsto_zero.mpr (by simpa only [graphNorm_sub_eq_dist] using hx')
  have hxy := Prod.ext_iff.mp (toLp_injective 2 (tendsto_nhds_unique hz hz'))
  obtain rfl : x = x' := hxy.1
  exact ⟨x'.2, hxy.2.symm⟩

/-- **Closed operators are those with a complete graph norm.** A partial linear map between Banach
spaces is closed if and only if its domain is complete for the graph norm: every graph-norm Cauchy
sequence in the domain converges in the graph norm to a vector of the domain. -/
theorem isClosed_iff_forall_exists_tendsto_graphNorm_sub [CompleteSpace E] [CompleteSpace F] :
    A.IsClosed ↔ ∀ u : ℕ → A.domain,
      (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, A.graphNorm (u m - u n) < ε) →
        ∃ x : A.domain, Tendsto (fun n => A.graphNorm (u n - x)) atTop (𝓝 0) :=
  ⟨fun hA _ hu => hA.exists_tendsto_graphNorm_sub hu,
    isClosed_of_forall_exists_tendsto_graphNorm_sub⟩

end Complete

end LinearPMap
