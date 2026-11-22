/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Bounded composition in the strong operator topology

Composition preserves pointwise convergence when the outer operators are uniformly bounded
in operator norm. Only that family needs a bound, and neither space needs completeness.
For sequences on a Banach space the bound follows automatically from Banach–Steinhaus.

Operator norm bounds also pass to pointwise limits
(`ContinuousLinearMap.opNorm_le_of_tendsto_pointwise`), so closed operator-norm balls are closed
in the strong operator topology
(`PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall`), and
finite-vector approximation in a strong-operator closure yields witnesses in the set
(`PointwiseConvergenceCLM.exists_mem_forall_norm_sub_apply_lt_of_mem_closure`).

On a complete real or complex Hilbert space, orthogonal projections form a strongly closed
set. Their uniform norm bound lets idempotence pass to the strong limit; self-adjointness
passes through inner products. The closedness statements use Mathlib's
`PointwiseConvergenceCLM` copy, leaving the norm topology on continuous linear maps unchanged.

For normal operators with a normal strong limit, the adjoints also converge strongly
(`ContinuousLinearMap.tendsto_adjoint_apply_of_isStarNormal`).

## References

* Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, §2.4.
-/

public section

open Filter Topology
open scoped InnerProduct InnerProductSpace

namespace ContinuousLinearMap

section Semilinear

variable {𝕜₁ 𝕜₂ E F ι : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ] [SeminormedAddCommGroup E] [NormedSpace 𝕜₁ E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- **Norm lower semicontinuity of strong limits.** If a net of continuous semilinear maps is
eventually bounded in operator norm by `C` along a nontrivial filter and converges pointwise to
`T₀`, then `‖T₀‖ ≤ C`. Neither space needs completeness. -/
theorem opNorm_le_of_tendsto_pointwise {l : Filter ι} [l.NeBot]
    {T : ι → E →SL[σ] F} {T₀ : E →SL[σ] F} {C : ℝ}
    (hC : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (T₀ x))) :
    ‖T₀‖ ≤ C := by
  have hC0 : 0 ≤ C := by
    obtain ⟨i, hi⟩ := hC.exists
    exact (norm_nonneg _).trans hi
  exact T₀.opNorm_le_bound hC0 fun x =>
    le_of_tendsto (hT x).norm (hC.mono fun i hi => (T i).le_of_opNorm_le hi x)

end Semilinear

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A strongly convergent sequence of operators on a Banach space is uniformly norm bounded. -/
theorem exists_norm_le_of_tendsto_pointwise [CompleteSpace E]
    {T : ℕ → E →L[𝕜] F} {T₀ : E →L[𝕜] F}
    (hT : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x))) :
    ∃ C : ℝ, ∀ n, ‖T n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (hT x)).exists_norm_le
  exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩

/-- Strong convergence is preserved by composition when the outer operators are eventually
uniformly norm bounded. The inner operators need no norm bound. -/
theorem tendsto_comp_apply_of_eventually_norm_le {l : Filter ι}
    {S : ι → F →L[𝕜] G} {T : ι → E →L[𝕜] F}
    {S₀ : F →L[𝕜] G} {T₀ : E →L[𝕜] F} {C : ℝ}
    (hS : ∀ y, Tendsto (fun i => S i y) l (𝓝 (S₀ y)))
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (T₀ x)))
    (hC : ∀ᶠ i in l, ‖S i‖ ≤ C) (x : E) :
    Tendsto (fun i => (S i).comp (T i) x) l (𝓝 (S₀.comp T₀ x)) :=
  tendsto_apply_of_eventually_norm_le (T := S) (g := fun i => T i x)
    hC (hS (T₀ x)) (hT x)

/-- Composition of strongly continuous operator families is strongly continuous on any set
where the outer family has a common operator-norm bound. Taking the parameter space to be a
product of strong operator spaces gives joint continuity on norm-bounded sets. -/
theorem continuousOn_pointwise_comp_of_norm_le {X : Type*} [TopologicalSpace X]
    {S : X → F →L[𝕜] G} {T : X → E →L[𝕜] F} {s : Set X} {C : ℝ}
    (hS : ContinuousOn (fun x => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) F G (S x)) s)
    (hT : ContinuousOn (fun x => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F (T x)) s)
    (hC : ∀ x ∈ s, ‖S x‖ ≤ C) :
    ContinuousOn (fun x =>
      toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E G ((S x).comp (T x))) s := by
  intro x hx
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  -- Evaluation of `toPointwiseConvergenceCLM … f` is definitionally evaluation of `f`,
  -- in both the hypotheses and the composition goal.
  exact tendsto_comp_apply_of_eventually_norm_le
    (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (hS x hx))
    (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (hT x hx))
    (eventually_mem_nhdsWithin.mono fun y hy => hC y hy)

/-- On a Banach intermediate space, composition preserves strong convergence of sequences
without an explicit uniform bound. This does not assert joint continuity on the whole space. -/
theorem tendsto_comp_apply_of_tendsto_pointwise [CompleteSpace F]
    {S : ℕ → F →L[𝕜] G} {T : ℕ → E →L[𝕜] F}
    {S₀ : F →L[𝕜] G} {T₀ : E →L[𝕜] F}
    (hS : ∀ y, Tendsto (fun n => S n y) atTop (𝓝 (S₀ y)))
    (hT : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x))) (x : E) :
    Tendsto (fun n => (S n).comp (T n) x) atTop (𝓝 (S₀.comp T₀ x)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_pointwise hS
  exact tendsto_comp_apply_of_eventually_norm_le hS hT (Eventually.of_forall hC) x

end ContinuousLinearMap

/-! ### Strong convergence of normal operators -/

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- If normal operators `T a` converge strongly to a normal operator `T₀`, then their adjoints
converge strongly to `T₀†`. -/
theorem tendsto_adjoint_apply_of_isStarNormal {α : Type*} {l : Filter α}
    {T : α → E →L[𝕜] E} {T₀ : E →L[𝕜] E} (hT : ∀ᶠ a in l, IsStarNormal (T a))
    (hT₀ : IsStarNormal T₀) (h : ∀ x, Tendsto (fun a ↦ T a x) l (𝓝 (T₀ x))) (y : E) :
    Tendsto (fun a ↦ ((T a)†) y) l (𝓝 ((T₀†) y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- Expand `‖(T a)† y - T₀† y‖²` and use `‖(T a)† y‖ = ‖T a y‖` for the normal `T a`.
  have hsq : ∀ᶠ a in l, ‖T a y‖ ^ 2 - 2 * RCLike.re ⟪y, T a ((T₀†) y)⟫_𝕜 + ‖(T₀†) y‖ ^ 2 =
      ‖((T a)†) y - (T₀†) y‖ ^ 2 := by
    filter_upwards [hT] with a ha
    rw [@norm_sub_sq 𝕜, ← isStarNormal_iff_norm_eq_adjoint.mp ha y, adjoint_inner_left]
  -- The expanded expression tends to the same expression for `T₀`, which vanishes.
  have h0 : ‖T₀ y‖ ^ 2 - 2 * RCLike.re ⟪y, T₀ ((T₀†) y)⟫_𝕜 + ‖(T₀†) y‖ ^ 2 = 0 := by
    rw [← adjoint_inner_left, isStarNormal_iff_norm_eq_adjoint.mp hT₀ y, ← @norm_sub_sq 𝕜,
      sub_self, norm_zero, zero_pow two_ne_zero]
  have hlim := (((h y).norm.pow 2).sub ((((RCLike.continuous_re (K := 𝕜)).tendsto _).comp
    ((tendsto_const_nhds (x := y)).inner (h ((T₀†) y)))).const_mul 2)).add
      (tendsto_const_nhds (x := ‖(T₀†) y‖ ^ 2))
  rw [h0] at hlim
  simpa [Real.sqrt_sq (norm_nonneg _)] using (hlim.congr' hsq).sqrt

end ContinuousLinearMap

namespace IsStarProjection

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A strong limit of orthogonal projections is an orthogonal projection, for arbitrary nets
and with no separability or dimension restriction. -/
theorem of_tendsto_pointwise {l : Filter ι} [l.NeBot]
    {P : ι → H →L[𝕜] H} {P₀ : H →L[𝕜] H}
    (hP : ∀ᶠ i in l, IsStarProjection (P i))
    (hlim : ∀ x, Tendsto (fun i => P i x) l (𝓝 (P₀ x))) : IsStarProjection P₀ := by
  have hsq := ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hlim hlim
    (hP.mono fun i hi => hi.norm_le _)
  have hidem : IsIdempotentElem P₀ := by
    apply ContinuousLinearMap.ext
    intro x
    exact tendsto_nhds_unique (hsq x)
      ((hlim x).congr' (hP.mono fun i hi => congrArg (fun T : H →L[𝕜] H => T x)
        hi.isIdempotentElem.eq.symm))
  refine ⟨hidem, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_⟩
  exact tendsto_nhds_unique
    (((hlim x).inner tendsto_const_nhds).congr' (hP.mono fun i hi =>
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hi.isSelfAdjoint x y)))
    (tendsto_const_nhds.inner (hlim y))

end IsStarProjection

namespace PointwiseConvergenceCLM

section ClosedBall

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ] [SeminormedAddCommGroup E] [NormedSpace 𝕜₁ E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Every closed operator-norm ball is closed in the topology of pointwise convergence (the strong
operator topology). Neither space needs completeness. -/
theorem isClosed_image_toPointwiseConvergenceCLM_closedBall (f₀ : E →SL[σ] F) (r : ℝ) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F ''
      Metric.closedBall f₀ r) := by
  refine isClosed_iff_forall_filter.mpr fun T l hl hmem hlim => ?_
  have : l.NeBot := hl
  have hmem' : ∀ᶠ S in l, ‖PointwiseConvergenceCLM.toCLM S - f₀‖ ≤ r := by
    filter_upwards [le_principal_iff.mp hmem] with S ⟨S', hS', hS⟩
    rw [← hS, PointwiseConvergenceCLM.toCLM_toPointwiseConvergenceCLM]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hS'
  refine ⟨PointwiseConvergenceCLM.toCLM T, ?_,
    PointwiseConvergenceCLM.toPointwiseConvergenceCLM_toCLM T⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact ContinuousLinearMap.opNorm_le_of_tendsto_pointwise
    (T := fun S : E →SLₚₜ[σ] F => PointwiseConvergenceCLM.toCLM S - f₀) hmem' fun x => by
      simpa using ((tendsto_iff_forall_tendsto.mp hlim) x).sub_const (f₀ x)

end ClosedBall

section Closure

variable {𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- For a finite family of vectors `v`, the set of operators whose values on `v` stay within `ε` of
a fixed operator `x` is open in the topology of pointwise convergence. -/
theorem isOpen_setOf_forall_norm_sub_apply_lt {ι : Type*} [Finite ι]
    (x : E →SL[σ] F) (v : ι → E) (ε : ℝ) :
    IsOpen {T : E →SLₚₜ[σ] F | ∀ i, ‖x (v i) - T (v i)‖ < ε} := by
  have heq : {T : E →SLₚₜ[σ] F | ∀ i, ‖x (v i) - T (v i)‖ < ε} =
      ⋂ i, {T : E →SLₚₜ[σ] F | ‖x (v i) - T (v i)‖ < ε} := by ext T; simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt (continuous_const.sub (continuous_eval_const (v i))).norm continuous_const

/-- If `x` lies in the strong operator closure of `A`, then for every finite family of vectors `v`
and `ε > 0` there is `a ∈ A` approximating `x` within `ε` on `v`. -/
theorem exists_mem_forall_norm_sub_apply_lt_of_mem_closure [ContinuousSMul 𝕜₁ E]
    {A : Set (E →SL[σ] F)} {x : E →SL[σ] F}
    (hx : ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F '' A))
    {ι : Type*} [Finite ι] (v : ι → E) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ i, ‖x (v i) - a (v i)‖ < ε := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨a, ha, hlt⟩ :=
    (ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff_norm.mp hx)
      (Finset.univ.image v) hε
  exact ⟨a, ha, fun i ↦ hlt (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i))⟩

end Closure

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Orthogonal projections are closed in the strong operator topology. -/
theorem isClosed_image_toPointwiseConvergenceCLM_setOf_isStarProjection :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      {P : H →L[𝕜] H | IsStarProjection P}) := by
  refine isClosed_iff_forall_filter.mpr fun P l hl hmem hlim => ?_
  have : l.NeBot := hl -- Supplies the instance for `IsStarProjection.of_tendsto_pointwise`.
  -- `ofFun.symm` and `toPointwiseConvergenceCLM` preserve the underlying operator
  -- definitionally, so their evaluations agree and rewrapping the limit gives `P`.
  refine ⟨(UniformConvergenceCLM.ofFun (RingHom.id 𝕜) H _).symm P,
    IsStarProjection.of_tendsto_pointwise ?_ (tendsto_iff_forall_tendsto.mp hlim), rfl⟩
  apply Filter.Eventually.mono (le_principal_iff.mp hmem)
  rintro i ⟨Q, hQ, hQi⟩
  subst i
  exact hQ

end PointwiseConvergenceCLM
