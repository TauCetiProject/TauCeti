/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction.Basic
public import TauCeti.Analysis.ODE.ConvexInvariance
import TauCeti.Analysis.ODE.ExistUnique

/-!
# The reaction ODE `R' = Q(R)` on four-tensors

Hamilton's maximum principle for systems reduces the preservation of a curvature condition under
Ricci flow to the invariance of a closed convex set of algebraic curvature tensors under the
reaction ODE `R' = Q(R)`, where `Q = TauCeti.FourTensor.reactionTensor`. This file sets up that ODE
on the four-tensors `FourTensor V` of a finite-dimensional real inner product space `V`, and the
notion of an invariant set.

Since `Q` is locally Lipschitz, solutions exist locally from every initial tensor
(`LocallyLipschitz.exists_eq_forall_mem_Icc_hasDerivWithinAt` applied to
`TauCeti.FourTensor.locallyLipschitz_reactionTensor`) and are unique
(`TauCeti.FourTensor.eqOn_Icc_of_hasDerivWithinAt_reactionTensor`). Since `Q` is homogeneous of
degree two, the rescaling `τ ↦ c R(c τ)` of a solution is again a solution. The space of
four-tensors carries the operator norm, which is not an inner product norm; invariance of closed
convex sets is nevertheless characterized by Nagumo's tangency condition, through its
finite-dimensional normed form
`Convex.forall_mem_posTangentConeAt_iff_forall_mapsTo_Icc_of_finiteDimensional`. In particular the
algebraic curvature tensors form an invariant subspace, since `Q` preserves them.

On the round line, with `n = dim V` and `I` the constant-curvature tensor of curvature one,
`Q(κ I) = 2 (n - 1) κ² I`, so the solution from `κ₀ I` at time `a` is
`κ₀ / (1 - 2 (n - 1) κ₀ (t - a)) • I`: it stays round, and for `n ≥ 2` and `κ₀ > 0` it blows up
at time `a + 1 / (2 (n - 1) κ₀)`, the lifetime of the round sphere of curvature `κ₀`.

## Main definitions

* `TauCeti.FourTensor.IsReactionInvariant`: a set of four-tensors is invariant under `R' = Q(R)`
  if every forward solution starting in it stays in it.

## Main statements

* `TauCeti.FourTensor.isReactionInvariant_iff_forall_mem_posTangentConeAt`: Nagumo's criterion
  for `Q`: a closed convex set is invariant exactly when `Q` is a positive tangent vector of the set
  at each of its points.
* `TauCeti.FourTensor.isReactionInvariant_algebraicCurvatureSubmodule`: solutions starting at an
  algebraic curvature tensor remain algebraic curvature tensors.
* `TauCeti.FourTensor.IsReactionInvariant.smul`: invariance is preserved by nonnegative scaling.
* `TauCeti.FourTensor.eqOn_Icc_of_hasDerivWithinAt_reactionTensor`: uniqueness of solutions.
* `TauCeti.FourTensor.continuousOn_and_hasDerivWithinAt_smul_comp_mul_reactionTensor`: for
  `c > 0` the rescaling `τ ↦ c R(c τ)` of a solution on `[a, b]` is a solution on `[a / c, b / c]`.
* `TauCeti.FourTensor.mul_sub_lt_one_of_hasDerivWithinAt_reactionTensor` and
  `TauCeti.FourTensor.eqOn_smul_constantCurvature_of_hasDerivWithinAt_reactionTensor`: a solution
  from `κ₀ I` is the explicit round solution, and exists on `[a, b]` only if
  `2 (n - 1) κ₀ (b - a) < 1`.
* `TauCeti.FourTensor.isReactionInvariant_setOf_smul_constantCurvature`: the nonnegative round ray
  is invariant.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 4.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, Section 1.
-/

public section

open Filter Metric Set
open scoped NNReal Pointwise Topology

noncomputable section

namespace TauCeti

namespace FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Solutions and the round line -/

/-- **Uniqueness for the reaction ODE.** Two solutions of `R' = Q(R)` on `[a, b]` which agree at
`a` agree on `[a, b]`. -/
theorem eqOn_Icc_of_hasDerivWithinAt_reactionTensor {f g : ℝ → FourTensor V} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (reactionTensor (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (reactionTensor (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) :=
  locallyLipschitz_reactionTensor.eqOn_Icc_of_hasDerivWithinAt hf hf' hg hg' ha

/-- **Parabolic rescaling.** If `R` solves `R' = Q(R)` at time `c t`, then `τ ↦ c • R (c τ)` solves
it at time `t`, since `Q` is homogeneous of degree two. -/
theorem hasDerivWithinAt_smul_comp_mul_reactionTensor {R : ℝ → FourTensor V} {s : Set ℝ}
    {c t : ℝ} (h : HasDerivWithinAt R (reactionTensor (R (c * t))) s (c * t)) :
    HasDerivWithinAt (fun τ ↦ c • R (c * τ)) (reactionTensor (c • R (c * t))) ((c * ·) ⁻¹' s)
      t := by
  have hlin : HasDerivWithinAt (c * ·) c ((c * ·) ⁻¹' s) t := by
    simpa using ((hasDerivAt_id t).const_mul c).hasDerivWithinAt
  rw [reactionTensor_smul, sq, mul_smul]
  exact (h.scomp t hlin (mapsTo_preimage _ _)).const_smul c

/-- **Parabolic rescaling of a solution.** For `c > 0`, if `R` solves `R' = Q(R)` on `[a, b]`,
then `τ ↦ c • R (c τ)` solves it on `[a / c, b / c]`. -/
theorem continuousOn_and_hasDerivWithinAt_smul_comp_mul_reactionTensor {R : ℝ → FourTensor V}
    {a b c : ℝ} (hc : 0 < c) (hR : ContinuousOn R (Icc a b))
    (hR' : ∀ t ∈ Ico a b, HasDerivWithinAt R (reactionTensor (R t)) (Ici t) t) :
    ContinuousOn (fun τ ↦ c • R (c * τ)) (Icc (a / c) (b / c)) ∧
      ∀ τ ∈ Ico (a / c) (b / c),
        HasDerivWithinAt (fun τ ↦ c • R (c * τ)) (reactionTensor (c • R (c * τ))) (Ici τ) τ := by
  refine ⟨(hR.comp (by fun_prop) ?_).const_smul c, fun τ hτ ↦ ?_⟩
  · rw [← preimage_const_mul_Icc₀ a b hc]
    exact mapsTo_preimage _ _
  · rw [← preimage_const_mul_Ico₀ a b hc] at hτ
    -- The pointwise rescaling holds within `(c * ·) ⁻¹' Ici (c τ) = Ici τ`.
    simpa [preimage_const_mul_Ici₀ _ hc, mul_div_cancel_left₀ _ hc.ne'] using
      hasDerivWithinAt_smul_comp_mul_reactionTensor (hR' _ hτ)

/-- **The round solution.** With `n = dim V`, the curve
`τ ↦ κ₀ / (1 - 2 (n - 1) κ₀ (τ - a)) • I` through `κ₀ I` at time `a`, where `I` is the
constant-curvature tensor of curvature one, solves `R' = Q(R)` wherever its denominator does not
vanish. -/
theorem hasDerivAt_div_smul_constantCurvature {κ₀ a t : ℝ}
    (ht : 1 - 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (t - a) ≠ 0) :
    HasDerivAt
      (fun τ ↦ (κ₀ / (1 - 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (τ - a))) •
        constantCurvature V)
      (reactionTensor ((κ₀ / (1 - 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (t - a))) •
        constantCurvature V)) t := by
  rw [reactionTensor_smul_constantCurvature]
  have hden : HasDerivAt (fun τ ↦ 1 - 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (τ - a))
      (-(2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀)) t := by
    simpa using (((hasDerivAt_id t).sub_const a).const_mul
      (2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀)).const_sub 1
  convert ((hasDerivAt_const t κ₀).div hden ht).smul_const (constantCurvature V) using 2
  field_simp
  ring

/-- The quadruple `(e₀, e₁, e₀, e₁)` built from the first two vectors `e₀, e₁` of the standard
orthonormal basis, on which a four-tensor is evaluated to read off its sectional curvature along
the plane spanned by `e₀, e₁`. -/
private def stdOrthonormalBasisQuad (hn : 2 ≤ Module.finrank ℝ V) : Fin 4 → V :=
  ![stdOrthonormalBasis ℝ V ⟨0, by omega⟩, stdOrthonormalBasis ℝ V ⟨1, by omega⟩,
    stdOrthonormalBasis ℝ V ⟨0, by omega⟩, stdOrthonormalBasis ℝ V ⟨1, by omega⟩]

/-- On the quadruple `(e₀, e₁, e₀, e₁)` built from the first two vectors of the standard
orthonormal basis, the tensor `κ I` takes the value `κ`. -/
private theorem smul_constantCurvature_apply_stdOrthonormalBasisQuad
    (hn : 2 ≤ Module.finrank ℝ V) (κ : ℝ) :
    (κ • constantCurvature V) (stdOrthonormalBasisQuad hn) = κ := by
  have h01 := (stdOrthonormalBasis ℝ V).orthonormal.2 (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
    (by simp [Fin.ext_iff])
  simp [stdOrthonormalBasisQuad, h01]

/-- The denominator `1 - c (τ - a)` of the round solution is positive on `[a, b]` once
`c (b - a) < 1`. -/
private theorem one_sub_mul_sub_pos {a b c τ : ℝ} (hτ : τ ∈ Icc a b) (hb : c * (b - a) < 1) :
    0 < 1 - c * (τ - a) := by
  rcases le_total c 0 with hc | hc
  · nlinarith [hτ.1]
  · nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right hτ.2 a) hc]

/-- A solution from `κ₀ I` is the round solution on `[a, b]` as long as the denominator of the
round solution stays positive there. -/
private theorem eqOn_smul_constantCurvature_of_mul_sub_lt_one {f : ℝ → FourTensor V}
    {a b κ₀ : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (reactionTensor (f t)) (Ici t) t)
    (ha : f a = κ₀ • constantCurvature V)
    (hb : 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (b - a) < 1) :
    EqOn f (fun t ↦ (κ₀ / (1 - 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (t - a))) •
      constantCurvature V) (Icc a b) :=
  eqOn_Icc_of_hasDerivWithinAt_reactionTensor hf hf'
    (fun τ hτ ↦ (hasDerivAt_div_smul_constantCurvature (one_sub_mul_sub_pos hτ hb).ne')
      |>.continuousAt.continuousWithinAt)
    (fun τ hτ ↦ (hasDerivAt_div_smul_constantCurvature
      (one_sub_mul_sub_pos (Ico_subset_Icc_self hτ) hb).ne').hasDerivWithinAt)
    (by simp [ha])

/-- For `c, κ₀ > 0` the coefficient `κ₀ / (1 - c (t - a))` of the round solution tends to `+∞` as
`t` increases to `a + c⁻¹`. -/
private theorem tendsto_div_one_sub_mul_sub_atTop {a c κ₀ : ℝ} (hc : 0 < c) (hκ₀ : 0 < κ₀) :
    Tendsto (fun t ↦ κ₀ / (1 - c * (t - a))) (𝓝[<] (a + c⁻¹)) atTop := by
  have hden : Tendsto (fun t ↦ 1 - c * (t - a)) (𝓝[<] (a + c⁻¹)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦ ?_⟩
    · have h0 : 1 - c * (a + c⁻¹ - a) = 0 := by simp [mul_inv_cancel₀ hc.ne']
      exact h0 ▸ (by fun_prop : Continuous fun t : ℝ ↦ 1 - c * (t - a)).continuousWithinAt.tendsto
    · have := mul_lt_mul_of_pos_left (sub_lt_sub_right (mem_Iio.1 ht) a) hc
      simp only [add_sub_cancel_left, mul_inv_cancel₀ hc.ne'] at this
      exact sub_pos.2 this
  simpa [div_eq_mul_inv] using (tendsto_inv_nhdsGT_zero.comp hden).const_mul_atTop hκ₀

/-- **Lifetime of the round solution.** With `n = dim V`, if the reaction ODE `R' = Q(R)` has a
solution on `[a, b]` starting from `κ₀ I`, then `2 (n - 1) κ₀ (b - a) < 1`. For `n ≥ 2` and
`κ₀ > 0` this says that `b - a` is less than the lifetime `1 / (2 (n - 1) κ₀)` of the round
solution, which blows up at that time. -/
theorem mul_sub_lt_one_of_hasDerivWithinAt_reactionTensor [Nontrivial V] {f : ℝ → FourTensor V}
    {a b κ₀ : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (reactionTensor (f t)) (Ici t) t)
    (ha : f a = κ₀ • constantCurvature V) :
    2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (b - a) < 1 := by
  set c := 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀
  by_contra! hb
  -- Only `c > 0` allows `c (b - a) ≥ 1`; as `n ≥ 1`, this forces `n ≥ 2` and `κ₀ > 0`, and the
  -- round solution blows up at time `T = a + c⁻¹`.
  have hc : 0 < c := by
    by_contra! hc
    linarith [mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.2 hab)]
  have hn1 : (1 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := V)
  have hκ₀ : 0 < κ₀ := pos_of_mul_pos_right hc (by linarith)
  have hn : 2 ≤ Module.finrank ℝ V := by
    have : (1 : ℝ) < Module.finrank ℝ V := by
      by_contra! h
      have : c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hκ₀.le
      linarith
    exact_mod_cast this
  set T := a + c⁻¹
  have haT : a < T := lt_add_of_pos_right a (inv_pos.2 hc)
  have hTb : T ≤ b := by
    have : c⁻¹ ≤ b - a := (inv_le_iff_one_le_mul₀' hc).2 hb
    simp only [T]; linarith
  -- On `[a, T)` the solution is the round solution, by uniqueness.
  have hround : ∀ t ∈ Ico a T,
      f t = (κ₀ / (1 - c * (t - a))) • constantCurvature V := by
    intro t ht
    have hct : c * (t - a) < 1 := by
      have := mul_lt_mul_of_pos_left (sub_lt_sub_right ht.2 a) hc
      simpa [T, mul_inv_cancel₀ hc.ne'] using this
    exact eqOn_smul_constantCurvature_of_mul_sub_lt_one
      (hf.mono (Icc_subset_Icc_right (ht.2.le.trans hTb)))
      (fun τ hτ ↦ hf' τ ⟨hτ.1, hτ.2.trans_le (ht.2.le.trans hTb)⟩) ha hct ⟨ht.1, le_rfl⟩
  -- Evaluating on an orthonormal pair, `κ₀ / (1 - c (t - a))` would have a finite limit at `T`.
  let φ : FourTensor V → ℝ := fun r ↦ r (stdOrthonormalBasisQuad hn)
  have hlim : Tendsto (fun t ↦ κ₀ / (1 - c * (t - a))) (𝓝[<] T) (𝓝 (φ (f T))) := by
    have hcont : ContinuousWithinAt (φ ∘ f) (Ico a T) T :=
      ((continuous_eval_const _).comp_continuousOn hf _
        ⟨haT.le, hTb⟩).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hTb))
    rw [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT haT] at hcont
    refine hcont.congr' ?_
    rw [← nhdsWithin_Ico_eq_nhdsLT haT]
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [φ, hround t ht, smul_constantCurvature_apply_stdOrthonormalBasisQuad hn]
  -- But it tends to `+∞`.
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_div_one_sub_mul_sub_atTop hc hκ₀) _ hlim

/-- **Solutions from the round line stay round.** With `n = dim V`, a solution of the reaction ODE
`R' = Q(R)` on `[a, b]` starting from `κ₀ I` is the round solution
`t ↦ κ₀ / (1 - 2 (n - 1) κ₀ (t - a)) • I` on all of `[a, b]`. -/
theorem eqOn_smul_constantCurvature_of_hasDerivWithinAt_reactionTensor {f : ℝ → FourTensor V}
    {a b κ₀ : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (reactionTensor (f t)) (Ici t) t)
    (ha : f a = κ₀ • constantCurvature V) :
    EqOn f (fun t ↦ (κ₀ / (1 - 2 * ((Module.finrank ℝ V : ℝ) - 1) * κ₀ * (t - a))) •
      constantCurvature V) (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · simp [Icc_eq_empty_of_lt hba]
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- Over the zero space every four-tensor vanishes.
    exact fun t _ ↦ ContinuousMultilinearMap.ext fun m ↦
      ((f t).map_coord_zero 0 (Subsingleton.elim _ _)).trans
        (ContinuousMultilinearMap.map_coord_zero _ 0 (Subsingleton.elim _ _)).symm
  exact eqOn_smul_constantCurvature_of_mul_sub_lt_one hf hf' ha
    (mul_sub_lt_one_of_hasDerivWithinAt_reactionTensor hab hf hf' ha)

/-! ### Invariant sets -/

/-- A set `K` of four-tensors is *invariant under the reaction ODE* `R' = Q(R)` if every forward
solution on an interval `[a, b]` which starts in `K` stays in `K`. -/
def IsReactionInvariant (K : Set (FourTensor V)) : Prop :=
  ∀ (R : ℝ → FourTensor V) (a b : ℝ), ContinuousOn R (Icc a b) →
    (∀ t ∈ Ico a b, HasDerivWithinAt R (reactionTensor (R t)) (Ici t) t) →
      R a ∈ K → MapsTo R (Icc a b) K

/-- Unfolding `IsReactionInvariant`: every forward solution of `R' = Q(R)` on an interval `[a, b]`
which starts in `K` stays in `K`. -/
theorem isReactionInvariant_iff {K : Set (FourTensor V)} :
    IsReactionInvariant K ↔ ∀ (R : ℝ → FourTensor V) (a b : ℝ), ContinuousOn R (Icc a b) →
      (∀ t ∈ Ico a b, HasDerivWithinAt R (reactionTensor (R t)) (Ici t) t) →
        R a ∈ K → MapsTo R (Icc a b) K :=
  Iff.rfl

/-- A solution of the reaction ODE on `[a, b]` which starts in an invariant set stays in it. -/
theorem IsReactionInvariant.mapsTo {K : Set (FourTensor V)} (hK : IsReactionInvariant K)
    {R : ℝ → FourTensor V} {a b : ℝ} (hR : ContinuousOn R (Icc a b))
    (hR' : ∀ t ∈ Ico a b, HasDerivWithinAt R (reactionTensor (R t)) (Ici t) t) (ha : R a ∈ K) :
    MapsTo R (Icc a b) K :=
  hK R a b hR hR' ha

/-- **Nagumo's criterion for the reaction ODE.** A closed convex set `K` of four-tensors is
invariant under `R' = Q(R)` if and only if `Q(r)` is a positive tangent vector of `K` at every
`r ∈ K`. -/
theorem isReactionInvariant_iff_forall_mem_posTangentConeAt {K : Set (FourTensor V)}
    (hKc : Convex ℝ K) (hK : IsClosed K) :
    IsReactionInvariant K ↔ ∀ r ∈ K, reactionTensor r ∈ posTangentConeAt K r :=
  (hKc.forall_mem_posTangentConeAt_iff_forall_mapsTo_Icc_of_finiteDimensional hK
    locallyLipschitz_reactionTensor).symm

/-- The algebraic curvature tensors are invariant under the reaction ODE: a solution which starts
as an algebraic curvature tensor remains one. -/
theorem isReactionInvariant_algebraicCurvatureSubmodule :
    IsReactionInvariant (algebraicCurvatureSubmodule V : Set (FourTensor V)) := by
  refine (isReactionInvariant_iff_forall_mem_posTangentConeAt
    (algebraicCurvatureSubmodule V).convex isClosed_algebraicCurvatureSubmodule).2 fun r hr ↦
      mem_posTangentConeAt_of_segment_subset ?_
  exact (algebraicCurvatureSubmodule V).convex.segment_subset hr
    (add_mem hr (reactionTensor_mem r hr))

/-- The intersection of two sets invariant under the reaction ODE is invariant. -/
theorem IsReactionInvariant.inter {K L : Set (FourTensor V)} (hK : IsReactionInvariant K)
    (hL : IsReactionInvariant L) : IsReactionInvariant (K ∩ L) :=
  fun _ _ _ hR hR' ha ↦ (hK.mapsTo hR hR' ha.1).inter (hL.mapsTo hR hR' ha.2)

/-- The intersection of a family of sets invariant under the reaction ODE is invariant. -/
theorem isReactionInvariant_iInter {ι : Sort*} {K : ι → Set (FourTensor V)}
    (hK : ∀ i, IsReactionInvariant (K i)) : IsReactionInvariant (⋂ i, K i) :=
  fun _ _ _ hR hR' ha ↦ mapsTo_iInter.2 fun i ↦ (hK i).mapsTo hR hR' (mem_iInter.1 ha i)

/-- Invariance under the reaction ODE is preserved by scaling by `c ≥ 0`, since the rescaling
`τ ↦ c⁻¹ • R (c⁻¹ τ)` of a solution `R` is again a solution. -/
theorem IsReactionInvariant.smul {K : Set (FourTensor V)} (hK : IsReactionInvariant K) {c : ℝ}
    (hc : 0 ≤ c) : IsReactionInvariant (c • K) := by
  intro R a b hR hR' ha
  obtain ⟨k, hk, hka⟩ := ha
  rcases hc.eq_or_lt with rfl | hc
  · -- `0 • K = {0}`, and the solution from `0` is constant.
    have h0 : EqOn R (fun _ ↦ 0) (Icc a b) :=
      eqOn_Icc_of_hasDerivWithinAt_reactionTensor hR hR' continuousOn_const
        (fun t _ ↦ by simpa using hasDerivWithinAt_const t (Ici t) (0 : FourTensor V))
        (by simp [← hka])
    exact fun t ht ↦ ⟨k, hk, by simp [h0 ht]⟩
  -- The rescaled solution `τ ↦ c⁻¹ • R (c⁻¹ τ)` lives on `[a / c⁻¹, b / c⁻¹]` and starts in `K`.
  have hc' : 0 < c⁻¹ := inv_pos.2 hc
  have hinv (τ : ℝ) : c⁻¹ * (τ * c) = τ := by rw [mul_comm τ, inv_mul_cancel_left₀ hc.ne']
  obtain ⟨hS, hS'⟩ := continuousOn_and_hasDerivWithinAt_smul_comp_mul_reactionTensor hc' hR hR'
  have hmaps := hK.mapsTo hS hS'
    (by simpa [hinv, ← hka, smul_smul, inv_mul_cancel₀ hc.ne'] using hk)
  -- So `R t = c • (c⁻¹ • R (c⁻¹ (t / c⁻¹)))` lies in `c • K`.
  refine fun t ht ↦ ⟨_, hmaps (x := t / c⁻¹) ⟨div_le_div_of_nonneg_right ht.1 hc'.le,
    div_le_div_of_nonneg_right ht.2 hc'.le⟩, ?_⟩
  simp [hinv, smul_smul, mul_inv_cancel₀ hc.ne']

/-- **The nonnegative round ray is invariant.** The set of the tensors `κ I` with `κ ≥ 0`, where
`I` is the constant-curvature tensor of curvature one, is invariant under the reaction ODE. -/
theorem isReactionInvariant_setOf_smul_constantCurvature :
    IsReactionInvariant {r : FourTensor V | ∃ κ : ℝ, 0 ≤ κ ∧ r = κ • constantCurvature V} := by
  rintro R a b hR hR' ⟨κ₀, hκ₀, ha⟩ t ht
  refine ⟨_, ?_, eqOn_smul_constantCurvature_of_hasDerivWithinAt_reactionTensor hR hR' ha ht⟩
  refine div_nonneg hκ₀ (one_sub_mul_sub_pos ht ?_).le
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- In dimension zero the coefficient `2 (n - 1) κ₀ = -2 κ₀` is nonpositive.
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
    nlinarith [ht.1.trans ht.2]
  exact mul_sub_lt_one_of_hasDerivWithinAt_reactionTensor (ht.1.trans ht.2) hR hR' ha

end FourTensor

end TauCeti
