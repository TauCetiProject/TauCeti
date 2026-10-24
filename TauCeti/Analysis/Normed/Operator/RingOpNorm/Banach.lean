/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RingOpNorm
public import TauCeti.Analysis.Normed.Ring.UnitBall

/-!
# The Banach module and Banach ring of operators over Tate scalars

Let `R` be a seminormed ring admitting a multiplicative pseudo-uniformiser
(`TauCeti.NormedRing.IsTate R`), and let `E`, `F` be seminormed `R`-modules with contractive
scalar actions. Over such scalars every continuous linear map has a uniform bound, so the operator
norm `ContinuousLinearMap.ringOpNorm` of `TauCeti/Analysis/Normed/Operator/RingOpNorm.lean`
satisfies the usual laws. This file installs the resulting structures on `E →L[R] F` as scoped
instances in the scope `TauCeti.RingOpNorm`:

* `E →L[R] F` is a seminormed group, normed when `F` is, and ultrametric when `F` is;
* scalar actions on `F` commuting with `R` act contractively on `E →L[R] F`; in particular
  `E →L[R] F` is an `R`-module with contractive action when `R` is commutative;
* evaluation `(f, x) ↦ f x` is jointly continuous;
* `E →L[R] F` is complete when `F` is a complete normed group;
* the endomorphisms `E →L[R] E` form a seminormed ring, normed when `E` is, with `‖1‖ = 1` as
  soon as `E` has a vector of nonzero norm, and composition is jointly continuous, so that they
  form a topological ring; scalars move out of either factor of a composition when `R` is
  commutative;
* `E →L[R] F` is Hausdorff when `F` is normed.

Mathlib's topology of bounded convergence on continuous linear maps is only defined over normed
fields, so over other scalar rings these instances introduce no diamond. Over a nontrivially
normed field the scoped normed group structure equals Mathlib's
(`TauCeti.RingOpNorm.seminormedAddCommGroup_eq`), but not definitionally, so the scope should not
be opened there. On the zero module every operator has norm zero (`norm_of_subsingleton`).

For a complete normed `R`-module `E`, the endomorphism ring is a Banach ring, so *Neumann
inversion* applies: for `‖t‖ < 1` the operator `1 - t` is invertible with inverse the Neumann
series `∑ tⁿ`. This is packaged as the continuous linear automorphism
`ContinuousLinearMap.oneSub t ht`. When `E` is ultrametric, `1 - t` and its inverse are
isometries, so the inverse has operator norm one on a module with a vector of nonzero norm.

## Main definitions

* `TauCeti.RingOpNorm.seminormedAddCommGroup`, `TauCeti.RingOpNorm.normedAddCommGroup`,
  `TauCeti.RingOpNorm.seminormedRing`, `TauCeti.RingOpNorm.normedRing`: the scoped operator-norm
  structures.
* `ContinuousLinearMap.oneSub t ht`: the automorphism `1 - t` of a complete normed module over
  Tate scalars, for `‖t‖ < 1`.

## Main results

* `TauCeti.RingOpNorm.completeSpace`: the operator space is complete when the target is.
* `TauCeti.RingOpNorm.isUltrametricDist`: the operator norm is ultrametric when the target is.
* `ContinuousLinearMap.coe_oneSub_symm`: the inverse of `1 - t` is `Ring.inverse (1 - t)`,
  the sum of the Neumann series.
* `ContinuousLinearMap.norm_oneSub_apply`, `ContinuousLinearMap.norm_oneSub_symm_apply` and
  `ContinuousLinearMap.ringOpNorm_oneSub_symm`: in the ultrametric case `1 - t` and its inverse
  preserve norms, and the inverse has operator norm one (the Neumann estimate
  `TauCeti.norm_inverse_one_sub` in the Banach ring of operators).

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §3.

The completeness proof follows Mathlib's `ContinuousLinearMap.ofTendstoOfBoundedRange` and
`ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq` in
`Mathlib/Analysis/Normed/Operator/Completeness.lean`.
-/

public section

open Filter Metric Topology
open scoped TauCeti.RingOpNorm

namespace TauCeti.RingOpNorm

open ContinuousLinearMap

section Seminormed

variable {R E F : Type*} [SeminormedRing R] [NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- Over Tate scalars, continuous linear maps between seminormed modules form a seminormed group
for the operator norm. -/
noncomputable scoped instance seminormedAddCommGroup : SeminormedAddCommGroup (E →L[R] F) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := norm
      map_zero' := ringOpNorm_zero
      add_le' := ringOpNorm_add_le
      neg' := ringOpNorm_neg }

/-- The operator norm is ultrametric when the target is. -/
scoped instance isUltrametricDist [IsUltrametricDist F] : IsUltrametricDist (E →L[R] F) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ringOpNorm_add_le_max

/-- A scalar action on the target commuting with `R` acts contractively on the operators. For
commutative `R` this makes `E →L[R] F` an `R`-module with contractive action. -/
scoped instance isBoundedSMul {S : Type*} [SeminormedAddCommGroup S] [DistribSMul S F]
    [IsBoundedSMul S F] [SMulCommClass R S F] : IsBoundedSMul S (E →L[R] F) where
  dist_smul_pair' c f g := by
    simpa [dist_eq_norm, ← smul_sub] using ringOpNorm_smul_le c (f - g)
  dist_pair_smul' a b f := by
    -- Without a right distributive law, bound `a • f - b • f` pointwise through the action on `F`.
    rw [dist_zero_right, dist_eq_norm]
    refine ringOpNorm_le_bound _ (by positivity) fun x ↦ ?_
    calc ‖(a • f - b • f) x‖ = dist (a • f x) (b • f x) := by simp [dist_eq_norm]
      _ ≤ dist a b * ‖f x‖ := by simpa using dist_pair_smul a b (f x)
      _ ≤ dist a b * ‖f‖ * ‖x‖ := by
        rw [mul_assoc]; gcongr; exact le_ringOpNorm f x

/-- Evaluation `(f, x) ↦ f x` is jointly continuous for the operator norm. -/
scoped instance continuousEval : ContinuousEval (E →L[R] F) E F where
  continuous_eval := continuous_iff_continuousAt.2 fun ⟨f, x⟩ ↦ by
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    -- `g y - f x = (g - f) y + f (y - x)`, and both terms are controlled by operator norms.
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun p ↦ ?_)
      (g := fun p : (E →L[R] F) × E ↦ ‖p.1 - f‖ * ‖p.2‖ + ‖f‖ * ‖p.2 - x‖) ?_
    · calc ‖p.1 p.2 - f x‖ = ‖(p.1 - f) p.2 + f (p.2 - x)‖ := by simp
        _ ≤ ‖p.1 - f‖ * ‖p.2‖ + ‖f‖ * ‖p.2 - x‖ :=
          norm_add_le_of_le (le_ringOpNorm _ _) (le_ringOpNorm _ _)
    · simpa using ((by fun_prop : Continuous fun p : (E →L[R] F) × E ↦
        ‖p.1 - f‖ * ‖p.2‖ + ‖f‖ * ‖p.2 - x‖).tendsto (f, x))

/-- Over Tate scalars the continuous endomorphisms of a seminormed module form a seminormed ring
for the operator norm. -/
noncomputable scoped instance seminormedRing : SeminormedRing (E →L[R] E) :=
  { seminormedAddCommGroup, ContinuousLinearMap.ring with
    norm_mul_le := ringOpNorm_comp_le }

/-- Composition of operators is jointly continuous for the operator norm. This is the continuity
of multiplication in `TauCeti.RingOpNorm.seminormedRing`, stated directly for the multiplication of
continuous linear maps so that instance search need not unfold the ring structure. -/
scoped instance continuousMul : ContinuousMul (E →L[R] E) :=
  (NonUnitalSeminormedRing.toIsTopologicalRing (α := E →L[R] E)).toContinuousMul

/-- The operators form a topological ring for the operator norm. As for
`TauCeti.RingOpNorm.continuousMul`, this is stated directly for continuous linear maps so that
instance search need not unfold the ring structure. -/
scoped instance isTopologicalRing : IsTopologicalRing (E →L[R] E) :=
  NonUnitalSeminormedRing.toIsTopologicalRing (α := E →L[R] E)

/-- The identity has operator norm one on a module with a vector of nonzero norm. -/
scoped instance normOneClass [NontrivialTopology E] : NormOneClass (E →L[R] E) :=
  ⟨ringOpNorm_id⟩

end Seminormed

section Comm

variable {R E : Type*} [SeminormedCommRing R] [NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]

/-- Scalars move out of the left factor of a composition of operators. This is stated directly:
for some modules, such as `C₀(I, R)`, instance search does not derive it from
`ContinuousLinearMap.algebra` through `IsScalarTower.right` once
`TauCeti.RingOpNorm.seminormedRing` is in scope. -/
scoped instance isScalarTower : IsScalarTower R (E →L[R] E) (E →L[R] E) :=
  ⟨fun a f g ↦ smul_comp a f g⟩

/-- Scalars move out of the right factor of a composition of operators. As for
`TauCeti.RingOpNorm.isScalarTower`, this is stated directly. -/
scoped instance smulCommClass : SMulCommClass R (E →L[R] E) (E →L[R] E) :=
  ⟨fun a f g ↦ (comp_smul f a g).symm⟩

end Comm

section Normed

variable {R E F : Type*} [SeminormedRing R] [NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [NormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- Over Tate scalars, continuous linear maps into a normed module form a normed group for the
operator norm. -/
noncomputable scoped instance normedAddCommGroup : NormedAddCommGroup (E →L[R] F) :=
  NormedAddCommGroup.ofSeparation fun f hf ↦ ContinuousLinearMap.ext fun x ↦
    norm_le_zero_iff.mp <| by simpa [hf] using le_ringOpNorm f x

/-- Over Tate scalars, continuous linear maps into a normed module form a Hausdorff space for the
operator norm. This is stated directly, since instance search does not find it through
`TauCeti.RingOpNorm.normedAddCommGroup`, whose metric is not reducibly the one of
`TauCeti.RingOpNorm.seminormedAddCommGroup`. -/
scoped instance t2Space : T2Space (E →L[R] F) := by
  let _ : MetricSpace (E →L[R] F) := normedAddCommGroup.toMetricSpace
  infer_instance

/-- Over Tate scalars the continuous endomorphisms of a normed module form a normed ring for the
operator norm. -/
noncomputable scoped instance normedRing {E : Type*} [NormedAddCommGroup E] [Module R E]
    [IsBoundedSMul R E] : NormedRing (E →L[R] E) :=
  { normedAddCommGroup, seminormedRing with }

/-- **Completeness of the operator space.** Over Tate scalars, continuous linear maps into a
complete normed module form a complete space for the operator norm. -/
scoped instance completeSpace [CompleteSpace F] : CompleteSpace (E →L[R] F) := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf ↦ ?_
  -- The sequence is pointwise Cauchy, so it has a pointwise limit `g`.
  have hfx (x : E) : CauchySeq fun n ↦ f n x := by
    have : LipschitzWith ‖x‖₊ fun g : E →L[R] F ↦ g x := .of_dist_le_mul fun g h ↦ by
      simpa [dist_eq_norm, mul_comm] using le_ringOpNorm (g - h) x
    exact this.uniformContinuous.comp_cauchySeq hf
  choose g hg using fun x ↦ cauchySeq_tendsto_of_complete (hfx x)
  -- The pointwise limit is linear, and bounded by a bound on the operator norms of the `f n`.
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hf.isBounded_range
  have hglim : Tendsto (fun n x ↦ f n x) atTop (𝓝 g) := tendsto_pi_nhds.2 hg
  let G : E →L[R] F :=
    (linearMapOfTendsto g (fun n ↦ (f n : E →ₗ[R] F)) hglim).mkContinuousOfExistsBound
      ⟨C, fun x ↦ le_of_tendsto (hg x).norm <| Eventually.of_forall fun n ↦
        le_of_ringOpNorm_le _ (hC _ ⟨n, rfl⟩) x⟩
  refine ⟨G, ?_⟩
  -- The Cauchy estimate `‖f n - f m‖ ≤ b n` for `m ≥ n` passes to the limit `m → ∞`.
  obtain ⟨b, hb₀, hfb, hb_lim⟩ := cauchySeq_iff_le_tendsto_0.1 hf
  refine tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ ringOpNorm_le_bound _ (hb₀ n) fun x ↦ ?_) hb_lim
  refine le_of_tendsto ((tendsto_const_nhds (x := f n x)).sub (hg x)).norm
    (eventually_atTop.2 ⟨n, fun m hm ↦ ?_⟩)
  rw [← sub_apply]
  exact le_of_ringOpNorm_le _ (by simpa [dist_eq_norm] using hfb n m n le_rfl hm) x

end Normed

/-- Over a nontrivially normed field, the scoped operator-norm group structure is Mathlib's
normed group structure on continuous linear maps. -/
theorem seminormedAddCommGroup_eq {K E F : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E] [SeminormedAddCommGroup F] [NormedSpace K F] :
    (seminormedAddCommGroup : SeminormedAddCommGroup (E →L[K] F)) =
      ContinuousLinearMap.toSeminormedAddCommGroup := by
  -- Two seminormed group structures with the same norm and group laws agree.
  suffices ∀ a b : SeminormedAddCommGroup (E →L[K] F),
      a.toNorm = b.toNorm → a.toAddCommGroup = b.toAddCommGroup → a = b from
    this _ _ (congrArg Norm.mk (funext ringOpNorm_eq_opNorm)) rfl
  rintro @⟨na, ga, ma, ha⟩ @⟨nb, gb, mb, hb⟩ (rfl : na = nb) (rfl : ga = gb)
  obtain rfl : ma = mb := PseudoMetricSpace.ext <| by
    ext x y
    rw [ha, hb]
  rfl

end TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {R E : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] [CompleteSpace E]

/-- **Neumann inversion.** On a complete normed module over Tate scalars, an operator `t` of
operator norm less than one makes `1 - t` a continuous linear automorphism, whose inverse is the
Neumann series `∑ tⁿ`. -/
noncomputable def oneSub (t : E →L[R] E) (ht : ‖t‖ < 1) : E ≃L[R] E :=
  ContinuousLinearEquiv.unitsEquiv R E (Units.oneSub t ht)

variable (t : E →L[R] E) (ht : ‖t‖ < 1)

/-- The automorphism `oneSub t ht` is the operator `1 - t`. -/
@[simp]
theorem coe_oneSub : (oneSub t ht : E →L[R] E) = 1 - t :=
  (rfl)

/-- The automorphism `oneSub t ht` sends `x` to `x - t x`. -/
@[simp]
theorem oneSub_apply (x : E) : oneSub t ht x = x - t x :=
  (rfl)

/-- The inverse of `1 - t` is the ring inverse of `1 - t` in the Banach ring of operators. -/
theorem coe_oneSub_symm : ((oneSub t ht).symm : E →L[R] E) = Ring.inverse (1 - t) :=
  ContinuousLinearMap.ext fun x ↦ congr($(geom_series_eq_inverse t ht) x)

/-- The inverse of `1 - t` is the sum of the Neumann series `∑ tⁿ`. -/
theorem hasSum_oneSub_symm : HasSum (fun n ↦ t ^ n) ((oneSub t ht).symm : E →L[R] E) := by
  rw [coe_oneSub_symm]
  exact hasSum_geom_series_inverse t ht

section Ultrametric

variable [IsUltrametricDist E]

/-- In an ultrametric module, `1 - t` preserves norms when `‖t‖ < 1`. -/
theorem norm_oneSub_apply (x : E) : ‖oneSub t ht x‖ = ‖x‖ := by
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · have htx : ‖t x‖ ≤ 0 := (le_ringOpNorm t x).trans (by simp [← hx])
    rw [← hx, oneSub_apply]
    exact le_antisymm ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _)
  · have htx : ‖t x‖ < ‖x‖ :=
      (le_ringOpNorm t x).trans_lt (mul_lt_of_lt_one_left hx ht)
    rw [oneSub_apply, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by simpa using htx.ne'), norm_neg, max_eq_left htx.le]

/-- In an ultrametric module, the inverse of `1 - t` preserves norms when `‖t‖ < 1`. -/
@[simp]
theorem norm_oneSub_symm_apply (x : E) : ‖(oneSub t ht).symm x‖ = ‖x‖ := by
  simpa using (norm_oneSub_apply t ht ((oneSub t ht).symm x)).symm

/-- In an ultrametric module with a nonzero vector, the inverse of `1 - t` has operator norm one
when `‖t‖ < 1`. -/
@[simp]
theorem ringOpNorm_oneSub_symm [Nontrivial E] : ‖((oneSub t ht).symm : E →L[R] E)‖ = 1 := by
  rw [coe_oneSub_symm]
  exact TauCeti.norm_inverse_one_sub ht

end Ultrametric

end ContinuousLinearMap
