/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.StrongTopology
public import TauCeti.Analysis.LocallyConvex.Bipolar
public import TauCeti.Analysis.LocallyConvex.DualProjectiveLimit
public import TauCeti.Analysis.LocallyConvex.FinalTopology

/-!
# Inductive limits of normed spaces with compact bonding maps

Let `B₀ → B₁ → B₂ → ⋯` be a sequence of normed spaces with continuous linear bonding maps
`T j : B j → B (j + 1)`, and let `L` be a topological vector space with compatible continuous
linear maps `ι j : B j → L`, `ι (j + 1) ∘ T j = ι j`. We say that `L` is the inductive limit of
the spectrum when every `ι j` is injective, every vector of `L` lies in the range of some `ι j`,
and a linear functional on `L` is continuous as soon as its composites with all `ι j` are
continuous. The last condition holds for the final locally convex topology of the maps `ι j`, by
`TauCeti.FinalLocallyConvexTopology.continuous_iff_continuous_comp`.

Precomposition with the maps `ι j` sends a continuous functional on `L` to a point of the
projective limit `TauCeti.dualProjectiveLimit T` (`TauCeti.dualProjectiveLimit.precomp`), and for
an inductive limit it is bijective (`TauCeti.dualProjectiveLimit.precomp_injective`,
`TauCeti.dualProjectiveLimit.precomp_surjective`).

When the bonding maps are weakly compact, in particular when they are compact, and continuous
functionals separate the points of `L`, the inductive limit is **regular**: a subset of `L` is
bounded exactly when it is the image of a bounded subset of a single space `B j`
(`TauCeti.isVonNBounded_iff_exists_subset_image_closedBall`). Indeed, evaluations at the points
of a bounded subset of `L` form a pointwise bounded family of functionals on the Fréchet space
`lim_j B j′`, and such a family consists of evaluations at a bounded subset of one space `B j`
(`TauCeti.dualProjectiveLimit.exists_forall_exists_norm_le_eval_eq`). Consequently the strong
topology on the dual of `L`, the topology of uniform convergence on bounded subsets, is the
projective-limit topology, and precomposition is an isomorphism of topological vector spaces
`L′_b ≃ lim_j B j′` (`TauCeti.dualProjectiveLimit.strongDualEquiv`).

Dually, when `L` is locally convex with separating continuous dual and the glued evaluation map
`TauCeti.dualProjectiveLimit.liftEval` is continuous (in particular whenever the topology of `L` is
at least as fine as `finalLocallyConvexTopology`, via
`TauCeti.dualProjectiveLimit.continuous_liftEval_of_le_finalLocallyConvexTopology`), evaluation is
a topological linear isomorphism `L ≃ StrongDual 𝕜 (dualProjectiveLimit T)`
(`TauCeti.dualProjectiveLimit.evalEquiv`): inverse continuity bounds any closed absolutely convex
zero-neighbourhood `U` in `L` via the boundedness of `precomp '' U°` in `dualProjectiveLimit T` and
the bipolar theorem `U°° = U`. Because `dualProjectiveLimit T` is complete and metrizable, its
strong dual is complete by `ContinuousLinearMap.instCompleteSpace`; transporting completeness along
the uniform embedding `evalEquiv` shows that `L` is complete
(`TauCeti.completeSpace_of_isWeaklyCompact_inductiveLimit`). Composing `evalEquiv` with the inverse
strong transpose of `strongDualEquiv` yields strong-bidual reflexivity
`L ≃ StrongDual 𝕜 (StrongDual 𝕜 L)` agreeing with canonical evaluation `StrongDual.eval 𝕜 L`
(`TauCeti.strongBidualEquivOfInductiveLimit`) and natural for continuous linear maps. For a `T₁`
space carrying `finalLocallyConvexTopology`, the vector-topology instances from
`TauCeti.Analysis.LocallyConvex.FinalTopology` together with the `RCLike` `SeparatingDual` instance
in `TauCeti.Analysis.LocallyConvex.Separation` discharge all hypotheses of these results directly.

A typical example is the space of holomorphic germs along a compact subset of `ℂⁿ`, the inductive
limit of the Banach spaces of bounded holomorphic functions on a shrinking sequence of
neighbourhoods, whose restriction maps are compact by Montel's theorem.

## Main declarations

* `TauCeti.isVonNBounded_iff_exists_subset_image_closedBall`: regularity of the inductive limit.
* `TauCeti.dualProjectiveLimit.strongDualEquiv`: the strong dual of the inductive limit is the
  projective limit of the dual spaces.
* `TauCeti.dualProjectiveLimit.continuous_liftEval_of_le_finalLocallyConvexTopology`: continuity of
  `liftEval` when the topology of `L` is at least as fine as `finalLocallyConvexTopology`.
* `TauCeti.dualProjectiveLimit.evalEquiv`: topological linear isomorphism
  `L ≃L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T)`.
* `TauCeti.completeSpace_of_isWeaklyCompact_inductiveLimit`: completeness of `L`.
* `TauCeti.strongBidualEquivOfInductiveLimit`: strong-bidual reflexivity
  `L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L)` agreeing with `StrongDual.eval 𝕜 L`.

## References

* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Metric Topology
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

open dualProjectiveLimit

/-- **Regularity of compact inductive limits.** Let `L` be the inductive limit of a sequence of
normed spaces `B j` with weakly compact bonding maps, in particular with compact bonding maps, and
suppose that continuous functionals separate the points of `L`. Then a subset of `L` is bounded
if and only if it lies in the image of a ball of a single space `B j`. -/
theorem isVonNBounded_iff_exists_subset_image_closedBall [SeparatingDual 𝕜 L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) {A : Set L} :
    Bornology.IsVonNBounded 𝕜 A ↔ ∃ j, ∃ R : ℝ, A ⊆ ι j '' closedBall 0 R := by
  refine ⟨fun hA ↦ ?_, fun ⟨j, R, hA⟩ ↦ ((NormedSpace.isVonNBounded_closedBall 𝕜 (B j) R).image
    (ι j)).subset hA⟩
  choose m y hy using hcover
  -- Evaluation at the points of `A` is a pointwise bounded family on `lim_j B j′`.
  have hbdd (f : dualProjectiveLimit T) :
      BddAbove (Set.range fun x : A ↦ ‖eval T (m x) (y x) f‖) := by
    obtain ⟨φ, rfl⟩ := precomp_surjective hι hinj (fun x ↦ ⟨m x, y x, hy x⟩) hfinal f
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      ((NormedSpace.isVonNBounded_iff 𝕜).1 (hA.image φ))
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa [hy] using hC _ (Set.mem_image_of_mem φ x.2)
  obtain ⟨j, R, hrep⟩ := exists_forall_exists_norm_le_eval_eq hT _ hbdd
  refine ⟨j, R, fun x hx ↦ ?_⟩
  obtain ⟨z, hz, heq⟩ := hrep ⟨x, hx⟩
  refine ⟨z, mem_closedBall_zero_iff.2 hz,
    (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun φ ↦ ?_⟩
  simpa [hy] using congr($heq (precomp ι hι φ))

namespace dualProjectiveLimit

/-- Inverse continuity of precomposition: by regularity, a bounded subset of `L` lies in the image
of a ball of some `B j`, on which a functional is controlled by its `j`-th coordinate norm. -/
private theorem continuous_symm_precomp [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) :
    Continuous (LinearEquiv.ofBijective (precomp ι hι).toLinearMap
      ⟨precomp_injective hι hcover, precomp_surjective hι hinj hcover hfinal⟩).symm := by
  have hbij : Function.Bijective (precomp ι hι).toLinearMap :=
    ⟨precomp_injective hι hcover, precomp_surjective hι hinj hcover hfinal⟩
  set e := LinearEquiv.ofBijective (precomp ι hι).toLinearMap hbij
  have he (f : dualProjectiveLimit T) {n : ℕ} (z : B n) :
      e.symm f (ι n z) = (f : ∀ n, StrongDual 𝕜 (B n)) n z := by
    conv_rhs =>
      rw [← LinearEquiv.apply_ofBijective_symm_apply (precomp ι hι).toLinearMap (h := hbij) f]
    rw [ContinuousLinearMap.coe_coe, precomp_apply, coe_comp, Function.comp_apply]
  refine continuous_of_continuousAt_zero e.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis (E := L) (σ := RingHom.id 𝕜)
    nhds_basis_ball).tendsto_right_iff).2 fun ⟨S, ε⟩ ⟨hS, hε⟩ ↦ ?_
  obtain ⟨j, R, hSR⟩ :=
    (isVonNBounded_iff_exists_subset_image_closedBall hT hι hinj hcover hfinal).1 hS
  filter_upwards [eventually_nhds_zero_forall_mem_closedBall_norm_lt T j R hε] with f hf x hx
  obtain ⟨z, hz, rfl⟩ := hSR hx
  simpa [mem_ball_zero_iff, he] using hf z hz

/-- **The strong dual of a compact inductive limit.** Let `L` be the inductive limit of a sequence
of normed spaces `B j` with weakly compact bonding maps, in particular with compact bonding maps,
and suppose that continuous functionals separate the points of `L`. Then precomposition with the
maps `ι j` is an isomorphism of topological vector spaces from the strong dual `L′_b` onto the
projective limit `lim_j B j′` of the dual Banach spaces. -/
def strongDualEquiv [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) :
    StrongDual 𝕜 L ≃L[𝕜] dualProjectiveLimit T where
  __ := LinearEquiv.ofBijective (precomp ι hι).toLinearMap
    ⟨precomp_injective hι hcover, precomp_surjective hι hinj hcover hfinal⟩
  continuous_toFun := (precomp ι hι).continuous
  continuous_invFun := continuous_symm_precomp hT hι hinj hcover hfinal

section StrongDualEquiv

variable [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
  (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
  (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
  (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ)

@[simp]
theorem coe_strongDualEquiv :
    ⇑(strongDualEquiv hT hι hinj hcover hfinal) = precomp ι hι :=
  (rfl)

/-- The functional on `L` corresponding to a compatible family `f` takes the value `f j z` at
`ι j z`. -/
@[simp]
theorem strongDualEquiv_symm_apply_apply (f : dualProjectiveLimit T) {n : ℕ} (z : B n) :
    (strongDualEquiv hT hι hinj hcover hfinal).symm f (ι n z) =
      (f : ∀ n, StrongDual 𝕜 (B n)) n z := by
  conv_rhs => rw [← (strongDualEquiv hT hι hinj hcover hfinal).apply_symm_apply f]
  rw [coe_strongDualEquiv, precomp_apply, coe_comp, Function.comp_apply]

end StrongDualEquiv

/-- Continuity of the glued evaluation `liftEval` implies the scalar universal property of the
inductive limit: any linear functional on `L` whose composites with all `ι n` are continuous
factors through `liftEval` via evaluation at the resulting point of `dualProjectiveLimit T`. -/
theorem continuous_of_continuous_comp_of_continuous_liftEval
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hc : Continuous (liftEval hι hinj hcover))
    (ψ : L →ₗ[𝕜] 𝕜) (hψ : ∀ n, Continuous (ψ ∘ ι n)) :
    Continuous ψ := by
  let f : dualProjectiveLimit T :=
    ⟨fun n ↦ ⟨ψ.comp (ι n).toLinearMap, hψ n⟩, mem_dualProjectiveLimit.2 fun n ↦ by
      ext z
      simp [← hι n]⟩
  refine ((StrongDual.eval 𝕜 (dualProjectiveLimit T) f).continuous.comp hc).congr fun x ↦ ?_
  obtain ⟨n, z, rfl⟩ := hcover x
  simp [f]

/-- When the topology of `L` is at least as fine as the final locally convex topology of the stage
maps `ι n` (topologies in Lean are ordered by reverse fineness), the glued evaluation map
`liftEval` is continuous. -/
theorem continuous_liftEval_of_le_finalLocallyConvexTopology
    [∀ n, Module ℝ (B n)] [∀ n, IsScalarTower ℝ 𝕜 (B n)] [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (ht : (inferInstance : TopologicalSpace L) ≤
      finalLocallyConvexTopology fun n ↦ (ι n).toLinearMap.restrictScalars ℝ) :
    Continuous (liftEval hι hinj hcover) := by
  have : ContinuousSMul ℝ (StrongDual 𝕜 (dualProjectiveLimit T)) :=
    IsScalarTower.continuousSMul 𝕜
  have hc₀ : @Continuous L (StrongDual 𝕜 (dualProjectiveLimit T))
      (finalLocallyConvexTopology fun n ↦ (ι n).toLinearMap.restrictScalars ℝ) inferInstance
      (liftEval hι hinj hcover) :=
    (FinalLocallyConvexTopology.continuous_iff_continuous_comp
      (fun n ↦ (ι n).toLinearMap.restrictScalars ℝ) (liftEval hι hinj hcover)).2 fun n ↦
      (eval T n).continuous.congr fun z ↦ by simp
  exact @Continuous.comp L L (StrongDual 𝕜 (dualProjectiveLimit T)) inferInstance
    (finalLocallyConvexTopology fun n ↦ (ι n).toLinearMap.restrictScalars ℝ) inferInstance
    id (liftEval hι hinj hcover) hc₀ (continuous_id_iff_le.2 ht)

/-- Inverse continuity of glued evaluation: for any closed absolutely convex zero-neighbourhood `U`
in `L`, the image `precomp ι hι '' U°` is bounded in `dualProjectiveLimit T`, and uniform control
by `1` on that bounded set forces `e.symm Ξ ∈ U°° = U` by the pairing identity and the bipolar
theorem. -/
private theorem continuous_symm_liftEval [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) :
    Continuous (LinearEquiv.ofBijective (liftEval hι hinj hcover)
      ⟨liftEval_injective hι hinj hcover, liftEval_surjective hT hι hinj hcover⟩).symm := by
  have hbij : Function.Bijective (liftEval hι hinj hcover) :=
    ⟨liftEval_injective hι hinj hcover, liftEval_surjective hT hι hinj hcover⟩
  set e := LinearEquiv.ofBijective (liftEval hι hinj hcover) hbij
  have : LocallyConvexSpace 𝕜 L :=
    (locallyConvexSpace_iff 𝕜 L).2 fun x ↦ (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x).congr
      (fun s ↦ and_congr_right' convex_RCLike_iff_convex_real.symm) fun _ _ ↦ rfl
  have : ContinuousAdd (StrongDual 𝕜 (dualProjectiveLimit T)) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  refine continuous_of_continuousAt_zero e.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((nhds_hasBasis_absConvex_closed 𝕜 L).tendsto_right_iff).2
    fun U ⟨hU₀, hUclosed, hUabs⟩ ↦ ?_
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id 𝕜)
    (isVonNBounded_image_precomp_polar hι hU₀) (closedBall_mem_nhds (0 : 𝕜) zero_lt_one)] with Ξ hΞ
  -- By the bipolar theorem `U°° = closure U = U`, bound every `φ ∈ U°` on `e.symm Ξ`.
  simp only [id_eq, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
  rw [← hUclosed.closure_eq, ← hUabs.bipolar_eq_closure ⟨0, mem_of_mem_nhds hU₀⟩]
  intro φ hφ
  have hpair : φ (e.symm Ξ) = Ξ (precomp ι hι φ) := by
    calc φ (e.symm Ξ)
        = liftEval hι hinj hcover (e.symm Ξ) (precomp ι hι φ) :=
            (liftEval_apply_precomp hι hinj hcover (e.symm Ξ) φ).symm
      _ = e (e.symm Ξ) (precomp ι hι φ) := by simp only [e, LinearEquiv.ofBijective_apply]
      _ = Ξ (precomp ι hι φ) := by rw [e.apply_symm_apply]
  simpa only [topDualPairing_apply, hpair, ← mem_closedBall_zero_iff] using
    hΞ (Set.mem_image_of_mem (precomp ι hι) hφ)

/-- **Evaluation isomorphism of a compact inductive limit.** Let `L` be a locally convex
topological vector space with separating continuous dual, presented as the union of injective
compatible continuous linear maps `ι j : B j →L[𝕜] L` from normed spaces with weakly compact
bonding maps, in particular with compact bonding maps. When the glued evaluation `liftEval` is
continuous, it is an isomorphism of topological vector spaces from `L` onto the strong dual
`StrongDual 𝕜 (dualProjectiveLimit T)` of the projective limit `lim_j B j′`. -/
def evalEquiv [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) (hc : Continuous (liftEval hι hinj hcover)) :
    L ≃L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) where
  __ := LinearEquiv.ofBijective (liftEval hι hinj hcover)
    ⟨liftEval_injective hι hinj hcover, liftEval_surjective hT hι hinj hcover⟩
  continuous_toFun := hc
  continuous_invFun := continuous_symm_liftEval hT hι hinj hcover

section EvalEquiv

variable [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
  [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
  (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
  (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) (hc : Continuous (liftEval hι hinj hcover))

@[simp]
theorem coe_evalEquiv :
    ⇑(evalEquiv hT hι hinj hcover hc) = liftEval hι hinj hcover :=
  (rfl)

@[simp]
theorem toLinearMap_evalEquiv :
    (evalEquiv hT hι hinj hcover hc).toLinearMap = liftEval hι hinj hcover :=
  (rfl)

@[simp]
theorem evalEquiv_ι_apply (n : ℕ) (z : B n) :
    evalEquiv hT hι hinj hcover hc (ι n z) = eval T n z :=
  liftEval_ι_apply hι hinj hcover n z

@[simp]
theorem evalEquiv_symm_eval (n : ℕ) (z : B n) :
    (evalEquiv hT hι hinj hcover hc).symm (eval T n z) = ι n z :=
  (evalEquiv hT hι hinj hcover hc).symm_apply_eq.2 (evalEquiv_ι_apply hT hι hinj hcover hc n z).symm

theorem evalEquiv_apply_precomp (x : L) (φ : StrongDual 𝕜 L) :
    evalEquiv hT hι hinj hcover hc x (precomp ι hι φ) = φ x :=
  liftEval_apply_precomp hι hinj hcover x φ

/-- Precomposition `strongDualEquiv` followed by canonical bidual evaluation
`dualProjectiveLimit.strongBidualEquiv` on `dualProjectiveLimit T` agrees with the inverse strong
transpose `arrowCongr` of `evalEquiv`. -/
theorem strongDualEquiv_trans_strongBidualEquiv :
    (strongDualEquiv hT hι hinj hcover
      (continuous_of_continuous_comp_of_continuous_liftEval hι hinj hcover hc)).trans
      (dualProjectiveLimit.strongBidualEquiv hT) =
    (evalEquiv hT hι hinj hcover hc).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) := by
  ext φ Ξ
  obtain ⟨x, rfl⟩ := (evalEquiv hT hι hinj hcover hc).surjective Ξ
  calc ((strongDualEquiv hT hι hinj hcover
          (continuous_of_continuous_comp_of_continuous_liftEval hι hinj hcover hc)).trans
          (dualProjectiveLimit.strongBidualEquiv hT)) φ (evalEquiv hT hι hinj hcover hc x)
      = dualProjectiveLimit.strongBidualEquiv hT
          (strongDualEquiv hT hι hinj hcover
            (continuous_of_continuous_comp_of_continuous_liftEval hι hinj hcover hc) φ)
          (evalEquiv hT hι hinj hcover hc x) := by
          rw [ContinuousLinearEquiv.trans_apply]
    _ = evalEquiv hT hι hinj hcover hc x (precomp ι hι φ) := by
          rw [dualProjectiveLimit.strongBidualEquiv_apply, coe_strongDualEquiv]
    _ = φ x := evalEquiv_apply_precomp hT hι hinj hcover hc x φ
    _ = φ ((evalEquiv hT hι hinj hcover hc).symm (evalEquiv hT hι hinj hcover hc x)) := by
          rw [(evalEquiv hT hι hinj hcover hc).symm_apply_apply]
    _ = (evalEquiv hT hι hinj hcover hc).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) φ
          (evalEquiv hT hι hinj hcover hc x) := by
          simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply]

end EvalEquiv

end dualProjectiveLimit

/-- **Completeness of compact normed inductive limits.** Let `L` be a locally convex uniform
additive group over `ℝ` or `ℂ` with separating continuous dual, presented as the union of injective
compatible continuous linear maps `ι j : B j →L[𝕜] L` from normed spaces with weakly compact
bonding maps (in particular with compact bonding maps) and continuous glued evaluation `liftEval`.
Then `L` is complete: `evalEquiv` is a uniform embedding into the strong dual of the Fréchet space
`dualProjectiveLimit T`, which is complete by `ContinuousLinearMap.instCompleteSpace`. -/
theorem completeSpace_of_isWeaklyCompact_inductiveLimit
    {L : Type*} [AddCommGroup L] [Module ℝ L] [Module 𝕜 L] [IsScalarTower ℝ 𝕜 L]
    [UniformSpace L] [IsUniformAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L]
    {ι : ∀ n, B n →L[𝕜] L} (hT : ∀ n, (T n).IsWeaklyCompact)
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hc : Continuous (dualProjectiveLimit.liftEval hι hinj hcover)) :
    CompleteSpace L :=
  (completeSpace_congr (e := (dualProjectiveLimit.evalEquiv hT hι hinj hcover hc).toEquiv)
    (dualProjectiveLimit.evalEquiv hT hι hinj hcover hc).isUniformEmbedding).mpr inferInstance

/-- **Strong-bidual reflexivity of compact normed inductive limits.** Composing `evalEquiv` with
the inverse strong transpose of `strongDualEquiv` gives a topological linear isomorphism
`L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L)` whose underlying map is canonical evaluation
`StrongDual.eval 𝕜 L`. -/
def strongBidualEquivOfInductiveLimit
    [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hc : Continuous (dualProjectiveLimit.liftEval hι hinj hcover)) :
    L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L) :=
  StrongDual.bidualEquivOfDualEquiv
    (dualProjectiveLimit.strongDualEquiv hT hι hinj hcover
      (dualProjectiveLimit.continuous_of_continuous_comp_of_continuous_liftEval
        hι hinj hcover hc))
    (dualProjectiveLimit.evalEquiv hT hι hinj hcover hc)
    fun x ℓ ↦ by
      rw [dualProjectiveLimit.coe_strongDualEquiv]
      exact dualProjectiveLimit.evalEquiv_apply_precomp hT hι hinj hcover hc x ℓ

section StrongBidual

variable [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
  [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L]
  (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
  (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
  (hc : Continuous (dualProjectiveLimit.liftEval hι hinj hcover))

@[simp]
theorem coe_strongBidualEquivOfInductiveLimit :
    ⇑(strongBidualEquivOfInductiveLimit hT hι hinj hcover hc) = StrongDual.eval 𝕜 L := by
  rw [strongBidualEquivOfInductiveLimit, StrongDual.coe_bidualEquivOfDualEquiv]

theorem strongBidualEquivOfInductiveLimit_apply (x : L) (ℓ : StrongDual 𝕜 L) :
    strongBidualEquivOfInductiveLimit hT hι hinj hcover hc x ℓ = ℓ x := by
  rw [coe_strongBidualEquivOfInductiveLimit, StrongDual.eval_apply]

/-- Naturality of `strongBidualEquivOfInductiveLimit` under double strong transposition of any
continuous linear map between compact normed inductive limits. -/
theorem precomp_precomp_comp_strongBidualEquivOfInductiveLimit
    {B₂ : ℕ → Type*} [∀ n, NormedAddCommGroup (B₂ n)] [∀ n, NormedSpace 𝕜 (B₂ n)]
    {T₂ : ∀ n, B₂ n →L[𝕜] B₂ (n + 1)}
    {L₂ : Type*} [AddCommGroup L₂] [Module ℝ L₂] [Module 𝕜 L₂] [IsScalarTower ℝ 𝕜 L₂]
    [TopologicalSpace L₂] [IsTopologicalAddGroup L₂] [ContinuousSMul 𝕜 L₂]
    [LocallyConvexSpace ℝ L₂] [SeparatingDual 𝕜 L₂]
    {ι₂ : ∀ n, B₂ n →L[𝕜] L₂}
    (hT₂ : ∀ n, (T₂ n).IsWeaklyCompact) (hι₂ : ∀ n, (ι₂ (n + 1)).comp (T₂ n) = ι₂ n)
    (hinj₂ : ∀ n, Function.Injective (ι₂ n)) (hcover₂ : ∀ x : L₂, ∃ n, ∃ y, ι₂ n y = x)
    (hc₂ : Continuous (dualProjectiveLimit.liftEval hι₂ hinj₂ hcover₂))
    (S : L →L[𝕜] L₂) :
    (ContinuousLinearMap.precomp 𝕜
      (ContinuousLinearMap.precomp 𝕜 S : StrongDual 𝕜 L₂ →L[𝕜] StrongDual 𝕜 L)).comp
        (strongBidualEquivOfInductiveLimit hT hι hinj hcover hc).toContinuousLinearMap =
      (strongBidualEquivOfInductiveLimit hT₂ hι₂ hinj₂ hcover₂ hc₂).toContinuousLinearMap.comp S :=
  StrongDual.precomp_precomp_comp_eq_of_coe_eq_eval _
    (coe_strongBidualEquivOfInductiveLimit hT hι hinj hcover hc) _
    (coe_strongBidualEquivOfInductiveLimit hT₂ hι₂ hinj₂ hcover₂ hc₂) S

/-- Any continuous linear map `S` between compact normed inductive limits is recovered from its
double strong transpose by conjugating with `strongBidualEquivOfInductiveLimit`. -/
theorem strongBidualEquivOfInductiveLimit_symm_comp_precomp_precomp
    {B₂ : ℕ → Type*} [∀ n, NormedAddCommGroup (B₂ n)] [∀ n, NormedSpace 𝕜 (B₂ n)]
    {T₂ : ∀ n, B₂ n →L[𝕜] B₂ (n + 1)}
    {L₂ : Type*} [AddCommGroup L₂] [Module ℝ L₂] [Module 𝕜 L₂] [IsScalarTower ℝ 𝕜 L₂]
    [TopologicalSpace L₂] [IsTopologicalAddGroup L₂] [ContinuousSMul 𝕜 L₂]
    [LocallyConvexSpace ℝ L₂] [SeparatingDual 𝕜 L₂]
    {ι₂ : ∀ n, B₂ n →L[𝕜] L₂}
    (hT₂ : ∀ n, (T₂ n).IsWeaklyCompact) (hι₂ : ∀ n, (ι₂ (n + 1)).comp (T₂ n) = ι₂ n)
    (hinj₂ : ∀ n, Function.Injective (ι₂ n)) (hcover₂ : ∀ x : L₂, ∃ n, ∃ y, ι₂ n y = x)
    (hc₂ : Continuous (dualProjectiveLimit.liftEval hι₂ hinj₂ hcover₂))
    (S : L →L[𝕜] L₂) :
    (strongBidualEquivOfInductiveLimit hT₂ hι₂ hinj₂ hcover₂ hc₂).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.precomp 𝕜
        (ContinuousLinearMap.precomp 𝕜 S : StrongDual 𝕜 L₂ →L[𝕜] StrongDual 𝕜 L)).comp
          (strongBidualEquivOfInductiveLimit hT hι hinj hcover hc).toContinuousLinearMap) = S :=
  StrongDual.symm_comp_precomp_precomp_comp_eq_of_coe_eq_eval _
    (coe_strongBidualEquivOfInductiveLimit hT hι hinj hcover hc) _
    (coe_strongBidualEquivOfInductiveLimit hT₂ hι₂ hinj₂ hcover₂ hc₂) S

end StrongBidual

end TauCeti
