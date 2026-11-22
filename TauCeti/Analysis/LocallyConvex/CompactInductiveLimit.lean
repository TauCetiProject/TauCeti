/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.DualProjectiveLimit
public import TauCeti.Analysis.LocallyConvex.FinalTopology
import Mathlib.Analysis.LocallyConvex.StrongTopology
import TauCeti.Analysis.LocallyConvex.Bounded
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Precomp
import TauCeti.Topology.Algebra.Module.Spaces.StrongDual

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

In the dual direction, gluing the continuous stage evaluations `B j →L[𝕜] (lim_k B k′)′_b` yields
`TauCeti.dualProjectiveLimit.evalInductive`. On any locally convex space `L` over `ℝ` or `ℂ`, an
explicit polar and bipolar comparison relates `evalInductive` to the topology of `L`: for any
`0`-neighborhood `U` in `L`, the image under `precomp ι hι` of `StrongDual.polar 𝕜 U` is von
Neumann bounded in `dualProjectiveLimit T`
(`TauCeti.dualProjectiveLimit.isVonNBounded_image_precomp_polar`), coincides with the evaluation
polar when `L` has the final functional-continuity property
(`TauCeti.dualProjectiveLimit.image_precomp_polar_eq`), and pulls back under `evalInductive` via
its polar to `_root_.closure U` when `U` is nonempty and absolutely convex
(`TauCeti.dualProjectiveLimit.preimage_polar_image_precomp_polar_eq_closure`). Inverse continuity
of `evalInductive` at `0` (`TauCeti.dualProjectiveLimit.comap_evalInductive_le_nhds_zero`) and its
inducing property when continuous
(`TauCeti.dualProjectiveLimit.isInducing_evalInductive_of_continuous`) follow from the general
strong-dual evaluation criterion in `TauCeti.Analysis.LocallyConvex.DoubleDual`.
Forward continuity of `evalInductive` holds whenever the topology of `L` is at least as fine as the
final locally convex topology of the maps `ι j`
(`TauCeti.dualProjectiveLimit.continuous_evalInductive_of_le_finalLocallyConvexTopology`), and also
whenever every `𝕜`-seminorm on `L` whose composites with all `ι j` are continuous is itself
continuous
(`TauCeti.dualProjectiveLimit.continuous_evalInductive_of_continuous_comp_seminorm`); it in
fact forces the topology of `L` to equal that final locally convex topology
(`TauCeti.dualProjectiveLimit.finalLocallyConvexTopology_eq_of_continuous_evalInductive`). When the
bonding maps are weakly compact and `evalInductive` is continuous (equivalently, `L` carries the
final locally convex topology), `L` is complete for its additive uniformity by transporting
completeness from the strong dual of the Fréchet space `dualProjectiveLimit T` along the surjective
uniformly inducing map `evalInductive`
(`TauCeti.dualProjectiveLimit.completeSpace_of_continuous_evalInductive`), and when `L` is also
`T₁`, `evalInductive` upgrades to the topological linear isomorphism
`L ≃L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T)` (`TauCeti.dualProjectiveLimit.evalEquiv`).

Finally, still when `L` is `T₁`, the bonding maps are weakly compact, and `evalInductive` is
continuous, composing `evalEquiv` with `(strongDualEquiv …).symm.arrowCongr (.refl 𝕜 𝕜)` constructs
the canonical strong-bidual isomorphism `L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L)`
(`TauCeti.dualProjectiveLimit.inductiveBidualEquiv`), which agrees pointwise with canonical
evaluation (`TauCeti.dualProjectiveLimit.inductiveBidualEquiv_apply_apply`), intertwines
continuous linear maps between such limits with their double strong transposes
(`TauCeti.dualProjectiveLimit.precomp_precomp_comp_inductiveBidualEquiv`), and matches
`strongDualEquiv` followed by `bidualEquiv` with `(evalEquiv …).arrowCongr (.refl 𝕜 𝕜)`
(`TauCeti.dualProjectiveLimit.strongDualEquiv_trans_bidualEquiv`).

A typical example is the space of holomorphic germs along a compact subset of `ℂⁿ`, the inductive
limit of the Banach spaces of bounded holomorphic functions on a shrinking sequence of
neighbourhoods, whose restriction maps are compact by Montel's theorem.

## Main declarations

* `TauCeti.isVonNBounded_iff_exists_subset_image_closedBall`: regularity of the inductive limit.
* `TauCeti.dualProjectiveLimit.strongDualEquiv`: the strong dual of the inductive limit is the
  projective limit of the dual spaces.
* `TauCeti.dualProjectiveLimit.preimage_polar_image_precomp_polar_eq_closure`: explicit polar and
  bipolar comparison for `evalInductive`.
* `TauCeti.dualProjectiveLimit.comap_evalInductive_le_nhds_zero`: inverse continuity of
  `evalInductive` at `0`.
* `TauCeti.dualProjectiveLimit.continuous_evalInductive_of_le_finalLocallyConvexTopology`,
  `TauCeti.dualProjectiveLimit.continuous_evalInductive_of_continuous_comp_seminorm`,
  `TauCeti.dualProjectiveLimit.finalLocallyConvexTopology_eq_of_continuous_evalInductive`: forward
  continuity and final-topology characterization.
* `TauCeti.dualProjectiveLimit.evalEquiv`: topological linear isomorphism
  `L ≃L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T)` when `evalInductive` is continuous.
* `TauCeti.dualProjectiveLimit.completeSpace_of_continuous_evalInductive`: completeness of `L` when
  `evalInductive` is continuous.
* `TauCeti.dualProjectiveLimit.inductiveBidualEquiv`: canonical strong-bidual isomorphism
  `L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L)` when `evalInductive` is continuous, and its naturality.

## References

* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
* H. H. Schaefer, *Topological Vector Spaces*, Chapter IV, §5.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Metric Topology
open scoped ComplexOrder NNReal

namespace TauCeti

section RCLike

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
  -- Evaluation at the points of `A` is a pointwise bounded family on `lim_j B j′`.
  have hbdd (f : dualProjectiveLimit T) :
      BddAbove (Set.range fun x : A ↦ ‖evalInductive hι hinj hcover x f‖) := by
    obtain ⟨φ, rfl⟩ := precomp_surjective hι hinj hcover hfinal f
    simpa using (hA.image φ).bddAbove_range_norm
  obtain ⟨j, R, hrep⟩ := exists_forall_exists_norm_le_eval_eq hT _ hbdd
  refine ⟨j, R, fun x hx ↦ ?_⟩
  obtain ⟨z, hz, heq⟩ := hrep ⟨x, hx⟩
  exact ⟨z, mem_closedBall_zero_iff.2 hz,
    evalInductive_injective hι hinj hcover ((evalInductive_ι hι hinj hcover j z).trans heq)⟩

end RCLike

namespace dualProjectiveLimit

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

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
  have hR : 0 < |R| + 1 := by positivity
  filter_upwards [(coord T j).continuous.tendsto' 0 0 (map_zero _) (ball_mem_nhds 0
    (div_pos hε hR))] with f hf x hx
  obtain ⟨z, hz, rfl⟩ := hSR hx
  rw [Set.mem_preimage, mem_ball_zero_iff, coord_apply, lt_div_iff₀ hR] at hf
  simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, mem_ball_zero_iff, he]
  calc ‖(f : ∀ n, StrongDual 𝕜 (B n)) j z‖ ≤ ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖ * (|R| + 1) :=
        (le_opNorm _ z).trans (mul_le_mul_of_nonneg_left
          ((mem_closedBall_zero_iff.1 hz).trans ((le_abs_self R).trans (le_add_of_nonneg_right
            zero_le_one))) (norm_nonneg _))
    _ < ε := hf

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

@[simp]
theorem strongDualEquiv_symm_precomp (φ : StrongDual 𝕜 L) :
    (strongDualEquiv hT hι hinj hcover hfinal).symm (precomp ι hι φ) = φ := by
  rw [← coe_strongDualEquiv hT hι hinj hcover hfinal, ContinuousLinearEquiv.symm_apply_apply]

/-- The functional on `L` corresponding to a compatible family `f` takes the value `f j z` at
`ι j z`. -/
@[simp]
theorem strongDualEquiv_symm_apply_apply (f : dualProjectiveLimit T) {n : ℕ} (z : B n) :
    (strongDualEquiv hT hι hinj hcover hfinal).symm f (ι n z) =
      (f : ∀ n, StrongDual 𝕜 (B n)) n z := by
  conv_rhs => rw [← (strongDualEquiv hT hι hinj hcover hfinal).apply_symm_apply f]
  rw [coe_strongDualEquiv, precomp_apply, coe_comp, Function.comp_apply]

/-- Evaluating the functional `(strongDualEquiv …).symm f` at any `x : L` agrees with pairing
`evalInductive … x` against `f`. -/
theorem strongDualEquiv_symm_apply_eq_evalInductive (f : dualProjectiveLimit T) (x : L) :
    (strongDualEquiv hT hι hinj hcover hfinal).symm f x =
      evalInductive hι hinj hcover x f := by
  obtain ⟨n, z, rfl⟩ := hcover x
  simp

end StrongDualEquiv

end RCLike

section PolarComparison

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

/-- For any `0`-neighborhood `U` in `L`, the image in `dualProjectiveLimit T` of its strong polar
`StrongDual.polar 𝕜 U` under `precomp ι hι` is von Neumann bounded. -/
theorem isVonNBounded_image_precomp_polar
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) {U : Set L} (hU : U ∈ 𝓝 (0 : L)) :
    Bornology.IsVonNBounded 𝕜 (precomp ι hι '' StrongDual.polar 𝕜 U) :=
  (StrongDual.isVonNBounded_polar hU).image (precomp ι hι)

/-- Under the final functional-continuity property on `L`, the image under `precomp ι hι` of the
strong polar of `U ⊆ L` coincides with the polar of `evalInductive hι hinj hcover '' U` in
`dualProjectiveLimit T`. -/
theorem image_precomp_polar_eq (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) (U : Set L) :
    precomp ι hι '' StrongDual.polar 𝕜 U =
      (topDualPairing 𝕜 (dualProjectiveLimit T)).polar (evalInductive hι hinj hcover '' U) := by
  ext f
  rw [Set.mem_image, LinearMap.polar_mem_iff]
  simp only [StrongDual.mem_polar_iff, Set.forall_mem_image, topDualPairing_apply]
  refine ⟨fun ⟨φ, hφ, hf⟩ x hx ↦ ?_, fun hf ↦ ?_⟩
  · subst hf
    rw [evalInductive_apply_precomp]
    exact hφ x hx
  · obtain ⟨φ, rfl⟩ := precomp_surjective hι hinj hcover hfinal f
    refine ⟨φ, fun x hx ↦ ?_, rfl⟩
    simpa using hf hx

/-- Pulling back the polar in `StrongDual 𝕜 (dualProjectiveLimit T)` of
`precomp ι hι '' StrongDual.polar 𝕜 U` along `evalInductive` recovers the bipolar of `U` in `L`. -/
theorem preimage_polar_image_precomp_polar (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) (U : Set L) :
    evalInductive hι hinj hcover ⁻¹' StrongDual.polar 𝕜 (precomp ι hι '' StrongDual.polar 𝕜 U) =
      (topDualPairing 𝕜 L).polar (StrongDual.polar 𝕜 U) := by
  ext x
  simp [StrongDual.mem_polar_iff, LinearMap.polar_mem_iff]

end

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

/-- **Explicit bipolar comparison for `evalInductive`.** For a nonempty absolutely convex subset
`U` of a locally convex space `L` over `ℝ` or `ℂ`, pulling back the strong polar of
`precomp ι hι '' StrongDual.polar 𝕜 U` along `evalInductive` gives `_root_.closure U`. -/
theorem preimage_polar_image_precomp_polar_eq_closure
    [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L]
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    {U : Set L} (hU : AbsConvex 𝕜 U) (hne : U.Nonempty) :
    evalInductive hι hinj hcover ⁻¹' StrongDual.polar 𝕜 (precomp ι hι '' StrongDual.polar 𝕜 U) =
      _root_.closure U := by
  rw [preimage_polar_image_precomp_polar, hU.bipolar_eq_closure hne]

end RCLike

end PolarComparison

section EvaluationIsomorphism

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

/-- **Inverse continuity of `evalInductive` at `0`.** In any locally convex space `L` over `ℝ` or
`ℂ` with compatible injective covering continuous linear maps `ι n : B n →L[𝕜] L`, the pullback of
`𝓝 0` along `evalInductive` is finer than or equal to `𝓝 (0 : L)`. -/
theorem comap_evalInductive_le_nhds_zero
    [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L]
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) :
    Filter.comap (evalInductive hι hinj hcover) (𝓝 0) ≤ 𝓝 (0 : L) :=
  comap_le_nhds_zero_of_forall_apply_eq (evalInductive_apply_precomp hι hinj hcover)

/-- If `evalInductive` is continuous on a locally convex space `L` over `ℝ` or `ℂ`, then it is
inducing. -/
theorem isInducing_evalInductive_of_continuous
    [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L]
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    IsInducing (evalInductive hι hinj hcover) :=
  isInducing_of_forall_apply_eq_of_continuous (evalInductive_apply_precomp hι hinj hcover) hcont

/-- **Forward continuity from the final locally convex topology.** Whenever the topology of `L` is
at least as fine as the final locally convex topology of the maps `ι n`, the glued evaluation map
`evalInductive` is continuous into `StrongDual 𝕜 (dualProjectiveLimit T)`. -/
theorem continuous_evalInductive_of_le_finalLocallyConvexTopology
    [∀ n, Module ℝ (B n)] [∀ n, IsScalarTower ℝ 𝕜 (B n)] [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hle : ‹TopologicalSpace L› ≤
      finalLocallyConvexTopology fun n ↦ (ι n).toLinearMap.restrictScalars ℝ) :
    Continuous (evalInductive hι hinj hcover) := by
  have : ContinuousSMul ℝ (StrongDual 𝕜 (dualProjectiveLimit T)) :=
    IsScalarTower.continuousSMul 𝕜
  have hcont₀ := (FinalLocallyConvexTopology.continuous_iff_continuous_comp
    (fun n ↦ (ι n).toLinearMap.restrictScalars ℝ) (evalInductive hι hinj hcover)).2 fun n ↦
      (eval T n).continuous.congr fun z ↦ (evalInductive_ι hι hinj hcover n z).symm
  exact continuous_iff_le_induced.2 (hle.trans (continuous_iff_le_induced.1 hcont₀))

end RCLike

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

/-- If `evalInductive` is continuous, then every linear functional on `L` whose composites with all
stage maps `ι n` are continuous is itself continuous on `L`. -/
theorem continuous_of_continuous_evalInductive_of_continuous_comp
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover))
    (ψ : L →ₗ[𝕜] 𝕜) (hψ : ∀ n, Continuous (ψ ∘ ι n)) :
    Continuous ψ := by
  let f : dualProjectiveLimit T :=
    ⟨fun n ↦ ⟨ψ.comp (ι n).toLinearMap, hψ n⟩, mem_dualProjectiveLimit.2 fun n ↦ by
      ext z
      exact congrArg ψ (congr($(hι n) z))⟩
  refine ((continuous_eval_const f).comp hcont).congr fun x ↦ ?_
  obtain ⟨n, z, rfl⟩ := hcover x
  simp [f]

/-- **Forward continuity from stagewise-tested seminorms.** If every `𝕜`-seminorm on `L` whose
composites with all stage maps `ι n` are continuous is itself continuous, then the glued evaluation
map `evalInductive` is continuous: on a bounded subset `Q` of `dualProjectiveLimit T`, each
coordinate projection is norm-bounded, so the supremum seminorm over `Q` is bounded on every stage
`B n` and therefore continuous on `L`. -/
theorem continuous_evalInductive_of_continuous_comp_seminorm [IsTopologicalAddGroup L]
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hsem : ∀ q : Seminorm 𝕜 L, (∀ n, Continuous (q ∘ ι n)) → Continuous q) :
    Continuous (evalInductive hι hinj hcover) := by
  refine continuous_of_continuousAt_zero (evalInductive hι hinj hcover).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis (σ := RingHom.id 𝕜)
    nhds_basis_ball).tendsto_right_iff).2 fun ⟨Q, ε⟩ ⟨hQ, hε⟩ ↦ ?_
  set p : Q → Seminorm 𝕜 L := fun f ↦ (normSeminorm 𝕜 𝕜).comp
    ((applyₗ 𝕜 (RingHom.id 𝕜) f.val).toLinearMap ∘ₗ evalInductive hι hinj hcover)
  have hstage (n : ℕ) : ∃ C : ℝ≥0, ∀ f : Q, ∀ z : B n, p f (ι n z) ≤ C * ‖z‖ := by
    obtain ⟨C, hC⟩ := dualProjectiveLimit.isVonNBounded_iff.mp hQ n
    refine ⟨C.toNNReal, fun f z ↦ ?_⟩
    have hfC : ‖(f.val : ∀ k, StrongDual 𝕜 (B k)) n‖ ≤ C.toNNReal :=
      (hC f.val f.property).trans (Real.le_coe_toNNReal C)
    simpa [p] using (le_opNorm _ z).trans (mul_le_mul_of_nonneg_right hfC (norm_nonneg z))
  have hbdd : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.2 fun x ↦ by
    obtain ⟨n, z, rfl⟩ := hcover x
    obtain ⟨C, hC⟩ := hstage n
    exact ⟨C * ‖z‖, by rintro _ ⟨f, rfl⟩; exact hC f z⟩
  have hp : Continuous ⇑(⨆ f, p f : Seminorm 𝕜 L) := hsem (⨆ f, p f) fun n ↦ by
    obtain ⟨C, hC⟩ := hstage n
    exact Seminorm.continuous_of_le (p := (⨆ f, p f).comp (ι n).toLinearMap)
      (q := C • normSeminorm 𝕜 (B n)) (continuous_const.mul continuous_norm) fun z ↦ by
      rw [Seminorm.comp_apply, Seminorm.coe_iSup_eq hbdd, iSup_apply]
      simpa [NNReal.smul_def] using Real.iSup_le (fun f ↦ hC f z) (by positivity)
  filter_upwards [(⨆ f, p f).ball_mem_nhds hp hε] with x hx f hf
  rw [Seminorm.mem_ball_zero] at hx
  simpa [p, mem_ball_zero_iff] using (Seminorm.le_def.1 (le_ciSup hbdd ⟨f, hf⟩) x).trans_lt hx

end

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

/-- Auxiliary helper identifying `finalLocallyConvexTopology` with the topology induced by
`evalInductive` on a fresh module `L₀` carrying no prior `TopologicalSpace` instance. -/
private theorem eq_induced_finalLocallyConvexTopology
    [∀ n, Module ℝ (B n)] [∀ n, IsScalarTower ℝ 𝕜 (B n)]
    {L₀ : Type*} [AddCommGroup L₀] [Module 𝕜 L₀] [Module ℝ L₀] [IsScalarTower ℝ 𝕜 L₀]
    (ιₗ : ∀ n, B n →ₗ[𝕜] L₀) (hι : ∀ n, (ιₗ (n + 1)).comp (T n).toLinearMap = ιₗ n)
    (hinj : ∀ n, Function.Injective (ιₗ n)) (hcover : ∀ x : L₀, ∃ n, ∃ y, ιₗ n y = x) :
    ∃ ev : L₀ → StrongDual 𝕜 (dualProjectiveLimit T),
      (∀ n z, ev (ιₗ n z) = eval T n z) ∧
      finalLocallyConvexTopology (fun n ↦ (ιₗ n).restrictScalars ℝ) =
        TopologicalSpace.induced ev inferInstance := by
  let f : ∀ n, B n →ₗ[ℝ] L₀ := fun n ↦ (ιₗ n).restrictScalars ℝ
  let _ : TopologicalSpace L₀ := finalLocallyConvexTopology f
  let _ : ContinuousSMul 𝕜 L₀ :=
    FinalLocallyConvexTopology.continuousSMul f fun n ↦ (ιₗ n).map_smul
  let ι₀ : ∀ n, B n →L[𝕜] L₀ := fun n ↦ ⟨ιₗ n, FinalLocallyConvexTopology.continuous f n⟩
  have hι₀ : ∀ n, (ι₀ (n + 1)).comp (T n) = ι₀ n := fun n ↦ by
    ext z
    exact congr($(hι n) z)
  have hcont₀ : Continuous (evalInductive hι₀ hinj hcover) :=
    continuous_evalInductive_of_le_finalLocallyConvexTopology hι₀ hinj hcover le_rfl
  exact ⟨evalInductive hι₀ hinj hcover, evalInductive_ι hι₀ hinj hcover,
    (isInducing_evalInductive_of_continuous hι₀ hinj hcover hcont₀).eq_induced⟩

/-- On a locally convex space `L` over `ℝ` or `ℂ` with compatible injective covering continuous
linear maps `ι n : B n →L[𝕜] L`, continuity of `evalInductive` forces the topology of `L` to equal
the final locally convex topology of the maps `ι n`. -/
theorem finalLocallyConvexTopology_eq_of_continuous_evalInductive
    [∀ n, Module ℝ (B n)] [∀ n, IsScalarTower ℝ 𝕜 (B n)]
    [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L]
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    finalLocallyConvexTopology (fun n ↦ (ι n).toLinearMap.restrictScalars ℝ) =
      ‹TopologicalSpace L› := by
  obtain ⟨ev, hev, ht₀⟩ := eq_induced_finalLocallyConvexTopology (fun n ↦ (ι n).toLinearMap)
    (fun n ↦ congrArg ContinuousLinearMap.toLinearMap (hι n)) hinj hcover
  have heq : ev = evalInductive hι hinj hcover := funext fun x ↦ by
    obtain ⟨n, z, rfl⟩ := hcover x
    exact (hev n z).trans (evalInductive_ι hι hinj hcover n z).symm
  rw [ht₀, heq, ← (isInducing_evalInductive_of_continuous hι hinj hcover hcont).eq_induced]

/-- **Canonical evaluation isomorphism onto the strong dual of `dualProjectiveLimit T`.** Let `L`
be a `T₁` locally convex space over `ℝ` or `ℂ`, covered by compatible injective continuous linear
maps `ι n : B n →L[𝕜] L` from normed spaces with weakly compact bonding maps `T n`. Whenever
`evalInductive` is continuous — in particular when `L` carries the final locally convex topology of
the `ι n` — it is a topological linear isomorphism `L ≃L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T)`.
-/
def evalEquiv [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    L ≃L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) :=
  strongDualEquivOfForallApplyEq (evalInductive_apply_precomp hι hinj hcover) hcont
    (evalInductive_surjective hT hι hinj hcover)

@[simp]
theorem coe_evalEquiv [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L]
    [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    ⇑(evalEquiv hT hι hinj hcover hcont) = evalInductive hι hinj hcover :=
  coe_strongDualEquivOfForallApplyEq _ _ _

@[simp]
theorem toLinearMap_evalEquiv [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L]
    [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    (evalEquiv hT hι hinj hcover hcont).toLinearMap = evalInductive hι hinj hcover :=
  toLinearMap_strongDualEquivOfForallApplyEq _ _ _

@[simp]
theorem evalEquiv_ι [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L]
    [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) (n : ℕ) (z : B n) :
    evalEquiv hT hι hinj hcover hcont (ι n z) = eval T n z := by
  simp

@[simp]
theorem evalEquiv_symm_eval [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L]
    [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) (n : ℕ) (z : B n) :
    (evalEquiv hT hι hinj hcover hcont).symm (eval T n z) = ι n z :=
  (evalEquiv hT hι hinj hcover hcont).symm_apply_eq.2
    (evalEquiv_ι hT hι hinj hcover hcont n z).symm

/-- Precomposition `strongDualEquiv` followed by canonical bidual evaluation
`dualProjectiveLimit.bidualEquiv` on `dualProjectiveLimit T` agrees with the inverse strong
transpose `arrowCongr` of `evalEquiv`. -/
theorem strongDualEquiv_trans_bidualEquiv [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    (strongDualEquiv hT hι hinj hcover
      (continuous_of_continuous_evalInductive_of_continuous_comp hι hinj hcover hcont)).trans
      (dualProjectiveLimit.bidualEquiv hT) =
    (evalEquiv hT hι hinj hcover hcont).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) := by
  let a := strongDualEquiv hT hι hinj hcover
    (continuous_of_continuous_evalInductive_of_continuous_comp hι hinj hcover hcont)
  let b := evalEquiv hT hι hinj hcover hcont
  have h : ∀ (x : L) (ℓ : StrongDual 𝕜 L), b x (a ℓ) = ℓ x := fun x ℓ ↦ by
    simp [a, b, evalInductive_apply_precomp]
  have hbidual : dualProjectiveLimit.bidualEquiv hT =
      ContinuousLinearEquiv.dualBidualEquivOfDualEquiv a b h := by
    ext f φ
    simp
  rw [hbidual]
  exact a.trans_dualBidualEquivOfDualEquiv b h

/-- **Completeness of compact inductive limits.** Let `L` be a locally convex uniform additive
group over `ℝ` or `ℂ`, covered by compatible injective continuous linear maps `ι n : B n →L[𝕜] L`
with weakly compact bonding maps `T n`. If `evalInductive` is continuous — in particular if `L`
carries the final locally convex topology — then `L` is complete with respect to its additive
uniformity. -/
theorem completeSpace_of_continuous_evalInductive {L : Type*} [AddCommGroup L] [Module 𝕜 L]
    [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [UniformSpace L] [IsUniformAddGroup L]
    [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] {ι : ∀ n, B n →L[𝕜] L}
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    CompleteSpace L :=
  ((AddMonoidHom.isUniformInducing_of_isInducing
    (isInducing_evalInductive_of_continuous hι hinj hcover hcont)).completeSpace_congr
    (evalInductive_surjective hT hι hinj hcover)).mpr inferInstance

/-- **Strong reflexivity of compact inductive limits.** When `L` is a `T₁` locally convex space over
`ℝ` or `ℂ` covered by compatible injective continuous linear maps with weakly compact bonding maps
and `evalInductive` is continuous, canonical bidual evaluation yields a topological linear
isomorphism from `L` onto its strong bidual `StrongDual 𝕜 (StrongDual 𝕜 L)`, factoring as
`evalEquiv` followed by `(strongDualEquiv …).symm.arrowCongr (.refl 𝕜 𝕜)`. -/
def inductiveBidualEquiv [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L]
    [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L) :=
  ContinuousLinearEquiv.bidualEquivOfDualEquiv
    (strongDualEquiv hT hι hinj hcover
      (continuous_of_continuous_evalInductive_of_continuous_comp hι hinj hcover hcont))
    (evalEquiv hT hι hinj hcover hcont)
    fun x ℓ ↦ by simp [evalInductive_apply_precomp]

/-- `inductiveBidualEquiv` factors as `evalEquiv` followed by the strong transpose of
`strongDualEquiv`. -/
theorem inductiveBidualEquiv_eq_trans [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    inductiveBidualEquiv hT hι hinj hcover hcont =
      (evalEquiv hT hι hinj hcover hcont).trans
        ((strongDualEquiv hT hι hinj hcover
          (continuous_of_continuous_evalInductive_of_continuous_comp hι hinj hcover
            hcont)).symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)) :=
  ContinuousLinearEquiv.bidualEquivOfDualEquiv_eq_trans _ _ _

/-- `inductiveBidualEquiv` agrees pointwise with canonical evaluation, sending `x : L` and
`ℓ : StrongDual 𝕜 L` to `ℓ x`. -/
@[simp]
theorem inductiveBidualEquiv_apply_apply [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) (x : L) (ℓ : StrongDual 𝕜 L) :
    inductiveBidualEquiv hT hι hinj hcover hcont x ℓ = ℓ x :=
  ContinuousLinearEquiv.bidualEquivOfDualEquiv_apply_apply _ _ _ x ℓ

/-- The underlying linear map of `inductiveBidualEquiv` is the canonical bidual evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)`. -/
@[simp]
theorem toLinearMap_inductiveBidualEquiv [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    (inductiveBidualEquiv hT hι hinj hcover hcont).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  ContinuousLinearEquiv.toLinearMap_bidualEquivOfDualEquiv _ _ _

/-- The inverse of the strong transpose of `inductiveBidualEquiv` is the canonical strong-bidual
evaluation map of `StrongDual 𝕜 L`. -/
@[simp]
theorem toLinearMap_inductiveBidualEquiv_arrowCongr_refl [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
    [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover)) :
    ((inductiveBidualEquiv hT hι hinj hcover hcont).arrowCongr (.refl 𝕜 𝕜)).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  (inductiveBidualEquiv hT hι hinj hcover hcont).toLinearMap_arrowCongr_refl_of_forall_apply_eq
    (inductiveBidualEquiv_apply_apply hT hι hinj hcover hcont)

/-- **Naturality of `inductiveBidualEquiv` for continuous linear maps.** Any continuous linear map
`u : L →L[𝕜] L'` between compact inductive limits is intertwined with its double strong transpose
`precomp 𝕜 (precomp 𝕜 u)` by `inductiveBidualEquiv`. -/
theorem precomp_precomp_comp_inductiveBidualEquiv
    [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L]
    [LocallyConvexSpace ℝ L] [T1Space L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hcont : Continuous (evalInductive hι hinj hcover))
    {B' : ℕ → Type*} [∀ n, NormedAddCommGroup (B' n)] [∀ n, NormedSpace 𝕜 (B' n)]
    {T' : ∀ n, B' n →L[𝕜] B' (n + 1)} {L' : Type*} [AddCommGroup L'] [Module 𝕜 L']
    [Module ℝ L'] [IsScalarTower ℝ 𝕜 L'] [TopologicalSpace L'] [IsTopologicalAddGroup L']
    [ContinuousSMul 𝕜 L'] [LocallyConvexSpace ℝ L'] [T1Space L'] {ι' : ∀ n, B' n →L[𝕜] L'}
    (hT' : ∀ n, (T' n).IsWeaklyCompact) (hι' : ∀ n, (ι' (n + 1)).comp (T' n) = ι' n)
    (hinj' : ∀ n, Function.Injective (ι' n)) (hcover' : ∀ x : L', ∃ n, ∃ y, ι' n y = x)
    (hcont' : Continuous (evalInductive hι' hinj' hcover'))
    (u : L →L[𝕜] L') :
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 u)).comp
        (inductiveBidualEquiv hT hι hinj hcover hcont).toContinuousLinearMap =
      (inductiveBidualEquiv hT' hι' hinj' hcover' hcont').toContinuousLinearMap.comp u :=
  u.precomp_precomp_comp_of_forall_apply_eq
    (inductiveBidualEquiv_apply_apply hT hι hinj hcover hcont)
    (inductiveBidualEquiv_apply_apply hT' hι' hinj' hcover' hcont')

end RCLike

end EvaluationIsomorphism

end dualProjectiveLimit

end TauCeti
