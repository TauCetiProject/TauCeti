/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.Bipolar
public import TauCeti.Analysis.LocallyConvex.DualProjectiveLimit
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Bidual

/-!
# Inductive limits of normed spaces with compact bonding maps

Let `B₀ → B₁ → B₂ → ⋯` be a sequence of normed spaces with continuous linear bonding maps
`T j : B j → B (j + 1)`, and let `L` be a topological vector space with compatible continuous
linear maps `ι j : B j → L`, `ι (j + 1) ∘ T j = ι j`. We say that `L` is the inductive limit of
the spectrum when every `ι j` is injective, every vector of `L` lies in the range of some `ι j`,
and a linear functional on `L` is continuous as soon as its composites with all `ι j` are
continuous. The last condition holds for the final locally convex topology of the maps `ι j`, by
`TauCeti.FinalLocallyConvexTopology.continuous_iff_continuous_comp`, and more strongly any
seminorm whose composites with all `ι j` are continuous is itself continuous, by
`TauCeti.FinalLocallyConvexTopology.continuous_seminorm_iff`.

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

When `L` is also a locally convex topological vector space whose continuous seminorms are tested on
the stages `B j`, canonical evaluation identifies `L` topologically with the strong dual of
`lim_j B j′` (`TauCeti.dualProjectiveLimit.evalEquiv`): forward continuity bounds the supremum over
a bounded subset of `lim_j B j′` on each stage `B j`, while inverse continuity bounds the inverse
on the polar of a closed absolutely convex zero-neighbourhood via the bipolar theorem
(`TauCeti.dualProjectiveLimit.forall_mem_image_precomp_polar_norm_evalEquiv_le_one_iff_mem`). Since
`lim_j B j′` is metrizable, its strong dual is complete, whence `L` is complete
(`TauCeti.completeSpace_of_isWeaklyCompact`), and transporting `evalEquiv` along `strongDualEquiv`
identifies `L` with its strong bidual (`TauCeti.strongBidualEquiv`), naturally in continuous linear
maps (`TauCeti.precomp_precomp_comp_strongBidualEquiv`).

A typical example is the space of holomorphic germs along a compact subset of `ℂⁿ`, the inductive
limit of the Banach spaces of bounded holomorphic functions on a shrinking sequence of
neighbourhoods, whose restriction maps are compact by Montel's theorem.

## Main declarations

* `TauCeti.isVonNBounded_iff_exists_subset_image_closedBall`: regularity of the inductive limit.
* `TauCeti.dualProjectiveLimit.strongDualEquiv`: the strong dual of the inductive limit is the
  projective limit of the dual spaces.
* `TauCeti.dualProjectiveLimit.evalEquiv`: canonical evaluation `L ≃L[𝕜] (lim_j B j′)′_b`.
* `TauCeti.dualProjectiveLimit.forall_mem_image_precomp_polar_norm_evalEquiv_le_one_iff_mem`:
  polar and bipolar comparison for `evalEquiv`.
* `TauCeti.strongBidualEquiv`: strong-bidual reflexivity `L ≃L[𝕜] (L′_b)′_b`.
* `TauCeti.precomp_precomp_comp_strongBidualEquiv`: naturality of `strongBidualEquiv`.
* `TauCeti.completeSpace_of_isWeaklyCompact`: completeness of the inductive limit `L`.

## References

* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Metric Topology
open scoped ComplexOrder NNReal

namespace TauCeti

/-- If every `𝕜`-seminorm on a topological additive group `L` whose composites with a family of
maps `f i : E i → L` are continuous is itself continuous, then the same holds for every `𝕜`-linear
map `L →ₗ[𝕜] F` into a seminormed `𝕜`-space `F`. -/
theorem continuous_of_continuous_comp_seminorm {𝕜 ι L F : Type*} [NormedField 𝕜]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : ∀ i, E i → L}
    (hsem : ∀ q : Seminorm 𝕜 L, (∀ i, Continuous (q ∘ f i)) → Continuous q)
    (ψ : L →ₗ[𝕜] F) (hψ : ∀ i, Continuous (ψ ∘ f i)) : Continuous ψ := by
  have hq : Continuous ((normSeminorm 𝕜 F).comp ψ) :=
    hsem _ fun i ↦ continuous_norm.comp (hψ i)
  refine continuous_of_continuousAt_zero ψ.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  exact Metric.nhds_basis_ball.tendsto_right_iff.2 fun ε hε ↦ by
    filter_upwards [((normSeminorm 𝕜 F).comp ψ).ball_mem_nhds hq hε] with x hx
    simpa [Seminorm.mem_ball_zero, mem_ball_zero_iff] using hx

section TopologicalSpace

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

end StrongDualEquiv

section EvalLinearMap

variable [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [SeparatingDual 𝕜 L]
  (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
  (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
  (hsem : ∀ q : Seminorm 𝕜 L, (∀ n, Continuous (q ∘ ι n)) → Continuous q)

/-- Canonical evaluation `x ↦ (f ↦ a⁻¹(f)(x))` from `L` into `StrongDual 𝕜 (dualProjectiveLimit T)`
as a linear map. -/
private def evalLinearMap : L →ₗ[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) :=
  (ContinuousLinearMap.precomp 𝕜
    (strongDualEquiv hT hι hinj hcover
      (continuous_of_continuous_comp_seminorm hsem)).symm.toContinuousLinearMap).toLinearMap.comp
    (applyₗ 𝕜 (RingHom.id 𝕜))

/-- Canonical evaluation `L → StrongDual 𝕜 (dualProjectiveLimit T)` is bijective: injectivity uses
Hahn–Banach separation on `L`, and surjectivity uses representation of continuous functionals on
`dualProjectiveLimit T` by stage vectors. -/
private theorem bijective_evalLinearMap :
    Function.Bijective (evalLinearMap hT hι hinj hcover hsem) := by
  set a := strongDualEquiv hT hι hinj hcover (continuous_of_continuous_comp_seminorm hsem)
  refine ⟨fun x y hxy ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun φ ↦ ?_,
    fun Ψ ↦ ?_⟩
  · simpa [evalLinearMap, a] using congr($hxy (a φ))
  · obtain ⟨j, z, rfl⟩ := exists_eval_eq hT Ψ
    refine ⟨ι j z, ?_⟩
    ext f
    simp [evalLinearMap]

/-- Forward continuity of canonical evaluation: on a bounded subset `Q` of `dualProjectiveLimit T`,
each coordinate projection is norm-bounded, so the supremum seminorm over `Q` is bounded on every
stage `B n` and therefore continuous on `L`. -/
private theorem continuous_evalLinearMap :
    Continuous (evalLinearMap hT hι hinj hcover hsem) := by
  set a := strongDualEquiv hT hι hinj hcover (continuous_of_continuous_comp_seminorm hsem)
  refine continuous_of_continuousAt_zero (evalLinearMap hT hι hinj hcover hsem).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis (σ := RingHom.id 𝕜)
    nhds_basis_ball).tendsto_right_iff).2 fun ⟨Q, ε⟩ ⟨hQ, hε⟩ ↦ ?_
  set p : Q → Seminorm 𝕜 L := fun f ↦ (normSeminorm 𝕜 𝕜).comp (a.symm f.1).toLinearMap
  have hstage (n : ℕ) : ∃ C : ℝ≥0, ∀ f : Q, ∀ z : B n, p f (ι n z) ≤ C * ‖z‖ := by
    obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' 𝕜).1 (hQ.image (coord T n))
    refine ⟨C.toNNReal, fun f z ↦ ?_⟩
    have hfC : ‖(f.1 : ∀ k, StrongDual 𝕜 (B k)) n‖ ≤ C.toNNReal := by
      have h := hC (coord T n f.1) (Set.mem_image_of_mem (coord T n) f.2)
      rw [coord_apply] at h
      exact h.trans (Real.le_coe_toNNReal C)
    simpa [p, a] using (le_opNorm _ z).trans (mul_le_mul_of_nonneg_right hfC (norm_nonneg z))
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
  simpa [p, evalLinearMap, a, mem_ball_zero_iff] using
    (Seminorm.le_def.1 (le_ciSup hbdd ⟨f, hf⟩) x).trans_lt hx

end EvalLinearMap

section EvalEquiv

variable [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
  [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L]
  (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
  (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
  (hsem : ∀ q : Seminorm 𝕜 L, (∀ n, Continuous (q ∘ ι n)) → Continuous q)

/-- Inverse continuity of canonical evaluation: for a closed `𝕜`-absolutely convex neighbourhood of
zero `U` in `L`, the image of `U°` in `dualProjectiveLimit T` is bounded, and functionals bounded by
`1` on that image map back into `U°° = U`. -/
private theorem continuous_symm_evalLinearMap :
    Continuous (LinearEquiv.ofBijective (evalLinearMap hT hι hinj hcover hsem)
      (bijective_evalLinearMap hT hι hinj hcover hsem)).symm := by
  have : LocallyConvexSpace 𝕜 L :=
    ⟨fun x ↦ by simpa only [convex_RCLike_iff_convex_real] using LocallyConvexSpace.convex_basis x⟩
  set e := LinearEquiv.ofBijective (evalLinearMap hT hι hinj hcover hsem)
    (bijective_evalLinearMap hT hι hinj hcover hsem)
  refine continuous_of_continuousAt_zero e.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine (nhds_hasBasis_absConvex_closed 𝕜 L).tendsto_right_iff.2
    fun U ⟨hU_nhds, hU_closed, hU_abs⟩ ↦ ?_
  have hpol_bdd : Bornology.IsVonNBounded 𝕜 (precomp ι hι '' StrongDual.polar 𝕜 U) :=
    (StrongDual.isVonNBounded_polar_of_mem_nhds_zero hU_nhds).image (precomp ι hι)
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo hpol_bdd
    (closedBall_mem_nhds (0 : 𝕜) zero_lt_one)] with Ψ hΨ
  rw [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, ← hU_closed.closure_eq,
    ← hU_abs.bipolar_eq_closure ⟨0, mem_of_mem_nhds hU_nhds⟩]
  intro φ hφ
  have hpair : φ (e.symm Ψ) = Ψ (precomp ι hι φ) := by
    have h : evalLinearMap hT hι hinj hcover hsem (e.symm Ψ) = Ψ :=
      LinearEquiv.apply_ofBijective_symm_apply _ Ψ
    conv_rhs => rw [← h]
    simp [evalLinearMap]
  simpa [topDualPairing_apply, hpair, mem_closedBall_zero_iff] using
    hΨ (Set.mem_image_of_mem (precomp ι hι) hφ)

/-- **Canonical evaluation onto the strong dual of the dual projective limit.** When `L` is a
separated locally convex space over `𝕜` whose continuous seminorms are tested on the stages `B j`,
canonical evaluation is a topological linear isomorphism `L ≃L[𝕜] (lim_j B j′)′_b`. -/
def evalEquiv : L ≃L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) where
  __ := LinearEquiv.ofBijective (evalLinearMap hT hι hinj hcover hsem)
    (bijective_evalLinearMap hT hι hinj hcover hsem)
  continuous_toFun := continuous_evalLinearMap hT hι hinj hcover hsem
  continuous_invFun := continuous_symm_evalLinearMap hT hι hinj hcover hsem

@[simp]
theorem evalEquiv_apply_apply (x : L) (f : dualProjectiveLimit T) :
    evalEquiv hT hι hinj hcover hsem x f =
      (strongDualEquiv hT hι hinj hcover
        (continuous_of_continuous_comp_seminorm hsem)).symm f x :=
  (rfl)

theorem evalEquiv_apply_precomp (x : L) (φ : StrongDual 𝕜 L) :
    evalEquiv hT hι hinj hcover hsem x (precomp ι hι φ) = φ x := by
  simp

@[simp]
theorem evalEquiv_ι (j : ℕ) (z : B j) :
    evalEquiv hT hι hinj hcover hsem (ι j z) = eval T j z := by
  ext f
  simp

@[simp]
theorem comp_ι_evalEquiv (j : ℕ) :
    (evalEquiv hT hι hinj hcover hsem).toContinuousLinearMap.comp (ι j) = eval T j := by
  ext z f
  simp

@[simp]
theorem evalEquiv_symm_eval (j : ℕ) (z : B j) :
    (evalEquiv hT hι hinj hcover hsem).symm (eval T j z) = ι j z := by
  rw [← evalEquiv_ι hT hι hinj hcover hsem, ContinuousLinearEquiv.symm_apply_apply]

/-- **Polar pairing comparison for `evalEquiv`.** Evaluating `evalEquiv x` on the image of a polar
`StrongDual.polar 𝕜 s` in `dualProjectiveLimit T` tests membership of `x` in the bipolar
`(topDualPairing 𝕜 L).polar (StrongDual.polar 𝕜 s)`. -/
theorem forall_mem_image_precomp_polar_norm_evalEquiv_le_one_iff (s : Set L) (x : L) :
    (∀ f ∈ precomp ι hι '' StrongDual.polar 𝕜 s,
      ‖evalEquiv hT hι hinj hcover hsem x f‖ ≤ 1) ↔
      x ∈ (topDualPairing 𝕜 L).polar (StrongDual.polar 𝕜 s) := by
  simp [LinearMap.polar_mem_iff]

/-- **Bipolar comparison for `evalEquiv`.** For a nonempty closed `𝕜`-absolutely convex subset `U`
of `L`, `x ∈ U` if and only if `‖evalEquiv x f‖ ≤ 1` for every `f` in the image of the polar
`StrongDual.polar 𝕜 U` in `dualProjectiveLimit T`. -/
theorem forall_mem_image_precomp_polar_norm_evalEquiv_le_one_iff_mem {U : Set L}
    (hU_closed : IsClosed U) (hU_abs : AbsConvex 𝕜 U) (hU_ne : U.Nonempty) (x : L) :
    (∀ f ∈ precomp ι hι '' StrongDual.polar 𝕜 U,
      ‖evalEquiv hT hι hinj hcover hsem x f‖ ≤ 1) ↔ x ∈ U := by
  rw [forall_mem_image_precomp_polar_norm_evalEquiv_le_one_iff,
    hU_abs.bipolar_eq_closure hU_ne, hU_closed.closure_eq]

end EvalEquiv

end dualProjectiveLimit

section StrongBidual

variable [IsTopologicalAddGroup L] [ContinuousSMul 𝕜 L] [Module ℝ L] [IsScalarTower ℝ 𝕜 L]
  [LocallyConvexSpace ℝ L] [SeparatingDual 𝕜 L]
  (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
  (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
  (hsem : ∀ q : Seminorm 𝕜 L, (∀ n, Continuous (q ∘ ι n)) → Continuous q)

/-- **Strong-bidual reflexivity of a compact inductive limit.** Canonical evaluation is a
topological linear isomorphism `L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L)`, obtained by composing
`dualProjectiveLimit.evalEquiv` with congruence along `dualProjectiveLimit.strongDualEquiv`. -/
def strongBidualEquiv : L ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 L) :=
  (evalEquiv hT hι hinj hcover hsem).trans
    ((strongDualEquiv hT hι hinj hcover
      (continuous_of_continuous_comp_seminorm hsem)).symm.arrowCongr
        (ContinuousLinearEquiv.refl 𝕜 𝕜))

@[simp]
theorem strongBidualEquiv_apply_apply (x : L) (ℓ : StrongDual 𝕜 L) :
    strongBidualEquiv hT hι hinj hcover hsem x ℓ = ℓ x := by
  simp [strongBidualEquiv]

@[simp]
theorem toLinearMap_strongBidualEquiv :
    (strongBidualEquiv hT hι hinj hcover hsem).toLinearMap = applyₗ 𝕜 (RingHom.id 𝕜) := by
  ext x ℓ
  simp

end StrongBidual

/-- **Naturality of strong-bidual reflexivity** for continuous linear maps between compact
inductive limits: double transposition `precomp 𝕜 (precomp 𝕜 S)` intertwines `strongBidualEquiv`
with `S`. -/
theorem precomp_precomp_comp_strongBidualEquiv
    {B₁ B₂ : ℕ → Type*}
    [∀ n, NormedAddCommGroup (B₁ n)] [∀ n, NormedSpace 𝕜 (B₁ n)]
    [∀ n, NormedAddCommGroup (B₂ n)] [∀ n, NormedSpace 𝕜 (B₂ n)]
    {T₁ : ∀ n, B₁ n →L[𝕜] B₁ (n + 1)} {T₂ : ∀ n, B₂ n →L[𝕜] B₂ (n + 1)}
    {L₁ L₂ : Type*}
    [AddCommGroup L₁] [Module 𝕜 L₁] [TopologicalSpace L₁] [IsTopologicalAddGroup L₁]
    [ContinuousSMul 𝕜 L₁] [Module ℝ L₁] [IsScalarTower ℝ 𝕜 L₁] [LocallyConvexSpace ℝ L₁]
    [SeparatingDual 𝕜 L₁]
    [AddCommGroup L₂] [Module 𝕜 L₂] [TopologicalSpace L₂] [IsTopologicalAddGroup L₂]
    [ContinuousSMul 𝕜 L₂] [Module ℝ L₂] [IsScalarTower ℝ 𝕜 L₂] [LocallyConvexSpace ℝ L₂]
    [SeparatingDual 𝕜 L₂]
    {ι₁ : ∀ n, B₁ n →L[𝕜] L₁} {ι₂ : ∀ n, B₂ n →L[𝕜] L₂}
    (hT₁ : ∀ n, (T₁ n).IsWeaklyCompact) (hι₁ : ∀ n, (ι₁ (n + 1)).comp (T₁ n) = ι₁ n)
    (hinj₁ : ∀ n, Function.Injective (ι₁ n)) (hcover₁ : ∀ x : L₁, ∃ n, ∃ y, ι₁ n y = x)
    (hsem₁ : ∀ q : Seminorm 𝕜 L₁, (∀ n, Continuous (q ∘ ι₁ n)) → Continuous q)
    (hT₂ : ∀ n, (T₂ n).IsWeaklyCompact) (hι₂ : ∀ n, (ι₂ (n + 1)).comp (T₂ n) = ι₂ n)
    (hinj₂ : ∀ n, Function.Injective (ι₂ n)) (hcover₂ : ∀ x : L₂, ∃ n, ∃ y, ι₂ n y = x)
    (hsem₂ : ∀ q : Seminorm 𝕜 L₂, (∀ n, Continuous (q ∘ ι₂ n)) → Continuous q)
    (S : L₁ →L[𝕜] L₂) :
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 S)).comp
        (strongBidualEquiv hT₁ hι₁ hinj₁ hcover₁ hsem₁).toContinuousLinearMap =
      (strongBidualEquiv hT₂ hι₂ hinj₂ hcover₂ hsem₂).toContinuousLinearMap.comp S :=
  ContinuousLinearEquiv.precomp_precomp_comp_eq_comp _
    (strongBidualEquiv_apply_apply hT₁ hι₁ hinj₁ hcover₁ hsem₁) _
    (strongBidualEquiv_apply_apply hT₂ hι₂ hinj₂ hcover₂ hsem₂) S

end TopologicalSpace

/-- **Completeness of a compact inductive limit.** A separated locally convex inductive limit of
normed spaces with weakly compact bonding maps whose continuous seminorms are tested stagewise is
complete, via the uniform isomorphism `dualProjectiveLimit.evalEquiv` onto the strong dual of the
metrizable space `dualProjectiveLimit T`. -/
theorem completeSpace_of_isWeaklyCompact
    {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
    [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
    {T : ∀ n, B n →L[𝕜] B (n + 1)}
    {L : Type*} [AddCommGroup L] [Module 𝕜 L] [UniformSpace L] [IsUniformAddGroup L]
    [ContinuousSMul 𝕜 L] [Module ℝ L] [IsScalarTower ℝ 𝕜 L] [LocallyConvexSpace ℝ L]
    [SeparatingDual 𝕜 L] {ι : ∀ n, B n →L[𝕜] L}
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hsem : ∀ q : Seminorm 𝕜 L, (∀ n, Continuous (q ∘ ι n)) → Continuous q) :
    CompleteSpace L := by
  let e := dualProjectiveLimit.evalEquiv hT hι hinj hcover hsem
  exact (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).2 inferInstance

end TauCeti
