/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TauCeti.Analysis.Normed.Operator.WeaklyCompact.Bidual
public import TauCeti.Topology.Algebra.Module.Spaces.StrongDual

/-!
# The projective limit of the duals of a Banach spectrum

Let `B₀ → B₁ → B₂ → ⋯` be a sequence of normed spaces with continuous linear bonding maps
`T j : B j → B (j + 1)`. Dualizing reverses the arrows, and the projective limit of the dual
spaces `B j′` is the space `TauCeti.dualProjectiveLimit T` of compatible families `(f j)` of
continuous functionals, `f (j + 1) ∘ T j = f j`. It is a closed submodule of the product
`∀ j, B j′`, and carries the subspace topology, which is the projective-limit topology given by
the seminorms `f ↦ ‖f j‖` (`TauCeti.dualProjectiveLimit.withSeminorms`). It is complete and
metrizable, so it is a Fréchet space, and in particular a Baire space. Earlier seminorms are
dominated by later ones
(`TauCeti.dualProjectiveLimit.norm_apply_le_prod_mul`), so every continuous seminorm, in
particular the modulus of every continuous functional, is bounded by a multiple of a single
seminorm `f ↦ ‖f j‖` (`TauCeti.dualProjectiveLimit.exists_bound_of_continuous`).

Each vector `x ∈ B j` defines the continuous functional `f ↦ f j x` on the projective limit
(`TauCeti.dualProjectiveLimit.eval`), continuous in `x` for the strong dual topology
(`TauCeti.dualProjectiveLimit.evalCLM`), and compatible with the bonding maps.
When the bonding maps are weakly compact, in particular when they are compact, every continuous
functional on the projective limit is such an evaluation
(`TauCeti.dualProjectiveLimit.exists_eval_eq`). More precisely, a linear functional bounded by
`C * ‖f j‖` is evaluation at a vector of the next stage `B (j + 1)` of norm at most `‖T j‖ * C`
(`TauCeti.dualProjectiveLimit.exists_norm_le_forall_apply_eq`): the functional descends to the
image of the projection to `B j′`, where Hahn–Banach and Gantmacher's criterion for `T j`
represent it (`ContinuousLinearMap.IsWeaklyCompact.exists_norm_le_forall_apply_eq`). Since the
projective limit is barrelled, a pointwise bounded family of continuous functionals is bounded by
a single coordinate norm, so it consists of evaluations at a norm-bounded set of vectors of one
space `B j` (`TauCeti.dualProjectiveLimit.exists_forall_exists_norm_le_eval_eq`). Consequently,
bounded sets of the strong dual `StrongDual 𝕜 (dualProjectiveLimit T)` are contained in images of
stage balls (`TauCeti.dualProjectiveLimit.isVonNBounded_strongDual_iff`), and canonical evaluation
is a topological linear isomorphism from `dualProjectiveLimit T` onto its strong bidual
(`TauCeti.dualProjectiveLimit.strongBidualEquiv`). No completeness or reflexivity of the spaces
`B j` is needed.

Given a topological vector space `L` with compatible continuous linear maps `ι j : B j → L`,
`ι (j + 1) ∘ T j = ι j`, precomposition with the maps `ι j` sends a continuous functional on `L`
to a point of the projective limit (`TauCeti.dualProjectiveLimit.precomp`) and sends polars of
zero-neighbourhoods in `L` to bounded subsets
(`TauCeti.dualProjectiveLimit.isVonNBounded_image_precomp_polar`). It is injective when the ranges
of the `ι j` cover `L` (`TauCeti.dualProjectiveLimit.precomp_injective`), and surjective when
moreover the `ι j` are injective and a linear functional on `L` is continuous as soon as its
composites with all `ι j` are (`TauCeti.dualProjectiveLimit.precomp_surjective`). Under
injectivity and covering of the maps `ι j`, the stage evaluations glue to a canonical linear map
`L →ₗ[𝕜] StrongDual 𝕜 (dualProjectiveLimit T)` (`TauCeti.dualProjectiveLimit.liftEval`), injective
when `L` has separating dual and surjective when the bonding maps are weakly compact.

## Main declarations

* `TauCeti.dualProjectiveLimit`: the projective limit `lim_j B j′` as a submodule of the product.
* `TauCeti.dualProjectiveLimit.coord`: its coordinate projections to the spaces `B j′`.
* `TauCeti.dualProjectiveLimit.withSeminorms`: its topology is given by the coordinate norms.
* `TauCeti.dualProjectiveLimit.eval`, `TauCeti.dualProjectiveLimit.evalCLM`: the evaluation map
  `B j → StrongDual 𝕜 (dualProjectiveLimit T)`.
* `TauCeti.dualProjectiveLimit.exists_norm_le_forall_apply_eq`: a functional bounded by the
  `j`-th coordinate norm is evaluation at a vector of `B (j + 1)`, with a norm bound.
* `TauCeti.dualProjectiveLimit.exists_forall_exists_norm_le_eval_eq`: for weakly compact bonding
  maps, a pointwise bounded family of continuous functionals consists of evaluations at a bounded
  set of vectors of a single space `B j`.
* `TauCeti.dualProjectiveLimit.isVonNBounded_strongDual_iff`: bounded sets of the strong dual of
  the projective limit lie in images of balls under `evalCLM`.
* `TauCeti.dualProjectiveLimit.strongBidualEquiv`: strong-bidual reflexivity of the projective
  limit for weakly compact bonding maps.
* `TauCeti.dualProjectiveLimit.precomp`: precomposition `L′ → lim_j B j′` with compatible maps
  `ι j : B j → L`.
* `TauCeti.dualProjectiveLimit.liftEval`: glued evaluation `L →ₗ[𝕜] StrongDual 𝕜 (lim_j B j′)`.

## References

* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
-/

public section

noncomputable section

open ContinuousLinearMap Filter TopologicalSpace Topology
open scoped NNReal

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  (T : ∀ n, B n →L[𝕜] B (n + 1))

/-- The projective limit `lim_j B j′` of the dual spaces of a sequence of normed spaces `B j`
with bonding maps `T j : B j → B (j + 1)`: the families `(f j)` of continuous functionals on the
spaces `B j` that are compatible with the bonding maps, `f (j + 1) ∘ T j = f j`. -/
def dualProjectiveLimit : Submodule 𝕜 (∀ n, StrongDual 𝕜 (B n)) where
  carrier := {f | ∀ n, (f (n + 1)).comp (T n) = f n}
  add_mem' {f g} hf hg n := by simp [add_comp, hf n, hg n]
  zero_mem' n := by simp
  smul_mem' c f hf n := by simp [smul_comp, hf n]

variable {T} in
@[simp]
theorem mem_dualProjectiveLimit {f : ∀ n, StrongDual 𝕜 (B n)} :
    f ∈ dualProjectiveLimit T ↔ ∀ n, (f (n + 1)).comp (T n) = f n :=
  Iff.rfl

/-- The projective limit is closed in the product of the dual spaces. -/
theorem isClosed_dualProjectiveLimit :
    IsClosed (dualProjectiveLimit T : Set (∀ n, StrongDual 𝕜 (B n))) := by
  have h : (dualProjectiveLimit T : Set (∀ n, StrongDual 𝕜 (B n))) =
      ⋂ n, {f | (f (n + 1)).comp (T n) = f n} := by
    ext f
    simp
  rw [h]
  exact isClosed_iInter fun n ↦ isClosed_eq
    ((precomp 𝕜 (T n)).continuous.comp (continuous_apply (n + 1))) (continuous_apply n)

instance : AddCommGroup (dualProjectiveLimit T) :=
  (dualProjectiveLimit T).addCommGroup

/-- The projective limit is complete. -/
instance : CompleteSpace (dualProjectiveLimit T) :=
  (isClosed_dualProjectiveLimit T).completeSpace_coe

/-- The projective limit is completely metrizable, being a closed subspace of a countable product
of Banach spaces. -/
instance : IsCompletelyPseudoMetrizableSpace (dualProjectiveLimit T) :=
  (isClosed_dualProjectiveLimit T).isCompletelyPseudoMetrizableSpace

namespace dualProjectiveLimit

/-- The `j`-th coordinate projection `lim_k B k′ → B j′` of the projective limit. -/
def coord (j : ℕ) : dualProjectiveLimit T →L[𝕜] StrongDual 𝕜 (B j) :=
  (ContinuousLinearMap.proj j).comp (dualProjectiveLimit T).subtypeL

variable {T}

@[simp]
theorem coord_apply (j : ℕ) (f : dualProjectiveLimit T) :
    coord T j f = (f : ∀ n, StrongDual 𝕜 (B n)) j :=
  (rfl)

@[simp]
theorem apply_succ_comp (f : dualProjectiveLimit T) (j : ℕ) :
    ((f : ∀ n, StrongDual 𝕜 (B n)) (j + 1)).comp (T j) = (f : ∀ n, StrongDual 𝕜 (B n)) j :=
  f.2 j

@[simp]
theorem apply_succ_apply (f : dualProjectiveLimit T) {j : ℕ} (x : B j) :
    (f : ∀ n, StrongDual 𝕜 (B n)) (j + 1) (T j x) = (f : ∀ n, StrongDual 𝕜 (B n)) j x :=
  congr($(apply_succ_comp f j) x)

/-- The coordinate norms increase along the projective system, up to the norms of the bonding
maps: `‖f j‖ ≤ ‖T j‖ ⋯ ‖T (k - 1)‖ * ‖f k‖` for `j ≤ k`. -/
theorem norm_apply_le_prod_mul (f : dualProjectiveLimit T) {j k : ℕ} (hjk : j ≤ k) :
    ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖ ≤
      (∏ i ∈ Finset.Ico j k, ‖T i‖) * ‖(f : ∀ n, StrongDual 𝕜 (B n)) k‖ := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    calc ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖
        ≤ (∏ i ∈ Finset.Ico j k, ‖T i‖) * ‖(f : ∀ n, StrongDual 𝕜 (B n)) k‖ := ih
      _ = (∏ i ∈ Finset.Ico j k, ‖T i‖) *
            ‖((f : ∀ n, StrongDual 𝕜 (B n)) (k + 1)).comp (T k)‖ := by
          rw [apply_succ_comp]
      _ ≤ (∏ i ∈ Finset.Ico j k, ‖T i‖) * (‖(f : ∀ n, StrongDual 𝕜 (B n)) (k + 1)‖ * ‖T k‖) :=
          mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (by positivity)
      _ = (∏ i ∈ Finset.Ico j (k + 1), ‖T i‖) * ‖(f : ∀ n, StrongDual 𝕜 (B n)) (k + 1)‖ := by
          rw [Finset.prod_Ico_succ_top hjk]
          ring

variable (T) in
/-- The topology of the projective limit is the projective-limit topology, given by the
seminorms `f ↦ ‖f j‖`. -/
theorem withSeminorms :
    WithSeminorms (𝕜 := 𝕜) (E := dualProjectiveLimit T) fun j : ℕ ↦
      (normSeminorm 𝕜 (StrongDual 𝕜 (B j))).comp (coord T j).toLinearMap := by
  have h := LinearMap.withSeminorms_induced (E := dualProjectiveLimit T) (σ₁₂ := RingHom.id 𝕜)
    ((withSeminorms_pi fun j ↦ norm_withSeminorms 𝕜 (StrongDual 𝕜 (B j))).congr_equiv
      (Equiv.sigmaPUnit ℕ).symm) (dualProjectiveLimit T).subtype
  convert h using 1
  · ext j f
    simp [SeminormFamily.comp_apply, SeminormFamily.sigma, Equiv.sigmaPUnit]
  · rfl

/-- Every continuous seminorm on the projective limit is bounded by a multiple of a single
coordinate norm `f ↦ ‖f j‖`. -/
theorem exists_bound_of_continuous (q : Seminorm 𝕜 (dualProjectiveLimit T)) (hq : Continuous q) :
    ∃ j, ∃ C : ℝ≥0, ∀ f, q f ≤ C * ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (withSeminorms T) q hq
  -- Every seminorm indexed by `s` is dominated by the seminorm of the largest index in `s`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ s, i ≤ N := ⟨s.sup id, fun i hi ↦ Finset.le_sup (f := id) hi⟩
  set D : ℝ≥0 := ∑ i ∈ s, ∏ k ∈ Finset.Ico i N, ‖T k‖₊
  refine ⟨N, C * D, fun f ↦ (hC f).trans ?_⟩
  have hsup : (s.sup fun j : ℕ ↦
      (normSeminorm 𝕜 (StrongDual 𝕜 (B j))).comp (coord T j).toLinearMap) f ≤
      D * ‖(f : ∀ n, StrongDual 𝕜 (B n)) N‖ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦ ?_
    refine (norm_apply_le_prod_mul f (hN i hi)).trans ?_
    gcongr
    simpa only [D, NNReal.coe_sum, NNReal.coe_prod, coe_nnNorm] using
      Finset.single_le_sum (f := fun i ↦ ∏ k ∈ Finset.Ico i N, ‖T k‖)
        (fun i _ ↦ by positivity) hi
  simpa [NNReal.smul_def, mul_assoc] using mul_le_mul_of_nonneg_left hsup C.coe_nonneg

/-- A subset of `dualProjectiveLimit T` is von Neumann bounded if and only if each coordinate norm
is uniformly bounded on it. -/
theorem isVonNBounded_iff {Q : Set (dualProjectiveLimit T)} :
    Bornology.IsVonNBounded 𝕜 Q ↔
      ∀ j, ∃ C : ℝ, ∀ f ∈ Q, ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖ ≤ C := by
  simp_rw [(withSeminorms T).isVonNBounded_iff_seminorm_bddAbove, bddAbove_def,
    Set.forall_mem_image]
  rfl

variable (T) in
/-- Evaluation at a vector of `B j` as a continuous functional on the projective limit,
`eval T j x f = f j x`. -/
def eval (j : ℕ) : B j →ₗ[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) where
  toFun x := (ContinuousLinearMap.apply 𝕜 𝕜 x).comp (coord T j)
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

@[simp]
theorem eval_apply (j : ℕ) (x : B j) (f : dualProjectiveLimit T) :
    eval T j x f = (f : ∀ n, StrongDual 𝕜 (B n)) j x :=
  (rfl)

/-- The evaluations are compatible with the bonding maps. -/
@[simp]
theorem eval_succ_apply (j : ℕ) (x : B j) : eval T (j + 1) (T j x) = eval T j x := by
  ext f
  simp

variable (T) in
/-- Stage evaluation `x ↦ (f ↦ f j x)` into the strong dual `StrongDual 𝕜 (dualProjectiveLimit T)`
as a continuous linear map, obtained by pulling back `NormedSpace.inclusionInDoubleDual` along the
coordinate projection `coord T j`. -/
def evalCLM (j : ℕ) : B j →L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) :=
  (ContinuousLinearMap.precomp 𝕜 (coord T j)).comp (NormedSpace.inclusionInDoubleDual 𝕜 (B j))

@[simp]
theorem toLinearMap_evalCLM (j : ℕ) : (evalCLM T j).toLinearMap = eval T j :=
  (rfl)

@[simp]
theorem coe_evalCLM (j : ℕ) : ⇑(evalCLM T j) = eval T j :=
  (rfl)

theorem evalCLM_apply (j : ℕ) (x : B j) (f : dualProjectiveLimit T) :
    evalCLM T j x f = (f : ∀ n, StrongDual 𝕜 (B n)) j x :=
  (rfl)

@[simp]
theorem evalCLM_comp (j : ℕ) : (evalCLM T (j + 1)).comp (T j) = evalCLM T j := by
  ext x f
  simp

/-- A linear functional on the projective limit that is bounded by `C` times the `j`-th
coordinate norm is evaluation at a vector of the next stage `B (j + 1)` of norm at most
`‖T j‖ * C`, provided the bonding map `T j` is weakly compact. -/
theorem exists_norm_le_forall_apply_eq {j : ℕ} (hT : (T j).IsWeaklyCompact)
    (φ : dualProjectiveLimit T →ₗ[𝕜] 𝕜) (C : ℝ≥0)
    (hφ : ∀ f, ‖φ f‖ ≤ C * ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖) :
    ∃ x : B (j + 1), ‖x‖ ≤ ‖T j‖ * C ∧
      ∀ f, φ f = (f : ∀ n, StrongDual 𝕜 (B n)) (j + 1) x := by
  -- `φ` vanishes on the kernel of the `j`-th coordinate, so it descends to its range.
  set π : dualProjectiveLimit T →ₗ[𝕜] StrongDual 𝕜 (B j) := (coord T j).toLinearMap
  have hπ (f : dualProjectiveLimit T) : π f = (f : ∀ n, StrongDual 𝕜 (B n)) j := coord_apply j f
  have hdesc {f f' : dualProjectiveLimit T} (h : π f = π f') : φ f = φ f' := by
    have hj : (f : ∀ n, StrongDual 𝕜 (B n)) j = (f' : ∀ n, StrongDual 𝕜 (B n)) j := by
      rwa [hπ, hπ] at h
    have h0 : φ (f - f') = 0 := by simpa [hj] using hφ (f - f')
    rwa [← sub_eq_zero, ← map_sub]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LinearMap.range π →ₗ[𝕜] 𝕜,
      ∀ f, ψ ⟨π f, LinearMap.mem_range_self π f⟩ = φ f := by
    choose g hg using fun h : LinearMap.range π ↦ LinearMap.mem_range.1 h.2
    refine ⟨{ toFun h := φ (g h), map_add' h h' := ?_, map_smul' c h := ?_ }, fun f ↦ ?_⟩
    · rw [← map_add]
      exact hdesc (by rw [map_add, hg, hg, hg, Submodule.coe_add])
    · rw [RingHom.id_apply, ← map_smul]
      exact hdesc (by rw [map_smul, hg, hg, Submodule.coe_smul])
    · exact hdesc (hg _)
  -- Hahn–Banach and the weak compactness of `T j` represent the descended functional.
  obtain ⟨x, hx, hrep⟩ := hT.exists_norm_le_forall_apply_eq (LinearMap.range π) ψ C
    (by
      rintro ⟨_, f, rfl⟩
      rw [hψ f]
      exact hφ f)
  refine ⟨x, hx, fun f ↦ ?_⟩
  have hmem : ((f : ∀ n, StrongDual 𝕜 (B n)) (j + 1)).comp (T j) ∈ LinearMap.range π :=
    LinearMap.mem_range.2 ⟨f, (hπ f).trans (apply_succ_comp f j).symm⟩
  calc φ f = ψ ⟨π f, LinearMap.mem_range_self π f⟩ := (hψ f).symm
    _ = ψ ⟨_, hmem⟩ := congrArg ψ (Subtype.ext ((hπ f).trans (apply_succ_comp f j).symm))
    _ = _ := (hrep _ hmem).symm

/-- **Uniform representation of bounded families.** If the bonding maps are weakly compact, in
particular if they are compact, then a pointwise bounded family of continuous linear functionals
on the projective limit `lim_j B j′` consists of evaluations at the vectors of a norm-bounded
subset of a single space `B j`. -/
theorem exists_forall_exists_norm_le_eval_eq (hT : ∀ n, (T n).IsWeaklyCompact) {ι : Type*}
    (φ : ι → StrongDual 𝕜 (dualProjectiveLimit T))
    (hφ : ∀ f, BddAbove (Set.range fun i ↦ ‖φ i f‖)) :
    ∃ j, ∃ R : ℝ, ∀ i, ∃ x : B j, ‖x‖ ≤ R ∧ eval T j x = φ i := by
  -- The projective limit is a Fréchet space, hence barrelled, so the supremum of the
  -- seminorms `f ↦ ‖φ i f‖` is a continuous seminorm.
  set q : ι → Seminorm 𝕜 (dualProjectiveLimit T) :=
    fun i ↦ (normSeminorm 𝕜 𝕜).comp (E := dualProjectiveLimit T) (φ i).toLinearMap
  have hq (i : ι) (f : dualProjectiveLimit T) : q i f = ‖φ i f‖ := by simp [q]
  have hbdd : BddAbove (Set.range q) := Seminorm.bddAbove_range_iff.2 fun f ↦ by
    simpa only [hq] using hφ f
  have hp : Continuous ⇑(⨆ i, q i : Seminorm 𝕜 (dualProjectiveLimit T)) := by
    rw [Seminorm.coe_iSup_eq hbdd]
    exact Seminorm.continuous_iSup q
      (fun i ↦ (continuous_norm.comp (φ i).continuous).congr fun f ↦ (hq i f).symm) hbdd
  have hφp (i : ι) (f : dualProjectiveLimit T) : ‖φ i f‖ ≤ (⨆ i, q i) f :=
    (hq i f).symm.le.trans (Seminorm.le_def.1 (le_ciSup hbdd i) f)
  obtain ⟨j, C, hC⟩ := exists_bound_of_continuous _ hp
  refine ⟨j + 1, ‖T j‖ * C, fun i ↦ ?_⟩
  obtain ⟨x, hx, hrep⟩ := exists_norm_le_forall_apply_eq (hT j) (φ i).toLinearMap C
    fun f ↦ (hφp i f).trans (hC f)
  exact ⟨x, hx, ContinuousLinearMap.ext fun f ↦ (hrep f).symm⟩

/-- If the bonding maps are weakly compact, in particular if they are compact, then every
continuous linear functional on the projective limit `lim_j B j′` is evaluation at a vector of
some space `B j`. -/
theorem exists_eval_eq (hT : ∀ n, (T n).IsWeaklyCompact)
    (φ : StrongDual 𝕜 (dualProjectiveLimit T)) : ∃ j, ∃ x : B j, eval T j x = φ := by
  obtain ⟨j, _, h⟩ := exists_forall_exists_norm_le_eval_eq hT (fun _ : Unit ↦ φ) fun _ ↦
    (Set.finite_range _).bddAbove
  obtain ⟨x, -, hx⟩ := h ()
  exact ⟨j, x, hx⟩

/-- For weakly compact bonding maps, a subset of the strong dual
`StrongDual 𝕜 (dualProjectiveLimit T)` is von Neumann bounded if and only if it lies in the image
of a closed ball of a single space `B j` under `evalCLM T j`. -/
theorem isVonNBounded_strongDual_iff (hT : ∀ n, (T n).IsWeaklyCompact)
    {S : Set (StrongDual 𝕜 (dualProjectiveLimit T))} :
    Bornology.IsVonNBounded 𝕜 S ↔
      ∃ j, ∃ R : ℝ, S ⊆ evalCLM T j '' Metric.closedBall 0 R := by
  refine ⟨fun hS ↦ ?_, fun ⟨j, R, hS⟩ ↦
    ((NormedSpace.isVonNBounded_closedBall 𝕜 (B j) R).image (evalCLM T j)).subset hS⟩
  have hbdd (f : dualProjectiveLimit T) :
      BddAbove (Set.range fun φ : S ↦ ‖(φ : StrongDual 𝕜 (dualProjectiveLimit T)) f‖) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      ((NormedSpace.isVonNBounded_iff 𝕜).1
        (hS.image (StrongDual.eval 𝕜 (dualProjectiveLimit T) f)))
    refine ⟨C, ?_⟩
    rintro _ ⟨φ, rfl⟩
    simpa using hC _ (Set.mem_image_of_mem (StrongDual.eval 𝕜 (dualProjectiveLimit T) f) φ.2)
  obtain ⟨j, R, hrep⟩ := exists_forall_exists_norm_le_eval_eq hT (fun φ : S ↦ φ.1) hbdd
  refine ⟨j, R, fun φ hφ ↦ ?_⟩
  obtain ⟨x, hx, heq⟩ := hrep ⟨φ, hφ⟩
  exact ⟨x, mem_closedBall_zero_iff.2 hx, heq⟩

variable (T) in
/-- Restricting a continuous functional on `StrongDual 𝕜 (dualProjectiveLimit T)` along the stage
evaluations `evalCLM T n` produces a compatible family in `dualProjectiveLimit T`, left-inverse to
canonical evaluation `StrongDual.eval`. -/
def fromStrongBidual :
    StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T)) →L[𝕜] dualProjectiveLimit T where
  toFun Ψ := ⟨fun n ↦ Ψ.comp (evalCLM T n),
    mem_dualProjectiveLimit.2 fun n ↦ by rw [comp_assoc, evalCLM_comp]⟩
  map_add' Ψ₁ Ψ₂ := by ext; simp
  map_smul' c Ψ := by ext; simp
  cont := (continuous_pi fun n ↦
    (ContinuousLinearMap.precomp 𝕜 (evalCLM T n)).continuous).subtype_mk _

@[simp]
theorem fromStrongBidual_apply
    (Ψ : StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T))) (n : ℕ) :
    (fromStrongBidual T Ψ : ∀ k, StrongDual 𝕜 (B k)) n = Ψ.comp (evalCLM T n) :=
  (rfl)

@[simp]
theorem fromStrongBidual_eval (f : dualProjectiveLimit T) :
    fromStrongBidual T (StrongDual.eval 𝕜 (dualProjectiveLimit T) f) = f := by
  ext n x
  simp

/-- When the bonding maps are weakly compact, `fromStrongBidual T` is also a right inverse to
canonical evaluation `StrongDual.eval`, because every continuous functional on
`dualProjectiveLimit T` is a stage evaluation. -/
@[simp]
theorem eval_fromStrongBidual (hT : ∀ n, (T n).IsWeaklyCompact)
    (Ψ : StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T))) :
    StrongDual.eval 𝕜 (dualProjectiveLimit T) (fromStrongBidual T Ψ) = Ψ := by
  ext φ
  obtain ⟨n, x, rfl⟩ := exists_eval_eq hT φ
  simp

/-- When the bonding maps are weakly compact, canonical evaluation from `dualProjectiveLimit T`
into its strong bidual is continuous. -/
theorem continuous_strongDual_eval (hT : ∀ n, (T n).IsWeaklyCompact) :
    Continuous (StrongDual.eval 𝕜 (dualProjectiveLimit T)) := by
  have : ContinuousAdd (StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T))) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  refine continuous_of_continuousAt_zero
    (StrongDual.eval 𝕜 (dualProjectiveLimit T)).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E := StrongDual 𝕜 (dualProjectiveLimit T)) (σ := RingHom.id 𝕜)
    Metric.nhds_basis_ball).tendsto_right_iff).2 fun ⟨S, ε⟩ ⟨hS, hε⟩ ↦ ?_
  obtain ⟨j, R, hSR⟩ := (isVonNBounded_strongDual_iff hT).1 hS
  have hR : 0 < |R| + 1 := by positivity
  filter_upwards [(coord T j).continuous.tendsto' 0 0 (map_zero _)
    (Metric.ball_mem_nhds 0 (div_pos hε hR))] with f hf φ hφ
  obtain ⟨x, hx, rfl⟩ := hSR hφ
  rw [Set.mem_preimage, mem_ball_zero_iff, coord_apply, lt_div_iff₀ hR] at hf
  simp only [LinearMap.toAddMonoidHom_coe, StrongDual.eval_apply, coe_evalCLM, eval_apply,
    mem_ball_zero_iff]
  calc ‖(f : ∀ n, StrongDual 𝕜 (B n)) j x‖
      ≤ ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖ * (|R| + 1) :=
        (le_opNorm _ x).trans (mul_le_mul_of_nonneg_left
          ((mem_closedBall_zero_iff.1 hx).trans
            ((le_abs_self R).trans (le_add_of_nonneg_right zero_le_one))) (norm_nonneg _))
    _ < ε := hf

/-- **Strong-bidual reflexivity of the dual projective limit.** When the bonding maps are weakly
compact, in particular when they are compact, canonical evaluation `StrongDual.eval` is an
isomorphism of topological vector spaces from `dualProjectiveLimit T` onto its strong bidual, with
inverse `fromStrongBidual T`. -/
def strongBidualEquiv (hT : ∀ n, (T n).IsWeaklyCompact) :
    dualProjectiveLimit T ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T)) where
  __ := StrongDual.eval 𝕜 (dualProjectiveLimit T)
  invFun := fromStrongBidual T
  left_inv := fromStrongBidual_eval
  right_inv := eval_fromStrongBidual hT
  continuous_toFun := continuous_strongDual_eval hT
  continuous_invFun := (fromStrongBidual T).continuous

@[simp]
theorem coe_strongBidualEquiv (hT : ∀ n, (T n).IsWeaklyCompact) :
    ⇑(strongBidualEquiv hT) = StrongDual.eval 𝕜 (dualProjectiveLimit T) :=
  (rfl)

theorem strongBidualEquiv_apply (hT : ∀ n, (T n).IsWeaklyCompact)
    (f : dualProjectiveLimit T) (φ : StrongDual 𝕜 (dualProjectiveLimit T)) :
    strongBidualEquiv hT f φ = φ f :=
  StrongDual.eval_apply f φ

@[simp]
theorem coe_strongBidualEquiv_symm (hT : ∀ n, (T n).IsWeaklyCompact) :
    ⇑(strongBidualEquiv hT).symm = fromStrongBidual T :=
  (rfl)

/-- The inverse of the strong transpose `precomp 𝕜 (strongBidualEquiv hT)` is a topological linear
isomorphism from `StrongDual 𝕜 (dualProjectiveLimit T)` onto its strong bidual acting by canonical
evaluation `Ξ ↦ Ξ φ`. -/
theorem arrowCongr_strongBidualEquiv_apply (hT : ∀ n, (T n).IsWeaklyCompact)
    (φ : StrongDual 𝕜 (dualProjectiveLimit T))
    (Ξ : StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T))) :
    (strongBidualEquiv hT).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) φ Ξ = Ξ φ :=
  StrongDual.arrowCongr_refl_apply_of_coe_eq_eval (strongBidualEquiv hT)
    (coe_strongBidualEquiv hT) φ Ξ

section Precomp

variable {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L] {ι : ∀ n, B n →L[𝕜] L}

variable (ι) in
/-- Precomposition with compatible maps `ι j : B j → L` sends a continuous functional `φ` on `L`
to the point `(φ ∘ ι j)_j` of the projective limit `lim_j B j′`. -/
def precomp (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) :
    StrongDual 𝕜 L →L[𝕜] dualProjectiveLimit T where
  toFun φ := ⟨fun n ↦ φ.comp (ι n), mem_dualProjectiveLimit.2 fun n ↦ by rw [comp_assoc, hι]⟩
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp
  cont := (continuous_pi fun n ↦ (ContinuousLinearMap.precomp 𝕜 (ι n)).continuous).subtype_mk _

@[simp]
theorem precomp_apply (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (φ : StrongDual 𝕜 L) (n : ℕ) :
    (precomp ι hι φ : ∀ n, StrongDual 𝕜 (B n)) n = φ.comp (ι n) :=
  (rfl)

/-- A continuous functional on `L` is determined by its composites with the maps `ι j` when the
ranges of these maps cover `L`. -/
theorem precomp_injective (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) :
    Function.Injective (precomp ι hι) := by
  intro φ ψ h
  ext x
  obtain ⟨n, y, rfl⟩ := hcover x
  simpa using congr($(congr_arg (coord T n) h) y)

/-- A vector of `B j` can be moved along the bonding maps to any later stage `B k`, without
changing its image in `L` or its value under a compatible family of functionals. -/
private theorem exists_stage_eq (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (f : dualProjectiveLimit T) {j k : ℕ} (hjk : j ≤ k) (y : B j) :
    ∃ y' : B k, ι k y' = ι j y ∧
      (f : ∀ n, StrongDual 𝕜 (B n)) k y' = (f : ∀ n, StrongDual 𝕜 (B n)) j y := by
  induction k, hjk using Nat.le_induction with
  | base => exact ⟨y, rfl, rfl⟩
  | succ k _ ih =>
    obtain ⟨y', hι', hf'⟩ := ih
    exact ⟨T k y', by rw [← hι', ← hι k, coe_comp, Function.comp_apply],
      by rw [apply_succ_apply, hf']⟩

/-- For injective maps `ι j`, a compatible family of functionals takes the same value on two
vectors with the same image in `L`. -/
private theorem apply_eq_of_eq (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (f : dualProjectiveLimit T) {j k : ℕ} {y : B j}
    {y' : B k} (h : ι j y = ι k y') :
    (f : ∀ n, StrongDual 𝕜 (B n)) j y = (f : ∀ n, StrongDual 𝕜 (B n)) k y' := by
  rcases le_total j k with hjk | hkj
  · obtain ⟨z, hz, hfz⟩ := exists_stage_eq hι f hjk y
    rw [← hfz, hinj k (hz.trans h)]
  · obtain ⟨z, hz, hfz⟩ := exists_stage_eq hι f hkj y'
    rw [← hfz, hinj j (h.trans hz.symm)]

/-- Every compatible family of continuous functionals on the spaces `B j` comes from a continuous
functional on their inductive limit `L`. -/
theorem precomp_surjective (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) :
    Function.Surjective (precomp ι hι) := by
  intro f
  choose m y hy using hcover
  -- The functional `x ↦ f (m x) (y x)` is well defined, whatever stage represents `x`.
  have hval (x : L) {n : ℕ} (z : B n) (hz : ι n z = x) :
      (f : ∀ n, StrongDual 𝕜 (B n)) (m x) (y x) = (f : ∀ n, StrongDual 𝕜 (B n)) n z :=
    apply_eq_of_eq hι hinj f ((hy x).trans hz.symm)
  let ψ : L →ₗ[𝕜] 𝕜 :=
    { toFun x := (f : ∀ n, StrongDual 𝕜 (B n)) (m x) (y x)
      map_add' x x' := by
        obtain ⟨z, hz, hfz⟩ := exists_stage_eq hι f (le_max_left (m x) (m x')) (y x)
        obtain ⟨z', hz', hfz'⟩ := exists_stage_eq hι f (le_max_right (m x) (m x')) (y x')
        rw [hval (x + x') (z + z') (by rw [map_add, hz, hz', hy, hy]), map_add, hfz, hfz']
      map_smul' c x := by
        rw [hval (c • x) (c • y x) (by rw [map_smul, hy]), map_smul, RingHom.id_apply] }
  have hψ (n : ℕ) (z : B n) : ψ (ι n z) = (f : ∀ n, StrongDual 𝕜 (B n)) n z := hval _ z rfl
  refine ⟨⟨ψ, hfinal ψ fun n ↦ ?_⟩, ?_⟩
  · exact ((f : ∀ n, StrongDual 𝕜 (B n)) n).continuous.congr fun z ↦ (hψ n z).symm
  · ext n z
    exact hψ n z

/-- The image under `precomp ι hι` of the polar of any zero-neighbourhood in `L` is von Neumann
bounded in `dualProjectiveLimit T`, since the preimage of that neighbourhood under each continuous
inclusion `ι n` is a zero-neighbourhood in the normed space `B n`. -/
theorem isVonNBounded_image_precomp_polar (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    {U : Set L} (hU : U ∈ 𝓝 (0 : L)) :
    Bornology.IsVonNBounded 𝕜 (precomp ι hι '' StrongDual.polar 𝕜 U) := by
  refine isVonNBounded_iff.2 fun n ↦ ?_
  have hUn : ι n ⁻¹' U ∈ 𝓝 (0 : B n) := (ι n).continuous.tendsto' 0 0 (map_zero _) hU
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 hUn)
  refine ⟨C, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  refine hC (φ.comp (ι n)) ((StrongDual.mem_polar_iff 𝕜 _).2 fun z hz ↦ ?_)
  exact (StrongDual.mem_polar_iff 𝕜 U).1 hφ (ι n z) hz

private theorem eval_choose_eq (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (x : L) {n : ℕ} (z : B n) (hz : ι n z = x) :
    eval T (hcover x).choose (hcover x).choose_spec.choose = eval T n z := by
  ext f
  exact apply_eq_of_eq hι hinj f ((hcover x).choose_spec.choose_spec.trans hz.symm)

/-- When the maps `ι n : B n →L[𝕜] L` are injective and cover `L`, the stage evaluations `eval T n`
glue to a well-defined linear map `L →ₗ[𝕜] StrongDual 𝕜 (dualProjectiveLimit T)`. -/
def liftEval (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) :
    L →ₗ[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) where
  toFun x := eval T (hcover x).choose (hcover x).choose_spec.choose
  map_add' x x' := by
    have hyx : ι (hcover x).choose (hcover x).choose_spec.choose = x :=
      (hcover x).choose_spec.choose_spec
    have hyx' : ι (hcover x').choose (hcover x').choose_spec.choose = x' :=
      (hcover x').choose_spec.choose_spec
    obtain ⟨z, hz, -⟩ := exists_stage_eq hι 0
      (le_max_left (hcover x).choose (hcover x').choose) (hcover x).choose_spec.choose
    obtain ⟨z', hz', -⟩ := exists_stage_eq hι 0
      (le_max_right (hcover x).choose (hcover x').choose) (hcover x').choose_spec.choose
    rw [eval_choose_eq hι hinj hcover (x + x') (z + z') (by rw [map_add, hz, hz', hyx, hyx']),
      map_add, eval_choose_eq hι hinj hcover x z (hz.trans hyx),
      eval_choose_eq hι hinj hcover x' z' (hz'.trans hyx')]
  map_smul' c x := by
    rw [eval_choose_eq hι hinj hcover (c • x) (c • (hcover x).choose_spec.choose)
      (by rw [map_smul, (hcover x).choose_spec.choose_spec]), map_smul, RingHom.id_apply]

@[simp]
theorem liftEval_ι_apply (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (n : ℕ) (z : B n) :
    liftEval hι hinj hcover (ι n z) = eval T n z :=
  eval_choose_eq hι hinj hcover (ι n z) z rfl

@[simp]
theorem liftEval_comp_ι (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) (n : ℕ) :
    (liftEval hι hinj hcover).comp (ι n).toLinearMap = eval T n := by
  ext z f
  simp

@[simp]
theorem liftEval_apply_precomp (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (x : L) (φ : StrongDual 𝕜 L) :
    liftEval hι hinj hcover x (precomp ι hι φ) = φ x := by
  obtain ⟨n, z, rfl⟩ := hcover x
  simp

/-- When continuous linear functionals separate points of `L`, the glued evaluation map `liftEval`
is injective. -/
theorem liftEval_injective [SeparatingDual 𝕜 L] (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) :
    Function.Injective (liftEval hι hinj hcover) := by
  intro x x' h
  exact (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun φ ↦ by
    simpa using congr($h (precomp ι hι φ))

/-- When the bonding maps are weakly compact, in particular when they are compact, every continuous
functional on `dualProjectiveLimit T` lies in the range of `liftEval`. -/
theorem liftEval_surjective (hT : ∀ n, (T n).IsWeaklyCompact)
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) :
    Function.Surjective (liftEval hι hinj hcover) := by
  intro Ξ
  obtain ⟨n, z, rfl⟩ := exists_eval_eq hT Ξ
  exact ⟨ι n z, liftEval_ι_apply hι hinj hcover n z⟩

end Precomp

end dualProjectiveLimit

end TauCeti
