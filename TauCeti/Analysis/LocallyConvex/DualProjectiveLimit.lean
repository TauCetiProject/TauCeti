/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TauCeti.Analysis.Normed.Operator.Compact.Adjoint
public import TauCeti.Analysis.Normed.Operator.WeaklyCompact.Bidual

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

Each vector `x ∈ B j` defines the continuous functional `f ↦ f j x` on the projective limit, and
sending `x` to this evaluation is a continuous linear map `B j →L[𝕜] StrongDual 𝕜
(dualProjectiveLimit T)` (`TauCeti.dualProjectiveLimit.eval`) compatible with the bonding maps.
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
canonical evaluation is a topological linear isomorphism from `dualProjectiveLimit T` onto its
strong bidual (`TauCeti.dualProjectiveLimit.strongBidualEquiv`), with inverse `Ψ ↦ (Ψ ∘ eval T j)`.
When the bonding maps are compact, Schauder's theorem makes each adjoint compact, so every bounded
subset of `dualProjectiveLimit T` has compact closure
(`TauCeti.dualProjectiveLimit.isCompact_closure_of_isVonNBounded`), making `dualProjectiveLimit T`
a Fréchet–Schwartz (and Montel) space. No completeness or reflexivity of the spaces `B j` is needed.

Given a topological vector space `L` with compatible continuous linear maps `ι j : B j → L`,
`ι (j + 1) ∘ T j = ι j`, precomposition with the maps `ι j` sends a continuous functional on `L`
to a point of the projective limit (`TauCeti.dualProjectiveLimit.precomp`). It is injective when
the ranges of the `ι j` cover `L` (`TauCeti.dualProjectiveLimit.precomp_injective`), and
surjective when moreover the `ι j` are injective and a linear functional on `L` is continuous as
soon as its composites with all `ι j` are (`TauCeti.dualProjectiveLimit.precomp_surjective`): a
compatible family of functionals then glues to a functional on `L`.

For an inductive limit `L` of Banach spaces with compact injective bonding maps, such as the
space of holomorphic germs along a compact set, the projective limit is therefore the dual of `L`,
and the uniform norm bound is the input for the bounded regularity of `L` and for the
identification of `L` with the strong dual of this Fréchet space.

## Main declarations

* `TauCeti.dualProjectiveLimit`: the projective limit `lim_j B j′` as a submodule of the product.
* `TauCeti.dualProjectiveLimit.coord`: its coordinate projections to the spaces `B j′`.
* `TauCeti.dualProjectiveLimit.withSeminorms`: its topology is given by the coordinate norms.
* `TauCeti.dualProjectiveLimit.eval`: the continuous evaluation map `B j →L[𝕜] (lim_k B k′)′_b`.
* `TauCeti.dualProjectiveLimit.exists_norm_le_forall_apply_eq`: a functional bounded by the
  `j`-th coordinate norm is evaluation at a vector of `B (j + 1)`, with a norm bound.
* `TauCeti.dualProjectiveLimit.exists_forall_exists_norm_le_eval_eq`: for weakly compact bonding
  maps, a pointwise bounded family of continuous functionals consists of evaluations at a bounded
  set of vectors of a single space `B j`.
* `TauCeti.dualProjectiveLimit.exists_eval_eq`: for weakly compact bonding maps, every continuous
  functional on the projective limit is an evaluation.
* `TauCeti.dualProjectiveLimit.strongBidualEquiv`: for weakly compact bonding maps, canonical
  evaluation is a topological linear isomorphism from `lim_j B j′` onto its strong bidual.
* `TauCeti.dualProjectiveLimit.isCompact_closure_of_isVonNBounded`: for compact bonding maps,
  every bounded subset of `lim_j B j′` has compact closure.
* `TauCeti.dualProjectiveLimit.precomp`: precomposition `L′ → lim_j B j′` with compatible maps
  `ι j : B j → L`.

## References

* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
-/

public section

noncomputable section

open ContinuousLinearMap TopologicalSpace
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

/-- Shortcut instance avoiding typeclass search through ring instances on the dependent product
`∀ n, StrongDual 𝕜 (B n)`. -/
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

variable (T) in
/-- Evaluation at a vector of `B j` as a continuous linear map into the strong dual of the
projective limit, `eval T j x f = f j x`. -/
def eval (j : ℕ) : B j →L[𝕜] StrongDual 𝕜 (dualProjectiveLimit T) :=
  (ContinuousLinearMap.precomp 𝕜 (coord T j)).comp (NormedSpace.inclusionInDoubleDual 𝕜 (B j))

@[simp]
theorem eval_apply (j : ℕ) (x : B j) (f : dualProjectiveLimit T) :
    eval T j x f = (f : ∀ n, StrongDual 𝕜 (B n)) j x :=
  (rfl)

/-- The continuous evaluation maps are compatible with the bonding maps. -/
@[simp]
theorem eval_succ_comp (j : ℕ) : (eval T (j + 1)).comp (T j) = eval T j := by
  ext x f
  simp

/-- The evaluations are compatible with the bonding maps. -/
@[simp]
theorem eval_succ_apply (j : ℕ) (x : B j) : eval T (j + 1) (T j x) = eval T j x :=
  congr($(eval_succ_comp (T := T) j) x)

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

/-- **Strong-bidual reflexivity of the dual projective limit.** When the bonding maps are weakly
compact, in particular when they are compact, canonical evaluation is a topological linear
isomorphism from `dualProjectiveLimit T` onto its strong bidual, with inverse `Ψ ↦ (Ψ ∘ eval T n)`.
-/
def strongBidualEquiv (hT : ∀ n, (T n).IsWeaklyCompact) :
    dualProjectiveLimit T ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T)) where
  toLinearMap := applyₗ 𝕜 (RingHom.id 𝕜)
  invFun Ψ := ⟨fun n ↦ Ψ.comp (eval T n),
    mem_dualProjectiveLimit.2 fun n ↦ by rw [comp_assoc, eval_succ_comp]⟩
  left_inv f := by
    ext n x
    rfl
  right_inv Ψ := by
    ext φ
    obtain ⟨n, x, rfl⟩ := exists_eval_eq hT φ
    rfl
  continuous_toFun := by
    have : ContinuousAdd ((dualProjectiveLimit T →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
      ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
    refine continuous_of_continuousAt_zero (applyₗ 𝕜 (RingHom.id 𝕜)).toAddMonoidHom ?_
    rw [ContinuousAt, map_zero]
    refine ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis (σ := RingHom.id 𝕜)
      Metric.nhds_basis_ball).tendsto_right_iff).2 fun ⟨S, ε⟩ ⟨hS, hε⟩ ↦ ?_
    set q : S → Seminorm 𝕜 (dualProjectiveLimit T) :=
      fun Φ ↦ (normSeminorm 𝕜 𝕜).comp (E := dualProjectiveLimit T) Φ.1.toLinearMap
    have hbdd : BddAbove (Set.range q) := Seminorm.bddAbove_range_iff.2 fun f ↦ by
      obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' 𝕜).1
        (hS.image (applyₗ 𝕜 (RingHom.id 𝕜) f))
      exact ⟨C, by rintro _ ⟨Φ, rfl⟩; exact hC _ (Set.mem_image_of_mem _ Φ.2)⟩
    have hp : Continuous ⇑(⨆ Φ, q Φ : Seminorm 𝕜 (dualProjectiveLimit T)) := by
      rw [Seminorm.coe_iSup_eq hbdd]
      exact Seminorm.continuous_iSup q (fun Φ ↦ continuous_norm.comp Φ.1.continuous) hbdd
    filter_upwards [(⨆ Φ, q Φ).ball_mem_nhds hp hε] with f hf Φ hΦ
    rw [Seminorm.mem_ball_zero] at hf
    simpa [q, mem_ball_zero_iff] using (Seminorm.le_def.1 (le_ciSup hbdd ⟨Φ, hΦ⟩) f).trans_lt hf
  continuous_invFun :=
    (continuous_pi fun n ↦ (ContinuousLinearMap.precomp 𝕜 (eval T n)).continuous).subtype_mk _

@[simp]
theorem strongBidualEquiv_apply_apply (hT : ∀ n, (T n).IsWeaklyCompact)
    (f : dualProjectiveLimit T) (φ : StrongDual 𝕜 (dualProjectiveLimit T)) :
    strongBidualEquiv hT f φ = φ f :=
  (rfl)

@[simp]
theorem strongBidualEquiv_symm_apply (hT : ∀ n, (T n).IsWeaklyCompact)
    (Ψ : StrongDual 𝕜 (StrongDual 𝕜 (dualProjectiveLimit T))) (n : ℕ) :
    ((strongBidualEquiv hT).symm Ψ : ∀ k, StrongDual 𝕜 (B k)) n = Ψ.comp (eval T n) :=
  (rfl)

@[simp]
theorem toLinearMap_strongBidualEquiv (hT : ∀ n, (T n).IsWeaklyCompact) :
    (strongBidualEquiv hT).toLinearMap = applyₗ 𝕜 (RingHom.id 𝕜) :=
  (rfl)

/-- **Montel / Fréchet–Schwartz compactness of the dual projective limit.** When every bonding map
`T n` is compact, every von Neumann bounded subset of `dualProjectiveLimit T` has compact closure.
-/
theorem isCompact_closure_of_isVonNBounded (hT : ∀ n, IsCompactOperator (T n))
    {A : Set (dualProjectiveLimit T)} (hA : Bornology.IsVonNBounded 𝕜 A) :
    IsCompact (closure A) := by
  have hK (n : ℕ) : IsCompact (closure (coord T n '' A)) := by
    have himg : coord T n '' A =
        ContinuousLinearMap.precomp 𝕜 (T n) '' (coord T (n + 1) '' A) := by
      ext g
      simp only [Set.mem_image, exists_exists_and_eq_and, coord_apply,
        ContinuousLinearMap.precomp_apply, apply_succ_comp]
    rw [himg]
    exact (hT n).precomp.isCompact_closure_image_of_isVonNBounded (hA.image (coord T (n + 1)))
  exact ((isClosed_dualProjectiveLimit T).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_univ_pi hK)).of_isClosed_subset isClosed_closure <|
      closure_minimal (fun f hf n _ ↦ subset_closure (Set.mem_image_of_mem (coord T n) hf))
        ((isClosed_set_pi fun _ _ ↦ isClosed_closure).preimage continuous_subtype_val)

/-- When every bonding map `T n` is compact, closed bounded subsets of `dualProjectiveLimit T` are
compact. -/
theorem isCompact_of_isClosed_of_isVonNBounded (hT : ∀ n, IsCompactOperator (T n))
    {A : Set (dualProjectiveLimit T)} (hclosed : IsClosed A) (hA : Bornology.IsVonNBounded 𝕜 A) :
    IsCompact A :=
  (isCompact_closure_of_isVonNBounded hT hA).of_isClosed_subset hclosed subset_closure

/-- When every bonding map `T n` is compact, bounded subsets of `dualProjectiveLimit T` are
totally bounded. -/
theorem totallyBounded_of_isVonNBounded (hT : ∀ n, IsCompactOperator (T n))
    {A : Set (dualProjectiveLimit T)} (hA : Bornology.IsVonNBounded 𝕜 A) :
    TotallyBounded A :=
  (isCompact_closure_of_isVonNBounded hT hA).totallyBounded.subset subset_closure

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

end Precomp

end dualProjectiveLimit

end TauCeti
