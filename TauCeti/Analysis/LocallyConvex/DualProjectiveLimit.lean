/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Baire.CompleteMetrizable
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

Each vector `x ∈ B j` defines the continuous functional `f ↦ f j x` on the projective limit
(`TauCeti.dualProjectiveLimit.eval`), and these evaluations are compatible with the bonding maps.
When the bonding maps are weakly compact, in particular when they are compact, every continuous
functional on the projective limit is such an evaluation
(`TauCeti.dualProjectiveLimit.exists_eval_eq`). More precisely, a linear functional bounded by
`C * ‖f j‖` is evaluation at a vector of the next stage `B (j + 1)` of norm at most `‖T j‖ * C`
(`TauCeti.dualProjectiveLimit.exists_norm_le_forall_apply_eq`): the functional descends to the
image of the projection to `B j′`, where Hahn–Banach and Gantmacher's criterion for `T j`
represent it (`ContinuousLinearMap.IsWeaklyCompact.exists_norm_le_forall_apply_eq`). Since the
projective limit is barrelled, a pointwise bounded family of continuous functionals is bounded by
a single coordinate norm, so it consists of evaluations at a norm-bounded set of vectors of one
space `B j` (`TauCeti.dualProjectiveLimit.exists_forall_exists_norm_le_eval_eq`). No completeness
or reflexivity of the spaces `B j` is needed.

For an inductive limit `L` of Banach spaces with compact injective bonding maps, such as the
space of holomorphic germs along a compact set, the projective limit is the dual of `L`, and the
uniform norm bound is the input for the bounded regularity of `L` and for the identification of
`L` with the strong dual of this Fréchet space.

## Main declarations

* `TauCeti.dualProjectiveLimit`: the projective limit `lim_j B j′` as a submodule of the product.
* `TauCeti.dualProjectiveLimit.coord`: its coordinate projections to the spaces `B j′`.
* `TauCeti.dualProjectiveLimit.withSeminorms`: its topology is given by the coordinate norms.
* `TauCeti.dualProjectiveLimit.eval`: the evaluation map `B j → (lim_k B k′)′`.
* `TauCeti.dualProjectiveLimit.exists_norm_le_forall_apply_eq`: a functional bounded by the
  `j`-th coordinate norm is evaluation at a vector of `B (j + 1)`, with a norm bound.
* `TauCeti.dualProjectiveLimit.exists_forall_exists_norm_le_eval_eq`: for weakly compact bonding
  maps, a pointwise bounded family of continuous functionals consists of evaluations at a bounded
  set of vectors of a single space `B j`.
* `TauCeti.dualProjectiveLimit.exists_eval_eq`: for weakly compact bonding maps, every continuous
  functional on the projective limit is an evaluation.

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
    simpa only [D, NNReal.coe_sum, NNReal.coe_prod, coe_nnnorm] using
      Finset.single_le_sum (f := fun i ↦ ∏ k ∈ Finset.Ico i N, ‖T k‖)
        (fun i _ ↦ by positivity) hi
  simpa [NNReal.smul_def, mul_assoc] using mul_le_mul_of_nonneg_left hsup C.coe_nonneg

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

end dualProjectiveLimit

end TauCeti
