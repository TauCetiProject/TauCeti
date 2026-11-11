/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import TauCeti.Analysis.Normed.Operator.RingOpNorm.OpenMapping
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps
import TauCeti.RingTheory.Huber.ModuleTopology.Submodule
import TauCeti.RingTheory.Noetherian.LinearMap

/-!
# Finite coordinates and closedness of finite submodules of `C₀`

A complete finitely generated submodule of `C₀(I, R)` over a complete ultrametric Tate normed
ring admits uniform relative approximation by finite coordinate projections. A sufficiently
accurate projection preserves the norm, giving finite-coordinate norm detection with constant one.
No freeness or Noetherian hypothesis is needed once the submodule is complete.

Over a commutative ring `R`, any finitely generated submodule of `C₀(X, M)` with values in a
Noetherian `R`-module `M` is already separated by finitely many point evaluations
(`Submodule.exists_finset_eq_zero_of_coe_eq_zero`). When `R` is moreover a complete ultrametric
Tate normed commutative ring and `M` is a complete normed `R`-module with bounded scalar action,
`Submodule.isClosed_of_forall_apply_eq_zero` shows that every finitely generated submodule of
`C₀(X, M)` is closed, complete, and carries the canonical `R`-module topology
(`Submodule.isClosed_zeroAtInfty_of_isNoetherian`,
`Submodule.completeSpace_zeroAtInfty_of_isNoetherian`,
`Submodule.isModuleTopology_zeroAtInfty_of_isNoetherian`). Completeness is exposed as an explicit
theorem rather than a global `CompleteSpace` instance on `↥P`, whose `Subtype` head would fire on
unrelated subtype goals.

Specialising to `[IsNoetherianRing R]` on `C₀(I, R)` removes the completeness hypothesis from
relative coordinate approximation and finite-coordinate norm bounds on arbitrary finite submodules
(`Submodule.exists_finset_norm_indicatorCLM_sub_le_of_isNoetherianRing`,
`Submodule.exists_finset_norm_eq_of_isNoetherianRing`,
`Submodule.exists_finset_norm_le_of_isNoetherianRing`), with no freeness assumption on `P`.

The argument uses `TauCeti.exists_linearCombination_eq_and_norm_le` to choose bounded coefficients
for a finite generating family and `Submodule.isClosed_of_forall_apply_eq_zero` to establish
closedness over Noetherian Banach–Tate rings, following K. Buzzard, *Eigenvarieties*, Lemmas
2.2–2.3, and C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
§2.1.
-/

public section

open Filter Topology
open scoped ZeroAtInfty NNReal
open ZeroAtInftyContinuousMap

namespace Submodule

section CompleteSubmodule

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NormedRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]

/-- Finite coordinate projections approximate the identity uniformly relative to the norm on a
complete finite submodule of `C₀(I, R)`. In particular this applies to closed finite submodules,
using the completeness instance `hP.completeSpace_coe`. -/
theorem exists_finset_norm_indicatorCLM_sub_le (P : Submodule R C₀(I, R))
    [Module.Finite R P] [CompleteSpace P] {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset I, ∀ f ∈ P, ‖indicatorCLM R (S : Set I) f - f‖ ≤ ε * ‖f‖ := by
  classical
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := P)
  obtain ⟨C, hC, hlift⟩ := TauCeti.exists_linearCombination_eq_and_norm_le v hv
  have htail : ∀ᶠ j in cofinite, ∀ k, ‖(v k : C₀(I, R)) j‖ < ε / C := by
    exact eventually_all.2 fun k ↦
      (NormedAddGroup.tendsto_nhds_zero.1 (v k : C₀(I, R)).tendsto_cofinite) _ (div_pos hε hC)
  let S := (eventually_cofinite.1 htail).toFinset
  refine ⟨S, fun f hf ↦ ?_⟩
  obtain ⟨c, hsum, hc⟩ := hlift ⟨f, hf⟩
  refine (ZeroAtInftyContinuousMap.norm_le (mul_nonneg hε.le (norm_nonneg f))).2 fun j ↦ ?_
  by_cases hj : j ∈ S
  · simpa [Set.indicator_apply, hj] using mul_nonneg hε.le (norm_nonneg f)
  · have hj' : ∀ k, ‖(v k : C₀(I, R)) j‖ < ε / C := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hj
    have hfj : (∑ k, c k • (v k : C₀(I, R)) j) = f j := by
      simpa using congrArg (fun g : P ↦ (g : C₀(I, R)) j) hsum
    have hbound : ‖f j‖ ≤ ε * ‖f‖ := by
      rw [← hfj]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg hε.le (norm_nonneg f)) fun k _ ↦ ?_
      calc
        ‖c k • (v k : C₀(I, R)) j‖ ≤ ‖c k‖ * ‖(v k : C₀(I, R)) j‖ := norm_smul_le _ _
        _ ≤ (C * ‖f‖) * (ε / C) :=
          mul_le_mul ((norm_le_pi_norm c k).trans hc) (hj' k).le (norm_nonneg _) (by positivity)
        _ = ε * ‖f‖ := by field_simp
    simpa [Set.indicator_apply, hj] using hbound

/-- On a complete finite submodule, the norm is the maximum of the norms at a fixed finite set
of coordinates. The supremum in `ℝ≥0` is zero when the set of coordinates is empty. -/
theorem exists_finset_norm_eq (P : Submodule R C₀(I, R))
    [Module.Finite R P] [CompleteSpace P] :
    ∃ S : Finset I, ∀ f ∈ P, ‖f‖ = (S.sup fun i ↦ ‖f i‖₊ : ℝ≥0) := by
  classical
  obtain ⟨S, hS⟩ := P.exists_finset_norm_indicatorCLM_sub_le (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨S, fun f hf ↦ ?_⟩
  have heq : ‖indicatorCLM R (S : Set I) f‖ = ‖f‖ := by
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    have hlt : ‖indicatorCLM R (S : Set I) f - f‖ < ‖f‖ :=
      (hS f hf).trans_lt (by nlinarith [norm_pos_iff.2 hf0])
    exact (IsUltrametricDist.norm_eq_of_norm_sub_lt_left
      (by simpa only [norm_sub_rev] using hlt)).symm
  rw [← heq, indicatorCLM_finset_apply, ← coe_nnnorm, nnnorm_sum_single]

/-- A complete finite submodule has a finite-coordinate bound with a positive constant.
The stronger theorem `exists_finset_norm_eq` shows that the constant can be taken to be one. -/
theorem exists_finset_norm_le (P : Submodule R C₀(I, R))
    [Module.Finite R P] [CompleteSpace P] :
    ∃ S : Finset I, ∃ C > 0, ∀ f ∈ P,
      ‖f‖ ≤ C * (S.sup fun i ↦ ‖f i‖₊ : ℝ≥0) := by
  obtain ⟨S, hS⟩ := P.exists_finset_norm_eq
  exact ⟨S, 1, one_pos, fun f hf ↦ by rw [hS f hf, one_mul]⟩

end CompleteSubmodule

section CoordinateDetection

/-- **Finite-coordinate detection on `C₀(X, M)`** (Buzzard, *Eigenvarieties*, Lemma 2.2): on a
finitely generated submodule of `C₀(X, M)` with values in a Noetherian module over a commutative
ring, vanishing at a fixed finite set of points forces vanishing everywhere. -/
theorem exists_finset_eq_zero_of_coe_eq_zero {X R M : Type*} [TopologicalSpace X]
    [CommRing R] [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Module R M]
    [ContinuousConstSMul R M] [IsNoetherian R M] (P : Submodule R C₀(X, M))
    [Module.Finite R P] :
    ∃ S : Finset X, ∀ f ∈ P, (∀ x ∈ S, f x = 0) → f = 0 := by
  let ev (x : X) : P →ₗ[R] M :=
    { toFun p := p.1 x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  obtain ⟨S, hS⟩ := TauCeti.exists_finset_eq_zero_of_forall_apply_eq_zero ev
    fun p hp ↦ Subtype.ext (ZeroAtInftyContinuousMap.ext fun x ↦ by simpa [ev] using hp x)
  exact ⟨S, fun f hf hfS ↦ congrArg Subtype.val (hS ⟨f, hf⟩ hfS)⟩

end CoordinateDetection

section NoetherianModule

variable {X R M : Type*} [TopologicalSpace X]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [CompleteSpace M] [Module R M] [IsBoundedSMul R M] [IsNoetherian R M]

/-- **Closedness of finite submodules of `C₀(X, M)`** (Buzzard, *Eigenvarieties*, Lemma 2.3;
Johansson–Newton, §2.1): over a complete ultrametric Tate normed commutative ring `R`, every
finitely generated submodule of `C₀(X, M)` with values in a complete Noetherian normed `R`-module
is closed. -/
theorem isClosed_zeroAtInfty_of_isNoetherian (P : Submodule R C₀(X, M))
    [Module.Finite R P] : IsClosed (P : Set C₀(X, M)) :=
  P.isClosed_of_forall_apply_eq_zero (evalCLM R)
    fun _ _ hf ↦ ZeroAtInftyContinuousMap.ext fun x ↦ by simpa using hf x

/-- Over a complete ultrametric Tate normed commutative ring `R`, every finitely generated
submodule of `C₀(X, M)` with values in a complete Noetherian normed `R`-module is complete. -/
theorem completeSpace_zeroAtInfty_of_isNoetherian (P : Submodule R C₀(X, M))
    [Module.Finite R P] : CompleteSpace P :=
  P.isClosed_zeroAtInfty_of_isNoetherian.completeSpace_coe

/-- Over a complete ultrametric Tate normed commutative ring `R`, every finitely generated
submodule of `C₀(X, M)` with values in a complete Noetherian normed `R`-module carries the
canonical `R`-module topology. -/
theorem isModuleTopology_zeroAtInfty_of_isNoetherian (P : Submodule R C₀(X, M))
    [Module.Finite R P] : IsModuleTopology R P :=
  P.isModuleTopology_of_forall_apply_eq_zero (evalCLM R)
    fun _ _ hf ↦ ZeroAtInftyContinuousMap.ext fun x ↦ by simpa using hf x

end NoetherianModule

section NoetherianRing

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [IsNoetherianRing R]

/-- Over a complete ultrametric Noetherian Tate normed commutative ring, finite coordinate
projections approximate the identity uniformly relative to the norm on any finite submodule of
`C₀(I, R)`, with no closedness or freeness assumption. -/
theorem exists_finset_norm_indicatorCLM_sub_le_of_isNoetherianRing
    (P : Submodule R C₀(I, R)) [Module.Finite R P] {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset I, ∀ f ∈ P, ‖indicatorCLM R (S : Set I) f - f‖ ≤ ε * ‖f‖ :=
  have := P.completeSpace_zeroAtInfty_of_isNoetherian
  P.exists_finset_norm_indicatorCLM_sub_le hε

/-- Over a complete ultrametric Noetherian Tate normed commutative ring, the norm on any finite
submodule of `C₀(I, R)` equals the maximum of the norms at a fixed finite set of coordinates, with
no closedness or freeness assumption. -/
theorem exists_finset_norm_eq_of_isNoetherianRing (P : Submodule R C₀(I, R))
    [Module.Finite R P] :
    ∃ S : Finset I, ∀ f ∈ P, ‖f‖ = (S.sup fun i ↦ ‖f i‖₊ : ℝ≥0) :=
  have := P.completeSpace_zeroAtInfty_of_isNoetherian
  P.exists_finset_norm_eq

/-- Over a complete ultrametric Noetherian Tate normed commutative ring, every finite submodule of
`C₀(I, R)` satisfies a finite-coordinate norm bound with a positive constant, with no closedness
or freeness assumption (Buzzard, *Eigenvarieties*, Lemma 2.3; Johansson–Newton, §2.1). -/
theorem exists_finset_norm_le_of_isNoetherianRing (P : Submodule R C₀(I, R))
    [Module.Finite R P] :
    ∃ S : Finset I, ∃ C > 0, ∀ f ∈ P,
      ‖f‖ ≤ C * (S.sup fun i ↦ ‖f i‖₊ : ℝ≥0) :=
  have := P.completeSpace_zeroAtInfty_of_isNoetherian
  P.exists_finset_norm_le

end NoetherianRing

section Examples

/-- On the zero submodule `⊥`, the empty coordinate set `∅` and constant `C = 1` witness the
finite-coordinate norm bound. -/
example {I E R : Type*} [TopologicalSpace I] [DiscreteTopology I] [NormedAddCommGroup E]
    [Semiring R] [Module R E] [ContinuousConstSMul R E] :
    ∀ f ∈ (⊥ : Submodule R C₀(I, E)),
      ‖f‖ ≤ (1 : ℝ) * ((∅ : Finset I).sup fun i ↦ ‖f i‖₊ : ℝ≥0) := by
  intro f hf
  simp_all

/-- On a submodule supported on a fixed finite set `S`, the coordinate set `S` itself and constant
`C = 1` witness the finite-coordinate norm bound with equality. -/
example {I E R : Type*} [TopologicalSpace I] [DiscreteTopology I] [SeminormedAddCommGroup E]
    [Semiring R] [Module R E] [ContinuousConstSMul R E] (S : Finset I)
    (P : Submodule R C₀(I, E)) (hP : ∀ f ∈ P, ∀ i ∉ S, f i = 0) :
    ∀ f ∈ P, ‖f‖ ≤ (1 : ℝ) * (S.sup fun i ↦ ‖f i‖₊ : ℝ≥0) := fun f hf ↦ by
  rw [norm_eq_sup_of_forall_eq_zero (hP f hf), one_mul]

/-- On a coordinate line `R ∙ single i b`, the singleton `{i}` and constant `C = 1` witness the
finite-coordinate norm bound. -/
example {I E R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
    [SeminormedAddCommGroup E] [Semiring R] [Module R E] [ContinuousConstSMul R E]
    (i : I) (b : E) :
    ∀ f ∈ Submodule.span R ({single i b} : Set C₀(I, E)),
      ‖f‖ ≤ (1 : ℝ) * (({i} : Finset I).sup fun j ↦ ‖f j‖₊ : ℝ≥0) := by
  intro f hf
  rw [norm_eq_sup_of_forall_eq_zero, one_mul]
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hf
  intro j hj
  simp [Finset.mem_singleton.not.1 hj]

/-- Over any complete ultrametric nontrivially normed field `K`, a finitely generated submodule of
`C₀(ℕ, K)` is closed and satisfies the finite-coordinate norm bound with all typeclass hypotheses
synthesised automatically. -/
example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (s : Finset C₀(ℕ, K)) :
    IsClosed (Submodule.span K (s : Set C₀(ℕ, K)) : Set C₀(ℕ, K)) ∧
      ∃ S : Finset ℕ, ∃ C > 0, ∀ h ∈ Submodule.span K (s : Set C₀(ℕ, K)),
        ‖h‖ ≤ C * (S.sup fun i ↦ ‖h i‖₊ : ℝ≥0) :=
  ⟨(Submodule.span K (s : Set C₀(ℕ, K))).isClosed_zeroAtInfty_of_isNoetherian,
    (Submodule.span K (s : Set C₀(ℕ, K))).exists_finset_norm_le_of_isNoetherianRing⟩

end Examples

end Submodule
