/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
public import TauCeti.Analysis.Normed.Operator.Nuclear
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Convex.TotallyBounded
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.TensorProduct.Associator
import TauCeti.Analysis.Normed.Module.TensorProduct.IntegralBilinearForm
import TauCeti.Analysis.Normed.Module.TensorProduct.Series
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# The approximation property and completed tensor products

Let `E` and `F` be normed spaces over `ℝ` or `ℂ`. The elementary functionals
`x ⊗ₜ y ↦ f x * g y`, for `f ∈ E*` and `g ∈ F*`, are bounded for the injective norm, so they
factor through the contraction `E ⊗̂π F → E ⊗̂ε F`. This file proves Grothendieck's equivalences
between the approximation property and the injectivity of this contraction:

* if `E` or `F` has the approximation property, the elementary functionals separate the points of
  `E ⊗̂π F`, so the contraction `E ⊗̂π F → E ⊗̂ε F` is injective;
* conversely, a normed space `E` has the approximation property as soon as the tensor trace
  `E* ⊗̂π E → 𝕜` vanishes on the kernel of `E* ⊗̂π E → E* ⊗̂ε E`, and in particular as soon as
  `F ⊗̂π E → F ⊗̂ε E` is injective for `F = E*` (hence iff it is injective for every Banach space
  `F`);
* when `E` is a Banach space, `E` has the approximation property iff the canonical operator
  `E* ⊗̂π E → (E →L[𝕜] E)` is injective, iff the tensor trace vanishes on its kernel (so that the
  nuclear trace is well-defined on `nuclearOperators 𝕜 E E`), and iff every nuclear representation
  `∑ n, f n v • x n = 0` (`∑ n, ‖f n‖ * ‖x n‖ < ∞`) of the zero operator has scalar trace
  `∑ n, f n (x n) = 0`.

For the forward implication, write `u = ∑ n, x n ⊗ₜ y n` with `∑ n, ‖x n‖` finite and `y n → 0`,
and let `B` be a bounded bilinear form on `E × F`. If `F` has the approximation property, there is
a finite-rank operator `R` on `F` within `δ` of the identity on the compact set `{y n} ∪ {0}`. The
form `(x, y) ↦ B x (R y)` is a finite sum of elementary forms, so it vanishes on `u` when all
elementary functionals do, while it differs from `B` on `u` by at most `‖B‖ * δ * ∑ n, ‖x n‖`.

For the converse, Grothendieck's compactness lemma places any compact subset `K ⊆ E` inside the
closed convex hull of a null sequence `x : ℕ → E`. Evaluating bounded endomorphisms of `E` along
`x` maps `E →L[𝕜] E` into `C₀(ℕ, E)`, whose continuous dual is `ℓ¹(ℕ, E*)`. A functional `Λ` on
`C₀(ℕ, E)` vanishing on the images of all finite-rank operators has summable coordinate
functionals `f n = Λ ∘ singleCLM 𝕜 n`, so `u = ∑ n, f n ⊗ₜ x n` defines an element of `E* ⊗̂π E`
annihilated by all rank-one forms `f ⊗ₜ y ↦ f v * g y` (`v ∈ E`, `g ∈ E*`), hence in the kernel
of `E* ⊗̂π E → E* ⊗̂ε E`. Vanishing of the trace gives `Λ x = ∑ n, f n (x n) = 0`, and Hahn–Banach
in `C₀(ℕ, E)` produces a finite-rank operator approximating the identity uniformly along `x`,
hence on `K`. Neither completeness of `E` nor any choice of basis is used in the tensor
characterizations.

## Main results

* `TauCeti.CompletedProjectiveTensor.eq_zero_of_hasApproximationProperty_right` and `_left`: if
  `F`, or `E`, has the approximation property, an element of `E ⊗̂π F` on which every elementary
  functional vanishes is zero.
* `CompletedProjectiveTensor.injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right`
  and `_left`: the contraction `E ⊗̂π F → E ⊗̂ε F` is injective when `F` or `E` has the
  approximation property.
* `TauCeti.CompletedProjectiveTensor.injective_toContinuousLinearMap_of_hasApproximationProperty`
  and `_strongDual`: the canonical operator `E* ⊗̂π F → (E →L[𝕜] F)` is injective when `F` or `E*`
  has the approximation property.
* `TauCeti.hasApproximationProperty_of_trace_eq_zero` and
  `TauCeti.hasApproximationProperty_iff_trace_eq_zero`: `E` has the approximation property iff the
  tensor trace `E* ⊗̂π E → 𝕜` vanishes on the kernel of `E* ⊗̂π E → E* ⊗̂ε E`.
* `TauCeti.hasApproximationProperty_iff_injective_toCompletedInjectiveTensor_strongDual` and
  `TauCeti.hasApproximationProperty_iff_forall_injective_toCompletedInjectiveTensor`: `E` has the
  approximation property iff `E* ⊗̂π E → E* ⊗̂ε E` is injective, iff `F ⊗̂π E → F ⊗̂ε E` is
  injective for every Banach space `F` (and symmetrically `E ⊗̂π F → E ⊗̂ε F`); consequently
  `TauCeti.HasApproximationProperty.of_strongDual` transfers the approximation property from `E*`
  to `E`.
* `TauCeti.hasApproximationProperty_iff_injective_toContinuousLinearMap`,
  `TauCeti.hasApproximationProperty_iff_trace_eq_zero_of_toContinuousLinearMap_eq_zero`,
  `TauCeti.hasApproximationProperty_iff_tsum_apply_eq_zero`, and `TauCeti.NuclearOperator.trace`:
  for a Banach space `E`, the canonical-operator, nuclear-trace, and nuclear-series
  characterizations of the approximation property, together with the contractive trace functional
  on `NuclearOperator 𝕜 E E` (`hasSum_trace`, `trace_mk'_comp_comm`) when `E` has the
  approximation property.

## References

* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955), Chap. I, §5, Théorème 6.
* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Theorem 4.3.
-/

public section

open Filter Set
open scoped TensorProduct Topology ZeroAtInfty

namespace TauCeti.CompletedProjectiveTensor

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If every elementary functional vanishes on `u`, then so does the functional induced by
`(x, y) ↦ B x (R y)` for a finite-rank operator `R`, which is a finite sum of elementary
functionals. -/
private theorem liftIsometry_bilinearComp_eq_zero {u : CompletedProjectiveTensor 𝕜 E F}
    (hu : ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F),
      liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u = 0)
    (B : E →L[𝕜] F →L[𝕜] 𝕜) {R : F →L[𝕜] F} (hR : R.toLinearMap.HasFiniteRange) :
    liftIsometry 𝕜 E F 𝕜 (B.bilinearComp (ContinuousLinearMap.id 𝕜 E) R) u = 0 := by
  obtain ⟨⟨w⟩, rfl⟩ := (InjectiveTensor.mem_range_toOperator_iff R).2 hR
  simp only [LinearIsometry.coe_toLinearMap, InjectiveTensor.toOperator_mk]
  clear hR
  induction w with
  | tmul g z =>
    have : B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator (g ⊗ₜ z)) =
        (B.flip z).smulRight g := by
      ext x y
      simp [mul_comm]
    rw [this]
    exact hu _ _
  | add w w' hw hw' =>
    have : B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator (w + w')) =
        B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator w) +
          B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator w') := by
      ext x y
      simp
    rw [this, map_add]
    simp [hw, hw']

/-- **Elementary functionals separate points under the approximation property.** If `F` has the
approximation property, an element of `E ⊗̂π F` on which every functional
`x ⊗ₜ y ↦ f x * g y` vanishes is zero. -/
theorem eq_zero_of_hasApproximationProperty_right (hF : HasApproximationProperty 𝕜 F)
    {u : CompletedProjectiveTensor 𝕜 E F}
    (hu : ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F),
      liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u = 0) :
    u = 0 := by
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun Λ ↦ ?_
  obtain ⟨B, rfl⟩ := (liftIsometry 𝕜 E F 𝕜).surjective Λ
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_hasSum_tmul_tendsto_zero u
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  set S := ∑' n, ‖x n‖
  set δ := ε / ((‖B‖ + 1) * (S + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  -- A finite-rank operator `R` within `δ` of the identity on the compact set `{y n} ∪ {0}`.
  obtain ⟨R, hR, hRy⟩ := hasApproximationProperty_iff.1 hF _ hy.isCompact_insert_range δ hδ
  -- The form `(x, y) ↦ B x y - B x (R y)` takes the same value as `B` on `u`, and is small on
  -- each term of the series.
  have hsum : HasSum (fun n ↦ B (x n) (y n - R (y n))) (liftIsometry 𝕜 E F 𝕜 B u) := by
    have h := hxy.map (liftIsometry 𝕜 E F 𝕜 (B - B.bilinearComp (ContinuousLinearMap.id 𝕜 E) R))
      (ContinuousLinearMap.continuous _)
    rw [LinearIsometryEquiv.map_sub, sub_apply,
      liftIsometry_bilinearComp_eq_zero hu B hR, sub_zero] at h
    simpa [Function.comp_def] using h
  have hbound (n : ℕ) : ‖B (x n) (y n - R (y n))‖ ≤ ‖B‖ * δ * ‖x n‖ := by
    have hn : ‖y n - R (y n)‖ ≤ δ := by
      rw [norm_sub_rev]
      exact (hRy _ (mem_insert_of_mem _ (mem_range_self n))).le
    calc ‖B (x n) (y n - R (y n))‖ ≤ ‖B‖ * ‖x n‖ * ‖y n - R (y n)‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * ‖x n‖ * δ := by gcongr
      _ = ‖B‖ * δ * ‖x n‖ := by ring
  calc ‖liftIsometry 𝕜 E F 𝕜 B u‖ ≤ ‖B‖ * δ * S :=
        hsum.norm_le_of_bounded (hx.hasSum.mul_left (‖B‖ * δ)) hbound
    _ = δ * (‖B‖ * S) := by ring
    _ ≤ δ * ((‖B‖ + 1) * (S + 1)) := by gcongr <;> linarith
    _ = 0 + ε := by rw [hδ_def, div_mul_cancel₀ _ (by positivity), zero_add]

/-- If `E` has the approximation property, an element of `E ⊗̂π F` on which every functional
`x ⊗ₜ y ↦ f x * g y` vanishes is zero. -/
theorem eq_zero_of_hasApproximationProperty_left (hE : HasApproximationProperty 𝕜 E)
    {u : CompletedProjectiveTensor 𝕜 E F}
    (hu : ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F),
      liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u = 0) :
    u = 0 := by
  have hcomm (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) :
      liftIsometry 𝕜 F E 𝕜 (g.smulRight f) (comm 𝕜 E F u) =
        liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u := by
    have h : liftIsometry 𝕜 F E 𝕜 (g.smulRight f) ∘L
        (comm 𝕜 E F).toContinuousLinearEquiv.toContinuousLinearMap =
          liftIsometry 𝕜 E F 𝕜 (f.smulRight g) :=
      continuousLinearMap_ext fun x y ↦ by simp [comm_coe, mul_comm]
    exact congr($h u)
  have h := eq_zero_of_hasApproximationProperty_right hE (u := comm 𝕜 E F u)
    fun g f ↦ (hcomm f g).trans (hu f g)
  rwa [LinearIsometryEquiv.map_eq_zero_iff] at h

/-- If `F` has the approximation property, the contraction `E ⊗̂π F → E ⊗̂ε F` is injective. -/
theorem injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right
    (hF : HasApproximationProperty 𝕜 F) :
    Function.Injective (toCompletedInjectiveTensor 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun _ hu ↦
    eq_zero_of_hasApproximationProperty_right hF
      (liftIsometry_smulRight_eq_zero_of_toCompletedInjectiveTensor_eq_zero hu)

/-- If `E` has the approximation property, the contraction `E ⊗̂π F → E ⊗̂ε F` is injective. -/
theorem injective_toCompletedInjectiveTensor_of_hasApproximationProperty_left
    (hE : HasApproximationProperty 𝕜 E) :
    Function.Injective (toCompletedInjectiveTensor 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun _ hu ↦
    eq_zero_of_hasApproximationProperty_left hE
      (liftIsometry_smulRight_eq_zero_of_toCompletedInjectiveTensor_eq_zero hu)

section Operator

variable [CompleteSpace F]

/-- If the Banach space `F` has the approximation property, the canonical operator
`E* ⊗̂π F → (E →L[𝕜] F)` is injective: every nuclear operator `E → F` has a unique representing
tensor. -/
theorem injective_toContinuousLinearMap_of_hasApproximationProperty
    (hF : HasApproximationProperty 𝕜 F) :
    Function.Injective (toContinuousLinearMap 𝕜 E F) :=
  injective_toContinuousLinearMap_iff.2
    (injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right hF)

/-- If the dual `E*` has the approximation property, the canonical operator
`E* ⊗̂π F → (E →L[𝕜] F)` is injective: every nuclear operator `E → F` has a unique representing
tensor. -/
theorem injective_toContinuousLinearMap_of_hasApproximationProperty_strongDual
    (hE : HasApproximationProperty 𝕜 (StrongDual 𝕜 E)) :
    Function.Injective (toContinuousLinearMap 𝕜 E F) :=
  injective_toContinuousLinearMap_iff.2
    (injective_toCompletedInjectiveTensor_of_hasApproximationProperty_left hE)

end Operator

end TauCeti.CompletedProjectiveTensor

/-! ### Grothendieck's tensor and trace characterizations -/

namespace TauCeti

section Normed

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open CompletedProjectiveTensor ZeroAtInftyContinuousMap in
/-- If the tensor trace `E* ⊗̂π E → 𝕜` vanishes on the kernel of `E* ⊗̂π E → E* ⊗̂ε E`, then the
identity of `E` can be approximated uniformly along any null sequence `x : ℕ → E` by bounded
finite-rank endomorphisms. -/
private theorem exists_hasFiniteRange_forall_norm_sub_lt_of_trace_eq_zero
    (htrace : ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E,
      toCompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) E u = 0 → trace 𝕜 E u = 0)
    {x : ℕ → E} (hx : Tendsto x atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : E →L[𝕜] E, R.toLinearMap.HasFiniteRange ∧ ∀ n, ‖R (x n) - x n‖ < δ := by
  have hseq (T : E →L[𝕜] E) : Tendsto (fun n ↦ T (x n)) cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop, ← map_zero T]
    exact (T.continuous.tendsto 0).comp hx
  let L : (E →L[𝕜] E) →ₗ[𝕜] C₀(ℕ, E) :=
    { toFun T := mkOfDiscrete (fun n ↦ T (x n)) (hseq T)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  set S : Submodule 𝕜 C₀(ℕ, E) := ((InjectiveTensor.toOperator 𝕜 E E).toLinearMap.range).map L
  -- Any functional `Λ` on `C₀(ℕ, E)` annihilating `S` corresponds to a tensor in `E* ⊗̂π E` whose
  -- image in `E* ⊗̂ε E` vanishes, so its trace `Λ (L id) = ∑ n, Λ_n (x n)` is zero.
  have hmem : L (ContinuousLinearMap.id 𝕜 E) ∈ S.topologicalClosure := by
    rw [Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero]
    intro Λ hΛ
    set f : ℕ → StrongDual 𝕜 E := fun n ↦ Λ.comp (singleCLM 𝕜 n)
    obtain ⟨C, hC⟩ := hx.norm.bddAbove_range
    have hfx : Summable fun n ↦ ‖f n‖ * ‖x n‖ :=
      .of_nonneg_of_le (fun _ ↦ by positivity)
        (fun n ↦ mul_le_mul_of_nonneg_left (hC ⟨n, rfl⟩) (norm_nonneg _))
        ((summable_norm_comp_singleCLM Λ).mul_right C)
    let t (n : ℕ) : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E :=
      (⟨f n ⊗ₜ x n⟩ : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) E)
    have hu : Summable t := .of_norm_bounded hfx fun n ↦ norm_coe_tmul_le (f n) (x n)
    have hu0 : toCompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) E (∑' n, t n) = 0 := by
      refine toCompletedInjectiveTensor_strongDual_eq_zero_iff.2 fun v g ↦ ?_
      have hmemS : L (g.smulRight v) ∈ S :=
        ⟨g.smulRight v, ⟨⟨g ⊗ₜ v⟩, by simp⟩, rfl⟩
      have h₁ := (liftIsometry 𝕜 (StrongDual 𝕜 E) E 𝕜
        ((NormedSpace.inclusionInDoubleDual 𝕜 E v).smulRight g)).hasSum hu.hasSum
      have h₂ := hasSum_comp_singleCLM Λ (L (g.smulRight v))
      simp only [t, liftIsometry_coe, ProjectiveTensor.liftIsometry_apply_tmul,
        ContinuousLinearMap.smulRight_apply, NormedSpace.dual_def, _root_.smul_apply,
        smul_eq_mul] at h₁
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, coe_mkOfDiscrete,
        ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul] at h₂
      have h₁' : HasSum (fun n ↦ g (x n) * f n v)
          (liftIsometry 𝕜 (StrongDual 𝕜 E) E 𝕜
            ((NormedSpace.inclusionInDoubleDual 𝕜 E v).smulRight g) (∑' n, t n)) := by
        simpa only [t, mul_comm] using h₁
      exact (h₁'.unique h₂).trans (hΛ _ hmemS)
    have htr := hasSum_trace hu.hasSum
    have hid := hasSum_comp_singleCLM Λ (L (ContinuousLinearMap.id 𝕜 E))
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, coe_mkOfDiscrete,
      ContinuousLinearMap.id_apply] at hid
    exact (hid.unique htr).trans (htrace _ hu0)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨_, ⟨R, hR, rfl⟩, hdist⟩ := hmem δ hδ
  refine ⟨R, (InjectiveTensor.mem_range_toOperator_iff R).1 hR, fun n ↦ ?_⟩
  rw [dist_comm, dist_eq_norm, ← map_sub] at hdist
  simpa [L, coe_mkOfDiscrete] using
    (norm_coe_le_norm (L (R - ContinuousLinearMap.id 𝕜 E)) n).trans_lt hdist

/-- If the tensor trace `E* ⊗̂π E → 𝕜` vanishes on the kernel of the contraction
`E* ⊗̂π E → E* ⊗̂ε E`, then `E` has the approximation property. -/
theorem hasApproximationProperty_of_trace_eq_zero
    (htrace : ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E,
      CompletedProjectiveTensor.toCompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) E u = 0 →
        CompletedProjectiveTensor.trace 𝕜 E u = 0) :
    HasApproximationProperty 𝕜 E := by
  refine hasApproximationProperty_iff.2 fun K hK ε hε ↦ ?_
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  obtain ⟨x, hx, hKx⟩ := hK.totallyBounded.exists_tendsto_zero_subset_closure_convexHull
  obtain ⟨R, hR, hRx⟩ :=
    exists_hasFiniteRange_forall_norm_sub_lt_of_trace_eq_zero htrace hx (half_pos hε)
  have hconv : closure (convexHull ℝ (range x)) ⊆ {z : E | ‖R z - z‖ ≤ ε / 2} := by
    refine closure_minimal (convexHull_min ?_ ?_) (isClosed_le (by fun_prop) continuous_const)
    · rintro _ ⟨n, rfl⟩
      exact (hRx n).le
    · have hball : {z : E | ‖R z - z‖ ≤ ε / 2} =
          ((R - ContinuousLinearMap.id 𝕜 E).restrictScalars ℝ : E →ₗ[ℝ] E) ⁻¹'
            Metric.closedBall 0 (ε / 2) := by
        ext z
        simp
      rw [hball]
      exact (convex_closedBall _ _).linear_preimage _
  exact ⟨R, hR, fun z hz ↦ (hconv (hKx hz)).trans_lt (half_lt_self hε)⟩

open CompletedProjectiveTensor in
/-- **Grothendieck's trace criterion for the approximation property.** A normed space `E` over `ℝ`
or `ℂ` has the approximation property iff the tensor trace `E* ⊗̂π E → 𝕜` vanishes on the kernel of
the contraction `E* ⊗̂π E → E* ⊗̂ε E`. -/
theorem hasApproximationProperty_iff_trace_eq_zero :
    HasApproximationProperty 𝕜 E ↔
      ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E,
        toCompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) E u = 0 → trace 𝕜 E u = 0 :=
  ⟨fun hE _ hu ↦ by
    rw [injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right hE
      (hu.trans (map_zero _).symm), map_zero],
    hasApproximationProperty_of_trace_eq_zero⟩

/-- A normed space `E` over `ℝ` or `ℂ` has the approximation property iff the contraction
`E* ⊗̂π E → E* ⊗̂ε E` is injective. -/
theorem hasApproximationProperty_iff_injective_toCompletedInjectiveTensor_strongDual :
    HasApproximationProperty 𝕜 E ↔
      Function.Injective
        (CompletedProjectiveTensor.toCompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) E) :=
  ⟨CompletedProjectiveTensor.injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right,
    fun hinj ↦ hasApproximationProperty_of_trace_eq_zero fun _ hu ↦ by
      rw [hinj (hu.trans (map_zero _).symm), map_zero]⟩

/-- Symmetric dual-tensor criterion: a normed space `E` over `ℝ` or `ℂ` has the approximation
property iff the contraction `E ⊗̂π E* → E ⊗̂ε E*` is injective. -/
theorem hasApproximationProperty_iff_injective_toCompletedInjectiveTensor_strongDual_right :
    HasApproximationProperty 𝕜 E ↔
      Function.Injective
        (CompletedProjectiveTensor.toCompletedInjectiveTensor 𝕜 E (StrongDual 𝕜 E)) :=
  hasApproximationProperty_iff_injective_toCompletedInjectiveTensor_strongDual.trans
    CompletedProjectiveTensor.injective_toCompletedInjectiveTensor_comm

/-- **Grothendieck's dual approximation property theorem.** If the strong dual `E*` of a normed
space `E` over `ℝ` or `ℂ` has the approximation property, then `E` itself has the approximation
property. -/
theorem HasApproximationProperty.of_strongDual
    (h : HasApproximationProperty 𝕜 (StrongDual 𝕜 E)) : HasApproximationProperty 𝕜 E :=
  hasApproximationProperty_iff_injective_toCompletedInjectiveTensor_strongDual.2
    (CompletedProjectiveTensor.injective_toCompletedInjectiveTensor_of_hasApproximationProperty_left
      h)

end Normed

section UniversalTensor

universe u v w

open CompletedProjectiveTensor in
/-- **Grothendieck's tensor-product characterization of the approximation property.** A normed
space `E` over `ℝ` or `ℂ` has the approximation property iff for every Banach space `F` the
contraction `F ⊗̂π E → F ⊗̂ε E` from the completed projective to the completed injective tensor
product is injective.

The Banach spaces `F` range over any universe containing those of `𝕜` and `E` (in particular the
same universe when `w = 0`); for the forward implication without completeness or universe
restrictions on `F`, see
`injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right`. -/
theorem hasApproximationProperty_iff_forall_injective_toCompletedInjectiveTensor
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    HasApproximationProperty 𝕜 E ↔
      ∀ (F : Type (max u v w)) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F],
        Function.Injective (toCompletedInjectiveTensor 𝕜 F E) := by
  refine ⟨fun hE F _ _ _ ↦
    injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right hE, fun h ↦ ?_⟩
  rw [hasApproximationProperty_iff_injective_toCompletedInjectiveTensor_strongDual]
  let e : ULift.{w} (StrongDual 𝕜 E) ≃L[𝕜] StrongDual 𝕜 E := ContinuousLinearEquiv.ulift
  exact injective_toCompletedInjectiveTensor_of_leftInverse_left
    (i := e.symm.toContinuousLinearMap) (r := e.toContinuousLinearMap) e.apply_symm_apply
    (h (ULift.{w} (StrongDual 𝕜 E)))

/-- Symmetric tensor-product characterization: a normed space `E` over `ℝ` or `ℂ` has the
approximation property iff for every Banach space `F` the contraction `E ⊗̂π F → E ⊗̂ε F` is
injective. -/
theorem hasApproximationProperty_iff_forall_injective_toCompletedInjectiveTensor_left
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    HasApproximationProperty 𝕜 E ↔
      ∀ (F : Type (max u v w)) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F],
        Function.Injective (CompletedProjectiveTensor.toCompletedInjectiveTensor 𝕜 E F) := by
  rw [hasApproximationProperty_iff_forall_injective_toCompletedInjectiveTensor.{u, v, w}]
  exact forall₄_congr fun F _ _ _ ↦
    CompletedProjectiveTensor.injective_toCompletedInjectiveTensor_comm

end UniversalTensor

section Banach

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A Banach space `E` over `ℝ` or `ℂ` has the approximation property iff the canonical operator
`E* ⊗̂π E → (E →L[𝕜] E)` is injective. -/
theorem hasApproximationProperty_iff_injective_toContinuousLinearMap :
    HasApproximationProperty 𝕜 E ↔
      Function.Injective (CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E) :=
  hasApproximationProperty_iff_injective_toCompletedInjectiveTensor_strongDual.trans
    CompletedProjectiveTensor.injective_toContinuousLinearMap_iff.symm

/-- A Banach space `E` over `ℝ` or `ℂ` has the approximation property iff the tensor trace
`E* ⊗̂π E → 𝕜` vanishes on the kernel of the canonical operator `E* ⊗̂π E → (E →L[𝕜] E)`, that is,
iff the nuclear trace is well-defined on `nuclearOperators 𝕜 E E`. -/
theorem hasApproximationProperty_iff_trace_eq_zero_of_toContinuousLinearMap_eq_zero :
    HasApproximationProperty 𝕜 E ↔
      ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E,
        CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E u = 0 →
          CompletedProjectiveTensor.trace 𝕜 E u = 0 := by
  rw [hasApproximationProperty_iff_trace_eq_zero]
  refine forall_congr' fun u ↦ imp_congr_left ?_
  rw [← CompletedProjectiveTensor.toOperator_comp_toCompletedInjectiveTensor,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    map_eq_zero_iff _ (CompletedInjectiveTensor.toOperator 𝕜 E E).injective]

/-- **Grothendieck's nuclear-series criterion for the approximation property.** A Banach space `E`
over `ℝ` or `ℂ` has the approximation property iff for every sequence of functionals
`f : ℕ → StrongDual 𝕜 E` and vectors `x : ℕ → E` with `∑ n, ‖f n‖ * ‖x n‖ < ∞` such that
`∑' n, f n v • x n = 0` for every `v : E`, one has `∑' n, f n (x n) = 0`. -/
theorem hasApproximationProperty_iff_tsum_apply_eq_zero :
    HasApproximationProperty 𝕜 E ↔
      ∀ (f : ℕ → StrongDual 𝕜 E) (x : ℕ → E),
        Summable (fun n ↦ ‖f n‖ * ‖x n‖) →
        (∀ v : E, ∑' n, f n v • x n = 0) →
        ∑' n, f n (x n) = 0 := by
  rw [hasApproximationProperty_iff_trace_eq_zero_of_toContinuousLinearMap_eq_zero]
  refine ⟨fun h f x hfx hv ↦ ?_, fun h u hu0 ↦ ?_⟩
  · let t (n : ℕ) : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E :=
      (⟨f n ⊗ₜ x n⟩ : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) E)
    have hu : Summable t :=
      .of_norm_bounded hfx fun n ↦ CompletedProjectiveTensor.norm_coe_tmul_le (f n) (x n)
    have hT : CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E (∑' n, t n) = 0 :=
      ContinuousLinearMap.ext fun v ↦
        (CompletedProjectiveTensor.hasSum_toContinuousLinearMap_apply hu.hasSum v)
          |>.tsum_eq.symm.trans (hv v)
    exact (CompletedProjectiveTensor.hasSum_trace hu.hasSum).tsum_eq.trans (h _ hT)
  · obtain ⟨f, x, hu, hfx, -⟩ :=
      CompletedProjectiveTensor.exists_hasSum_tmul_of_norm_lt u (lt_add_one ‖u‖)
    have hv (v : E) : ∑' n, f n v • x n = 0 := by
      simpa [hu0] using
        (CompletedProjectiveTensor.hasSum_toContinuousLinearMap_apply hu v).tsum_eq
    exact (CompletedProjectiveTensor.hasSum_trace hu).tsum_eq.symm.trans (h f x hfx hv)

namespace NuclearOperator

/-- On a Banach space `E` over `ℝ` or `ℂ` with the approximation property, the **nuclear trace**
`NuclearOperator 𝕜 E E →L[𝕜] 𝕜` transports `CompletedProjectiveTensor.trace 𝕜 E` across the
isometric isomorphism `completedProjectiveTensorEquiv`. -/
noncomputable def trace (hE : HasApproximationProperty 𝕜 E) :
    NuclearOperator 𝕜 E E →L[𝕜] 𝕜 :=
  CompletedProjectiveTensor.trace 𝕜 E ∘L
    (completedProjectiveTensorEquiv
      (CompletedProjectiveTensor.injective_toContinuousLinearMap_of_hasApproximationProperty
        hE)).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Evaluating the nuclear trace on `T` applies the tensor trace to the unique tensor in
`E* ⊗̂π E` representing `T`. -/
theorem trace_apply (hE : HasApproximationProperty 𝕜 E) (T : NuclearOperator 𝕜 E E) :
    trace hE T = CompletedProjectiveTensor.trace 𝕜 E
      ((completedProjectiveTensorEquiv
        (CompletedProjectiveTensor.injective_toContinuousLinearMap_of_hasApproximationProperty
          hE)).symm T) :=
  (rfl)

/-- Evaluating the nuclear trace on the nuclear operator associated with a tensor `u` recovers the
tensor trace of `u`. -/
@[simp]
theorem trace_completedProjectiveTensorEquiv (hE : HasApproximationProperty 𝕜 E)
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E) :
    trace hE (completedProjectiveTensorEquiv
        (CompletedProjectiveTensor.injective_toContinuousLinearMap_of_hasApproximationProperty hE)
        u) =
      CompletedProjectiveTensor.trace 𝕜 E u := by
  simp [trace]

/-- If `u ∈ E* ⊗̂π E` represents `T : NuclearOperator 𝕜 E E`, then the nuclear trace of `T`
equals the tensor trace of `u`. -/
theorem trace_eq_of_toContinuousLinearMap_eq (hE : HasApproximationProperty 𝕜 E)
    {T : NuclearOperator 𝕜 E E} {u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E}
    (hu : CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E u = T.toContinuousLinearMap) :
    trace hE T = CompletedProjectiveTensor.trace 𝕜 E u := by
  have hinj :=
    CompletedProjectiveTensor.injective_toContinuousLinearMap_of_hasApproximationProperty
      (E := E) hE
  rw [trace_apply]
  congr 1
  exact hinj (by simp [hu])

/-- On a rank-one nuclear operator `smulRight f x`, the nuclear trace evaluates `f x`. -/
@[simp]
theorem trace_smulRight (hE : HasApproximationProperty 𝕜 E) (f : StrongDual 𝕜 E) (x : E) :
    trace hE (smulRight f x) = f x := by
  simp [trace]

/-- The nuclear trace is a contraction on `NuclearOperator 𝕜 E E`. -/
theorem norm_trace_le (hE : HasApproximationProperty 𝕜 E) : ‖trace hE‖ ≤ 1 :=
  ((CompletedProjectiveTensor.trace 𝕜 E).opNorm_comp_linearIsometryEquiv _).trans_le
    CompletedProjectiveTensor.norm_trace_le

/-- If `T : NuclearOperator 𝕜 E E` has a nuclear series representation
`T v = ∑ i, f i v • x i` with `∑ i, ‖f i‖ * ‖x i‖ < ∞`, then
`trace hE T = ∑ i, f i (x i)`. -/
theorem hasSum_trace {ι : Type*} (hE : HasApproximationProperty 𝕜 E)
    {f : ι → StrongDual 𝕜 E} {x : ι → E} {T : NuclearOperator 𝕜 E E}
    (hfx : Summable fun i ↦ ‖f i‖ * ‖x i‖)
    (hT : ∀ v, HasSum (fun i ↦ f i v • x i) (T.toContinuousLinearMap v)) :
    HasSum (fun i ↦ f i (x i)) (trace hE T) := by
  let t (i : ι) : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E :=
    (⟨f i ⊗ₜ x i⟩ : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) E)
  have hu : Summable t :=
    .of_norm_bounded hfx fun i ↦ CompletedProjectiveTensor.norm_coe_tmul_le (f i) (x i)
  have hTu : CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E (∑' i, t i) =
      T.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun v ↦
      (CompletedProjectiveTensor.hasSum_toContinuousLinearMap_apply hu.hasSum v).unique (hT v)
  rw [trace_eq_of_toContinuousLinearMap_eq hE hTu]
  exact CompletedProjectiveTensor.hasSum_trace hu.hasSum

end NuclearOperator

end Banach

section TraceCyclicity

variable {𝕜 D E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Cyclicity of the nuclear trace: for a bounded operator `A : E →L[𝕜] D` and a nuclear operator
`T : D →L[𝕜] E` between Banach spaces with the approximation property, `A ∘L T` and `T ∘L A` have
the same nuclear trace. -/
theorem NuclearOperator.trace_mk'_comp_comm (hD : HasApproximationProperty 𝕜 D)
    (hE : HasApproximationProperty 𝕜 E) (A : E →L[𝕜] D) {T : D →L[𝕜] E}
    (hT : T ∈ nuclearOperators 𝕜 D E) :
    NuclearOperator.trace hD (NuclearOperator.mk' (comp_left_mem_nuclearOperators A hT)) =
      NuclearOperator.trace hE (NuclearOperator.mk' (comp_right_mem_nuclearOperators hT A)) := by
  obtain ⟨u, rfl⟩ := mem_nuclearOperators.1 hT
  have hAT : CompletedProjectiveTensor.toContinuousLinearMap 𝕜 D D
      (CompletedProjectiveTensor.mapL (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 D)) A u) =
      (NuclearOperator.mk' (comp_left_mem_nuclearOperators A hT)).toContinuousLinearMap := by
    have hid : ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.id 𝕜 D) =
        ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 D) := by ext; rfl
    simpa [hid] using CompletedProjectiveTensor.toContinuousLinearMap_mapL A
      (ContinuousLinearMap.id 𝕜 D) u
  have hTA : CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E
      (CompletedProjectiveTensor.mapL (ContinuousLinearMap.precomp 𝕜 A)
        (ContinuousLinearMap.id 𝕜 E) u) =
      (NuclearOperator.mk' (comp_right_mem_nuclearOperators hT A)).toContinuousLinearMap := by
    simpa using CompletedProjectiveTensor.toContinuousLinearMap_mapL
      (ContinuousLinearMap.id 𝕜 E) A u
  rw [NuclearOperator.trace_eq_of_toContinuousLinearMap_eq hD hAT,
    NuclearOperator.trace_eq_of_toContinuousLinearMap_eq hE hTA,
    CompletedProjectiveTensor.trace_mapL_precomp]

end TraceCyclicity

end TauCeti
