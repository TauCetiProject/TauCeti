/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Bounded bilinear maps and bounded scalar actions over a normed ring

Over a seminormed commutative ring `R`, which need not be a field, an `R`-bilinear map `β` with
`‖β x y‖ ≤ C * ‖x‖ * ‖y‖` is jointly continuous (`LinearMap.continuous₂_of_bound`), and so is a
scalar action with `‖r • m‖ ≤ C * ‖r‖ * ‖m‖` (`TauCeti.continuousSMul_of_norm_smul_le`). For an
`R`-algebra `S`, such a bound on the action makes the structure map bounded
(`TauCeti.exists_norm_algebraMap_le_of_norm_smul_le`).

A fibrewise linear change of coordinates `(x, v) ↦ (x, e x v)`, with `e` continuous at `a`, tends
to `(a, 0)` at `(a, 0)` (`ContinuousAt.tendsto_prodMk_clm_apply`).

Since the invertible operators from a Banach space form an open set, invertibility at the zeros of
a map `d` is uniform on a compact set: if `A x` is invertible wherever `d x = 0` on a compact `K`,
with `d` and `A` continuous on `K`, then every operator close to `A x` at a point `x ∈ K` where
`d x` is small is invertible (`IsCompact.exists_pos_forall_isInvertible_of_norm_le`). This drives
the persistence of nondegenerate critical points and fixed points under small perturbations.
-/

public section

open Filter Metric Set Topology
open scoped NNReal

variable {R : Type*} [SeminormedCommRing R]

/-- An `R`-bilinear map bounded by `C * ‖x‖ * ‖y‖` is jointly continuous. -/
theorem LinearMap.continuous₂_of_bound {X Y Z : Type*} [SeminormedAddCommGroup X]
    [Module R X] [SeminormedAddCommGroup Y] [Module R Y] [SeminormedAddCommGroup Z] [Module R Z]
    (β : X →ₗ[R] Y →ₗ[R] Z) (C : ℝ) (hβ : ∀ x y, ‖β x y‖ ≤ C * ‖x‖ * ‖y‖) :
    Continuous fun p : X × Y ↦ β p.1 p.2 :=
  IsBoundedBilinearMap.continuous (𝕜 := R)
    { add_left := fun x₁ x₂ y ↦ by simp
      smul_left := fun c x y ↦ by simp
      add_right := fun x y₁ y₂ ↦ by simp
      smul_right := fun c x y ↦ by simp
      bound := ⟨max C 1, by positivity, fun x y ↦
        (hβ x y).trans (by gcongr; exact le_max_left _ _)⟩ }

/-- A scalar action bounded by `C * ‖r‖ * ‖m‖` is continuous. -/
theorem TauCeti.continuousSMul_of_norm_smul_le {M : Type*} [SeminormedAddCommGroup M]
    [Module R M]
    (h : ∃ C : ℝ≥0, ∀ (r : R) (m : M), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) : ContinuousSMul R M :=
  h.elim fun C hC ↦ ⟨(LinearMap.lsmul R M).continuous₂_of_bound C hC⟩

/-- If the action of `R` on an `R`-algebra `S` is bounded, `‖r • s‖ ≤ C * ‖r‖ * ‖s‖`, then so is
the structure map: `‖algebraMap R S r‖ ≤ C * ‖1‖ * ‖r‖`. -/
theorem TauCeti.exists_norm_algebraMap_le_of_norm_smul_le {S : Type*} [SeminormedRing S]
    [Algebra R S] (h : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) :
    ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖ :=
  h.elim fun C hC ↦ ⟨C * ‖(1 : S)‖₊, fun r ↦ by
    simpa [Algebra.algebraMap_eq_smul_one, mul_right_comm] using hC r 1⟩

/-- A fibrewise linear change of coordinates `(x, v) ↦ (x, e x v)`, with `e` continuous at `a`,
tends to `(a, 0)` at `(a, 0)`. -/
theorem ContinuousAt.tendsto_prodMk_clm_apply {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace X] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {e : X → E →L[𝕜] F} {a : X} (he : ContinuousAt e a) :
    Tendsto (fun z : X × E ↦ (z.1, e z.1 z.2)) (𝓝 (a, 0)) (𝓝 (a, 0)) := by
  have h : ContinuousAt (fun z : X × E ↦ e z.1 z.2) (a, 0) :=
    (he.comp (f := Prod.fst) (x := (a, (0 : E))) continuousAt_fst).clm_apply continuousAt_snd
  simpa using continuousAt_fst.tendsto.prodMk_nhds h.tendsto

/-- **Invertibility near the zeros of a map is uniform on a compact set.**

Let `d` and `A` be continuous on a compact set `K`, where `A` takes values in the operators from a
Banach space, and let `A x` be invertible at every zero `x ∈ K` of `d`. Then there is `δ > 0` such
that, at every point `x ∈ K` with `‖d x‖ ≤ δ`, every operator within `δ` of `A x` is invertible. -/
theorem IsCompact.exists_pos_forall_isInvertible_of_norm_le {𝕜 X F E G : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X] [NormedAddCommGroup F] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {K : Set X}
    (hK : IsCompact K) {d : X → F} {A : X → E →L[𝕜] G} (hd : ContinuousOn d K)
    (hA : ContinuousOn A K) (h : ∀ x ∈ K, d x = 0 → (A x).IsInvertible) :
    ∃ δ > 0, ∀ x ∈ K, ∀ T : E →L[𝕜] G, ‖d x‖ ≤ δ → ‖T - A x‖ ≤ δ → T.IsInvertible := by
  -- The non-invertible operators form a closed set `S`; if it is empty there is nothing to prove.
  set S : Set (E →L[𝕜] G) := {T | ¬T.IsInvertible}
  have hS : IsClosed S := ContinuousLinearMap.isOpen_setOfPred_isInvertible.isClosed_compl
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun x _ T _ _ ↦ ?_⟩
    by_contra hT
    exact hSe.subset (mem_ofPred.2 hT)
  -- `φ x` is positive on `K`: at a zero of `d` the operator `A x` lies outside `S`.
  set φ : X → ℝ := fun x ↦ ‖d x‖ + infDist (A x) S
  have hφ : ContinuousOn φ K := hd.norm.add ((continuous_infDist_pt S).comp_continuousOn hA)
  have hpos (x : X) (hx : x ∈ K) : 0 < φ x := by
    by_cases h₀ : d x = 0
    · have hx' := (hS.notMem_iff_infDist_pos hSne).1 fun hxS ↦ hxS (h x hx h₀)
      simpa [φ, h₀] using hx'
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.2 h₀) infDist_nonneg
  -- By compactness, `φ` has a positive lower bound `m` on `K`.
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ x ∈ K, m ≤ φ x := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hφ
    exact ⟨φ x₀, hpos x₀ hx₀, fun x hx ↦ hmin hx⟩
  -- If `‖d x‖ ≤ m / 3`, then `A x` is at distance at least `2m / 3` from `S`, so an operator in
  -- `S` cannot lie within `m / 3` of it.
  refine ⟨m / 3, by positivity, fun x hx T hdx hT ↦ ?_⟩
  by_contra hTS
  have hinf : infDist (A x) S ≤ ‖T - A x‖ :=
    (infDist_le_dist_of_mem (mem_ofPred.2 hTS : T ∈ S)).trans_eq (dist_comm _ _ |>.trans
      (dist_eq_norm _ _))
  linarith [hmK x hx]

end
