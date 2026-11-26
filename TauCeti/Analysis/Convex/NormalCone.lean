/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import TauCeti.Analysis.Convex.Subdifferential
public import TauCeti.Topology.Order.OrderClosed

/-!
# Normal cones and the constrained subdifferential sum rule

Let `V` be a real topological vector space and `C ⊆ V`. The **normal cone** of `C` at `u` is the
set `N_C(u) = {f | ∀ v ∈ C, f (v - u) ≤ 0}` of continuous linear functionals
(`TauCeti.normalCone`), and the **indicator** of `C` is the function `ι_C : V → EReal` with value
`0` on `C` and `⊤` outside (`TauCeti.constraintIndicator`). Subgradients are taken for the
evaluation pairing `(v, f) ↦ f v` between `V` and its dual, `(topDualPairing ℝ V).flip`.

For a real energy `E : V → ℝ`, a point `u ∈ C` minimizes `E` on `C` exactly when
`0 ∈ ∂(E + ι_C)(u)` (`TauCeti.isMinOn_iff_zero_mem_subdifferential_add_constraintIndicator`).
The **sum rule** `∂(E + ι_C)(u) = ∂E(u) + N_C(u)`, a case of the Moreau–Rockafellar theorem,
holds when `C` is convex and `E` is convex and continuous at some point of `C`
(`TauCeti.subdifferential_add_constraintIndicator_eq`); the inclusion `⊇` holds with no
hypothesis (`TauCeti.subdifferential_add_normalCone_subset`). So a convex energy continuous at a
point of a convex constraint has `0 ∈ ∂E(u) + N_C(u)` at every constrained minimizer `u`.

The proof of `⊆` separates. For `f ∈ ∂(E + ι_C)(u)`, the tilted energy
`g v = E v - E u - f (v - u)` is nonnegative on `C` and vanishes at `u`, so the interior of the
strict epigraph of `g` misses the convex set `{(v, t) | v ∈ C, t ≤ 0}` of `V × ℝ`. Continuity of
`E` at `x₀ ∈ C` puts `(x₀, g x₀ + 1)` in that interior, so the geometric Hahn–Banach theorem
gives a functional `(v, t) ↦ ℓ v + λ t` separating the two sets. Testing at `(x₀, t)` for large
`t` shows `λ < 0`, so the separating hyperplane is not vertical. Dividing by `-λ` gives `h` with
`g v ≥ h (v - u)` everywhere and `h (w - u) ≥ 0` on `C`: then `f + h ∈ ∂E(u)` and `-h ∈ N_C(u)`.

## Main declarations

* `TauCeti.normalCone C u`: the normal cone `N_C(u)`, a `PointedCone` defined as the dual cone
  `PointedCone.dual` of `u - C`; `TauCeti.normalCone_univ` and
  `TauCeti.normalCone_anti` give the unconstrained case and restriction, and
  `TauCeti.normalCone_image_add` translation.
* `TauCeti.constraintIndicator C`: the indicator `ι_C`;
  `TauCeti.subdifferential_constraintIndicator` identifies `∂ι_C(u)` with `N_C(u)` for `u ∈ C`.
* `TauCeti.isMinOn_iff_zero_mem_subdifferential_add_constraintIndicator`: constrained minima.
* `TauCeti.subdifferential_add_normalCone_subset` and
  `TauCeti.subdifferential_add_constraintIndicator_eq`: the sum rule.

## References

* I. Ekeland and R. Témam, *Convex Analysis and Variational Problems*, Classics in Applied
  Mathematics 28, SIAM 1999, Chapter I, §5, Proposition 5.6.
* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §23,
  Theorem 23.8.
-/

public section

noncomputable section

open Set Topology Pointwise

namespace TauCeti

section Indicator

variable {X : Type*}

/-- The indicator `ι_C` of a set `C` in convex analysis: `0` on `C` and `⊤` outside. -/
def constraintIndicator (C : Set X) (v : X) : EReal := by
  classical
  exact if v ∈ C then 0 else ⊤

/-- The indicator vanishes on the set. -/
@[simp]
theorem constraintIndicator_of_mem {C : Set X} {v : X} (hv : v ∈ C) :
    constraintIndicator C v = 0 := by
  simp [constraintIndicator, hv]

/-- The indicator is `⊤` off the set. -/
@[simp]
theorem constraintIndicator_of_notMem {C : Set X} {v : X} (hv : v ∉ C) :
    constraintIndicator C v = ⊤ := by
  simp [constraintIndicator, hv]

/-- A real energy plus the indicator of `C` is the energy on `C` and `⊤` outside. -/
theorem coe_add_constraintIndicator (E : X → ℝ) (C : Set X) [DecidablePred (· ∈ C)] :
    (fun v ↦ (E v : EReal) + constraintIndicator C v) =
      fun v ↦ if v ∈ C then (E v : EReal) else ⊤ := by
  funext v
  by_cases hv : v ∈ C <;> simp [hv]

end Indicator

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The normal cone `N_C(u) = {f | ∀ v ∈ C, f (v - u) ≤ 0}` of a set `C` at a point `u`: the dual
cone of the translate `u - C` for the evaluation pairing. -/
def normalCone (C : Set V) (u : V) : PointedCone ℝ (StrongDual ℝ V) :=
  PointedCone.dual (topDualPairing ℝ V).flip ((u - ·) '' C)

/-- The defining condition of the normal cone. -/
@[simp]
theorem mem_normalCone_iff {C : Set V} {u : V} {f : StrongDual ℝ V} :
    f ∈ normalCone C u ↔ ∀ v ∈ C, f (v - u) ≤ 0 := by
  simp only [normalCone, PointedCone.mem_dual, forall_mem_image, LinearMap.flip_apply,
    topDualPairing_apply]
  refine forall₂_congr fun v _ ↦ ?_
  rw [← neg_sub, map_neg, neg_nonneg]

/-- Enlarging the set shrinks the normal cone: `C ⊆ D` gives `N_D(u) ≤ N_C(u)`. -/
@[gcongr]
theorem normalCone_anti {C D : Set V} (h : C ⊆ D) (u : V) : normalCone D u ≤ normalCone C u :=
  PointedCone.dual_anti (image_mono h)

/-- **The unconstrained case**: the normal cone of the whole space is `⊥ = {0}`. -/
@[simp]
theorem normalCone_univ (u : V) : normalCone (univ : Set V) u = ⊥ := by
  rw [normalCone, image_univ_of_surjective fun w ↦ ⟨u - w, sub_sub_cancel u w⟩,
    PointedCone.dual_univ, Submodule.zero_eq_bot]
  intro f g hfg
  ext v
  exact LinearMap.congr_fun hfg v

/-- **Translation**: the normal cone of `C + a` at `u + a` is the normal cone of `C` at `u`. -/
theorem normalCone_image_add (C : Set V) (u a : V) :
    normalCone ((· + a) '' C) (u + a) = normalCone C u := by
  ext f
  simp only [mem_normalCone_iff, forall_mem_image, add_sub_add_right_eq_sub]

/-- The normal cone is closed for any topology on the dual in which evaluations are
continuous. -/
theorem isClosed_normalCone [TopologicalSpace (StrongDual ℝ V)]
    (h : ∀ v : V, Continuous fun f : StrongDual ℝ V ↦ f v) (C : Set V) (u : V) :
    IsClosed (normalCone C u : Set (StrongDual ℝ V)) :=
  PointedCone.isClosed_dual h

/-- A subgradient of `E + ι_C` at a point `u` of `C` is a functional `f` with
`E u + f (v - u) ≤ E v` on `C`. -/
theorem mem_subdifferential_add_constraintIndicator_iff {E : V → ℝ} {C : Set V} {u : V}
    (hu : u ∈ C) {f : StrongDual ℝ V} :
    f ∈ subdifferential (topDualPairing ℝ V).flip
        (fun v ↦ (E v : EReal) + constraintIndicator C v) u ↔
      ∀ v ∈ C, E u + f (v - u) ≤ E v := by
  classical
  rw [coe_add_constraintIndicator, mem_subdifferential_ite_iff _ hu]
  simp only [LinearMap.flip_apply, topDualPairing_apply]

/-- The subdifferential of `E + ι_C` is empty off `C`. -/
theorem subdifferential_add_constraintIndicator_of_notMem (E : V → ℝ) {C : Set V} {u : V}
    (hu : u ∉ C) :
    subdifferential (topDualPairing ℝ V).flip (fun v ↦ (E v : EReal) + constraintIndicator C v) u =
      ∅ :=
  subdifferential_eq_empty_of_eq_top _ (by simp [hu])

/-- The subdifferential of the indicator of `C` at a point of `C` is the normal cone. -/
theorem subdifferential_constraintIndicator {C : Set V} {u : V} (hu : u ∈ C) :
    subdifferential (topDualPairing ℝ V).flip (constraintIndicator C) u = normalCone C u := by
  have hfun : constraintIndicator C =
      fun v ↦ (((fun _ : V ↦ (0 : ℝ)) v : ℝ) : EReal) + constraintIndicator C v := by
    funext v
    simp
  ext f
  rw [hfun, mem_subdifferential_add_constraintIndicator_iff hu]
  simp

/-- The subdifferential of the indicator of `C` is empty off `C`. -/
theorem subdifferential_constraintIndicator_of_notMem {C : Set V} {u : V} (hu : u ∉ C) :
    subdifferential (topDualPairing ℝ V).flip (constraintIndicator C) u = ∅ :=
  subdifferential_eq_empty_of_eq_top _ (constraintIndicator_of_notMem hu)

/-- **Constrained minima.** A point `u ∈ C` minimizes a real energy `E` on `C` exactly when
`0 ∈ ∂(E + ι_C)(u)`. No convexity is needed. -/
theorem isMinOn_iff_zero_mem_subdifferential_add_constraintIndicator {E : V → ℝ} {C : Set V}
    {u : V} (hu : u ∈ C) :
    IsMinOn E C u ↔
      0 ∈ subdifferential (topDualPairing ℝ V).flip
        (fun v ↦ (E v : EReal) + constraintIndicator C v) u := by
  rw [mem_subdifferential_add_constraintIndicator_iff hu, isMinOn_iff]
  simp

/-- **The sum rule, easy inclusion**: `∂E(u) + N_C(u) ⊆ ∂(E + ι_C)(u)` at every point `u ∈ C`, with
no hypothesis on `E` or `C`. -/
theorem subdifferential_add_normalCone_subset {E : V → ℝ} {C : Set V} {u : V} (hu : u ∈ C) :
    subdifferential (topDualPairing ℝ V).flip (fun v ↦ (E v : EReal)) u + normalCone C u ⊆
      subdifferential (topDualPairing ℝ V).flip
        (fun v ↦ (E v : EReal) + constraintIndicator C v) u := by
  rintro _ ⟨f, hf, h, hh, rfl⟩
  rw [mem_subdifferential_add_constraintIndicator_iff hu]
  intro v hv
  have h₁ := (mem_subdifferential_coe_iff _ E).1 hf v
  have h₂ := mem_normalCone_iff.1 hh v hv
  simp only [LinearMap.flip_apply, topDualPairing_apply, add_apply] at h₁ ⊢
  linarith

section SumRule

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- The last step of the separation: a nonvertical functional `(v, t) ↦ ℓ v + λ t`, `λ < 0`,
bounded by `c` on the graph of `g` and below by `c` on `C × {0}`, gives `h = ℓ / (-λ)` with
`g v ≥ h (v - u)` and `h (w - u) ≥ 0` on `C`, when `g u = 0`. -/
private theorem exists_le_and_nonneg_of_le {g : V → ℝ} {C : Set V} {u : V} {ℓ : StrongDual ℝ V}
    {lam c : ℝ} (hlam : lam < 0) (hle : ∀ v, ℓ v + lam * g v ≤ c) (hC : ∀ w ∈ C, c ≤ ℓ w)
    (huC : u ∈ C) (hgu : g u = 0) :
    ∃ h : StrongDual ℝ V, (∀ v, h (v - u) ≤ g v) ∧ ∀ w ∈ C, 0 ≤ h (w - u) := by
  have hu := hle u
  rw [hgu, mul_zero, add_zero] at hu
  have hcu := hC u huC
  refine ⟨(-lam)⁻¹ • ℓ, fun v ↦ ?_, fun w hw ↦ ?_⟩
  · have h := hle v
    rw [smul_apply, smul_eq_mul, map_sub, inv_mul_le_iff₀ (by linarith)]
    nlinarith
  · rw [smul_apply, smul_eq_mul, map_sub]
    exact mul_nonneg (inv_nonneg.2 (by linarith)) (by linarith [hC w hw])

/-- **Separation for the sum rule.** If a convex real function `g`, continuous at a point `x₀` of
a convex set `C`, is nonnegative on `C` and vanishes at `u ∈ C`, then there is a continuous linear
functional `h` with `g v ≥ h (v - u)` everywhere and `h (w - u) ≥ 0` on `C`. -/
theorem exists_le_and_nonneg_of_convexOn {g : V → ℝ} (hg : ConvexOn ℝ univ g) {C : Set V}
    (hC : Convex ℝ C) {x₀ u : V} (hx₀ : x₀ ∈ C) (hgx₀ : ContinuousAt g x₀) (hu : u ∈ C)
    (hgu : g u = 0) (hgC : ∀ w ∈ C, 0 ≤ g w) :
    ∃ h : StrongDual ℝ V, (∀ v, h (v - u) ≤ g v) ∧ ∀ w ∈ C, 0 ≤ h (w - u) := by
  set K : Set (V × ℝ) := {p | g p.1 < p.2}
  set T : Set (V × ℝ) := {p | p.1 ∈ C ∧ p.2 ≤ 0}
  have hKc : Convex ℝ K := by simpa using hg.convex_strict_epigraph
  have hTc : Convex ℝ T := hC.prod (convex_Iic 0)
  -- The point `(x₀, g x₀ + 1)` is interior to the strict epigraph.
  have hint : (x₀, g x₀ + 1) ∈ interior K := hgx₀.mem_interior_strict_epigraph (lt_add_one _)
  have hdisj : Disjoint (interior K) T := by
    refine Set.disjoint_left.2 fun p hpK hpT ↦ ?_
    have : g p.1 < p.2 := interior_subset hpK
    have := hgC p.1 hpT.1
    linarith [hpT.2]
  obtain ⟨φ, c, hφK, hφT⟩ :=
    geometric_hahn_banach_open hKc.interior isOpen_interior hTc hdisj
  -- Write `φ (v, t) = ℓ v + λ t`.
  set ℓ : StrongDual ℝ V := φ.comp (ContinuousLinearMap.inl ℝ V ℝ) 
  set lam : ℝ := φ (0, 1) 
  have hφ (v : V) (t : ℝ) : φ (v, t) = ℓ v + lam * t := by
    have hvt : ((v, t) : V × ℝ) = (v, 0) + t • (0, 1) := by ext <;> simp
    rw [hvt, map_add, map_smul]
    simp [ℓ, lam, mul_comm]
  -- `φ ≤ c` on the whole strict epigraph, by closure.
  have hφK' : ∀ p ∈ K, φ p ≤ c := by
    have hcl : K ⊆ closure (interior K) := by
      rw [hKc.closure_interior_eq_closure_of_nonempty_interior ⟨_, hint⟩]
      exact subset_closure
    intro p hp
    exact (closure_minimal (fun q hq ↦ (hφK q hq).le) (isClosed_le φ.continuous
      continuous_const)) (hcl hp)
  -- The separating hyperplane is not vertical: `λ < 0`.
  have hlam_neg : lam < 0 := by
    have h₁ := hφK (x₀, max (g x₀ + 1) 1) (hgx₀.mem_interior_strict_epigraph
      (lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)))
    have h₂ := hφT (x₀, 0) ⟨hx₀, le_rfl⟩
    rw [hφ] at h₁ h₂
    have : lam * max (g x₀ + 1) 1 < 0 := by linarith
    exact neg_of_mul_neg_left this (le_max_of_le_right zero_le_one)
  -- `ℓ v + λ g v ≤ c` everywhere.
  have hle (v : V) : ℓ v + lam * g v ≤ c := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have h := hφK' (v, g v + ε / (-lam)) (by
      have : 0 < ε / (-lam) := div_pos hε (by linarith)
      simpa [K] using this)
    rw [hφ, mul_add] at h
    have hlam0 : lam ≠ 0 := hlam_neg.ne
    have h' : lam * (ε / -lam) = -ε := by field_simp
    linarith
  exact exists_le_and_nonneg_of_le hlam_neg hle (fun w hw ↦ by
    simpa [hφ] using hφT (w, 0) ⟨hw, le_rfl⟩) hu hgu

/-- **The sum rule** (Moreau–Rockafellar): for a convex set `C`, a convex real energy `E`
continuous at some point of `C`, and `u ∈ C`, `∂(E + ι_C)(u) = ∂E(u) + N_C(u)`. -/
theorem subdifferential_add_constraintIndicator_eq {E : V → ℝ} (hE : ConvexOn ℝ univ E)
    {C : Set V} (hC : Convex ℝ C) {x₀ : V} (hx₀ : x₀ ∈ C) (hEx₀ : ContinuousAt E x₀) {u : V}
    (hu : u ∈ C) :
    subdifferential (topDualPairing ℝ V).flip (fun v ↦ (E v : EReal) + constraintIndicator C v) u =
      subdifferential (topDualPairing ℝ V).flip (fun v ↦ (E v : EReal)) u + normalCone C u := by
  refine Subset.antisymm (fun f hf ↦ ?_) (subdifferential_add_normalCone_subset hu)
  rw [mem_subdifferential_add_constraintIndicator_iff hu] at hf
  -- Tilt `E` by `f` and separate.
  have hg : ConvexOn ℝ univ (fun v ↦ E v - E u - f (v - u)) := by
    have hfun : (fun v ↦ E v - E u - f (v - u)) = fun v ↦ (E - ⇑f) v + (f u - E u) := by
      funext v
      simp only [map_sub, Pi.sub_apply]
      ring
    rw [hfun]
    exact (hE.sub (f.toLinearMap.concaveOn convex_univ)).add_const (f u - E u)
  have hgc : ContinuousAt (fun v ↦ E v - E u - f (v - u)) x₀ :=
    (hEx₀.sub continuousAt_const).sub
      (f.continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const))
  obtain ⟨h, hh, hC'⟩ := exists_le_and_nonneg_of_convexOn hg hC hx₀ hgc hu (by simp)
    (fun w hw ↦ by linarith [hf w hw])
  · refine ⟨f + h, ?_, -h, mem_normalCone_iff.2 fun w hw ↦ by simpa using hC' w hw, by simp⟩
    rw [mem_subdifferential_coe_iff]
    intro v
    have := hh v
    simp only [LinearMap.flip_apply, topDualPairing_apply, add_apply] at this ⊢
    linarith

end SumRule

end TauCeti
