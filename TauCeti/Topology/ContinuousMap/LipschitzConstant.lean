/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Star
public import TauCeti.Topology.MetricSpace.Holder

/-!
# The Lipschitz constant of a continuous map

For a continuous map `f : C(X, E)` from a metric space, `ContinuousMap.classicalLip f` is its
extended Lipschitz constant

`classicalLip f = sup_{x ≠ y} edist (f x) (f y) / edist x y ∈ [0, ∞]`,

with the empty supremum equal to `0`. It is Mathlib's extended Hölder seminorm `eHolderNorm 1 f`
of exponent one. On the real continuous functions of a compact metric space it is the classical
Lip-norm of Rieffel, the extended seminorm whose state metric on the probability measures is the
`1`-Wasserstein distance; this file records its finite domain, kernel and seminorm laws.

`classicalLip f ≤ r` is exactly `LipschitzWith r f`, and `classicalLip f` is finite exactly when
`f` is Lipschitz. The seminorm laws hold: it vanishes exactly on constant maps, is invariant under
negation, under adding a constant and under an isometric star, is subadditive and absolutely
homogeneous, and satisfies the Leibniz estimate
`classicalLip (f * g) ≤ ‖f‖_∞ classicalLip g + ‖g‖_∞ classicalLip f` for bounded maps into a
normed ring.

The distance of `X` is recovered from bounded `1`-Lipschitz real functions:
`d(x, y) = max {|f x - f y| : f ∈ C_b(X, ℝ), classicalLip f ≤ 1}`, attained by the bounded
function `z ↦ min (d(z, x)) (d(x, y))`. Bounded functions suffice, so no uniform norm on all of
`C(X, ℝ)` is needed when `X` is not compact.

## Main declarations

* `ContinuousMap.classicalLip`: the extended Lipschitz constant of a continuous map.
* `ContinuousMap.classicalLip_eq_iSup`: it is the supremum of the difference quotients.
* `ContinuousMap.classicalLip_le_coe_iff`: `classicalLip f ≤ r ↔ LipschitzWith r f`.
* `ContinuousMap.classicalLip_lt_top_iff`: it is finite exactly on the Lipschitz maps.
* `ContinuousMap.classicalLip_eq_zero_iff`: it vanishes exactly on constant maps.
* `ContinuousMap.classicalLip_add_le`, `ContinuousMap.classicalLip_smul`,
  `ContinuousMap.classicalLip_star`: the seminorm and star laws.
* `ContinuousMap.classicalLip_mul_le_of_forall_nnnorm_le`, `ContinuousMap.classicalLip_mul_le`:
  the Leibniz estimate, for bounded maps and on a compact space.
* `TauCeti.isGreatest_dist_classicalLip`, `TauCeti.edist_eq_iSup_classicalLip`: the distance is
  the greatest difference of values of a bounded `1`-Lipschitz real function.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), §8.
-/

public section

open scoped NNReal ENNReal BoundedContinuousFunction

namespace ContinuousMap

variable {X E : Type*} [MetricSpace X]

section PseudoEMetricSpace

variable [PseudoEMetricSpace E] {f : C(X, E)}

/-- The extended Lipschitz constant `sup_{x ≠ y} edist (f x) (f y) / edist x y` of a continuous
map from a metric space, with the empty supremum equal to `0`; it is the extended Hölder seminorm
`eHolderNorm 1 f` of exponent one. On `C(X, ℝ)` this is the classical Lip-norm. -/
noncomputable def classicalLip (f : C(X, E)) : ℝ≥0∞ :=
  eHolderNorm 1 f

theorem classicalLip_def (f : C(X, E)) : classicalLip f = eHolderNorm 1 f :=
  (rfl)

/-- The Lipschitz constant is the supremum of the difference quotients over distinct points. -/
theorem classicalLip_eq_iSup (f : C(X, E)) :
    classicalLip f = ⨆ (x) (y) (_ : x ≠ y), edist (f x) (f y) / edist x y := by
  simp [classicalLip_def, eHolderNorm_eq_iSup]

/-- The Lipschitz constant is at most `C` exactly when `C` is a Lipschitz bound for `f`. -/
theorem classicalLip_le_iff {C : ℝ≥0∞} :
    classicalLip f ≤ C ↔ ∀ x y, edist (f x) (f y) ≤ C * edist x y := by
  simp [classicalLip_def, eHolderNorm_le_iff]

/-- The Lipschitz inequality with the Lipschitz constant as constant. -/
theorem edist_le_classicalLip_mul (f : C(X, E)) (x y : X) :
    edist (f x) (f y) ≤ classicalLip f * edist x y :=
  classicalLip_le_iff.1 le_rfl x y

/-- The Lipschitz constant is at most `r` exactly when `f` is `r`-Lipschitz. -/
theorem classicalLip_le_coe_iff {r : ℝ≥0} : classicalLip f ≤ r ↔ LipschitzWith r f :=
  classicalLip_le_iff

/-- A map with finite Lipschitz constant is Lipschitz with that constant. -/
theorem lipschitzWith_classicalLip (hf : classicalLip f ≠ ∞) :
    LipschitzWith (classicalLip f).toNNReal f :=
  classicalLip_le_coe_iff.1 (ENNReal.coe_toNNReal hf).ge

/-- The Lipschitz constant is finite exactly on the Lipschitz maps. -/
theorem classicalLip_lt_top_iff : classicalLip f < ∞ ↔ ∃ K, LipschitzWith K f := by
  simp [classicalLip_def, MemHolder, holderWith_one]

/-- On a subsingleton space, in particular on the empty space, every Lipschitz constant is `0`. -/
@[simp]
theorem classicalLip_of_subsingleton [Subsingleton X] (f : C(X, E)) : classicalLip f = 0 :=
  nonpos_iff_eq_zero.1 <| classicalLip_le_iff.2 fun x y ↦ by simp [Subsingleton.elim x y]

@[simp]
theorem classicalLip_const (c : E) : classicalLip (const X c) = 0 :=
  eHolderNorm_const X 1 c

/-- On a space with at most the two points `x` and `y`, the Lipschitz constant of `f` is the
single difference quotient `edist (f x) (f y) / edist x y`; for `x = y` both sides are `0`. -/
theorem classicalLip_eq_edist_div_of_forall_eq_or_eq {x y : X} (h : ∀ z, z = x ∨ z = y)
    (f : C(X, E)) : classicalLip f = edist (f x) (f y) / edist x y := by
  rcases eq_or_ne x y with rfl | hxy
  · have : Subsingleton X := ⟨fun a b ↦ (h a).elim (fun ha ↦ (h b).elim (by grind) (by grind))
      fun ha ↦ (h b).elim (by grind) (by grind)⟩
    simp
  refine le_antisymm (classicalLip_le_iff.2 fun a b ↦ ?_) ?_
  · have hle : edist (f x) (f y) ≤ edist (f x) (f y) / edist x y * edist x y :=
      (ENNReal.div_mul_cancel (edist_pos.2 hxy).ne' (edist_ne_top x y)).ge
    rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
    · simp
    · exact hle
    · rwa [edist_comm (f a), edist_comm a b]
    · simp
  · rw [classicalLip_eq_iSup]
    exact le_iSup₂_of_le x y (le_iSup_of_le hxy le_rfl)

end PseudoEMetricSpace

/-- The Lipschitz constant vanishes exactly on constant maps. -/
theorem classicalLip_eq_zero_iff [EMetricSpace E] {f : C(X, E)} :
    classicalLip f = 0 ↔ ∀ x y, f x = f y :=
  eHolderNorm_eq_zero

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E]

@[simp]
theorem classicalLip_zero : classicalLip (0 : C(X, E)) = 0 :=
  eHolderNorm_zero X 1

/-- The Lipschitz constant is subadditive. -/
theorem classicalLip_add_le (f g : C(X, E)) :
    classicalLip (f + g) ≤ classicalLip f + classicalLip g :=
  classicalLip_le_iff.2 fun x y ↦ (edist_add_add_le _ _ _ _).trans <| by
    rw [add_mul]
    exact add_le_add (edist_le_classicalLip_mul f x y) (edist_le_classicalLip_mul g x y)

@[simp]
theorem classicalLip_neg (f : C(X, E)) : classicalLip (-f) = classicalLip f := by
  simp [classicalLip_eq_iSup]

theorem classicalLip_sub_le (f g : C(X, E)) :
    classicalLip (f - g) ≤ classicalLip f + classicalLip g := by
  simpa [sub_eq_add_neg] using classicalLip_add_le f (-g)

/-- Adding a constant does not change the Lipschitz constant. -/
@[simp]
theorem classicalLip_add_const (f : C(X, E)) (c : E) :
    classicalLip (f + const X c) = classicalLip f := by
  simp [classicalLip_eq_iSup]

/-- The Lipschitz constant is absolutely homogeneous. -/
theorem classicalLip_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜)
    (f : C(X, E)) : classicalLip (c • f) = ‖c‖₊ * classicalLip f := by
  simp [classicalLip_eq_iSup, edist_smul₀, ENNReal.smul_def, ENNReal.mul_iSup, mul_div_assoc]

/-- An isometric star does not change the Lipschitz constant. -/
@[simp]
theorem classicalLip_star [StarAddMonoid E] [NormedStarGroup E] (f : C(X, E)) :
    classicalLip (star f) = classicalLip f := by
  simp [classicalLip_eq_iSup]

end SeminormedAddCommGroup

section Leibniz

variable {R : Type*} [NonUnitalSeminormedRing R]

/-- **Leibniz estimate** for the Lipschitz constant of a product of bounded maps into a normed
ring: if `‖f‖ ≤ a` and `‖g‖ ≤ b` pointwise, then
`classicalLip (f * g) ≤ a * classicalLip g + b * classicalLip f`. -/
theorem classicalLip_mul_le_of_forall_nnnorm_le {f g : C(X, R)} {a b : ℝ≥0}
    (hf : ∀ x, ‖f x‖₊ ≤ a) (hg : ∀ x, ‖g x‖₊ ≤ b) :
    classicalLip (f * g) ≤ a * classicalLip g + b * classicalLip f := by
  refine classicalLip_le_iff.2 fun x y ↦ ?_
  have key : ‖f x * g x - f y * g y‖₊ ≤ a * ‖g x - g y‖₊ + ‖f x - f y‖₊ * b := by
    rw [show f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y by noncomm_ring]
    refine (nnNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (nnNorm_mul_le _ _).trans (by gcongr; exact hf x)
    · exact (nnNorm_mul_le _ _).trans (by gcongr; exact hg y)
  have hf' := edist_le_classicalLip_mul f x y
  have hg' := edist_le_classicalLip_mul g x y
  simp only [edist_nndist, nnDist_eq_nnNorm, mul_apply] at hf' hg' ⊢
  calc (‖f x * g x - f y * g y‖₊ : ℝ≥0∞)
      ≤ a * ‖g x - g y‖₊ + ‖f x - f y‖₊ * b := by exact_mod_cast key
    _ ≤ a * (classicalLip g * nndist x y) + classicalLip f * nndist x y * b := by gcongr
    _ = (a * classicalLip g + b * classicalLip f) * nndist x y := by ring

/-- **Leibniz estimate** on a compact space:
`classicalLip (f * g) ≤ ‖f‖ * classicalLip g + ‖g‖ * classicalLip f` for the uniform norms. -/
theorem classicalLip_mul_le [CompactSpace X] (f g : C(X, R)) :
    classicalLip (f * g) ≤ ‖f‖₊ * classicalLip g + ‖g‖₊ * classicalLip f :=
  classicalLip_mul_le_of_forall_nnnorm_le (fun x ↦ f.norm_coe_le_norm x)
    (fun x ↦ g.norm_coe_le_norm x)

end Leibniz

end ContinuousMap

namespace TauCeti

open ContinuousMap

variable {X : Type*} [MetricSpace X]

/-- The distance between two points is the greatest difference `|f x - f y|` of the values of a
bounded continuous real function with Lipschitz constant at most `1`; it is attained by
`z ↦ min (dist z x) (dist x y)`. -/
theorem isGreatest_dist_classicalLip (x y : X) :
    IsGreatest {r | ∃ f : X →ᵇ ℝ, classicalLip (f : C(X, ℝ)) ≤ 1 ∧ |f x - f y| = r}
      (dist x y) := by
  refine ⟨?_, ?_⟩
  · let w : C(X, ℝ) := ⟨fun z ↦ min (dist z x) (dist x y), by fun_prop⟩
    refine ⟨BoundedContinuousFunction.mkOfBound w (dist x y) fun a b ↦ ?_, ?_, ?_⟩
    · rw [Real.dist_eq]
      exact abs_sub_le_of_nonneg_of_le (le_min dist_nonneg dist_nonneg) (min_le_right _ _)
        (le_min dist_nonneg dist_nonneg) (min_le_right _ _)
    · rw [← ENNReal.coe_one, classicalLip_le_coe_iff]
      exact (LipschitzWith.dist_left x).min_const (dist x y)
    · simp [w, dist_comm y x]
  · rintro r ⟨f, hf, rfl⟩
    rw [← ENNReal.coe_one, classicalLip_le_coe_iff] at hf
    simpa [Real.dist_eq] using hf.dist_le_mul x y

/-- The extended distance between two points is the supremum of `edist (f x) (f y)` over the
bounded continuous real functions `f` with Lipschitz constant at most `1`. -/
theorem edist_eq_iSup_classicalLip (x y : X) :
    edist x y = ⨆ (f : X →ᵇ ℝ) (_ : classicalLip (f : C(X, ℝ)) ≤ 1), edist (f x) (f y) := by
  refine le_antisymm ?_ (iSup₂_le fun f hf ↦ ?_)
  · obtain ⟨f, hf, hxy⟩ := (isGreatest_dist_classicalLip x y).1
    refine le_iSup₂_of_le f hf ?_
    rw [edist_dist, edist_dist, Real.dist_eq, hxy]
  · simpa using (classicalLip_le_iff.1 hf) x y

end TauCeti
