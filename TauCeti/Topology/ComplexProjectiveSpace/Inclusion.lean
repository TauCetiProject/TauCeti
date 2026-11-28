/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Basic
public import TauCeti.Topology.CWComplex.Classical.ComplexProjective
public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# The inclusion `CPⁿ ⊆ CPⁿ⁺¹`

Appending a zero last coordinate is Mathlib's linear isometry
`LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.castLEEmb _) : ℂⁿ⁺¹ → ℂⁿ⁺²`, the zero extension along
`Fin.castLE`. It carries unit vectors to
unit vectors (`TauCeti.ComplexProjectiveSpace.sphereInclusion`) and commutes with unit complex
scalars, so it descends to the sphere-quotient models of complex projective space: the inclusion
`TauCeti.ComplexProjectiveSpace.inclusion n : CPⁿ → CPⁿ⁺¹`, a closed embedding
(`TauCeti.ComplexProjectiveSpace.isClosedEmbedding_inclusion`). Its image consists of the classes
of the unit vectors whose last coordinate vanishes
(`TauCeti.ComplexProjectiveSpace.mk_mem_range_inclusion_iff`).

In the CW structure `TauCeti.ComplexProjectiveSpace.cwComplex (n + 1)`, the cells of dimension
`2i` are the classes of the unit vectors whose last nonzero coordinate is the `i`-th. So the cells
of dimension at most `2n + 1` make up the image of `CPⁿ`
(`TauCeti.ComplexProjectiveSpace.skeletonLT_eq_range_inclusion`), and adding the single cell of
dimension `2n + 2` gives all of `CPⁿ⁺¹`
(`TauCeti.ComplexProjectiveSpace.skeletonLT_cwComplex_eq_univ`, for the CW structure alone).

These inclusions model the finite stages of the infinite complex projective space `CP∞`.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.inclusion`: the inclusion `CPⁿ → CPⁿ⁺¹`.
* `TauCeti.ComplexProjectiveSpace.mk_mem_range_inclusion_iff`: its image.
* `TauCeti.ComplexProjectiveSpace.skeletonLT_eq_range_inclusion`: `CPⁿ` is the
  `(2n + 1)`-skeleton of `CPⁿ⁺¹`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.6 (`CPⁿ⁺¹` as `CPⁿ` with a `2(n + 1)`-cell attached).
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti.ComplexProjectiveSpace

variable (n : ℕ)

/-- Appending a zero last coordinate, `ℂⁿ⁺¹ → ℂⁿ⁺²`, on unit vectors. -/
def sphereInclusion (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1 :=
  ⟨LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.castLEEmb (Nat.le_succ (n + 1))) x, by
    rw [mem_sphere_zero_iff_norm, LinearIsometry.norm_map, norm_eq_of_mem_sphere]⟩

@[simp]
theorem coe_sphereInclusion (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (sphereInclusion n x : EuclideanSpace ℂ (Fin (n + 2))) =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.castLEEmb (Nat.le_succ (n + 1))) x :=
  (rfl)

theorem sphereInclusion_smul (c : sphere (0 : ℂ) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    sphereInclusion n (c • x) = c • sphereInclusion n x :=
  Subtype.ext (LinearIsometry.map_smul _ (c : ℂ) _)

/-- The only index `j` of `Fin (n + 2)` with `n + 1 ≤ j` is the last one. -/
private theorem eq_last_of_le (j : Fin (n + 2)) (hj : n + 1 ≤ (j : ℕ)) : j = Fin.last (n + 1) :=
  Fin.ext (by have := j.is_lt; rw [Fin.val_last]; omega)

/-- **The inclusion `CPⁿ → CPⁿ⁺¹`**, sending the class of a unit vector `x` to the class of
`(x, 0)` (`TauCeti.ComplexProjectiveSpace.inclusion_mk`). -/
def inclusion : C(ComplexProjectiveSpace n, ComplexProjectiveSpace (n + 1)) where
  toFun := ComplexProjectiveSpace.lift n (fun x ↦ mk (n + 1) (sphereInclusion n x))
    fun c x ↦ by rw [sphereInclusion_smul, mk_smul]
  continuous_toFun := (isOpenQuotientMap_mk n).isQuotientMap.continuous_iff.2 <|
    ((continuous_mk (n + 1)).comp <|
      ((LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.castLEEmb (Nat.le_succ (n + 1)))).continuous.comp
        continuous_subtypeVal).subtype_mk _).congr fun x ↦
        (ComplexProjectiveSpace.lift_mk n _ _ x).symm

/-- The inclusion `CPⁿ → CPⁿ⁺¹` sends the class of a unit vector `x` to the class of `(x, 0)`. -/
@[simp]
theorem inclusion_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    inclusion n (mk n x) = mk (n + 1) (sphereInclusion n x) :=
  ComplexProjectiveSpace.lift_mk n _ _ x

/-- The inclusion `CPⁿ → CPⁿ⁺¹` is injective: if `(x, 0) = c • (y, 0)` then `x = c • y`. -/
theorem inclusion_injective : Function.Injective (inclusion n) := by
  intro p q h
  induction p using ComplexProjectiveSpace.inductionOn with | h x => ?_
  induction q using ComplexProjectiveSpace.inductionOn with | h y => ?_
  rw [inclusion_mk, inclusion_mk, mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  rw [← sphereInclusion_smul] at hc
  exact (mk_eq_mk_iff n x y).2 ⟨c, Subtype.ext
    ((LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.castLEEmb (Nat.le_succ (n + 1)))).injective
      (congrArg Subtype.val hc))⟩

/-- The inclusion `CPⁿ → CPⁿ⁺¹` is a closed embedding. -/
theorem isClosedEmbedding_inclusion : IsClosedEmbedding (inclusion n) :=
  (inclusion n).continuous.isClosedEmbedding (inclusion_injective n)

/-- **The image of `CPⁿ` in `CPⁿ⁺¹`** consists of the classes of the unit vectors whose last
coordinate vanishes. -/
theorem mk_mem_range_inclusion_iff (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) :
    mk (n + 1) y ∈ range (inclusion n) ↔
      (y : EuclideanSpace ℂ (Fin (n + 2))) (Fin.last (n + 1)) = 0 := by
  constructor
  · rintro ⟨p, hp⟩
    induction p using ComplexProjectiveSpace.inductionOn with | h x => ?_
    rw [inclusion_mk, eq_comm, mk_eq_mk_iff] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [← sphereInclusion_smul, coe_sphereInclusion]
    exact EuclideanSpace.piLpExtendByZero_castLEEmb_apply_of_le _ _ (Fin.val_last _).ge
  · intro hy
    have hv := EuclideanSpace.piLpExtendByZero_castLEEmb_take (Nat.le_succ (n + 1)) fun j hj ↦ by
      rwa [eq_last_of_le n j hj]
    refine ⟨mk n ⟨EuclideanSpace.take (Nat.le_succ (n + 1)) y, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm,
        ← (LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.castLEEmb (Nat.le_succ (n + 1)))).norm_map,
        hv, norm_eq_of_mem_sphere]
    · rw [inclusion_mk]
      exact congrArg (mk (n + 1)) (Subtype.ext hv)

/-- **`CPⁿ` is the `(2n + 1)`-skeleton of `CPⁿ⁺¹`**: the cells of `CPⁿ⁺¹` of dimension below
`2n + 2` make up the image of the inclusion `CPⁿ → CPⁿ⁺¹`. -/
theorem skeletonLT_eq_range_inclusion :
    letI := cwComplex (n + 1)
    (skeletonLT (univ : Set (ComplexProjectiveSpace (n + 1))) ((2 * n + 2 : ℕ) : ℕ∞) :
      Set (ComplexProjectiveSpace (n + 1))) = range (inclusion n) := by
  let := cwComplex (n + 1)
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT]
  ext p
  obtain ⟨y, rfl⟩ := mk_surjective (n + 1) p
  rw [mk_mem_range_inclusion_iff]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨m, hm, j, hj⟩
    obtain ⟨i, rfl, hji⟩ := exists_openCell_cwComplex_eq j
    rw [hji, mk_mem_openCell_iff] at hj
    have hi : (i : ℕ) < n + 1 := by norm_cast at hm; omega
    exact hj.2 _ (Fin.lt_def.2 (by rw [Fin.val_last]; exact hi))
  · intro hy
    obtain ⟨i, hi, hyi⟩ := exists_lt_mk_mem_openCell y (k := n + 1) fun j hj ↦ by
      rwa [eq_last_of_le n j hj]
    obtain ⟨j, hj⟩ := exists_openCell_cwComplex_eq_openCell i
    exact ⟨2 * i, by norm_cast; omega, j, hj ▸ hyi⟩

end TauCeti.ComplexProjectiveSpace
