/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Basic

/-!
# The inclusion `CPⁿ ⊆ CPⁿ⁺¹`

Appending a zero last coordinate is a linear isometry `ℂⁿ⁺¹ → ℂⁿ⁺²`
(`TauCeti.ComplexProjectiveSpace.appendZero`). It carries unit vectors to unit vectors and commutes
with unit complex scalars, so it descends to the sphere-quotient models of complex projective
space: the inclusion `TauCeti.ComplexProjectiveSpace.inclusion n : CPⁿ → CPⁿ⁺¹`, a closed
embedding (`TauCeti.ComplexProjectiveSpace.isClosedEmbedding_inclusion`). Its image consists of
the classes of the unit vectors whose last coordinate vanishes
(`TauCeti.ComplexProjectiveSpace.mk_mem_range_inclusion_iff`).

These inclusions are the finite-stage maps of the infinite complex projective space `CP∞`.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.appendZero`: `ℂⁿ⁺¹ → ℂⁿ⁺²`, `v ↦ (v, 0)`.
* `TauCeti.ComplexProjectiveSpace.inclusion`: the inclusion `CPⁿ → CPⁿ⁺¹`.
* `TauCeti.ComplexProjectiveSpace.mk_mem_range_inclusion_iff`: its image.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.6 (`CPⁿ⁺¹` as `CPⁿ` with a `2(n + 1)`-cell attached).
-/

public section

noncomputable section

open Metric

namespace TauCeti.ComplexProjectiveSpace

variable (n : ℕ)

/-- Appending a zero last coordinate, `ℂⁿ⁺¹ → ℂⁿ⁺²`, `v ↦ (v, 0)`, a linear isometry. -/
def appendZero : EuclideanSpace ℂ (Fin (n + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (n + 2)) where
  toFun v := WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℂ) (WithLp.ofLp v) 0)
  map_add' v w := by
    ext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
  map_smul' c v := by
    ext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
  norm_map' v := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]

@[simp]
theorem appendZero_apply_castSucc (v : EuclideanSpace ℂ (Fin (n + 1))) (i : Fin (n + 1)) :
    appendZero n v i.castSucc = v i := by
  simp [appendZero]

@[simp]
theorem appendZero_apply_last (v : EuclideanSpace ℂ (Fin (n + 1))) :
    appendZero n v (Fin.last (n + 1)) = 0 := by
  simp [appendZero]

/-- A vector of `ℂⁿ⁺²` with vanishing last coordinate is `(v, 0)` for its first coordinates `v`. -/
theorem appendZero_init {w : EuclideanSpace ℂ (Fin (n + 2))} (hw : w (Fin.last (n + 1)) = 0) :
    appendZero n (WithLp.toLp 2 fun i ↦ w i.castSucc) = w := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · rw [appendZero_apply_last, hw]
  · rw [appendZero_apply_castSucc]

/-- `appendZero` on unit vectors. -/
private def sphereAppendZero (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1 :=
  ⟨appendZero n x, by rw [mem_sphere_zero_iff_norm, LinearIsometry.norm_map,
    norm_eq_of_mem_sphere]⟩

private theorem sphereAppendZero_smul (c : sphere (0 : ℂ) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    sphereAppendZero n (c • x) = c • sphereAppendZero n x :=
  Subtype.ext (LinearIsometry.map_smul _ (c : ℂ) _)

/-- **The inclusion `CPⁿ → CPⁿ⁺¹`**, sending the class of a unit vector `x` to the class of
`(x, 0)` (`TauCeti.ComplexProjectiveSpace.inclusion_mk`). -/
def inclusion : C(ComplexProjectiveSpace n, ComplexProjectiveSpace (n + 1)) where
  toFun := ComplexProjectiveSpace.lift n (fun x ↦ mk (n + 1) (sphereAppendZero n x))
    fun c x ↦ by rw [sphereAppendZero_smul, mk_smul]
  continuous_toFun := (isOpenQuotientMap_mk n).isQuotientMap.continuous_iff.2 <|
    ((continuous_mk (n + 1)).comp <|
      ((appendZero n).continuous.comp continuous_subtypeVal).subtype_mk _).congr fun x ↦
        (ComplexProjectiveSpace.lift_mk n _ _ x).symm

/-- The inclusion `CPⁿ → CPⁿ⁺¹` sends the class of a unit vector `x` to the class of `(x, 0)`. -/
theorem inclusion_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    inclusion n (mk n x) =
      mk (n + 1) ⟨appendZero n x, by rw [mem_sphere_zero_iff_norm, LinearIsometry.norm_map,
        norm_eq_of_mem_sphere]⟩ :=
  ComplexProjectiveSpace.lift_mk n _ _ x

/-- The inclusion `CPⁿ → CPⁿ⁺¹` is injective: if `(x, 0) = c • (y, 0)` then `x = c • y`. -/
theorem inclusion_injective : Function.Injective (inclusion n) := by
  intro p q h
  induction p using ComplexProjectiveSpace.inductionOn with | h x => ?_
  induction q using ComplexProjectiveSpace.inductionOn with | h y => ?_
  rw [inclusion_mk, inclusion_mk, mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  refine (mk_eq_mk_iff n x y).2 ⟨c, Subtype.ext ((appendZero n).injective ?_)⟩
  rw [Sphere.coe_sphere_smul, LinearIsometry.map_smul]
  exact congrArg Subtype.val hc

/-- The inclusion `CPⁿ → CPⁿ⁺¹` is a closed embedding. -/
theorem isClosedEmbedding_inclusion : Topology.IsClosedEmbedding (inclusion n) :=
  (inclusion n).continuous.isClosedEmbedding (inclusion_injective n)

/-- **The image of `CPⁿ` in `CPⁿ⁺¹`** consists of the classes of the unit vectors whose last
coordinate vanishes. -/
theorem mk_mem_range_inclusion_iff (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) :
    mk (n + 1) y ∈ Set.range (inclusion n) ↔
      (y : EuclideanSpace ℂ (Fin (n + 2))) (Fin.last (n + 1)) = 0 := by
  constructor
  · rintro ⟨p, hp⟩
    induction p using ComplexProjectiveSpace.inductionOn with | h x => ?_
    rw [inclusion_mk, eq_comm, mk_eq_mk_iff] at hp
    obtain ⟨c, rfl⟩ := hp
    simp
  · intro hy
    have hv := appendZero_init n hy
    refine ⟨mk n ⟨WithLp.toLp 2 fun i ↦ (y : EuclideanSpace ℂ (Fin (n + 2))) i.castSucc, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, ← (appendZero n).norm_map, hv, norm_eq_of_mem_sphere]
    · rw [inclusion_mk]
      exact congrArg (mk (n + 1)) (Subtype.ext hv)

end TauCeti.ComplexProjectiveSpace
