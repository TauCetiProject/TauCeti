/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transitivity
public import Mathlib.GroupTheory.GroupAction.Primitive
public import TauCeti.LinearAlgebra.Matrix.Nondegenerate
public import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# The symplectic group acts primitively on projective space

Let `ω(x, y) = xᵀ J y` be the standard alternating form on `V = Fin (m + m) → K` over a field `K`.
The standard symplectic group `Sp_{2m}(K)` (`TauCeti.GLSymplecticFin m K`) acts on the projective
space `ℙ K V`. This file proves that the action is primitive; transitivity is the instance in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transitivity`.

Unlike the special linear group, `Sp_{2m}(K)` is not doubly transitive on `ℙ K V` once `m ≥ 2`: it
preserves the relation `ω(x, y) = 0` between points. The stabilizer of a point `⟨u⟩` has two orbits
on the other points, the points `⟨x⟩ ≠ ⟨u⟩` with `ω(u, x) = 0` and those with `ω(u, x) ≠ 0`. Both
orbits are reached by symplectic transvections fixing `u`: if `ω(u, x) = ω(u, y)` and
`ω(y, x) ≠ 0`, then the transvection along `y - x` with parameter `ω(y, x)⁻¹` fixes `u` and sends
`x` to `y`, and two such steps connect any two vectors `x, y` off the line of `u` with
`ω(u, x) = ω(u, y)`
(`TauCeti.GLSymplecticFin.exists_smul_eq_self_and_smul_eq_of_dotProduct_JFin_mulVec_eq`).

A block containing `⟨u⟩` and another point is therefore a union of `⟨u⟩` with whole orbits of the
stabilizer. If it contains the points not orthogonal to `⟨u⟩`, it also contains a point orthogonal
to `⟨u⟩` but not to one of those, and conversely; either way it contains both orbits, so it is the
whole space. The argument covers every rank, including `m = 1`, where no point other than `⟨u⟩` is
orthogonal to it.

Primitivity, through `MulAction.IsPreprimitive.isQuasiPreprimitive`, is the quasiprimitivity input
of Iwasawa's simplicity criterion `MulAction.IwasawaStructure.isSimpleGroup` for the projective
symplectic group.

## Main results

* `TauCeti.GLSymplecticFin.exists_smul_eq_self_and_smul_eq_of_dotProduct_JFin_mulVec_eq`: the
  stabilizer of a vector `u` moves `x` to `y` whenever both lie off the line of `u` and
  `ω(u, x) = ω(u, y)`.
* `TauCeti.GLSymplecticFin.isPreprimitive`: `Sp_{2m}(K)` acts primitively on `ℙ K V`.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, §§4--6.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8.
-/

public section

open Matrix MulAction
open scoped LinearAlgebra.Projectivization Pointwise

namespace TauCeti.GLSymplecticFin

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- **One transvection step.** If `ω(y, x) ≠ 0` and `ω(u, x) = ω(u, y)`, the transvection along
`y - x` with parameter `ω(y, x)⁻¹` fixes `u` and sends `x` to `y`. -/
private theorem exists_smul_eq_self_and_smul_eq_of_ne_zero {u x y : Fin (m + m) → K}
    (h : u ⬝ᵥ (JFin m K *ᵥ x) = u ⬝ᵥ (JFin m K *ᵥ y)) (hyx : y ⬝ᵥ (JFin m K *ᵥ x) ≠ 0) :
    ∃ g : GLSymplecticFin m K, g • u = u ∧ g • x = y := by
  refine ⟨symplecticTransvection (y - x) (y ⬝ᵥ (JFin m K *ᵥ x))⁻¹, ?_, ?_⟩ <;>
    rw [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec]
  · rw [coe_symplecticTransvection_mulVec]
    simp [sub_dotProduct, dotProduct_JFin_mulVec_eq_neg u x, dotProduct_JFin_mulVec_eq_neg u y, h]
  · exact coe_symplecticTransvection_sub_mulVec hyx

/-- **The stabilizer of a vector `u` is transitive on each level set of `ω(u, ·)` off the line of
`u`.** If neither `x` nor `y` is a multiple of `u` and `ω(u, x) = ω(u, y)`, a product of at most
two symplectic transvections fixes `u` and sends `x` to `y`. For `u = 0` this is the transitivity
of `Sp_{2m}(K)` on nonzero vectors. -/
theorem exists_smul_eq_self_and_smul_eq_of_dotProduct_JFin_mulVec_eq {u x y : Fin (m + m) → K}
    (hx : x ∉ K ∙ u) (hy : y ∉ K ∙ u) (h : u ⬝ᵥ (JFin m K *ᵥ x) = u ⬝ᵥ (JFin m K *ᵥ y)) :
    ∃ g : GLSymplecticFin m K, g • u = u ∧ g • x = y := by
  by_cases hyx : y ⬝ᵥ (JFin m K *ᵥ x) = 0
  swap
  · exact exists_smul_eq_self_and_smul_eq_of_ne_zero h hyx
  -- Pass through `z = x + w` with `ω(u, w) = 0` and `w` orthogonal to neither `x` nor `y`.
  obtain ⟨w, hwu, hwx, hwy⟩ : ∃ w, u ⬝ᵥ (JFin m K *ᵥ w) = 0 ∧ x ⬝ᵥ (JFin m K *ᵥ w) ≠ 0 ∧
      y ⬝ᵥ (JFin m K *ᵥ w) ≠ 0 := by
    obtain ⟨w₁, hw₁u, hw₁x⟩ :=
      nondegenerate_JFin.separatingLeft.exists_ortho_and_not_ortho_of_notMem_span hx
    obtain ⟨w₂, hw₂u, hw₂y⟩ :=
      nondegenerate_JFin.separatingLeft.exists_ortho_and_not_ortho_of_notMem_span hy
    by_cases h₁ : y ⬝ᵥ (JFin m K *ᵥ w₁) = 0
    · by_cases h₂ : x ⬝ᵥ (JFin m K *ᵥ w₂) = 0
      · exact ⟨w₁ + w₂, by simp [mulVec_add, hw₁u, hw₂u], by simp [mulVec_add, h₂, hw₁x],
          by simp [mulVec_add, h₁, hw₂y]⟩
      · exact ⟨w₂, hw₂u, h₂, hw₂y⟩
    · exact ⟨w₁, hw₁u, hw₁x, h₁⟩
  have hz : u ⬝ᵥ (JFin m K *ᵥ x) = u ⬝ᵥ (JFin m K *ᵥ (x + w)) := by simp [mulVec_add, hwu]
  obtain ⟨g₁, hg₁u, hg₁x⟩ := exists_smul_eq_self_and_smul_eq_of_ne_zero hz (by
    simpa [add_dotProduct, dotProduct_JFin_mulVec_eq_neg x w] using hwx)
  obtain ⟨g₂, hg₂u, hg₂z⟩ := exists_smul_eq_self_and_smul_eq_of_ne_zero (hz.symm.trans h) (by
    simpa [mulVec_add, hyx] using hwy)
  exact ⟨g₂ * g₁, by rw [mul_smul, hg₁u, hg₂u], by rw [mul_smul, hg₁x, hg₂z]⟩

/-- A vector off the line of `u` is nonzero. -/
private theorem ne_zero_of_notMem_span {u x : Fin (m + m) → K} (hx : x ∉ K ∙ u) : x ≠ 0 :=
  (ne_of_mem_of_not_mem (Submodule.zero_mem _) hx).symm

/-- A vector `z` not orthogonal to `u` is not a multiple of a vector `a` orthogonal to `u`. -/
private theorem notMem_span_of_dotProduct_JFin_mulVec {u a z : Fin (m + m) → K}
    (ha : u ⬝ᵥ (JFin m K *ᵥ a) = 0) (hz : u ⬝ᵥ (JFin m K *ᵥ z) ≠ 0) : z ∉ K ∙ a := fun hza ↦ by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hza
  simp [mulVec_smul, ha] at hz

/-- **A block contains each orbit of a point stabilizer that it meets.** If a block contains `⟨u⟩`
and another point `⟨x⟩`, it contains every point `⟨y⟩ ≠ ⟨u⟩` with `ω(u, y)` vanishing exactly when
`ω(u, x)` does. -/
private theorem mk_mem_of_isBlock {B : Set (ℙ K (Fin (m + m) → K))}
    (hB : IsBlock (GLSymplecticFin m K) B) {u x y : Fin (m + m) → K} (hu : u ≠ 0)
    (hx : x ∉ K ∙ u) (hy : y ∉ K ∙ u) (huB : Projectivization.mk K u hu ∈ B)
    (hxB : Projectivization.mk K x (ne_zero_of_notMem_span hx) ∈ B)
    (h : u ⬝ᵥ (JFin m K *ᵥ x) = 0 ↔ u ⬝ᵥ (JFin m K *ᵥ y) = 0) :
    Projectivization.mk K y (ne_zero_of_notMem_span hy) ∈ B := by
  -- Rescale `y` to a vector `a • y` on the same level set of `ω(u, ·)` as `x`.
  obtain ⟨a, ha, hay⟩ : ∃ a : K, a ≠ 0 ∧ u ⬝ᵥ (JFin m K *ᵥ x) = u ⬝ᵥ (JFin m K *ᵥ (a • y)) := by
    by_cases hy₀ : u ⬝ᵥ (JFin m K *ᵥ y) = 0
    · exact ⟨1, one_ne_zero, by rw [one_smul, hy₀, h.mpr hy₀]⟩
    · have hx₀ : u ⬝ᵥ (JFin m K *ᵥ x) ≠ 0 := fun hx₀ ↦ hy₀ (h.mp hx₀)
      refine ⟨u ⬝ᵥ (JFin m K *ᵥ x) / u ⬝ᵥ (JFin m K *ᵥ y), div_ne_zero hx₀ hy₀, ?_⟩
      rw [mulVec_smul, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hy₀]
  have hay' : a • y ∉ K ∙ u := (Submodule.smul_mem_iff _ ha).not.mpr hy
  obtain ⟨g, hgu, hgx⟩ := exists_smul_eq_self_and_smul_eq_of_dotProduct_JFin_mulVec_eq hx hay' hay
  rw [Subgroup.smul_def] at hgu hgx
  have hgB : g • B = B := hB.smul_eq_of_mem huB (by
    simpa only [Subgroup.smul_def, Projectivization.smul_mk, hgu] using huB)
  have hmk : Projectivization.mk K y (ne_zero_of_notMem_span hy) =
      g • Projectivization.mk K x (ne_zero_of_notMem_span hx) := by
    rw [Subgroup.smul_def, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    exact ⟨a⁻¹, by rw [hgx, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩
  rw [hmk, ← hgB]
  exact Set.smul_mem_smul_set hxB

/-- **The symplectic group acts primitively on projective space.** A block containing two points
`⟨u⟩ ≠ ⟨x⟩` contains a point orthogonal to `⟨u⟩` and a point not orthogonal to it, hence both
orbits of the stabilizer of `⟨u⟩` on the other points, hence everything. -/
instance isPreprimitive : IsPreprimitive (GLSymplecticFin m K) (ℙ K (Fin (m + m) → K)) where
  isTrivialBlock_of_isBlock {B} hB := by
    rcases B.subsingleton_or_nontrivial with hB₁ | ⟨p, hp, q, hq, hpq⟩
    · exact Or.inl hB₁
    refine Or.inr (Set.eq_univ_of_forall fun r ↦ ?_)
    induction p using Projectivization.ind with | h u hu =>
    induction q using Projectivization.ind with | h x hx₀ =>
    induction r using Projectivization.ind with | h y hy₀ =>
    have hx : x ∉ K ∙ u := (Projectivization.mk_eq_mk_iff_mem_span hx₀ hu).not.mp (Ne.symm hpq)
    by_cases hyu : y ∈ K ∙ u
    · rwa [(Projectivization.mk_eq_mk_iff_mem_span hy₀ hu).mpr hyu]
    have hu' : u ∉ K ∙ x := (Projectivization.mk_eq_mk_iff_mem_span hu hx₀).not.mp hpq
    by_cases hux : u ⬝ᵥ (JFin m K *ᵥ x) = 0
    · -- `⟨x⟩` is orthogonal to `⟨u⟩`, so `B` contains every point orthogonal to `⟨u⟩`.
      by_cases huy : u ⬝ᵥ (JFin m K *ᵥ y) = 0
      · exact mk_mem_of_isBlock hB hu hx hyu hp hq (iff_of_true hux huy)
      -- A point `⟨s⟩` orthogonal to `⟨x⟩` but not to `⟨u⟩` lies in the block of `⟨x⟩`, which
      -- is `B`.
      obtain ⟨s, hsx, hsu⟩ :=
        nondegenerate_JFin.separatingLeft.exists_ortho_and_not_ortho_of_notMem_span hu'
      have hsB := mk_mem_of_isBlock hB hx₀ hu' (notMem_span_of_dotProduct_JFin_mulVec hux hsu) hq
        hp (iff_of_true (by simp [dotProduct_JFin_mulVec_eq_neg u x, hux]) hsx)
      exact mk_mem_of_isBlock hB hu
        (notMem_span_of_dotProduct_JFin_mulVec (dotProduct_JFin_mulVec_self u) hsu) hyu hp hsB
        (iff_of_false hsu huy)
    · -- `⟨x⟩` is not orthogonal to `⟨u⟩`, so `B` contains every point not orthogonal to `⟨u⟩`.
      by_cases huy : u ⬝ᵥ (JFin m K *ᵥ y) = 0
      swap
      · exact mk_mem_of_isBlock hB hu hx hyu hp hq (iff_of_false hux huy)
      have hxu : x ⬝ᵥ (JFin m K *ᵥ u) ≠ 0 := by
        rwa [dotProduct_JFin_mulVec_eq_neg, neg_ne_zero]
      -- If `⟨y⟩` is not orthogonal to `⟨x⟩`, it lies in the block of `⟨x⟩`, which is `B`.
      have hyx : ∀ z, u ⬝ᵥ (JFin m K *ᵥ z) = 0 → z ∉ K ∙ u → z ∉ K ∙ x := fun z hz hzu hzx ↦ by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzx
        obtain rfl : c = 0 := by simpa [mulVec_smul, hux] using hz
        simp at hzu
      by_cases hxy : x ⬝ᵥ (JFin m K *ᵥ y) = 0
      swap
      · exact mk_mem_of_isBlock hB hx₀ hu' (hyx y huy hyu) hq hp (iff_of_false hxu hxy)
      -- Otherwise `⟨y + u⟩` is orthogonal to `⟨u⟩` but not to `⟨x⟩`: it lies in `B`, and `⟨y⟩` is
      -- in the same orbit of the stabilizer of `⟨u⟩`.
      have hsu : u ⬝ᵥ (JFin m K *ᵥ (y + u)) = 0 := by simp [mulVec_add, huy]
      have hs : y + u ∉ K ∙ u := fun hs ↦
        hyu (by simpa using Submodule.sub_mem _ hs (Submodule.mem_span_singleton_self u))
      have hsB := mk_mem_of_isBlock hB hx₀ hu' (hyx _ hsu hs) hq hp (iff_of_false hxu (by
        simpa [mulVec_add, hxy] using hxu))
      exact mk_mem_of_isBlock hB hu hs hyu hp hsB (iff_of_true hsu huy)

end TauCeti.GLSymplecticFin
