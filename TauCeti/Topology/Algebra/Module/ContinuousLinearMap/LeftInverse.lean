/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Left inverses for triangular operators

An operator on a product which retains the first coordinate admits a continuous linear
left inverse exactly when its restriction to the second factor does. This is the linear
algebra of the differential of a parameter-preserving family of immersions.

The construction uses Mathlib's `ContinuousLinearMap.HasLeftInverse`: subtract the
contribution of the first coordinate, then apply a left inverse on the second factor.

Given an operator `L : E →L[R] F` and an auxiliary operator `P : F →L[R] Y` with `P ∘ L`
invertible, `ContinuousLinearMap.leftInverseAlong L P = (P ∘ L)⁻¹ P` is the left inverse of `L`
along `ker P`: its kernel is `ker P` (`ContinuousLinearMap.ker_leftInverseAlong`), it is the only
continuous left inverse of `L` vanishing on `ker P` (`ContinuousLinearMap.eq_leftInverseAlong`),
and as a linear map it is Mathlib's `LinearMap.linearProjOfIsCompl`
(`ContinuousLinearMap.toLinearMap_leftInverseAlong`). Moreover `ker P` is a topological complement
of the range of `L` (`ContinuousLinearMap.isTopCompl_range_ker_of_isInvertible_comp`), and
`1 - L (P ∘ L)⁻¹ P` is the projection onto `ker P` along that range
(`ContinuousLinearMap.id_sub_comp_leftInverseAlong_eq_projectionL`). The Banach-space and
parameter-family theory of this construction is in
`TauCeti.Analysis.Normed.Operator.Splitting.RangeComplement`.

A continuous linear injection of a space into a finite-dimensional space of strictly larger
dimension over a complete field has a continuous left inverse and a nonzero continuous covector
annihilating its range (`ContinuousLinearMap.exists_leftInverse_ne_zero_comp_eq_zero`).

A space with a continuous linear map into a complete space that has a continuous linear left
inverse is complete (`ContinuousLinearMap.HasLeftInverse.completeSpace`), as a retract of a
complete space; this needs uniform additive groups, but no separation and no norm.
-/

public section

namespace ContinuousLinearMap

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G] [IsTopologicalAddGroup G]

/-- A continuous linear operator retaining the first coordinate is split-injective
exactly when its restriction to the second factor is split-injective. -/
theorem hasLeftInverse_fst_prod_iff (A : E × F →L[R] G) :
    ((fst R E F).prod A).HasLeftInverse ↔ (A.comp (inr R E F)).HasLeftInverse := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨snd R E F ∘L L ∘L inr R E G, fun y => by simpa using congrArg Prod.snd (hL (0, y))⟩
  · rintro ⟨L, hL⟩
    refine ⟨(fst R E G).prod (L ∘L (snd R E G - A ∘L inl R E F ∘L fst R E G)), ?_⟩
    rintro ⟨x, y⟩
    have hA : A (x, y) = A (x, 0) + A (0, y) := by rw [← map_add]; simp
    simpa [hA] using hL y

section Uniform

variable {R E F : Type*} [Semiring R]
  [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E] [Module R E]
  [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F] [Module R F]

/-- The source of a continuous linear map between uniform additive groups which has a continuous
linear left inverse is complete when the target is. -/
theorem HasLeftInverse.completeSpace [CompleteSpace F] {L : E →L[R] F} (hL : L.HasLeftInverse) :
    CompleteSpace E :=
  .of_comp_eq_id hL.leftInverse L hL.leftInverse_leftInverse.comp_eq_id
    hL.leftInverse.continuous L.uniformContinuous

end Uniform

section FiniteDimensional

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]

/-- A continuous linear injection of a space `F` into a finite-dimensional space `E` of strictly
larger dimension has a continuous left inverse and a nonzero continuous covector annihilating
its range. -/
theorem exists_leftInverse_ne_zero_comp_eq_zero (A : F →L[𝕜] E)
    (hA : Function.Injective A) (h : Module.finrank 𝕜 F < Module.finrank 𝕜 E) :
    ∃ (P : E →L[𝕜] F) (a : E →L[𝕜] 𝕜),
      Function.LeftInverse P A ∧ a ≠ 0 ∧ a ∘L A = 0 := by
  obtain ⟨P, hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hA
  have hlt := Submodule.lt_top_of_finrank_lt_finrank
    (s := LinearMap.range A.toLinearMap) (by rwa [LinearMap.finrank_range_of_inj hA])
  obtain ⟨a, ha, haA⟩ := (LinearMap.range A.toLinearMap).exists_le_ker_of_lt_top hlt
  refine ⟨P, a.toContinuousLinearMap, hP, fun hz ↦ ha (congrArg ContinuousLinearMap.toLinearMap hz),
    ?_⟩
  ext c
  exact haA (LinearMap.mem_range_self _ c)

end FiniteDimensional

section LeftInverseAlong

open Function

variable {R E F Y : Type*} [Ring R]
  [AddCommGroup E] [TopologicalSpace E] [Module R E]
  [AddCommGroup F] [TopologicalSpace F] [Module R F]
  [AddCommGroup Y] [TopologicalSpace Y] [Module R Y]
  {L : E →L[R] F} {P : F →L[R] Y}

/-- The left inverse `(P ∘ L)⁻¹ ∘ P` of `L` along the kernel of `P`. It is a left inverse of
`L` with kernel `ker P` whenever `P ∘ L` is invertible
(`ContinuousLinearMap.leftInverseAlong_comp_self`,
`ContinuousLinearMap.ker_leftInverseAlong`), and otherwise a junk value built from the total
inverse `ContinuousLinearMap.inverse`. -/
noncomputable def leftInverseAlong (L : E →L[R] F) (P : F →L[R] Y) : F →L[R] E :=
  (P ∘L L).inverse ∘L P

/-- The defining formula of the left inverse along `ker P`. -/
theorem leftInverseAlong_def (L : E →L[R] F) (P : F →L[R] Y) :
    leftInverseAlong L P = (P ∘L L).inverse ∘L P :=
  (rfl)

/-- The value of the left inverse along `ker P`. -/
theorem leftInverseAlong_apply (L : E →L[R] F) (P : F →L[R] Y) (f : F) :
    leftInverseAlong L P f = (P ∘L L).inverse (P f) :=
  (rfl)

/-- `(P ∘ L)⁻¹ P` is a left inverse of `L`. -/
@[simp]
theorem leftInverseAlong_comp_self (h : (P ∘L L).IsInvertible) :
    leftInverseAlong L P ∘L L = .id R E := by
  rw [leftInverseAlong_def, comp_assoc, h.inverse_comp_self]

/-- `(P ∘ L)⁻¹ P` is a left inverse of `L`. -/
@[simp]
theorem leftInverseAlong_apply_self (h : (P ∘L L).IsInvertible) (x : E) :
    leftInverseAlong L P (L x) = x := by
  simpa [leftInverseAlong_apply] using h.inverse_apply_self x

/-- The left inverse along `ker P` does not change the value of `P` after applying `L`. -/
@[simp]
theorem apply_apply_leftInverseAlong (h : (P ∘L L).IsInvertible) (f : F) :
    P (L (leftInverseAlong L P f)) = P f := by
  simpa [leftInverseAlong_apply] using h.self_apply_inverse (P f)

/-- The kernel of the left inverse along `ker P` is exactly `ker P`. -/
@[simp]
theorem ker_leftInverseAlong (h : (P ∘L L).IsInvertible) :
    (leftInverseAlong L P).ker = P.ker := by
  ext f
  simp only [LinearMap.mem_ker, coe_coe, leftInverseAlong_apply]
  exact ⟨fun hf ↦ by simpa [hf] using (h.self_apply_inverse (P f)).symm,
    fun hf ↦ by rw [hf, map_zero]⟩

/-- `f - L ((P ∘ L)⁻¹ P f)` lies in the kernel of `P`. -/
theorem sub_apply_leftInverseAlong_mem_ker (h : (P ∘L L).IsInvertible) (f : F) :
    f - L (leftInverseAlong L P f) ∈ P.ker := by
  simp [LinearMap.mem_ker, h]

/-- **Uniqueness of the left inverse along a complement.** A left inverse of `L` that vanishes on
`ker P` is `(P ∘ L)⁻¹ P`. -/
theorem eq_leftInverseAlong (h : (P ∘L L).IsInvertible) {K : F →L[R] E}
    (hKL : K ∘L L = .id R E) (hK : P.ker ≤ K.ker) : K = leftInverseAlong L P := by
  ext f
  have hw : K (f - L (leftInverseAlong L P f)) = 0 := hK (sub_apply_leftInverseAlong_mem_ker h f)
  rw [map_sub, sub_eq_zero, ← comp_apply K L, hKL, id_apply] at hw
  exact hw

/-- The left inverse along `ker P` depends on `P` only through its kernel. -/
theorem leftInverseAlong_congr {Y' : Type*} [AddCommGroup Y'] [TopologicalSpace Y'] [Module R Y']
    {P' : F →L[R] Y'} (h : (P ∘L L).IsInvertible) (h' : (P' ∘L L).IsInvertible)
    (hker : P.ker = P'.ker) : leftInverseAlong L P = leftInverseAlong L P' :=
  eq_leftInverseAlong h' (leftInverseAlong_comp_self h) (by rw [← hker, ker_leftInverseAlong h])

/-- If `P ∘ L` is invertible, the kernel of `P` is a topological complement of the range of
`L`. -/
theorem isTopCompl_range_ker_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    L.range.IsTopCompl P.ker := by
  have hrange : (L ∘L (P ∘L L).inverse).range = L.range := by
    simpa using LinearMap.range_comp_of_range_eq_top (L : E →ₗ[R] F)
      (LinearMap.range_eq_top.mpr h.inverse.surjective)
  have hleft : LeftInverse P (L ∘L (P ∘L L).inverse) := fun y ↦ by
    simpa using h.self_apply_inverse y
  exact hrange ▸ isTopCompl_range_ker_of_leftInverse _ _ hleft

/-- As a linear map, the left inverse along `ker P` is Mathlib's left inverse
`LinearMap.linearProjOfIsCompl` of the injection `L` along the complement `ker P` of its range.
`ContinuousLinearMap.leftInverseAlong` realizes it continuously by the explicit formula
`(P ∘ L)⁻¹ P`. -/
theorem toLinearMap_leftInverseAlong (h : (P ∘L L).IsInvertible) :
    (leftInverseAlong L P : F →ₗ[R] E) =
      LinearMap.linearProjOfIsCompl P.ker (L : E →ₗ[R] F)
        (Injective.of_comp (f := P) h.injective)
        (isTopCompl_range_ker_of_isInvertible_comp h).isCompl := by
  ext f
  have hf := sub_apply_leftInverseAlong_mem_ker h f
  conv_rhs => rw [← sub_add_cancel f (L (leftInverseAlong L P f))]
  rw [map_add, LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ hf, zero_add]
  exact (LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ (leftInverseAlong L P f)).symm

/-- `L (P ∘ L)⁻¹ P` is the projection onto the range of `L` along `ker P`. -/
theorem comp_leftInverseAlong_eq_projectionL (h : (P ∘L L).IsInvertible) :
    L ∘L leftInverseAlong L P =
      L.range.projectionL P.ker (isTopCompl_range_ker_of_isInvertible_comp h) := by
  have hc := isTopCompl_range_ker_of_isInvertible_comp h
  ext f
  have hrange : L.range.projectionL P.ker hc (L (leftInverseAlong L P f)) =
      L (leftInverseAlong L P f) :=
    (Submodule.projectionL_eq_self_iff hc _).mpr ⟨leftInverseAlong L P f, rfl⟩
  have hker : L.range.projectionL P.ker hc (f - L (leftInverseAlong L P f)) = 0 :=
    Submodule.projectionL_apply_eq_zero_of_mem_right hc (sub_apply_leftInverseAlong_mem_ker h f)
  rw [map_sub, hrange, sub_eq_zero] at hker
  exact hker.symm

/-- `L f + S` lies in the kernel of `P` exactly for the correction `f = -(P ∘ L)⁻¹ P S`. In
particular this correction depends on `P` only through its kernel. -/
theorem apply_add_mem_ker_iff (h : (P ∘L L).IsInvertible) {S : F} {x : E} :
    L x + S ∈ P.ker ↔ x = -leftInverseAlong L P S := by
  constructor
  · intro hx
    have hK : leftInverseAlong L P (L x + S) = 0 := by
      have hx' : L x + S ∈ (leftInverseAlong L P).ker := by rwa [ker_leftInverseAlong h]
      exact LinearMap.mem_ker.mp hx'
    rw [map_add, leftInverseAlong_apply_self h] at hK
    exact eq_neg_of_add_eq_zero_left hK
  · rintro rfl
    simp [LinearMap.mem_ker, h]

variable [IsTopologicalAddGroup F]

/-- **The projection along the range.** If `P ∘ L` is invertible, `1 - L (P ∘ L)⁻¹ P` is the
projection onto `ker P` along the range of `L`. In particular it depends on `P` only through its
kernel. -/
theorem id_sub_comp_leftInverseAlong_eq_projectionL (h : (P ∘L L).IsInvertible) :
    .id R F - L ∘L leftInverseAlong L P =
      P.ker.projectionL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm := by
  rw [comp_leftInverseAlong_eq_projectionL h, Submodule.projectionL_eq_id_sub_projectionL
    (isTopCompl_range_ker_of_isInvertible_comp h)]

/-- **The leading correction.** For `S ∈ F`, the vector `f = -(P ∘ L)⁻¹ P S` satisfies
`L f + S = Π S`, where `Π` is the projection onto `ker P` along the range of `L`. -/
theorem apply_neg_leftInverseAlong_add_eq_projectionL (h : (P ∘L L).IsInvertible) (S : F) :
    L (-leftInverseAlong L P S) + S =
      P.ker.projectionL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm S := by
  rw [← id_sub_comp_leftInverseAlong_eq_projectionL h, map_neg, sub_apply, id_apply, comp_apply]
  abel

end LeftInverseAlong

end ContinuousLinearMap
