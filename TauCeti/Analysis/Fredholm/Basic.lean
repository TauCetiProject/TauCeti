/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Fredholm operators

This file introduces the analytic notion of a **Fredholm operator** between normed spaces for the
nonlinear-analysis substrate of the analytic Heegaard Floer roadmap (Lane F0, "Fredholm operators
and index theory"). A continuous linear map `T : E →L[𝕜] F` is Fredholm when its kernel is
finite dimensional, its range is closed, and its cokernel `F ⧸ range T` is finite dimensional.

The **index** of such an operator is the integer `dim ker T − dim coker T`. Mathlib already builds
the purely algebraic index of a linear map, `LinearMap.index`, together with its behaviour under
negation and nonzero scaling; this file reuses that development at the level of continuous linear
maps rather than restating it. The genuinely new, analytic content here is the Fredholm
*predicate* — in particular the closed-range condition and the finite dimensionality of the kernel
and cokernel — and the facts that continuous linear equivalences and operators between
finite-dimensional spaces are Fredholm.

## Main declarations

* `TauCeti.IsFredholm`: the Fredholm predicate on a continuous linear map.
* `TauCeti.index`: the Fredholm index `dim ker T − dim coker T`, defined via `LinearMap.index`.
* `TauCeti.index_eq_finrank_sub`: the index as `dim ker T − dim coker T`.
* `TauCeti.isFredholm_id` and `TauCeti.index_id`: the identity is Fredholm of index `0`.
* `TauCeti.ContinuousLinearEquiv.isFredholm` and `TauCeti.ContinuousLinearEquiv.index_eq_zero`: a
  continuous linear equivalence is Fredholm of index `0`.
* `TauCeti.isFredholm_of_finiteDimensional` and `TauCeti.index_eq_finrank_sub_finrank`: every
  operator between finite-dimensional spaces is Fredholm, with index `dim E − dim F`.
* `TauCeti.IsFredholm.neg`, `TauCeti.IsFredholm.smul`: Fredholmness is preserved by negation and
  by nonzero scalar multiples, with the index unchanged.
* `TauCeti.IsFredholm.comp_equiv` and `TauCeti.IsFredholm.equiv_comp`: composing with a continuous
  linear equivalence on either side preserves Fredholmness and the index.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1, where the index is `dim ker D − dim coker D`.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A continuous linear map between normed spaces is a **Fredholm operator** if its kernel is
finite dimensional, its range is closed, and its cokernel is finite dimensional.

Closedness of the range is a genuine hypothesis: over an incomplete space a finite-dimensional
cokernel need not force it. It is bundled here following the standard convention (McDuff--Salamon,
Appendix A.1). -/
structure IsFredholm (T : E →L[𝕜] F) : Prop where
  /-- The kernel of a Fredholm operator is finite dimensional. -/
  finiteDimensional_ker : FiniteDimensional 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F))
  /-- The range of a Fredholm operator is closed. -/
  isClosed_range : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)
  /-- The cokernel of a Fredholm operator is finite dimensional. -/
  finiteDimensional_coker : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F))

/-- The **index** of a continuous linear map, `dim ker T − dim coker T`, defined as the index of
the underlying linear map. For non-Fredholm operators the value is junk, matching the convention of
`LinearMap.index`. -/
@[expose] noncomputable def index (T : E →L[𝕜] F) : ℤ := (T : E →ₗ[𝕜] F).index

lemma index_def (T : E →L[𝕜] F) : index T = (T : E →ₗ[𝕜] F).index := rfl

/-- The index is `dim ker T − dim coker T`. -/
lemma index_eq_finrank_sub (T : E →L[𝕜] F) :
    index T = (finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) : ℤ) -
      finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) :=
  LinearMap.index_eq_finrank_sub

/-- The identity operator is Fredholm: its kernel is trivial and its range is everything. -/
lemma isFredholm_id : IsFredholm (ContinuousLinearMap.id 𝕜 E) where
  finiteDimensional_ker := by
    rw [ContinuousLinearMap.coe_id, LinearMap.ker_id]
    infer_instance
  isClosed_range := by
    rw [ContinuousLinearMap.coe_id, LinearMap.range_id]
    simp
  finiteDimensional_coker := by
    rw [ContinuousLinearMap.coe_id, LinearMap.range_id]
    infer_instance

/-- The identity operator has index `0`. -/
@[simp] lemma index_id : index (ContinuousLinearMap.id 𝕜 E) = 0 := by
  rw [index_def, ContinuousLinearMap.coe_id, LinearMap.index_id]

namespace ContinuousLinearEquiv

/-- The underlying linear map of a continuous linear equivalence, written with the
linear-equivalence coercion so that submodule lemmas apply. -/
private lemma coe_continuousLinearEquiv (e : E ≃L[𝕜] F) :
    ((e : E →L[𝕜] F) : E →ₗ[𝕜] F) = (e.toLinearEquiv : E →ₗ[𝕜] F) := by
  ext x; simp

/-- A continuous linear equivalence is a Fredholm operator. -/
lemma isFredholm (e : E ≃L[𝕜] F) : IsFredholm (e : E →L[𝕜] F) where
  finiteDimensional_ker := by
    rw [coe_continuousLinearEquiv, LinearEquiv.ker]
    infer_instance
  isClosed_range := by
    rw [coe_continuousLinearEquiv, LinearEquiv.range]
    simp
  finiteDimensional_coker := by
    rw [coe_continuousLinearEquiv, LinearEquiv.range]
    infer_instance

/-- A continuous linear equivalence has index `0`. -/
@[simp] lemma index_eq_zero (e : E ≃L[𝕜] F) : index (e : E →L[𝕜] F) = 0 := by
  rw [index_def]
  exact LinearEquiv.index_eq_zero

end ContinuousLinearEquiv

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Every continuous linear map between finite-dimensional spaces is Fredholm. -/
lemma isFredholm_of_finiteDimensional (T : E →L[𝕜] F) : IsFredholm T where
  finiteDimensional_ker := inferInstance
  isClosed_range := (LinearMap.range (T : E →ₗ[𝕜] F)).closed_of_finiteDimensional
  finiteDimensional_coker := inferInstance

omit [CompleteSpace 𝕜] in
/-- Between finite-dimensional spaces the index is `dim E − dim F`, for any operator. -/
lemma index_eq_finrank_sub_finrank (T : E →L[𝕜] F) :
    index T = (finrank 𝕜 E : ℤ) - finrank 𝕜 F := by
  rw [index_def, LinearMap.index_eq_of_finiteDimensional]

end FiniteDimensional

/-- The negation of a Fredholm operator is Fredholm. -/
lemma IsFredholm.neg {T : E →L[𝕜] F} (hT : IsFredholm T) : IsFredholm (-T) where
  finiteDimensional_ker := by
    rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.ker_neg]
    exact hT.finiteDimensional_ker
  isClosed_range := by
    rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.range_neg]
    exact hT.isClosed_range
  finiteDimensional_coker := by
    rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.range_neg]
    exact hT.finiteDimensional_coker

/-- The index is unchanged by negation. -/
@[simp] lemma index_neg (T : E →L[𝕜] F) : index (-T) = index T := by
  rw [index_def, index_def, ContinuousLinearMap.toLinearMap_neg, LinearMap.index_neg]

/-- A nonzero scalar multiple of a Fredholm operator is Fredholm. -/
lemma IsFredholm.smul {T : E →L[𝕜] F} (hT : IsFredholm T) {c : 𝕜} (hc : c ≠ 0) :
    IsFredholm (c • T) where
  finiteDimensional_ker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.ker_smul _ _ hc]
    exact hT.finiteDimensional_ker
  isClosed_range := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ hc]
    exact hT.isClosed_range
  finiteDimensional_coker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ hc]
    exact hT.finiteDimensional_coker

/-- The index is unchanged by a nonzero scalar multiple. -/
lemma index_smul (T : E →L[𝕜] F) {c : 𝕜} (hc : c ≠ 0) : index (c • T) = index T := by
  rw [index_def, index_def, ContinuousLinearMap.toLinearMap_smul, LinearMap.index_smul _ hc]

section CompEquiv

variable {T : E →L[𝕜] F}

/-- The underlying linear map of `e.comp T`, for a continuous linear equivalence `e`, written with
the linear-equivalence coercion so that submodule and quotient lemmas apply. -/
private lemma coe_comp_equiv (e : F ≃L[𝕜] G) :
    (((e : F →L[𝕜] G).comp T : E →L[𝕜] G) : E →ₗ[𝕜] G) =
      (e.toLinearEquiv : F →ₗ[𝕜] G).comp (T : E →ₗ[𝕜] F) := by
  ext x; simp

/-- The underlying linear map of `T.comp e`, for a continuous linear equivalence `e`. -/
private lemma coe_equiv_comp (e : G ≃L[𝕜] E) :
    ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      (T : E →ₗ[𝕜] F).comp (e.toLinearEquiv : G →ₗ[𝕜] E) := by
  ext x; simp

/-- Postcomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator. -/
lemma IsFredholm.comp_equiv (hT : IsFredholm T) (e : F ≃L[𝕜] G) :
    IsFredholm ((e : F →L[𝕜] G).comp T) := by
  haveI := hT.finiteDimensional_ker
  haveI := hT.finiteDimensional_coker
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_comp_equiv, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 e.toLinearEquiv.injective)]
    exact hT.finiteDimensional_ker
  · rw [coe_comp_equiv, LinearMap.range_comp]
    simpa [Submodule.map_coe] using e.isClosed_image.2 hT.isClosed_range
  · rw [coe_comp_equiv, LinearMap.range_comp]
    exact (Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl).finiteDimensional

/-- Postcomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_comp_equiv (e : F ≃L[𝕜] G) :
    index ((e : F →L[𝕜] G).comp T) = index T := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, coe_comp_equiv]
  congr 1
  · congr 1
    rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 e.toLinearEquiv.injective)]
  · congr 1
    rw [LinearMap.range_comp]
    exact (LinearEquiv.finrank_eq
      (Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl)).symm

/-- Precomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator. -/
lemma IsFredholm.equiv_comp (hT : IsFredholm T) (e : G ≃L[𝕜] E) :
    IsFredholm (T.comp (e : G →L[𝕜] E)) := by
  haveI := hT.finiteDimensional_ker
  haveI := hT.finiteDimensional_coker
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_equiv_comp, LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm]
    exact (e.toLinearEquiv.symm.submoduleMap _).finiteDimensional
  · rw [coe_equiv_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 e.toLinearEquiv.surjective)]
    exact hT.isClosed_range
  · rw [coe_equiv_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 e.toLinearEquiv.surjective)]
    exact hT.finiteDimensional_coker

/-- Precomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_equiv_comp (e : G ≃L[𝕜] E) :
    index (T.comp (e : G →L[𝕜] E)) = index T := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, coe_equiv_comp]
  congr 1
  · congr 1
    rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  · congr 1
    rw [LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 e.toLinearEquiv.surjective)]

end CompEquiv

end TauCeti
