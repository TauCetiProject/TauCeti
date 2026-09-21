/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.Index
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Adjoints of Fredholm operators

This file proves the closed-range theorem for adjoints on Hilbert spaces and applies it to
Fredholm operators. If a continuous linear map has closed range, then its adjoint has range
equal to the orthogonal complement of the original kernel. Consequently, taking adjoints
preserves Fredholm operators and negates their index.

The proof restricts an operator with closed range to a continuous linear equivalence from the
orthogonal complement of its kernel onto its range. The adjoint of this equivalence is
surjective, which removes the closure from Mathlib's general identity
`T.orthogonal_ker : T.kerᗮ = T†.range.topologicalClosure`.

## Main declarations

* `ContinuousLinearMap.orthogonalKerEquivRange`: the restriction of a closed-range
  operator to the orthogonal complement of its kernel.
* `ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range`: the
  closed-range theorem for adjoints.
* `ContinuousLinearMap.isClosed_range_adjoint_iff`: an operator has closed range if and
  only if its adjoint does.
* `ContinuousLinearMap.IsFredholm.adjoint`: the adjoint of a Fredholm operator is Fredholm.
* `ContinuousLinearMap.index_adjoint`: taking the adjoint negates the Fredholm index.

The argument and index convention follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

open Module
open scoped InnerProduct

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F]

section

section Restriction

variable [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The restriction of a closed-range operator to the orthogonal complement of its kernel is a
continuous linear equivalence onto its range. -/
noncomputable def _root_.ContinuousLinearMap.orthogonalKerEquivRange (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ ≃L[𝕜]
      LinearMap.range (T : E →ₗ[𝕜] F) := by
  let K := LinearMap.ker (T : E →ₗ[𝕜] F)
  let R := LinearMap.range (T : E →ₗ[𝕜] F)
  letI : CompleteSpace Kᗮ := K.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace R := hT.completeSpace_coe
  exact (LinearMap.kerComplementEquivRange (T : E →ₗ[𝕜] F)
    K.isCompl_orthogonal.symm).toContinuousLinearEquivOfContinuous
      ((T.continuous.comp continuous_subtype_val).subtype_mk _)

/-- The closed-range restriction equivalence acts by the original operator. -/
@[simp]
theorem _root_.ContinuousLinearMap.orthogonalKerEquivRange_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (x : (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ) : (ContinuousLinearMap.orthogonalKerEquivRange T hT x :
      F) = T x := by
  let : CompleteSpace (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ :=
    (LinearMap.ker (T : E →ₗ[𝕜] F)).isClosed_orthogonal.completeSpace_coe
  let : CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] F)) :=
    hT.completeSpace_coe
  let e := LinearMap.kerComplementEquivRange (T : E →ₗ[𝕜] F)
    (LinearMap.ker (T : E →ₗ[𝕜] F)).isCompl_orthogonal.symm
  let he : Continuous e :=
    (T.continuous.comp continuous_subtype_val).subtype_mk _
  -- Expose the `LinearEquiv` underlying the continuous wrapper so its application lemma applies.
  change ((e.toContinuousLinearEquivOfContinuous he x :
    LinearMap.range (T : E →ₗ[𝕜] F)) : F) = T x
  rw [LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous]
  exact LinearMap.kerComplementEquivRange_apply_coe _ _ x

/-- Applying a closed-range operator to the inverse of its orthogonal-kernel restriction
recovers the given range element. -/
@[simp]
theorem _root_.ContinuousLinearMap.orthogonalKerEquivRange_symm_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (y : LinearMap.range (T : E →ₗ[𝕜] F)) :
    T ((ContinuousLinearMap.orthogonalKerEquivRange T hT).symm y) = (y : F) :=
  (ContinuousLinearMap.orthogonalKerEquivRange_apply T hT _).symm.trans <|
    congr_arg Subtype.val ((ContinuousLinearMap.orthogonalKerEquivRange T hT).apply_symm_apply y)

end Restriction

end

section HilbertCodomain

variable [InnerProductSpace 𝕜 F] [CompleteSpace F]


/-- The adjoint of a continuous linear equivalence is bijective. -/
private theorem _root_.ContinuousLinearMap.adjoint_bijective (e : E ≃L[𝕜] F) :
    Function.Bijective ((e : E →L[𝕜] F)†) := by
  let A : F →L[𝕜] E := ((e : E →L[𝕜] F)†)
  let B : E →L[𝕜] F := ((e.symm : F →L[𝕜] E)†)
  have hBA : B.comp A = ContinuousLinearMap.id 𝕜 F := by
    rw [← ContinuousLinearMap.adjoint_comp]
    have he : (e : E →L[𝕜] F).comp (e.symm : F →L[𝕜] E) =
        ContinuousLinearMap.id 𝕜 F := by
      ext x
      simp
    rw [he, ContinuousLinearMap.adjoint_id]
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 E := by
    rw [← ContinuousLinearMap.adjoint_comp]
    rw [e.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id]
  -- Fold the displayed adjoint back to the local name used for the inverse identities.
  change Function.Bijective A
  constructor
  · intro x y hxy
    apply_fun B at hxy
    simpa only [← ContinuousLinearMap.comp_apply, hBA, ContinuousLinearMap.id_apply] using hxy
  · intro x
    refine ⟨B x, ?_⟩
    simp only [← ContinuousLinearMap.comp_apply, hAB, ContinuousLinearMap.id_apply]

/-- The adjoint maps into the orthogonal complement of the kernel. Mathlib's
`ContinuousLinearMap.orthogonal_ker` identifies `(ker T)ᗮ` with the *closure* of the adjoint's
range, and the range is contained in its closure. -/
private theorem _root_.ContinuousLinearMap.adjoint_mem_orthogonal_ker (T : E →L[𝕜] F) (y : F) :
    (T†) y ∈ (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ := by
  rw [T.orthogonal_ker]
  exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ y)

/-- The adjoint of `T`, restricted to the range of `T` and corestricted to `(ker T)ᗮ`, is
surjective: it *is* the adjoint of the isomorphism `(ker T)ᗮ ≃L range T`, and the adjoint of an
isomorphism is bijective. -/
private theorem _root_.ContinuousLinearMap.codRestrict_domRestrict_adjoint_surjective
    (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    Function.Surjective
      (((T†).domRestrict (LinearMap.range (T : E →ₗ[𝕜] F))).codRestrict
        (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ fun y => ContinuousLinearMap.adjoint_mem_orthogonal_ker T
          y) := by
  set K := LinearMap.ker (T : E →ₗ[𝕜] F) with hK
  set R := LinearMap.range (T : E →ₗ[𝕜] F) with hR
  set e : Kᗮ ≃L[𝕜] R := ContinuousLinearMap.orthogonalKerEquivRange T hT with he
  have he_apply (x : Kᗮ) : (e x : F) = T (x : E) := by
    simpa only [he] using ContinuousLinearMap.orthogonalKerEquivRange_apply T hT x
  -- Peeling both restriction wrappers off the corestricted adjoint, once and by name.
  have hcoe (y : R) :
      ((((T†).domRestrict R).codRestrict Kᗮ
          (fun y => ContinuousLinearMap.adjoint_mem_orthogonal_ker T y)) y : E)
        = (T†) (y : F) :=
    (ContinuousLinearMap.coe_codRestrict_apply _ _ _ y).trans
      (congrFun (ContinuousLinearMap.coe_domRestrict (T†) R) y)
  have hB : ((T†).domRestrict R).codRestrict Kᗮ
    (fun y => ContinuousLinearMap.adjoint_mem_orthogonal_ker T y)
      = ((e : Kᗮ →L[𝕜] R)†) :=
    (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun y x => by
      rw [Submodule.coe_inner, hcoe, Submodule.coe_inner, T.adjoint_inner_left,
        ContinuousLinearEquiv.coe_coe, he_apply]
  rw [hB]
  exact (ContinuousLinearMap.adjoint_bijective e).2

/-- A continuous linear map with closed range has adjoint range equal to the orthogonal
complement of its kernel. -/
theorem _root_.ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    LinearMap.range (T† : F →ₗ[𝕜] E) =
      (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    exact ContinuousLinearMap.adjoint_mem_orthogonal_ker T y
  · obtain ⟨y, hy⟩ := ContinuousLinearMap.codRestrict_domRestrict_adjoint_surjective T hT ⟨x, hx⟩
    exact ⟨(y : F), congr_arg Subtype.val hy⟩

/-- If a continuous linear map between Hilbert spaces has closed range, then so does its
adjoint. -/
theorem _root_.ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    IsClosed (LinearMap.range (T† : F →ₗ[𝕜] E) : Set E) := by
  rw [ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range T hT]
  exact (LinearMap.ker (T : E →ₗ[𝕜] F)).isClosed_orthogonal

/-- A continuous linear map between Hilbert spaces has closed range if and only if its adjoint
does. -/
@[simp]
theorem _root_.ContinuousLinearMap.isClosed_range_adjoint_iff (T : E →L[𝕜] F) :
    IsClosed (LinearMap.range (T† : F →ₗ[𝕜] E) : Set E) ↔
      IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F) := by
  constructor
  · intro hT
    simpa using ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range (T†) hT
  · exact ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range T



/-- The cokernel of a closed-range operator is continuously linearly equivalent to the kernel of
its adjoint. -/
noncomputable def _root_.ContinuousLinearMap.cokerEquivKerAdjoint (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) ≃L[𝕜]
      LinearMap.ker (T† : F →ₗ[𝕜] E) := by
  let range := LinearMap.range (T : E →ₗ[𝕜] F)
  letI : CompleteSpace range := hT.completeSpace_coe
  exact range.quotientEquivOrthogonal.toContinuousLinearEquiv.trans
    (LinearIsometryEquiv.ofEq _ _ T.orthogonal_range).toContinuousLinearEquiv

/-- On quotient representatives, the cokernel--adjoint-kernel equivalence is orthogonal
projection onto the orthogonal complement of the range. -/
@[simp]
theorem _root_.ContinuousLinearMap.coe_cokerEquivKerAdjoint_apply_mk (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) (y : F) :
    (ContinuousLinearMap.cokerEquivKerAdjoint T hT (Submodule.Quotient.mk y) : F) =
      ((LinearMap.range (T : E →ₗ[𝕜] F))ᗮ.orthogonalProjectionOnto y : F) := by
  simp [ContinuousLinearMap.cokerEquivKerAdjoint,
    Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto]

/-- The inverse cokernel--adjoint-kernel equivalence sends a kernel vector to its quotient
class. -/
@[simp]
theorem _root_.ContinuousLinearMap.cokerEquivKerAdjoint_symm_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) (y : LinearMap.ker (T† : F →ₗ[𝕜] E)) :
    (ContinuousLinearMap.cokerEquivKerAdjoint T hT).symm y = Submodule.Quotient.mk (y : F) := by
  let range := LinearMap.range (T : E →ₗ[𝕜] F)
  let : CompleteSpace range := hT.completeSpace_coe
  simp [ContinuousLinearMap.cokerEquivKerAdjoint]

/-- The cokernel of the adjoint of a closed-range operator is continuously linearly equivalent to
the original kernel. -/
noncomputable def _root_.ContinuousLinearMap.cokerAdjointEquivKer (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    (E ⧸ LinearMap.range (T† : F →ₗ[𝕜] E)) ≃L[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] F) :=
  (ContinuousLinearMap.cokerEquivKerAdjoint (T†)
      (ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range T hT)).trans
    (LinearIsometryEquiv.ofEq _ _ <| by simp).toContinuousLinearEquiv

/-- On quotient representatives, the adjoint-cokernel--kernel equivalence is orthogonal
projection onto the orthogonal complement of the adjoint range. -/
@[simp]
theorem _root_.ContinuousLinearMap.coe_cokerAdjointEquivKer_apply_mk (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) (x : E) :
    (ContinuousLinearMap.cokerAdjointEquivKer T hT (Submodule.Quotient.mk x) : E) =
      ((LinearMap.range (T† : F →ₗ[𝕜] E))ᗮ.orthogonalProjectionOnto x : E) := by
  simp [ContinuousLinearMap.cokerAdjointEquivKer,
    ContinuousLinearMap.coe_cokerEquivKerAdjoint_apply_mk]

/-- The inverse adjoint-cokernel--kernel equivalence sends a kernel vector to its quotient
class. -/
@[simp]
theorem _root_.ContinuousLinearMap.cokerAdjointEquivKer_symm_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) (x : LinearMap.ker (T : E →ₗ[𝕜] F)) :
    (ContinuousLinearMap.cokerAdjointEquivKer T hT).symm x = Submodule.Quotient.mk (x : E) := by
  simp [ContinuousLinearMap.cokerAdjointEquivKer]


/-- The adjoint of a Fredholm operator between Hilbert spaces is Fredholm. -/
theorem _root_.ContinuousLinearMap.IsFredholm.adjoint {T : E →L[𝕜] F}
    (hT : ContinuousLinearMap.IsFredholm T) :
    ContinuousLinearMap.IsFredholm (T†) := by
  have := hT.finite_coker
  have := hT.finite_ker
  apply ContinuousLinearMap.IsFredholm.of_finite_ker_coker
  · exact (ContinuousLinearMap.cokerEquivKerAdjoint T
      hT.isClosed_range).toLinearEquiv.finiteDimensional
  · exact (ContinuousLinearMap.cokerAdjointEquivKer T
      hT.isClosed_range).symm.toLinearEquiv.finiteDimensional

/-- A continuous linear map between Hilbert spaces is Fredholm if and only if its adjoint is
Fredholm. -/
@[simp]
theorem isFredholm_adjoint_iff (T : E →L[𝕜] F) :
    ContinuousLinearMap.IsFredholm (T†) ↔ ContinuousLinearMap.IsFredholm T := by
  constructor
  · intro hT
    simpa using hT.adjoint
  · exact ContinuousLinearMap.IsFredholm.adjoint


/-- Taking the adjoint of a Fredholm operator negates its index. -/
@[simp]
theorem _root_.ContinuousLinearMap.index_adjoint (T : E →L[𝕜] F)
    (hT : ContinuousLinearMap.IsFredholm T) :
    ContinuousLinearMap.index (T†) = -ContinuousLinearMap.index T := by
  rw [ContinuousLinearMap.index_eq_finrank_sub, ContinuousLinearMap.index_eq_finrank_sub,
    ← LinearEquiv.finrank_eq
      (ContinuousLinearMap.cokerEquivKerAdjoint T hT.isClosed_range).toLinearEquiv,
    LinearEquiv.finrank_eq
      (ContinuousLinearMap.cokerAdjointEquivKer T hT.isClosed_range).toLinearEquiv]
  omega


end HilbertCodomain

end TauCeti

end
