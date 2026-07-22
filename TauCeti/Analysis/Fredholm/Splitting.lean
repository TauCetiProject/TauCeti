/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Splittings for Fredholm operators

This file proves the kernel and range splitting statements for a Fredholm operator between
Banach spaces. Over `IsRCLikeNormedField` scalars, the finite-dimensional kernel has a closed
complement by Hahn--Banach. The closed range has a closed complement because its quotient, the
cokernel, is finite-dimensional. The operator restricts to a continuous linear equivalence from
the chosen kernel complement onto its range.

These are the splittings used in the local normal form of a Fredholm map and in finite-dimensional
reduction. The complements are deliberately noncanonical; their defining properties, rather than
their chosen values, form the public API.

## Main declarations

* `TauCeti.IsFredholm.kernelClosedComplemented`: the kernel of a Fredholm operator is
  topologically complemented.
* `TauCeti.IsFredholm.rangeClosedComplemented`: the range of a Fredholm operator is
  topologically complemented.
* `TauCeti.IsFredholm.kernelComplement` and `TauCeti.IsFredholm.cokernelComplement`: chosen closed
  complements to the kernel and range.
* `TauCeti.IsFredholm.kernelComplementEquivRange`: the restriction of the operator is a continuous
  linear equivalence from the kernel complement to the range.

The argument follows the kernel/cokernel splitting in McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1. The existence of a complement to a
finite-dimensional subspace is Mathlib's Hahn--Banach theorem
`Submodule.ClosedComplemented.of_finiteDimensional`.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace IsFredholm

variable {T : E →L[𝕜] F} (hT : _root_.TauCeti.IsFredholm T)

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The kernel of a Fredholm operator is topologically complemented. -/
theorem kernelClosedComplemented (hT : _root_.TauCeti.IsFredholm T) :
    (LinearMap.ker (T : E →ₗ[𝕜] F)).ClosedComplemented := by
  letI := _root_.TauCeti.IsFredholm.finiteDimensional_ker hT
  exact Submodule.ClosedComplemented.of_finiteDimensional _

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The range of a Fredholm operator is topologically complemented. -/
theorem rangeClosedComplemented (hT : _root_.TauCeti.IsFredholm T) :
    (LinearMap.range (T : E →ₗ[𝕜] F)).ClosedComplemented := by
  letI := _root_.TauCeti.IsFredholm.finiteDimensional_coker hT
  exact Submodule.ClosedComplemented.of_finiteDimensional_quotient
    (_root_.TauCeti.IsFredholm.isClosed_range hT)

/-- A chosen closed complement to the kernel of a Fredholm operator. -/
noncomputable def kernelComplement : Submodule 𝕜 E :=
  hT.kernelClosedComplemented.complement

/-- A chosen finite-dimensional complement to the range of a Fredholm operator. It represents
the cokernel inside the codomain. -/
noncomputable def cokernelComplement : Submodule 𝕜 F :=
  hT.rangeClosedComplemented.complement

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The kernel and its chosen complement are topological complements. -/
theorem isTopCompl_kernel_kernelComplement :
    Submodule.IsTopCompl (LinearMap.ker (T : E →ₗ[𝕜] F)) hT.kernelComplement :=
  hT.kernelClosedComplemented.isTopCompl_complement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The range and its chosen complement are topological complements. -/
theorem isTopCompl_range_cokernelComplement :
    Submodule.IsTopCompl (LinearMap.range (T : E →ₗ[𝕜] F)) hT.cokernelComplement :=
  hT.rangeClosedComplemented.isTopCompl_complement

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The chosen complement to the kernel is closed. -/
theorem isClosed_kernelComplement : IsClosed (hT.kernelComplement : Set E) :=
  hT.kernelClosedComplemented.isClosed_complement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The chosen complement to the range is closed. -/
theorem isClosed_cokernelComplement : IsClosed (hT.cokernelComplement : Set F) :=
  hT.rangeClosedComplemented.isClosed_complement

/-- The codomain is continuously linearly equivalent to the product of the range and a chosen
cokernel representative. -/
noncomputable def rangeProdCokernelComplementEquiv :
    (LinearMap.range (T : E →ₗ[𝕜] F) × hT.cokernelComplement) ≃L[𝕜] F :=
  Submodule.prodEquivOfIsTopCompl _ _ hT.isTopCompl_range_cokernelComplement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem rangeProdCokernelComplementEquiv_apply
    (x : LinearMap.range (T : E →ₗ[𝕜] F) × hT.cokernelComplement) :
    hT.rangeProdCokernelComplementEquiv x = (x.1 : F) + x.2 :=
  Submodule.prodEquivOfIsTopCompl_apply hT.isTopCompl_range_cokernelComplement x

/-- The domain is continuously linearly equivalent to the product of the kernel and a chosen
kernel complement. -/
noncomputable def kernelProdComplementEquiv :
    (LinearMap.ker (T : E →ₗ[𝕜] F) × hT.kernelComplement) ≃L[𝕜] E :=
  Submodule.prodEquivOfIsTopCompl _ _ hT.isTopCompl_kernel_kernelComplement

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem kernelProdComplementEquiv_apply
    (x : LinearMap.ker (T : E →ₗ[𝕜] F) × hT.kernelComplement) :
    hT.kernelProdComplementEquiv x = (x.1 : E) + x.2 :=
  Submodule.prodEquivOfIsTopCompl_apply hT.isTopCompl_kernel_kernelComplement x

/-- The restriction of a Fredholm operator to its chosen kernel complement, with codomain
restricted to its range. -/
noncomputable def kernelComplementToRange :
    hT.kernelComplement →L[𝕜] LinearMap.range (T : E →ₗ[𝕜] F) :=
  (T.codRestrict _ (LinearMap.mem_range_self _)).domRestrict hT.kernelComplement

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem kernelComplementToRange_apply (x : hT.kernelComplement) :
    (hT.kernelComplementToRange x : F) = T x := by
  simp [kernelComplementToRange]

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
private theorem kernelComplementToRange_injective :
    Function.Injective hT.kernelComplementToRange := by
  intro x y hxy
  apply Subtype.ext
  have hker : (x : E) - y ∈ LinearMap.ker (T : E →ₗ[𝕜] F) := by
    rw [LinearMap.mem_ker, map_sub]
    rw [sub_eq_zero]
    simpa only [kernelComplementToRange_apply, ContinuousLinearMap.coe_coe] using
      congrArg Subtype.val hxy
  have hcomp : (x : E) - y ∈ hT.kernelComplement := sub_mem x.2 y.2
  have hbot : (x : E) - y ∈ (⊥ : Submodule 𝕜 E) := by
    rw [← hT.isTopCompl_kernel_kernelComplement.isCompl.disjoint.eq_bot]
    exact ⟨hker, hcomp⟩
  exact sub_eq_zero.mp (by simpa using hbot)

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
private theorem kernelComplementToRange_surjective :
    Function.Surjective hT.kernelComplementToRange := by
  intro y
  obtain ⟨x, hx⟩ := y.2
  let z := (hT.kernelProdComplementEquiv).symm x
  refine ⟨z.2, Subtype.ext ?_⟩
  have hdecomp : (z.1 : E) + z.2 = x := by
    rw [← hT.kernelProdComplementEquiv_apply]
    exact hT.kernelProdComplementEquiv.apply_symm_apply x
  calc
    (hT.kernelComplementToRange z.2 : F) = T (z.2 : E) :=
      hT.kernelComplementToRange_apply z.2
    _ = T ((z.1 : E) + z.2) := by simp
    _ = T x := congrArg T hdecomp
    _ = y := hx

/-- A Fredholm operator restricts to a continuous linear equivalence from its chosen kernel
complement onto its range. -/
noncomputable def kernelComplementEquivRange :
    hT.kernelComplement ≃L[𝕜] LinearMap.range (T : E →ₗ[𝕜] F) := by
  letI : CompleteSpace hT.kernelComplement := hT.isClosed_kernelComplement.completeSpace_coe
  letI : CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] F)) :=
    (_root_.TauCeti.IsFredholm.isClosed_range hT).completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective hT.kernelComplementToRange
    (LinearMap.ker_eq_bot.2 hT.kernelComplementToRange_injective)
    (LinearMap.range_eq_top.2 hT.kernelComplementToRange_surjective)

omit [CompleteSpace 𝕜] in
@[simp]
theorem kernelComplementEquivRange_apply (x : hT.kernelComplement) :
    (hT.kernelComplementEquivRange x : F) = T x := by
  simp [kernelComplementEquivRange, kernelComplementToRange_apply]

end IsFredholm

end TauCeti

end
