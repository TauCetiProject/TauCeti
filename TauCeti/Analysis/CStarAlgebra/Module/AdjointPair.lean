/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Adjoint pairs of functions on C⋆-modules

An everywhere-defined function with an everywhere-defined adjoint is automatically
complex-linear and commutes with the coefficient action. Between complete modules
it is also continuous. Neither linearity nor boundedness is assumed in these results.
This is the starting point for constructing adjointable module operators.

We reuse `LinearMap.IsAdjointPair` on the flipped forms `CStarModule.innerₛₗ.flip`:
Mathlib's predicate expects forms linear in the first slot, whereas the module inner
product is conjugate-linear there. Thus its defining equality is the star of the
usual adjoint identity. `LinearMap.IsAdjointPair.inner_eq` recovers the usual identity.
For right Hilbert A-modules, instantiate the coefficient type below with `Aᵐᵒᵖ`.
No unit, fullness, countable generation, or nonzero-module hypothesis is needed.

## References

* Raeburn–Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Definition 2.17 and the discussion of adjointable operators.
-/

public section

open CStarModule

namespace CStarModule

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
  {T : E → F} {S : F → E}

/-- Adjoint pairs for the flipped forms are exactly adjoint pairs in the usual
conjugate-linear-first inner-product convention. -/
@[simp]
theorem isAdjointPair_inner_iff :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S ↔
      ∀ x y, inner A (T x) y = inner A x (S y) := by
  constructor
  · intro h x y
    simpa [innerₛₗ_apply] using congrArg star (h x y)
  · intro h x y
    simpa [innerₛₗ_apply] using congrArg star (h x y)

end CStarModule

namespace LinearMap.IsAdjointPair

section Algebraic

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
  {T : E → F} {S : F → E}

/-- The usual adjoint identity, in the conjugate-linear-first convention. -/
theorem inner_eq
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : E) (y : F) :
    inner A (T x) y = inner A x (S y) :=
  isAdjointPair_inner_iff.mp h x y

/-- Interchanging a C⋆-module adjoint pair again gives an adjoint pair. -/
theorem symm
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    IsAdjointPair (innerₛₗ (A := A) (E := F)).flip
      (innerₛₗ (A := A) (E := E)).flip S T :=
  fun y x => (h.inner_eq x y).symm

/-- The first member of a C⋆-module adjoint pair is uniquely determined by the second. -/
theorem unique_left
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S)
    {T' : E → F}
    (h' : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T' S) : T = T' := by
  funext x
  exact CStarModule.ext_inner_right fun y => (h.inner_eq x y).trans (h'.inner_eq x y).symm

/-- An everywhere-defined C⋆-module adjoint is unique, even as a plain function. -/
theorem unique_right
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S)
    {S' : F → E}
    (h' : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S') : S = S' :=
  h.symm.unique_left h'.symm

/-- An adjoint identity forces additivity; no additivity is assumed of either function. -/
theorem map_add
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x y : E) :
    T (x + y) = T x + T y := by
  apply CStarModule.ext_inner_right (A := A)
  intro z
  simp [h.inner_eq]

/-- An adjoint identity forces complex linearity. -/
theorem map_smul
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (c : ℂ) (x : E) :
    T (c • x) = c • T x := by
  apply CStarModule.ext_inner_right (A := A)
  intro y
  simp [h.inner_eq]

/-- An adjoint identity forces compatibility with the coefficient action. For a right
module over B, use A = Bᵐᵒᵖ. -/
theorem map_op_smul
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (a : A) (x : E) :
    T (a • x) = a • T x := by
  apply CStarModule.ext_inner_right (A := A)
  intro y
  simp [h.inner_eq]

/-- Bundle the complex linearity forced by a C⋆-module adjoint identity. -/
def toLinearMap
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : E →ₗ[ℂ] F where
  toFun := T
  map_add' := h.map_add
  map_smul' := h.map_smul

@[simp]
theorem toLinearMap_apply
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : E) : h.toLinearMap x = T x := (rfl)

end Algebraic

section Analytic

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  {T : E → F} {S : F → E}

/-- The graph of a function admitting an everywhere-defined C⋆-module adjoint is closed.
Completeness is not needed for this assertion. -/
theorem isClosed_graph
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    IsClosed (h.toLinearMap.graph : Set (E × F)) := by
  have heq : (h.toLinearMap.graph : Set (E × F)) =
      ⋂ y : F, {p | inner A p.2 y = inner A p.1 (S y)} := by
    ext p
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, toLinearMap_apply,
      Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hp y
      rw [hp, h.inner_eq]
    · intro hp
      exact CStarModule.ext_inner_right fun y => (hp y).trans (h.inner_eq p.1 y).symm
  rw [heq]
  exact isClosed_iInter fun y => isClosed_eq
    (CStarModule.continuous_inner.comp (continuous_snd.prodMk continuous_const))
    (CStarModule.continuous_inner.comp (continuous_fst.prodMk continuous_const))

variable [CompleteSpace E] [CompleteSpace F]

/-- The closed graph theorem makes an everywhere-defined C⋆-module adjoint pair continuous. -/
theorem continuous
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : Continuous T :=
  h.toLinearMap.continuous_of_isClosed_graph h.isClosed_graph

/-- Bundle the bounded complex-linear map forced by the adjoint identity on complete modules. -/
def toContinuousLinearMap
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : E →L[ℂ] F where
  toLinearMap := h.toLinearMap
  cont := h.continuous

@[simp]
theorem toContinuousLinearMap_apply
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : E) :
    h.toContinuousLinearMap x = T x := (rfl)

/-- Both functions in an adjoint pair on complete C⋆-modules are bounded complex-linear
maps commuting with the coefficient action. In particular this applies to nonunital right
Hilbert modules by taking the coefficient algebra to be an opposite algebra. -/
theorem exists_continuousLinearMaps
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    ∃ (T' : E →L[ℂ] F) (S' : F →L[ℂ] E),
      (∀ x, T' x = T x) ∧ (∀ y, S' y = S y) ∧
      (∀ (a : A) (x : E), T (a • x) = a • T x) ∧
      (∀ (a : A) (y : F), S (a • y) = a • S y) :=
  ⟨h.toContinuousLinearMap, h.symm.toContinuousLinearMap,
    h.toContinuousLinearMap_apply, h.symm.toContinuousLinearMap_apply,
    h.map_op_smul, h.symm.map_op_smul⟩

end Analytic

end LinearMap.IsAdjointPair
