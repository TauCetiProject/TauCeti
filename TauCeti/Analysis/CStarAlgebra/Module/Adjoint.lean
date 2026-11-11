/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Adjoint pairs between right Hilbert C⋆-modules

Right Hilbert `A`-modules are represented with Mathlib's class as `CStarModule Aᵐᵒᵖ E`: the right
action is `x a = MulOpposite.op a • x` and the `A`-valued inner product is
`MulOpposite.unop (inner Aᵐᵒᵖ x y)`. Two plain functions `T : E → F` and `S : F → E` form an
adjoint pair when `⟨T x, y⟩ = ⟨x, S y⟩` for all `x` and `y`. We express this with Mathlib's
`LinearMap.IsAdjointPair` for the flipped sesquilinear inner products
`(CStarModule.innerₛₗ (A := Aᵐᵒᵖ)).flip`, exactly as Mathlib does for inner product spaces in
`LinearMap.isAdjointPair_inner`; the flip is needed because `LinearMap.IsAdjointPair` is
formulated for forms that are linear in the first variable. The characterisation
`LinearMap.isAdjointPair_innerₛₗ_flip_iff` recovers the usual identity.

In contrast with Hilbert spaces, a bounded module map between Hilbert C⋆-modules need not have an
adjoint, so the adjoint identity is extra structure. Conversely, the identity alone is very
strong: because the inner product is nondegenerate, it forces both functions to be additive,
complex linear and `A`-linear, and if both modules are complete the closed graph theorem makes
them continuous. Bounded adjoint pairs satisfy the C⋆-identity `‖S ∘ T‖ = ‖T‖ ^ 2` together with
`‖S‖ = ‖T‖`, the analytic input for the C⋆-algebra of adjointable operators on a Hilbert
C⋆-module.

## Main declarations

* `CStarModule.ext_inner_left`, `CStarModule.ext_inner_right`: nondegeneracy of the inner
  product of a Hilbert C⋆-module.
* `LinearMap.isAdjointPair_innerₛₗ_flip_iff`: adjoint pairs are characterised by
  `⟨T x, y⟩ = ⟨x, S y⟩`.
* `LinearMap.IsAdjointPair.symm`, `LinearMap.IsAdjointPair.left_unique`,
  `LinearMap.IsAdjointPair.right_unique`: adjoint pairs are symmetric, and each member determines
  the other.
* `LinearMap.IsAdjointPair.map_add`, `LinearMap.IsAdjointPair.map_smul`,
  `LinearMap.IsAdjointPair.map_op_smul`: a member of an adjoint pair is additive, complex
  linear and `A`-linear.
* `LinearMap.IsAdjointPair.toContinuousLinearMap`: between complete modules, a member of an
  adjoint pair is a continuous linear map (`LinearMap.IsAdjointPair.exists_continuousLinearMaps`).
* `LinearMap.IsAdjointPair.norm_adjoint_comp_self`: the C⋆-identity `‖S ∘ T‖ = ‖T‖ ^ 2` for a
  bounded adjoint pair, and `LinearMap.IsAdjointPair.norm_eq`: `‖S‖ = ‖T‖`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Lemma 2.18.
* The proof of the C⋆-identity follows Mathlib's `ContinuousLinearMap.norm_adjoint_comp_self` for
  inner product spaces.
-/

public section

open Filter Topology

namespace CStarModule

section ext

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- The inner product of a Hilbert C⋆-module is nondegenerate: two vectors with the same inner
products against every vector, taken in the second variable, are equal. -/
theorem ext_inner_left {x y : E} (h : ∀ v, inner A v x = inner A v y) : x = y := by
  rw [← sub_eq_zero, ← inner_self (A := A), inner_sub_right, h, sub_self]

/-- The inner product of a Hilbert C⋆-module is nondegenerate: two vectors with the same inner
products against every vector, taken in the first variable, are equal. -/
theorem ext_inner_right {x y : E} (h : ∀ v, inner A x v = inner A y v) : x = y := by
  rw [← sub_eq_zero, ← inner_self (A := A), inner_sub_left, h, sub_self]

end ext

end CStarModule

namespace LinearMap

open CStarModule

section Algebraic

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]
  [AddCommGroup F] [Module ℂ F] [SMul Aᵐᵒᵖ F] [Norm F] [CStarModule Aᵐᵒᵖ F]
  {T T' : E → F} {S S' : F → E}

/-- Two functions between right Hilbert `A`-modules form an adjoint pair for the flipped inner
products exactly when `⟨T x, y⟩ = ⟨x, S y⟩` for all `x` and `y`. -/
theorem isAdjointPair_innerₛₗ_flip_iff :
    IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip T S ↔
      ∀ x y, inner Aᵐᵒᵖ (T x) y = inner Aᵐᵒᵖ x (S y) := by
  refine forall₂_congr fun x y ↦ ?_
  rw [flip_apply, flip_apply, innerₛₗ_apply, innerₛₗ_apply, ← star_inner (T x), ← star_inner x,
    star_inj, eq_comm]

namespace IsAdjointPair

/-- The adjoint identity `⟨T x, y⟩ = ⟨x, S y⟩` of an adjoint pair. -/
theorem inner_apply_left
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S)
    (x : E) (y : F) : inner Aᵐᵒᵖ (T x) y = inner Aᵐᵒᵖ x (S y) :=
  isAdjointPair_innerₛₗ_flip_iff.mp h x y

/-- Adjoint pairs between right Hilbert `A`-modules are symmetric: `⟨S y, x⟩ = ⟨y, T x⟩`. -/
theorem symm
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip S T :=
  isAdjointPair_innerₛₗ_flip_iff.mpr fun y x ↦ by
    rw [← star_inner x, ← h.inner_apply_left, star_inner]

/-- The adjoint of a function between right Hilbert `A`-modules is unique when it exists. -/
theorem right_unique
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S)
    (h' : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S') :
    S = S' :=
  funext fun y ↦ ext_inner_left (A := Aᵐᵒᵖ) fun x ↦ by
    rw [← h.inner_apply_left, h'.inner_apply_left]

/-- A function between right Hilbert `A`-modules is determined by its adjoint. -/
theorem left_unique
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S)
    (h' : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T' S) :
    T = T' :=
  h.symm.right_unique h'.symm

/-- A function between right Hilbert `A`-modules that has an adjoint is additive. -/
theorem map_add
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S)
    (x y : E) : T (x + y) = T x + T y :=
  ext_inner_right (A := Aᵐᵒᵖ) fun v ↦ by simp [h.inner_apply_left]

/-- A function between right Hilbert `A`-modules that has an adjoint is complex linear. -/
theorem map_smul
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S)
    (c : ℂ) (x : E) : T (c • x) = c • T x :=
  ext_inner_right (A := Aᵐᵒᵖ) fun v ↦ by simp [h.inner_apply_left]

/-- A function between right Hilbert `A`-modules that has an adjoint is `A`-linear: it commutes
with the right action `x a = MulOpposite.op a • x`. -/
theorem map_op_smul
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S)
    (a : Aᵐᵒᵖ) (x : E) : T (a • x) = a • T x :=
  ext_inner_right (A := Aᵐᵒᵖ) fun v ↦ by simp [h.inner_apply_left]

end IsAdjointPair

end Algebraic

section Normed

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

namespace IsAdjointPair

section Continuity

variable [CompleteSpace E] [CompleteSpace F] {T : E → F} {S : F → E}

/-- A function between complete right Hilbert `A`-modules that has an adjoint, as a continuous
complex linear map. -/
noncomputable def toContinuousLinearMap
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    E →L[ℂ] F :=
  -- Closed graph theorem: if `xₙ → x` and `T xₙ → y`, then `⟨y, v⟩ = lim ⟨xₙ, S v⟩ = ⟨T x, v⟩`.
  ContinuousLinearMap.ofSeqClosedGraph (g := ⟨⟨T, h.map_add⟩, h.map_smul⟩)
    fun u x y hu hTu ↦ ext_inner_right (A := Aᵐᵒᵖ) fun v ↦ by
      refine tendsto_nhds_unique (((continuous_inner (A := Aᵐᵒᵖ)).tendsto (y, v)).comp
        (hTu.prodMk_nhds tendsto_const_nhds)) ?_
      simp_rw [Function.comp_def, coe_mk, AddHom.coe_mk, h.inner_apply_left]
      exact ((continuous_inner (A := Aᵐᵒᵖ)).tendsto (x, S v)).comp
        (hu.prodMk_nhds tendsto_const_nhds)

@[simp]
theorem coe_toContinuousLinearMap
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    ⇑h.toContinuousLinearMap = T := (rfl)

/-- A function between complete right Hilbert `A`-modules that has an adjoint is continuous. -/
theorem continuous
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    Continuous T :=
  h.toContinuousLinearMap.continuous

end Continuity

section Norm

variable {T : E →L[ℂ] F} {S : F →L[ℂ] E}

/-- For a bounded adjoint pair, `‖T‖ ^ 2 ≤ ‖S ∘ T‖`. -/
theorem sq_norm_le_norm_comp
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    ‖T‖ ^ 2 ≤ ‖S.comp T‖ := by
  -- `‖T x‖ ^ 2 = ‖⟨x, S (T x)⟩‖ ≤ ‖S ∘ T‖ * ‖x‖ ^ 2` for every `x`.
  rw [← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) fun x ↦ ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  calc ‖T x‖ ^ 2 = ‖inner Aᵐᵒᵖ x (S (T x))‖ := by
        rw [CStarModule.norm_sq_eq Aᵐᵒᵖ, h.inner_apply_left]
    _ ≤ ‖x‖ * ‖S.comp T x‖ := norm_inner_le E
    _ ≤ ‖x‖ * (‖S.comp T‖ * ‖x‖) := by gcongr; exact (S.comp T).le_opNorm x
    _ = (√‖S.comp T‖ * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        ring

/-- The two members of a bounded adjoint pair have the same operator norm. -/
theorem norm_eq
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    ‖S‖ = ‖T‖ := by
  -- Each norm is bounded by the other: `‖T‖ ^ 2 ≤ ‖S ∘ T‖ ≤ ‖S‖ * ‖T‖`, and symmetrically.
  have hT : ‖T‖ ^ 2 ≤ ‖S‖ * ‖T‖ := h.sq_norm_le_norm_comp.trans (S.opNorm_comp_le T)
  have hS : ‖S‖ ^ 2 ≤ ‖T‖ * ‖S‖ := h.symm.sq_norm_le_norm_comp.trans (T.opNorm_comp_le S)
  apply le_antisymm <;> nlinarith [norm_nonneg T, norm_nonneg S]

/-- The C⋆-identity for a bounded adjoint pair between right Hilbert `A`-modules:
`‖S ∘ T‖ = ‖T‖ ^ 2`. -/
theorem norm_adjoint_comp_self
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    ‖S.comp T‖ = ‖T‖ ^ 2 :=
  le_antisymm ((S.opNorm_comp_le T).trans_eq (by rw [h.norm_eq, sq])) h.sq_norm_le_norm_comp

end Norm

/-- Two functions between complete right Hilbert `A`-modules satisfying the adjoint identity
`⟨T x, y⟩ = ⟨x, S y⟩` are continuous complex linear maps, and `T` is `A`-linear. -/
theorem exists_continuousLinearMaps [CompleteSpace E] [CompleteSpace F]
    {T : E → F} {S : F → E}
    (h : IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip
      T S) :
    ∃ (T' : E →L[ℂ] F) (S' : F →L[ℂ] E),
      (∀ x, T' x = T x) ∧ (∀ y, S' y = S y) ∧ ∀ (a : Aᵐᵒᵖ) (x : E), T (a • x) = a • T x :=
  ⟨h.toContinuousLinearMap, h.symm.toContinuousLinearMap, fun _ ↦ rfl, fun _ ↦ rfl,
    h.map_op_smul⟩

end IsAdjointPair

end Normed

end LinearMap
