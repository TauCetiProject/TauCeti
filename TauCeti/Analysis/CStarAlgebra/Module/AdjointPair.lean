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
usual adjoint identity. `LinearMap.IsAdjointPair.inner_eq_cstarModule` recovers that identity.
For right Hilbert A-modules, instantiate the coefficient type below with `Aᵐᵒᵖ`.
No unit, fullness, countable generation, or nonzero-module hypothesis is needed.

The predicate `CStarModule.IsAdjointable A T` records that a plain function `T : E → F` admits a
plain adjoint `S : F → E`. Its closure under the algebraic operations and the automatic additivity,
complex linearity, and coefficient compatibility of adjointable functions
(`CStarModule.IsAdjointable.map_add`, `CStarModule.IsAdjointable.map_smul`,
`CStarModule.IsAdjointable.map_smul_coeff`) need no `[StarModule ℂ A]` hypothesis.

For bounded adjoint pairs, `LinearMap.IsAdjointPair.norm_adjoint_comp_self_cstarModule` proves
the C⋆-identity `‖S ∘ T‖ = ‖T‖ ^ 2`, and `LinearMap.IsAdjointPair.norm_eq_cstarModule` proves
`‖S‖ = ‖T‖`.

## References

* Raeburn–Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Definition 2.17 and the discussion of adjointable operators.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* The proof of the C⋆-identity follows Mathlib's `ContinuousLinearMap.norm_adjoint_comp_self` for
  inner product spaces.
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
theorem inner_eq_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : E) (y : F) :
    inner A (T x) y = inner A x (S y) :=
  isAdjointPair_inner_iff.mp h x y

/-- Interchanging a C⋆-module adjoint pair again gives an adjoint pair. -/
theorem symm_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    IsAdjointPair (innerₛₗ (A := A) (E := F)).flip
      (innerₛₗ (A := A) (E := E)).flip S T :=
  isAdjointPair_inner_iff.mpr fun y x => by
    simpa only [star_inner] using congrArg star (h.inner_eq_cstarModule x y).symm

/-- The first member of a C⋆-module adjoint pair is uniquely determined by the second. -/
theorem unique_left_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S)
    {T' : E → F}
    (h' : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T' S) : T = T' := by
  funext x
  exact CStarModule.ext_inner_right fun y =>
    (h.inner_eq_cstarModule x y).trans (h'.inner_eq_cstarModule x y).symm

/-- An everywhere-defined C⋆-module adjoint is unique, even as a plain function. -/
theorem unique_right_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S)
    {S' : F → E}
    (h' : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S') : S = S' :=
  h.symm_cstarModule.unique_left_cstarModule h'.symm_cstarModule

/-- An adjoint identity forces additivity; no additivity is assumed of either function. -/
theorem map_add_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x y : E) :
    T (x + y) = T x + T y := by
  apply CStarModule.ext_inner_right (A := A)
  intro z
  simp [h.inner_eq_cstarModule]

/-- An adjoint identity forces complex linearity. -/
theorem map_smul_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (c : ℂ) (x : E) :
    T (c • x) = c • T x := by
  apply CStarModule.ext_inner_right (A := A)
  intro y
  simp [h.inner_eq_cstarModule]

/-- An adjoint identity forces compatibility with the coefficient action. For a right
module over B, use A = Bᵐᵒᵖ. -/
theorem map_smul_coeff_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (a : A) (x : E) :
    T (a • x) = a • T x := by
  apply CStarModule.ext_inner_right (A := A)
  intro y
  simp [h.inner_eq_cstarModule]

/-- Bundle the complex linearity forced by a C⋆-module adjoint identity. -/
def toLinearMapCStarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : E →ₗ[ℂ] F where
  toFun := T
  map_add' := h.map_add_cstarModule
  map_smul' := h.map_smul_cstarModule

@[simp]
theorem toLinearMapCStarModule_apply
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : E) :
    h.toLinearMapCStarModule x = T x := (rfl)

end Algebraic

section Analytic

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  {T : E → F} {S : F → E}

/-- The graph of a function admitting an everywhere-defined C⋆-module adjoint is closed.
Completeness is not needed for this assertion. -/
theorem isClosed_graph_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    IsClosed (h.toLinearMapCStarModule.graph : Set (E × F)) := by
  have heq : (h.toLinearMapCStarModule.graph : Set (E × F)) =
      ⋂ y : F, {p | inner A p.2 y = inner A p.1 (S y)} := by
    ext p
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, toLinearMapCStarModule_apply,
      Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hp y
      rw [hp, h.inner_eq_cstarModule]
    · intro hp
      exact CStarModule.ext_inner_right fun y =>
        (hp y).trans (h.inner_eq_cstarModule p.1 y).symm
  rw [heq]
  exact isClosed_iInter fun y => isClosed_eq
    (CStarModule.continuous_inner.comp (continuous_snd.prodMk continuous_const))
    (CStarModule.continuous_inner.comp (continuous_fst.prodMk continuous_const))

variable [CompleteSpace E] [CompleteSpace F]

/-- The first function of an adjoint pair between complete C⋆-modules is continuous;
apply to `h.symm_cstarModule` for the second. -/
theorem continuous_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : Continuous T :=
  h.toLinearMapCStarModule.continuous_of_isClosed_graph h.isClosed_graph_cstarModule

/-- Bundle the bounded complex-linear map forced by the adjoint identity on complete modules. -/
noncomputable def toContinuousLinearMapCStarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : E →L[ℂ] F :=
  ContinuousLinearMap.ofIsClosedGraph h.isClosed_graph_cstarModule

@[simp]
theorem toContinuousLinearMapCStarModule_apply
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : E) :
    h.toContinuousLinearMapCStarModule x = T x :=
  congrFun (ContinuousLinearMap.coeFn_ofIsClosedGraph h.isClosed_graph_cstarModule) x

/-- Both functions in an adjoint pair on complete C⋆-modules are bounded complex-linear
maps commuting with the coefficient action. In particular this applies to nonunital right
Hilbert modules by taking the coefficient algebra to be an opposite algebra. -/
theorem exists_continuousLinearMaps_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    ∃ (T' : E →L[ℂ] F) (S' : F →L[ℂ] E),
      (∀ x, T' x = T x) ∧ (∀ y, S' y = S y) ∧
      (∀ (a : A) (x : E), T (a • x) = a • T x) ∧
      (∀ (a : A) (y : F), S (a • y) = a • S y) :=
  ⟨h.toContinuousLinearMapCStarModule, h.symm_cstarModule.toContinuousLinearMapCStarModule,
    h.toContinuousLinearMapCStarModule_apply,
    h.symm_cstarModule.toContinuousLinearMapCStarModule_apply,
    h.map_smul_coeff_cstarModule, h.symm_cstarModule.map_smul_coeff_cstarModule⟩

end Analytic

section Norm

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  {T : E →L[ℂ] F} {S : F →L[ℂ] E}

/-- For a bounded C⋆-module adjoint pair, `‖T‖ ^ 2 ≤ ‖S ∘ T‖`. -/
private theorem sq_norm_le_norm_comp_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    ‖T‖ ^ 2 ≤ ‖S.comp T‖ := by
  -- `‖T x‖ ^ 2 = ‖⟨x, S (T x)⟩‖ ≤ ‖S ∘ T‖ * ‖x‖ ^ 2` for every `x`.
  rw [← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) fun x ↦ ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  calc ‖T x‖ ^ 2 = ‖inner A x (S (T x))‖ := by
        rw [CStarModule.norm_sq_eq A, h.inner_eq_cstarModule]
    _ ≤ ‖x‖ * ‖S.comp T x‖ := norm_inner_le E
    _ ≤ ‖x‖ * (‖S.comp T‖ * ‖x‖) := by gcongr; exact (S.comp T).le_opNorm x
    _ = (√‖S.comp T‖ * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        ring

/-- The two members of a bounded C⋆-module adjoint pair have the same operator norm. -/
theorem norm_eq_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    ‖S‖ = ‖T‖ := by
  -- Each norm is bounded by the other: `‖T‖ ^ 2 ≤ ‖S ∘ T‖ ≤ ‖S‖ * ‖T‖`, and symmetrically.
  have hT : ‖T‖ ^ 2 ≤ ‖S‖ * ‖T‖ :=
    (sq_norm_le_norm_comp_cstarModule h).trans (S.opNorm_comp_le T)
  have hS : ‖S‖ ^ 2 ≤ ‖T‖ * ‖S‖ :=
    (sq_norm_le_norm_comp_cstarModule h.symm_cstarModule).trans (T.opNorm_comp_le S)
  apply le_antisymm <;> nlinarith [norm_nonneg T, norm_nonneg S]

/-- The C⋆-identity for a bounded C⋆-module adjoint pair: `‖S ∘ T‖ = ‖T‖ ^ 2`. This is the
analytic input for the C⋆-algebra of adjointable operators on a Hilbert C⋆-module. -/
theorem norm_adjoint_comp_self_cstarModule
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    ‖S.comp T‖ = ‖T‖ ^ 2 :=
  le_antisymm ((S.opNorm_comp_le T).trans_eq (by rw [h.norm_eq_cstarModule, sq]))
    (sq_norm_le_norm_comp_cstarModule h)

end Norm

end LinearMap.IsAdjointPair

/-! ### The adjointability predicate on functions -/

namespace CStarModule

/-- A plain function `T : E → F` between `A`-inner-product spaces is *adjointable* if there exists a
plain function `S : F → E` satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A` for all `x` and `y`. On complete
Hilbert C⋆-modules, this forces both `T` and `S` to be bounded `ℂ`-linear `A`-module maps. -/
def IsAdjointable (A : Type*) {E F : Type*} [Inner A E] [Inner A F] (T : E → F) : Prop :=
  ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y)

section Inner

variable {A E F G : Type*}

theorem isAdjointable_def [Inner A E] [Inner A F] {T : E → F} :
    IsAdjointable A T ↔ ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y) :=
  Iff.rfl

@[simp]
theorem isAdjointable_id [Inner A E] : IsAdjointable A (id : E → E) :=
  ⟨id, fun _ _ => rfl⟩

theorem IsAdjointable.comp [Inner A E] [Inner A F] [Inner A G] {S : F → G} {T : E → F}
    (hS : IsAdjointable A S) (hT : IsAdjointable A T) :
    IsAdjointable A (S ∘ T) := by
  rcases hS with ⟨S', hS'⟩
  rcases hT with ⟨T', hT'⟩
  exact ⟨T' ∘ S', fun x z => (hS' (T x) z).trans (hT' x (S' z))⟩

end Inner

section Basic

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

@[simp]
theorem isAdjointable_zero : IsAdjointable A (0 : E → F) :=
  ⟨0, fun _ _ => by simp⟩

theorem IsAdjointable.add {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ + T₂) :=
  let ⟨S₁, h₁⟩ := h₁; let ⟨S₂, h₂⟩ := h₂
  ⟨S₁ + S₂, fun x y => by simp [h₁ x y, h₂ x y]⟩

theorem IsAdjointable.neg {T : E → F} (h : IsAdjointable A T) : IsAdjointable A (-T) :=
  let ⟨S, h⟩ := h
  ⟨-S, fun x y => by simp only [Pi.neg_apply, inner_neg_left', inner_neg_right', h x y]⟩

theorem IsAdjointable.sub {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ - T₂) :=
  sub_eq_add_neg T₁ T₂ ▸ h₁.add h₂.neg

theorem IsAdjointable.map_add {T : E → F} (h : IsAdjointable A T) (x y : E) :
    T (x + y) = T x + T y :=
  let ⟨_, h⟩ := h
  CStarModule.ext_inner_right (A := A) fun z => by
    rw [h (x + y) z, CStarModule.inner_add_left, ← h x z, ← h y z, ← CStarModule.inner_add_left]

theorem IsAdjointable.map_smul {T : E → F} (h : IsAdjointable A T) (c : ℂ) (x : E) :
    T (c • x) = c • T x :=
  let ⟨S, h⟩ := h
  CStarModule.ext_inner_left (A := A) fun z => by
    rw [← CStarModule.star_inner, h (c • x) z, CStarModule.star_inner,
      CStarModule.inner_smul_right_complex, ← CStarModule.star_inner x (S z), ← h x z,
      CStarModule.star_inner, ← CStarModule.inner_smul_right_complex]

theorem IsAdjointable.map_smul_coeff {T : E → F} (h : IsAdjointable A T) (a : A) (x : E) :
    T (a • x) = a • T x :=
  let ⟨_, h⟩ := h
  CStarModule.ext_inner_right (A := A) fun z => by
    rw [h (a • x) z, CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_left, ← h x z]

end Basic

section StarModule

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

theorem isAdjointable_iff_exists_isAdjointPair {T : E → F} :
    IsAdjointable A T ↔
      ∃ S : F → E, LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
        (innerₛₗ (A := A) (E := F)).flip T S := by
  simp_rw [isAdjointPair_inner_iff, IsAdjointable]

theorem IsAdjointable.smul {T : E → F} (c : ℂ) (h : IsAdjointable A T) :
    IsAdjointable A (c • T) :=
  let ⟨S, h⟩ := h
  ⟨star c • S, fun x y => by simp [h x y]⟩

end StarModule

end CStarModule
