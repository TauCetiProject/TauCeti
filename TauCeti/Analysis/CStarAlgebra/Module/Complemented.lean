/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Topology.ContinuousMap.StarOrdered
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
public import TauCeti.Analysis.CStarAlgebra.Module.Orthogonal

import Mathlib.Topology.Perfect
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Analysis.CStarAlgebra.Module.Action

/-!
# Orthogonally complemented submodules of Hilbert C⋆-modules

Unlike in Hilbert spaces, a closed C⋆-submodule `F` of a Hilbert C⋆-module `E` need not satisfy
`F ⊔ F.orthogonal = ⊤`, nor even `F.orthogonal.orthogonal = F`. We define
`TauCeti.CStarSubmodule.IsOrthogonallyComplemented F` as `F ⊔ F.orthogonal = ⊤` and establish the
fundamental characterizations without assuming completeness of `E` or closedness of `F`:

* `F.IsOrthogonallyComplemented` is equivalent to the subtype inclusion `F.subtype : F → E`
  admitting an adjoint `P : E → F` (equivalently, `F.subtypeL` admitting a bounded adjoint
  `P : E →L[ℂ] F`), in which case `P` is uniquely given by `hF.orthogonalProjectionOnto`.
* `F.IsOrthogonallyComplemented` is equivalent to `F` being the range of a bounded self-adjoint
  idempotent `Q : E →L[ℂ] E` (or even a plain self-adjoint idempotent `Q : E → E`), in which case
  `Q` is uniquely given by `hF.starProjection`.
* Every orthogonally complemented submodule is automatically norm-closed, satisfies
  `F.orthogonal.orthogonal = F`, and yields an inner-product- and coefficient-preserving linear
  isometry equivalence `hF.orthogonalAddEquiv : C⋆ᵐᵒᵈ(A, F × F.orthogonal) ≃ₗᵢ[ℂ] E`.

We also verify three concrete regimes:

1. For any star projection `p` in a (possibly nonunital) C⋆-algebra `A`, the right ideal
   `CStarSubmodule.rightFixedSubmodule p = {x | p * x = x}` is orthogonally complemented in the
   right self-module `CStarModule Aᵐᵒᵖ A`, with orthogonal projection `x ↦ p * x`.
2. Over `A = ℂ`, `F.orthogonal` and `F.IsOrthogonallyComplemented` agree with Mathlib's
   `Submodule.orthogonal` and `Submodule.HasOrthogonalProjection`, and `hF.starProjection` agrees
   with `F.toSubmodule.starProjection`.
3. For any compact Hausdorff space `X` and non-isolated point `x₀ : X` (in particular `X = [0, 1]`
   and `x₀ = 0`), the closed right ideal
   `CStarSubmodule.vanishingAt X x₀ = {f ∈ C(X, ℂ) | f x₀ = 0}` has orthogonal complement `⊥`,
   satisfies `J < J.orthogonal.orthogonal = ⊤`, is not orthogonally complemented, and its
   inclusion into `C(X, ℂ)` admits no C⋆-module adjoint.

## Main declarations

* `TauCeti.CStarSubmodule.IsOrthogonallyComplemented`: `F ⊔ F.orthogonal = ⊤`.
* `TauCeti.CStarSubmodule.IsOrthogonallyComplemented.orthogonalProjectionOnto`,
  `TauCeti.CStarSubmodule.IsOrthogonallyComplemented.starProjection`,
  `TauCeti.CStarSubmodule.IsOrthogonallyComplemented.orthogonalAddEquiv`: canonical orthogonal
  projections and unitary direct-sum decomposition.
* `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_adjoint_subtype`,
  `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_adjoint_subtypeL`,
  `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_selfAdjoint_idempotent`,
  `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_starProjection`: characterizations
  of orthogonal complementability.
* `TauCeti.CStarSubmodule.isOrthogonallyComplemented_rightFixedSubmodule`,
  `TauCeti.CStarSubmodule.isOrthogonallyComplemented_complex_iff`,
  `TauCeti.CStarSubmodule.not_isOrthogonallyComplemented_vanishingAt`,
  `TauCeti.CStarSubmodule.not_isOrthogonallyComplemented_vanishingAt_unitInterval`: concrete
  witnesses and scalar comparison.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1 and
  Chapter 3.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open MulOpposite
open scoped WithCStarModule

namespace TauCeti.CStarSubmodule

/-! ### Orthogonal complementability: algebraic characterization -/

section ComplementedAlgebraic

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- A C⋆-submodule `F` is *orthogonally complemented* if `F ⊔ F.orthogonal = ⊤`, i.e. every vector
decomposes as a sum of an element of `F` and an element of `F.orthogonal`. -/
def IsOrthogonallyComplemented (F : CStarSubmodule A E) : Prop :=
  F ⊔ F.orthogonal = ⊤

theorem isOrthogonallyComplemented_iff_exists_add {F : CStarSubmodule A E} :
    F.IsOrthogonallyComplemented ↔ ∀ x : E, ∃ y ∈ F, ∃ z ∈ F.orthogonal, y + z = x := by
  let _ := CStarModule.distribSMul A E
  rw [IsOrthogonallyComplemented, eq_top_iff]
  refine ⟨fun h x ↦ mem_sup.mp (h (mem_top x)), fun h x _ ↦ mem_sup.mpr (h x)⟩

theorem isOrthogonallyComplemented_iff_isCompl {F : CStarSubmodule A E} :
    F.IsOrthogonallyComplemented ↔ IsCompl F F.orthogonal :=
  ⟨fun h ↦ ⟨F.orthogonal_disjoint, codisjoint_iff.mpr h⟩, fun h ↦ h.codisjoint.eq_top⟩

theorem IsOrthogonallyComplemented.isCompl_toSubmodule {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : IsCompl F.toSubmodule F.orthogonal.toSubmodule where
  disjoint := by
    let _ := CStarModule.distribSMul A E
    exact disjoint_iff.mp F.orthogonal_disjoint
  codisjoint := by
    let _ := CStarModule.distribSMul A E
    rw [codisjoint_iff, ← toSubmodule_sup, hF, toSubmodule_top]

theorem isOrthogonallyComplemented_bot : (⊥ : CStarSubmodule A E).IsOrthogonallyComplemented := by
  simp [IsOrthogonallyComplemented]

theorem isOrthogonallyComplemented_top : (⊤ : CStarSubmodule A E).IsOrthogonallyComplemented := by
  simp [IsOrthogonallyComplemented]

/-- An orthogonally complemented submodule equals its double orthogonal complement `F⊥⊥`. -/
theorem IsOrthogonallyComplemented.orthogonal_orthogonal {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : F.orthogonal.orthogonal = F := by
  let _ := CStarModule.distribSMul A E
  refine le_antisymm (fun x hx ↦ ?_) (le_orthogonal_orthogonal F)
  obtain ⟨y, hy, z, hz, rfl⟩ := isOrthogonallyComplemented_iff_exists_add.mp hF x
  have hz' : z ∈ F.orthogonal.orthogonal := by
    have hsub : y + z - y ∈ F.orthogonal.orthogonal :=
      F.orthogonal.orthogonal.sub_mem hx (le_orthogonal_orthogonal F hy)
    simpa only [add_sub_cancel_left] using hsub
  have hmem : z ∈ F.orthogonal ⊓ F.orthogonal.orthogonal := ⟨hz, hz'⟩
  rw [inf_orthogonal_eq_bot, mem_bot] at hmem
  simpa [hmem] using hy

/-- The orthogonal complement of an orthogonally complemented submodule is again orthogonally
complemented. -/
theorem IsOrthogonallyComplemented.orthogonal {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : F.orthogonal.IsOrthogonallyComplemented := by
  rw [IsOrthogonallyComplemented, hF.orthogonal_orthogonal, sup_comm]
  exact hF

/-- Purely algebraic characterization: `F` is orthogonally complemented if and only if `F` is the
range of a self-adjoint idempotent function `Q : E → E`. -/
theorem isOrthogonallyComplemented_iff_exists_selfAdjoint_idempotent {F : CStarSubmodule A E} :
    F.IsOrthogonallyComplemented ↔
      ∃ Q : E → E, LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
        (CStarModule.innerₛₗ (A := A) (E := E)).flip Q Q ∧
        (∀ x, Q (Q x) = Q x) ∧ Set.range Q = (F : Set E) := by
  constructor
  · intro hF
    let Q := F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule
    have hQsub : ∀ x : E, x - Q x ∈ F.orthogonal := fun x ↦ by
      have hdecomp := Submodule.projection_add_projection_eq_self hF.isCompl_toSubmodule x
      have heq : x - Q x =
          F.orthogonal.toSubmodule.projection F.toSubmodule hF.isCompl_toSubmodule.symm x :=
        sub_eq_of_eq_add' hdecomp.symm
      exact heq ▸ Submodule.projection_apply_mem hF.isCompl_toSubmodule.symm x
    refine ⟨Q, CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦ ?_, fun x ↦ ?_, ?_⟩
    · have h1 : inner A (Q x) (y - Q y) = 0 :=
        inner_right_of_mem_orthogonal (Submodule.projection_apply_mem hF.isCompl_toSubmodule x)
          (hQsub y)
      have h2 : inner A (x - Q x) (Q y) = 0 :=
        inner_left_of_mem_orthogonal (Submodule.projection_apply_mem hF.isCompl_toSubmodule y)
          (hQsub x)
      rw [CStarModule.inner_sub_right, sub_eq_zero] at h1
      rw [CStarModule.inner_sub_left, sub_eq_zero] at h2
      exact h1.trans h2.symm
    · exact Submodule.projection_apply_left hF.isCompl_toSubmodule
        ⟨Q x, Submodule.projection_apply_mem hF.isCompl_toSubmodule x⟩
    · ext y
      refine ⟨?_, fun hy ↦ ⟨y, Submodule.projection_apply_left hF.isCompl_toSubmodule ⟨y, hy⟩⟩⟩
      rintro ⟨x, rfl⟩
      exact Submodule.projection_apply_mem hF.isCompl_toSubmodule x
  · rintro ⟨Q, hQ, hidem, hrange⟩
    rw [isOrthogonallyComplemented_iff_exists_add]
    intro x
    have hQx : Q x ∈ F := SetLike.mem_coe.mp (hrange ▸ Set.mem_range_self x)
    refine ⟨Q x, hQx, x - Q x, ?_, add_sub_cancel _ _⟩
    refine sub_mem_orthogonal_of_inner_right fun u hu ↦ ?_
    have hu' : u ∈ Set.range Q := hrange.symm ▸ SetLike.mem_coe.mpr hu
    obtain ⟨v, rfl⟩ := hu'
    calc inner A (Q v) x = inner A (Q (Q v)) x := by rw [hidem v]
      _ = inner A (Q v) (Q x) := hQ.inner_eq_cstarModule (Q v) x

end ComplementedAlgebraic

section ComplementedNormed

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
  [CStarModule A E]

/-- Characterization without analytic C⋆-algebra assumptions: `F` is orthogonally complemented if
and only if its subtype inclusion `F.subtype : F → E` admits a (plain-function) C⋆-module adjoint
`P : E → F`. -/
theorem isOrthogonallyComplemented_iff_exists_adjoint_subtype {F : CStarSubmodule A E} :
    F.IsOrthogonallyComplemented ↔
      ∃ P : E → F, LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := F)).flip
        (CStarModule.innerₛₗ (A := A) (E := E)).flip F.subtype P := by
  constructor
  · intro hF
    let P : E → F := F.toSubmodule.projectionOnto F.orthogonal.toSubmodule hF.isCompl_toSubmodule
    refine ⟨P, CStarModule.isAdjointPair_inner_iff.mpr fun u x ↦ ?_⟩
    have hsub : x - (P x : E) ∈ F.orthogonal := by
      have hdecomp := Submodule.projection_add_projection_eq_self hF.isCompl_toSubmodule x
      have heq : x - (P x : E) =
          F.orthogonal.toSubmodule.projection F.toSubmodule hF.isCompl_toSubmodule.symm x :=
        sub_eq_of_eq_add' hdecomp.symm
      exact heq ▸ Submodule.projection_apply_mem hF.isCompl_toSubmodule.symm x
    have horth : inner A (u : E) (x - (P x : E)) = 0 :=
      inner_right_of_mem_orthogonal u.property hsub
    rw [CStarModule.inner_sub_right, sub_eq_zero] at horth
    rw [subtype_apply, inner_coe]
    exact horth
  · rintro ⟨P, hP⟩
    rw [isOrthogonallyComplemented_iff_exists_add]
    intro x
    refine ⟨P x, (P x).property, x - P x, ?_, add_sub_cancel _ _⟩
    refine sub_mem_orthogonal_of_inner_right fun u hu ↦ ?_
    simpa only [subtype_apply, inner_coe] using hP.inner_eq_cstarModule ⟨u, hu⟩ x

end ComplementedNormed

/-! ### Bounded orthogonal projections and direct-sum decomposition -/

section ComplementedAnalytic

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- An orthogonally complemented C⋆-submodule and its orthogonal complement form topological
complements (without assuming completeness of `E`). -/
theorem IsOrthogonallyComplemented.isTopCompl {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : F.toSubmodule.IsTopCompl F.orthogonal.toSubmodule where
  isCompl := hF.isCompl_toSubmodule
  continuous_projection := by
    refine AddMonoidHomClass.continuous_of_bound _ 1 fun x ↦ ?_
    rw [one_mul]
    have hdecomp := Submodule.projection_add_projection_eq_self hF.isCompl_toSubmodule x
    have horth :
        inner A (F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x)
          (F.orthogonal.toSubmodule.projection F.toSubmodule hF.isCompl_toSubmodule.symm x) = 0 :=
      inner_right_of_mem_orthogonal (Submodule.projection_apply_mem hF.isCompl_toSubmodule x)
        (Submodule.projection_apply_mem hF.isCompl_toSubmodule.symm x)
    calc ‖F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x‖
        ≤ ‖F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x +
            F.orthogonal.toSubmodule.projection F.toSubmodule hF.isCompl_toSubmodule.symm x‖ :=
          CStarModule.norm_le_norm_add_left_of_inner_eq_zero horth
      _ = ‖x‖ := by rw [hdecomp]

/-- Every orthogonally complemented C⋆-submodule is norm-closed. -/
theorem IsOrthogonallyComplemented.isClosed {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : IsClosed (F : Set E) := by
  rw [← hF.orthogonal_orthogonal]
  exact isClosed_orthogonal F.orthogonal

/-- The canonical bounded orthogonal projection `E →L[ℂ] F` onto an orthogonally complemented
C⋆-submodule `F`. -/
noncomputable def IsOrthogonallyComplemented.orthogonalProjectionOnto {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : E →L[ℂ] F :=
  F.toSubmodule.projectionOntoL F.orthogonal.toSubmodule hF.isTopCompl

/-- The canonical bounded orthogonal projection `E →L[ℂ] E` with range `F` and kernel
`F.orthogonal`. -/
noncomputable def IsOrthogonallyComplemented.starProjection {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : E →L[ℂ] E :=
  F.toSubmodule.projectionL F.orthogonal.toSubmodule hF.isTopCompl

@[simp]
theorem IsOrthogonallyComplemented.coe_orthogonalProjectionOnto_apply {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) :
    (hF.orthogonalProjectionOnto x : E) = hF.starProjection x :=
  (rfl)

theorem IsOrthogonallyComplemented.subtypeL_comp_orthogonalProjectionOnto {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    F.subtypeL.comp hF.orthogonalProjectionOnto = hF.starProjection :=
  ContinuousLinearMap.ext fun x ↦ by
    rw [ContinuousLinearMap.comp_apply, subtypeL_apply, coe_orthogonalProjectionOnto_apply]

@[simp]
theorem IsOrthogonallyComplemented.orthogonalProjectionOnto_apply_self {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : F) :
    hF.orthogonalProjectionOnto (x : E) = x :=
  Submodule.projectionOntoL_apply_left hF.isTopCompl x

@[simp]
theorem IsOrthogonallyComplemented.orthogonalProjectionOnto_comp_subtypeL {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    hF.orthogonalProjectionOnto.comp F.subtypeL = ContinuousLinearMap.id ℂ F :=
  ContinuousLinearMap.ext fun x ↦ by
    rw [ContinuousLinearMap.comp_apply, subtypeL_apply, ContinuousLinearMap.id_apply,
      hF.orthogonalProjectionOnto_apply_self]

theorem IsOrthogonallyComplemented.orthogonalProjectionOnto_apply_eq_zero_iff
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) {x : E} :
    hF.orthogonalProjectionOnto x = 0 ↔ x ∈ F.orthogonal :=
  Submodule.projectionOntoL_apply_eq_zero_iff hF.isTopCompl

@[simp]
theorem IsOrthogonallyComplemented.ker_orthogonalProjectionOnto {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    hF.orthogonalProjectionOnto.ker = F.orthogonal.toSubmodule :=
  Submodule.ker_projectionOntoL hF.isTopCompl

@[simp]
theorem IsOrthogonallyComplemented.range_orthogonalProjectionOnto {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    hF.orthogonalProjectionOnto.range = ⊤ :=
  Submodule.range_projectionOntoL hF.isTopCompl

theorem IsOrthogonallyComplemented.starProjection_apply_mem {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) : hF.starProjection x ∈ F :=
  Submodule.projectionL_apply_mem hF.isTopCompl x

theorem IsOrthogonallyComplemented.sub_starProjection_mem_orthogonal {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) : x - hF.starProjection x ∈ F.orthogonal := by
  have hdecomp := Submodule.projectionL_add_projectionL_eq_self hF.isTopCompl x
  have heq : x - hF.starProjection x =
      F.orthogonal.toSubmodule.projectionL F.toSubmodule hF.isTopCompl.symm x :=
    sub_eq_of_eq_add' hdecomp.symm
  exact heq ▸ Submodule.projectionL_apply_mem hF.isTopCompl.symm x

theorem IsOrthogonallyComplemented.starProjection_apply_of_mem {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) {x : E} (hx : x ∈ F) : hF.starProjection x = x :=
  Submodule.projectionL_apply_left hF.isTopCompl ⟨x, hx⟩

theorem IsOrthogonallyComplemented.starProjection_apply_eq_self_iff {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) {x : E} : hF.starProjection x = x ↔ x ∈ F :=
  ⟨fun h ↦ h ▸ hF.starProjection_apply_mem x, hF.starProjection_apply_of_mem⟩

theorem IsOrthogonallyComplemented.starProjection_apply_eq_zero_iff {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) {x : E} : hF.starProjection x = 0 ↔ x ∈ F.orthogonal :=
  Submodule.projectionL_apply_eq_zero_iff hF.isTopCompl

theorem IsOrthogonallyComplemented.eq_starProjection_of_mem_orthogonal {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) {x y : E} (hy : y ∈ F) (hxy : x - y ∈ F.orthogonal) :
    hF.starProjection x = y := by
  let _ := CStarModule.distribSMul A E
  have h1 : hF.starProjection x - y ∈ F := F.sub_mem (hF.starProjection_apply_mem x) hy
  have h2 : hF.starProjection x - y ∈ F.orthogonal := by
    have heq : hF.starProjection x - y = (x - y) - (x - hF.starProjection x) := by abel
    rw [heq]
    exact F.orthogonal.sub_mem hxy (hF.sub_starProjection_mem_orthogonal x)
  have hmem : hF.starProjection x - y ∈ F ⊓ F.orthogonal := ⟨h1, h2⟩
  rw [inf_orthogonal_eq_bot, mem_bot] at hmem
  exact sub_eq_zero.mp hmem

@[simp]
theorem IsOrthogonallyComplemented.range_starProjection {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : hF.starProjection.range = F.toSubmodule :=
  Submodule.range_projectionL hF.isTopCompl

@[simp]
theorem IsOrthogonallyComplemented.ker_starProjection {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : hF.starProjection.ker = F.orthogonal.toSubmodule :=
  Submodule.ker_projectionL hF.isTopCompl

@[simp]
theorem IsOrthogonallyComplemented.isIdempotentElem_starProjection {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : IsIdempotentElem hF.starProjection :=
  Submodule.isIdempotentElem_projectionL hF.isTopCompl

theorem IsOrthogonallyComplemented.starProjection_orthogonal {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    hF.orthogonal.starProjection = ContinuousLinearMap.id ℂ E - hF.starProjection := by
  ext x
  simp only [sub_apply, ContinuousLinearMap.id_apply]
  refine hF.orthogonal.eq_starProjection_of_mem_orthogonal
    (hF.sub_starProjection_mem_orthogonal x) ?_
  rw [sub_sub_cancel, hF.orthogonal_orthogonal]
  exact hF.starProjection_apply_mem x

/-- The orthogonal projection `hF.orthogonalProjectionOnto` is the C⋆-module adjoint of the subtype
inclusion `F.subtypeL`. -/
theorem IsOrthogonallyComplemented.isAdjointPair_subtypeL_orthogonalProjectionOnto
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := F)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip F.subtypeL hF.orthogonalProjectionOnto := by
  refine CStarModule.isAdjointPair_inner_iff.mpr fun u x ↦ ?_
  have horth : inner A (u : E) (x - hF.starProjection x) = 0 :=
    inner_right_of_mem_orthogonal u.property (hF.sub_starProjection_mem_orthogonal x)
  rw [CStarModule.inner_sub_right, sub_eq_zero] at horth
  rw [subtypeL_apply, inner_coe, coe_orthogonalProjectionOnto_apply]
  exact horth

/-- `hF.starProjection` is self-adjoint for the `A`-valued inner product. -/
theorem IsOrthogonallyComplemented.isAdjointPair_starProjection {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip hF.starProjection hF.starProjection := by
  refine CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦ ?_
  have h1 := hF.isAdjointPair_subtypeL_orthogonalProjectionOnto.inner_eq_cstarModule
    (hF.orthogonalProjectionOnto x) y
  have h2 :=
    hF.isAdjointPair_subtypeL_orthogonalProjectionOnto.symm_cstarModule.inner_eq_cstarModule
      x (hF.orthogonalProjectionOnto y)
  simpa only [subtypeL_apply, coe_orthogonalProjectionOnto_apply] using h1.trans h2

theorem IsOrthogonallyComplemented.orthogonalProjectionOnto_smul_coeff {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (a : A) (x : E) :
    hF.orthogonalProjectionOnto (a • x) = a • hF.orthogonalProjectionOnto x :=
  hF.isAdjointPair_subtypeL_orthogonalProjectionOnto.symm_cstarModule.map_smul_coeff_cstarModule a x

theorem IsOrthogonallyComplemented.starProjection_smul_coeff {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (a : A) (x : E) :
    hF.starProjection (a • x) = a • hF.starProjection x :=
  hF.isAdjointPair_starProjection.map_smul_coeff_cstarModule a x

theorem IsOrthogonallyComplemented.norm_starProjection_apply_le {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) : ‖hF.starProjection x‖ ≤ ‖x‖ := by
  have horth : inner A (hF.starProjection x) (x - hF.starProjection x) = 0 :=
    inner_right_of_mem_orthogonal (hF.starProjection_apply_mem x)
      (hF.sub_starProjection_mem_orthogonal x)
  simpa only [add_sub_cancel] using CStarModule.norm_le_norm_add_left_of_inner_eq_zero horth

theorem IsOrthogonallyComplemented.norm_orthogonalProjectionOnto_apply_le {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) : ‖hF.orthogonalProjectionOnto x‖ ≤ ‖x‖ :=
  hF.norm_starProjection_apply_le x

theorem IsOrthogonallyComplemented.norm_starProjection_le {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : ‖hF.starProjection‖ ≤ 1 :=
  hF.starProjection.opNorm_le_bound zero_le_one fun x ↦ by
    simpa only [one_mul] using hF.norm_starProjection_apply_le x

theorem IsOrthogonallyComplemented.norm_orthogonalProjectionOnto_le {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : ‖hF.orthogonalProjectionOnto‖ ≤ 1 :=
  hF.orthogonalProjectionOnto.opNorm_le_bound zero_le_one fun x ↦ by
    simpa only [one_mul] using hF.norm_orthogonalProjectionOnto_apply_le x

/-- Uniqueness of the adjoint of `F.subtype`: any function adjoint to `F.subtype` equals
`hF.orthogonalProjectionOnto`. -/
theorem IsOrthogonallyComplemented.eq_orthogonalProjectionOnto_of_isAdjointPair
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) {P : E → F}
    (hP : LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := F)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip F.subtype P) :
    P = hF.orthogonalProjectionOnto := by
  have hL := hF.isAdjointPair_subtypeL_orthogonalProjectionOnto
  rw [coe_subtypeL] at hL
  exact (hL.unique_right_cstarModule hP).symm

/-- Uniqueness of the orthogonal projection onto `F`: any self-adjoint idempotent with range `F`
equals `hF.starProjection`. -/
theorem IsOrthogonallyComplemented.eq_starProjection_of_isAdjointPair_idempotent
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) {Q : E → E}
    (hQ : LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip Q Q)
    (hidem : ∀ x, Q (Q x) = Q x) (hrange : Set.range Q = (F : Set E)) :
    Q = hF.starProjection := by
  funext x
  refine (hF.eq_starProjection_of_mem_orthogonal
    (SetLike.mem_coe.mp (hrange ▸ Set.mem_range_self x)) ?_).symm
  refine sub_mem_orthogonal_of_inner_right fun u hu ↦ ?_
  have hu' : u ∈ Set.range Q := hrange.symm ▸ SetLike.mem_coe.mpr hu
  obtain ⟨v, rfl⟩ := hu'
  calc inner A (Q v) x = inner A (Q (Q v)) x := by rw [hidem v]
    _ = inner A (Q v) (Q x) := hQ.inner_eq_cstarModule (Q v) x

/-- An orthogonally complemented C⋆-submodule `F` yields a unitary direct-sum decomposition
`C⋆ᵐᵒᵈ(A, F × F.orthogonal) ≃ₗᵢ[ℂ] E` preserving inner products and the `A`-action. -/
noncomputable def IsOrthogonallyComplemented.orthogonalAddEquiv {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : C⋆ᵐᵒᵈ(A, F × F.orthogonal) ≃ₗᵢ[ℂ] E where
  toFun := F.orthogonalAddₗᵢ
  map_add' := F.orthogonalAddₗᵢ.map_add'
  map_smul' := F.orthogonalAddₗᵢ.map_smul'
  invFun x := (WithCStarModule.equiv A (F × F.orthogonal)).symm
    (hF.orthogonalProjectionOnto x, hF.orthogonal.orthogonalProjectionOnto x)
  left_inv p := by
    apply (WithCStarModule.equiv A (F × F.orthogonal)).injective
    ext
    · simp only [WithCStarModule.equiv_symm_fst, WithCStarModule.equiv_fst,
        orthogonalAddₗᵢ_apply, map_add, hF.orthogonalProjectionOnto_apply_self,
        hF.orthogonalProjectionOnto_apply_eq_zero_iff.mpr p.2.property, add_zero]
    · simp only [WithCStarModule.equiv_symm_snd, WithCStarModule.equiv_snd,
        orthogonalAddₗᵢ_apply, map_add, hF.orthogonal.orthogonalProjectionOnto_apply_self,
        hF.orthogonal.orthogonalProjectionOnto_apply_eq_zero_iff.mpr
          (le_orthogonal_orthogonal F p.1.property), zero_add]
  right_inv x := by
    simp only [orthogonalAddₗᵢ_apply, WithCStarModule.equiv_symm_fst,
      WithCStarModule.equiv_symm_snd, coe_orthogonalProjectionOnto_apply,
      hF.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply, add_sub_cancel]
  norm_map' := F.orthogonalAddₗᵢ.norm_map'

@[simp]
theorem IsOrthogonallyComplemented.orthogonalAddEquiv_apply {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (p : C⋆ᵐᵒᵈ(A, F × F.orthogonal)) :
    hF.orthogonalAddEquiv p = (p.1 : E) + (p.2 : E) :=
  F.orthogonalAddₗᵢ_apply p

@[simp]
theorem IsOrthogonallyComplemented.orthogonalAddEquiv_symm_fst {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) :
    (hF.orthogonalAddEquiv.symm x).1 = hF.orthogonalProjectionOnto x :=
  (rfl)

@[simp]
theorem IsOrthogonallyComplemented.orthogonalAddEquiv_symm_snd {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) :
    (hF.orthogonalAddEquiv.symm x).2 = hF.orthogonal.orthogonalProjectionOnto x :=
  (rfl)

theorem IsOrthogonallyComplemented.inner_orthogonalAddEquiv {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (p q : C⋆ᵐᵒᵈ(A, F × F.orthogonal)) :
    inner A (hF.orthogonalAddEquiv p) (hF.orthogonalAddEquiv q) = inner A p q :=
  F.inner_orthogonalAddₗᵢ p q

theorem IsOrthogonallyComplemented.orthogonalAddEquiv_smul_coeff {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (a : A) (p : C⋆ᵐᵒᵈ(A, F × F.orthogonal)) :
    hF.orthogonalAddEquiv (a • p) = a • hF.orthogonalAddEquiv p :=
  F.orthogonalAddₗᵢ_smul_coeff a p

theorem IsOrthogonallyComplemented.isAdjointPair_orthogonalAddEquiv {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    LinearMap.IsAdjointPair
      (CStarModule.innerₛₗ (A := A) (E := C⋆ᵐᵒᵈ(A, F × F.orthogonal))).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip
      hF.orthogonalAddEquiv hF.orthogonalAddEquiv.symm :=
  CStarModule.isAdjointPair_inner_iff.mpr fun p x ↦ by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      hF.inner_orthogonalAddEquiv p (hF.orthogonalAddEquiv.symm x)

/-- Bounded characterization: `F` is orthogonally complemented if and only if its continuous subtype
inclusion `F.subtypeL : F →L[ℂ] E` admits a bounded C⋆-module adjoint `P : E →L[ℂ] F`. Completeness
of `E` and closedness of `F` are not assumed. -/
theorem isOrthogonallyComplemented_iff_exists_adjoint_subtypeL {F : CStarSubmodule A E} :
    F.IsOrthogonallyComplemented ↔
      ∃ P : E →L[ℂ] F, LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := F)).flip
        (CStarModule.innerₛₗ (A := A) (E := E)).flip F.subtypeL P :=
  ⟨fun hF ↦ ⟨hF.orthogonalProjectionOnto, hF.isAdjointPair_subtypeL_orthogonalProjectionOnto⟩,
    fun ⟨P, hP⟩ ↦ isOrthogonallyComplemented_iff_exists_adjoint_subtype.mpr ⟨P, by
      rw [← coe_subtypeL]
      exact hP⟩⟩

/-- Bounded characterization: `F` is orthogonally complemented if and only if `F` is the range of a
bounded self-adjoint idempotent `Q : E →L[ℂ] E`. Completeness of `E` and closedness of `F` are not
assumed. -/
theorem isOrthogonallyComplemented_iff_exists_starProjection {F : CStarSubmodule A E} :
    F.IsOrthogonallyComplemented ↔
      ∃ Q : E →L[ℂ] E,
        LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
          (CStarModule.innerₛₗ (A := A) (E := E)).flip Q Q ∧
        IsIdempotentElem Q ∧ Q.range = F.toSubmodule := by
  constructor
  · intro hF
    exact ⟨hF.starProjection, hF.isAdjointPair_starProjection, hF.isIdempotentElem_starProjection,
      hF.range_starProjection⟩
  · rintro ⟨Q, hQ, hidem, hrange⟩
    refine isOrthogonallyComplemented_iff_exists_selfAdjoint_idempotent.mpr
      ⟨Q, hQ, fun x ↦ by simpa using DFunLike.congr_fun hidem.eq x, ?_⟩
    rw [← coe_toSubmodule, ← hrange]
    rfl

end ComplementedAnalytic

/-! ### Projection right ideals in the right self-module -/

section ProjectionIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private lemma isAdjointPair_mul_left {p : A} (hp : IsSelfAdjoint p) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := Aᵐᵒᵖ) (E := A)).flip
      (CStarModule.innerₛₗ (A := Aᵐᵒᵖ) (E := A)).flip (fun x ↦ p * x) (fun x ↦ p * x) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦ unop_injective <| by
    simp only [CStarModule.unop_inner_mulOpposite, star_mul, hp.star_eq, mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
private lemma mul_left_idempotent {p : A} (hp : IsIdempotentElem p) (x : A) :
    p * (p * x) = p * x := by
  rw [← mul_assoc, hp.eq]

omit [PartialOrder A] [StarOrderedRing A] in
private lemma range_mul_left {p : A} (hp : IsIdempotentElem p) :
    Set.range (fun x : A ↦ p * x) = (rightFixedSubmodule p : Set A) := by
  ext x
  exact (mem_rightFixedSubmodule_iff_exists_mul hp).symm

/-- Every star projection `p` in a (possibly nonunital) C⋆-algebra `A` defines an orthogonally
complemented right ideal `rightFixedSubmodule p = {x | p * x = x}` in `CStarModule Aᵐᵒᵖ A`. -/
theorem isOrthogonallyComplemented_rightFixedSubmodule {p : A} (hp : IsStarProjection p) :
    (rightFixedSubmodule p).IsOrthogonallyComplemented :=
  isOrthogonallyComplemented_iff_exists_selfAdjoint_idempotent.mpr
    ⟨fun x ↦ p * x, isAdjointPair_mul_left hp.isSelfAdjoint,
      mul_left_idempotent hp.isIdempotentElem, range_mul_left hp.isIdempotentElem⟩

/-- The orthogonal projection onto the right ideal `rightFixedSubmodule p` is left multiplication
by `p`. -/
theorem starProjection_rightFixedSubmodule {p : A} (hp : IsStarProjection p) (x : A) :
    (isOrthogonallyComplemented_rightFixedSubmodule hp).starProjection x = p * x := by
  have h := isOrthogonallyComplemented_rightFixedSubmodule hp
  exact (congrFun (h.eq_starProjection_of_isAdjointPair_idempotent
    (isAdjointPair_mul_left hp.isSelfAdjoint) (mul_left_idempotent hp.isIdempotentElem)
    (range_mul_left hp.isIdempotentElem)) x).symm

/-- The orthogonal complement of the projection right ideal `{x | p * x = x}` in the right
self-module `CStarModule Aᵐᵒᵖ A` is `{x | p * x = 0}`. -/
theorem mem_orthogonal_rightFixedSubmodule {p : A} (hp : IsStarProjection p) {x : A} :
    x ∈ (rightFixedSubmodule p).orthogonal ↔ p * x = 0 := by
  rw [← (isOrthogonallyComplemented_rightFixedSubmodule hp).starProjection_apply_eq_zero_iff,
    starProjection_rightFixedSubmodule hp x]

end ProjectionIdeal

/-! ### Comparison with Hilbert spaces (`A = ℂ`) -/

section ComplexComparison

open ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Over `A = ℂ`, `CStarSubmodule.orthogonal` agrees with Mathlib's `Submodule.orthogonal`. -/
theorem toSubmodule_orthogonal_complex (F : CStarSubmodule ℂ E) :
    F.orthogonal.toSubmodule = F.toSubmoduleᗮ := by
  ext y
  simp [Submodule.mem_orthogonal]

/-- Over `A = ℂ`, orthogonal complementability of a C⋆-submodule agrees with Mathlib's
`Submodule.HasOrthogonalProjection`. -/
theorem isOrthogonallyComplemented_complex_iff (F : CStarSubmodule ℂ E) :
    F.IsOrthogonallyComplemented ↔ F.toSubmodule.HasOrthogonalProjection := by
  rw [isOrthogonallyComplemented_iff_exists_add]
  constructor
  · intro h
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := h x
    refine ⟨y, hy, ?_⟩
    rw [add_sub_cancel_left, ← toSubmodule_orthogonal_complex]
    exact hz
  · intro h x
    obtain ⟨y, hy, hsub⟩ := h.exists_orthogonal x
    refine ⟨y, hy, x - y, ?_, add_sub_cancel _ _⟩
    rw [← mem_toSubmodule, toSubmodule_orthogonal_complex]
    exact hsub

/-- Over `A = ℂ` in a complete inner product space, every closed submodule is orthogonally
complemented. -/
theorem isOrthogonallyComplemented_of_isClosed_complex [CompleteSpace E] (F : CStarSubmodule ℂ E)
    (hF : IsClosed (F : Set E)) : F.IsOrthogonallyComplemented := by
  have _ : CompleteSpace F.toSubmodule := hF.completeSpace_coe
  exact (isOrthogonallyComplemented_complex_iff F).mpr inferInstance

/-- Over `A = ℂ`, `IsOrthogonallyComplemented.starProjection` agrees with Mathlib's
`Submodule.starProjection`. -/
theorem starProjection_complex (F : CStarSubmodule ℂ E) [F.toSubmodule.HasOrthogonalProjection] :
    ((isOrthogonallyComplemented_complex_iff F).mpr inferInstance).starProjection =
      F.toSubmodule.starProjection := by
  ext x
  refine ((isOrthogonallyComplemented_complex_iff F).mpr
    inferInstance).eq_starProjection_of_mem_orthogonal
    (F.toSubmodule.starProjection_apply_mem x) ?_
  rw [← mem_toSubmodule, toSubmodule_orthogonal_complex]
  exact F.toSubmodule.sub_starProjection_mem_orthogonal x

end ComplexComparison

/-! ### Non-complemented closed right ideals in `C(X, ℂ)` and `C([0, 1], ℂ)` -/

section ContinuousMapCounterexample

open ComplexOrder

/-- The right ideal `{f ∈ C(X, ℂ) | f x₀ = 0}` of continuous complex-valued functions vanishing at
`x₀`, viewed as a C⋆-submodule of the right self-module `C(X, ℂ)`. -/
def vanishingAt (X : Type*) [TopologicalSpace X] (x₀ : X) :
    CStarSubmodule C(X, ℂ)ᵐᵒᵖ C(X, ℂ) where
  carrier := {f : C(X, ℂ) | f x₀ = 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    simp [hf, hg]
  zero_mem' := rfl
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    simp [hf]
  smul_mem_coeff' g f hf := by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    simp [smul_eq_mul_unop, hf]

@[simp]
theorem mem_vanishingAt {X : Type*} [TopologicalSpace X] {x₀ : X} {f : C(X, ℂ)} :
    f ∈ vanishingAt X x₀ ↔ f x₀ = 0 :=
  (Iff.rfl)

theorem isClosed_vanishingAt {X : Type*} [TopologicalSpace X] (x₀ : X) :
    IsClosed (vanishingAt X x₀ : Set C(X, ℂ)) :=
  isClosed_eq (continuous_eval_const x₀) continuous_const

theorem vanishingAt_ne_top (X : Type*) [TopologicalSpace X] (x₀ : X) :
    vanishingAt X x₀ ≠ ⊤ := by
  intro h
  have h1 : (1 : C(X, ℂ)) ∈ vanishingAt X x₀ := h ▸ mem_top 1
  rw [mem_vanishingAt, ContinuousMap.one_apply] at h1
  exact one_ne_zero h1

/-- If `X` is compact Hausdorff and `{x₀}ᶜ` is dense (i.e. `x₀` is not isolated), then the closed
right ideal `vanishingAt X x₀` has orthogonal complement `⊥` in `C(X, ℂ)`. -/
theorem orthogonal_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    (vanishingAt X x₀).orthogonal = ⊥ := by
  let _ := CStarModule.distribSMul C(X, ℂ)ᵐᵒᵖ C(X, ℂ)
  rw [eq_bot_iff]
  intro g hg
  have hzero : Set.EqOn g (0 : C(X, ℂ)) ({x₀}ᶜ : Set X) := by
    intro y hy
    have hne : x₀ ≠ y := Ne.symm (Set.mem_compl_singleton_iff.mp hy)
    obtain ⟨φ, hφ0, hφ1, _⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := x₀)) (isClosed_singleton (x := y))
      (Set.disjoint_singleton.mpr hne)
    let f : C(X, ℂ) := ⟨fun x ↦ (φ x : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩
    have hf : f ∈ vanishingAt X x₀ := by
      rw [mem_vanishingAt]
      simp [f, hφ0 rfl]
    have hprod := (mem_orthogonal_unop_iff.mp hg) f hf
    rw [CStarModule.unop_inner_mulOpposite] at hprod
    have hval := congrArg (fun h : C(X, ℂ) ↦ h y) hprod
    simpa [f, hφ1 rfl] using hval
  exact ContinuousMap.ext fun x ↦ hzero.closure g.continuous continuous_const (hx₀ x)

theorem orthogonal_orthogonal_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    (vanishingAt X x₀).orthogonal.orthogonal = ⊤ := by
  rw [orthogonal_vanishingAt hx₀, orthogonal_bot]

/-- For any compact Hausdorff space `X` and non-isolated point `x₀`, the closed right ideal
`vanishingAt X x₀` is strictly smaller than its double orthogonal complement `⊤`. -/
theorem lt_orthogonal_orthogonal_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    vanishingAt X x₀ < (vanishingAt X x₀).orthogonal.orthogonal := by
  rw [orthogonal_orthogonal_vanishingAt hx₀]
  exact lt_top_iff_ne_top.mpr (vanishingAt_ne_top X x₀)

/-- For any compact Hausdorff space `X` and non-isolated point `x₀`, the closed right ideal
`vanishingAt X x₀` is not orthogonally complemented in `C(X, ℂ)`. -/
theorem not_isOrthogonallyComplemented_vanishingAt {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    ¬ (vanishingAt X x₀).IsOrthogonallyComplemented := by
  intro h
  exact (lt_orthogonal_orthogonal_vanishingAt hx₀).ne h.orthogonal_orthogonal.symm

/-- For any compact Hausdorff space `X` and non-isolated point `x₀`, the inclusion of the closed
right ideal `vanishingAt X x₀` into `C(X, ℂ)` has no C⋆-module adjoint. -/
theorem not_exists_adjoint_subtype_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    ¬ ∃ P : C(X, ℂ) → vanishingAt X x₀,
      LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := C(X, ℂ)ᵐᵒᵖ) (E := vanishingAt X x₀)).flip
        (CStarModule.innerₛₗ (A := C(X, ℂ)ᵐᵒᵖ) (E := C(X, ℂ))).flip
        (vanishingAt X x₀).subtype P := by
  rw [← isOrthogonallyComplemented_iff_exists_adjoint_subtype]
  exact not_isOrthogonallyComplemented_vanishingAt hx₀

/-- The closed right ideal `J = {f ∈ C([0, 1], ℂ) | f 0 = 0}` is strictly contained in `J⊥⊥ = ⊤`. -/
theorem lt_orthogonal_orthogonal_vanishingAt_unitInterval :
    vanishingAt unitInterval 0 < (vanishingAt unitInterval 0).orthogonal.orthogonal :=
  lt_orthogonal_orthogonal_vanishingAt (dense_compl_singleton (0 : unitInterval))

/-- The closed right ideal `J = {f ∈ C([0, 1], ℂ) | f 0 = 0}` is closed yet not orthogonally
complemented in `C([0, 1], ℂ)`. -/
theorem not_isOrthogonallyComplemented_vanishingAt_unitInterval :
    ¬ (vanishingAt unitInterval 0).IsOrthogonallyComplemented :=
  not_isOrthogonallyComplemented_vanishingAt (dense_compl_singleton (0 : unitInterval))

/-- The subtype inclusion of `J = {f ∈ C([0, 1], ℂ) | f 0 = 0}` into `C([0, 1], ℂ)` admits no
C⋆-module adjoint. -/
theorem not_exists_adjoint_subtype_vanishingAt_unitInterval :
    ¬ ∃ P : C(unitInterval, ℂ) → vanishingAt unitInterval 0,
      LinearMap.IsAdjointPair
        (CStarModule.innerₛₗ (A := C(unitInterval, ℂ)ᵐᵒᵖ) (E := vanishingAt unitInterval 0)).flip
        (CStarModule.innerₛₗ (A := C(unitInterval, ℂ)ᵐᵒᵖ) (E := C(unitInterval, ℂ))).flip
        (vanishingAt unitInterval 0).subtype P :=
  not_exists_adjoint_subtype_vanishingAt (dense_compl_singleton (0 : unitInterval))

end ContinuousMapCounterexample

end TauCeti.CStarSubmodule

namespace Submodule

open ComplexOrder TauCeti.CStarSubmodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Over `A = ℂ`, the orthogonal complement of a `Submodule ℂ E` viewed as a `CStarSubmodule ℂ E`
agrees with Mathlib's `Submodule.orthogonal`. -/
theorem toSubmodule_orthogonal_toCStarSubmodule_complex (K : Submodule ℂ E) :
    K.toCStarSubmodule.orthogonal.toSubmodule = Kᗮ := by
  rw [toSubmodule_orthogonal_complex, Submodule.toSubmodule_toCStarSubmodule,
    Submodule.restrictScalars_self]

/-- Over `A = ℂ`, a `Submodule ℂ E` is orthogonally complemented as a `CStarSubmodule ℂ E` if and
only if it satisfies `Submodule.HasOrthogonalProjection`. -/
theorem isOrthogonallyComplemented_toCStarSubmodule_complex_iff (K : Submodule ℂ E) :
    K.toCStarSubmodule.IsOrthogonallyComplemented ↔ K.HasOrthogonalProjection := by
  rw [isOrthogonallyComplemented_complex_iff, Submodule.toSubmodule_toCStarSubmodule,
    Submodule.restrictScalars_self]

end Submodule
