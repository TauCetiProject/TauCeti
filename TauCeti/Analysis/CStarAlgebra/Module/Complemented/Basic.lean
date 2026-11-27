/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
public import TauCeti.Analysis.CStarAlgebra.Module.Orthogonal

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
* For any star projection `p` in a (possibly nonunital) C⋆-algebra `A`, the right ideal
  `CStarSubmodule.rightFixedSubmodule p = {x | p * x = x}` is orthogonally complemented in the
  right self-module `CStarModule Aᵐᵒᵖ A`, with orthogonal projection `x ↦ p * x`.

For comparison with `Submodule.HasOrthogonalProjection` when `A = ℂ`, see
`TauCeti.Analysis.CStarAlgebra.Module.Complemented.Complex`. For the standard counterexample of a
non-complemented closed right ideal in `C(X, ℂ)` and `C([0, 1], ℂ)`, see
`TauCeti.Analysis.CStarAlgebra.Module.Complemented.Counterexample`.

## Main declarations

* `TauCeti.CStarSubmodule.IsOrthogonallyComplemented`: `F ⊔ F.orthogonal = ⊤`.
* `TauCeti.CStarSubmodule.IsOrthogonallyComplemented.orthogonalProjectionOnto`,
  `TauCeti.CStarSubmodule.IsOrthogonallyComplemented.starProjection`,
  `TauCeti.CStarSubmodule.IsOrthogonallyComplemented.orthogonalAddEquiv`: canonical orthogonal
  projections and unitary direct-sum decomposition.
* `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_adjoint_subtype`,
  `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_adjoint_subtypeL`,
  `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_selfAdjoint_idempotent`,
  `TauCeti.CStarSubmodule.isOrthogonallyComplemented_iff_exists_bounded_selfAdjoint_idempotent`:
  characterizations of orthogonal complementability.
* `TauCeti.CStarSubmodule.isOrthogonallyComplemented_rightFixedSubmodule`,
  `TauCeti.CStarSubmodule.starProjection_rightFixedSubmodule`,
  `TauCeti.CStarSubmodule.mem_orthogonal_rightFixedSubmodule`: projection right ideals.

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

private lemma IsOrthogonallyComplemented.sub_projection_mem_orthogonal
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) (x : E) :
    x - F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x ∈
      F.orthogonal := by
  have hdecomp := Submodule.projection_add_projection_eq_self hF.isCompl_toSubmodule x
  have heq : x - F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x =
      F.orthogonal.toSubmodule.projection F.toSubmodule hF.isCompl_toSubmodule.symm x :=
    sub_eq_of_eq_add' hdecomp.symm
  exact heq ▸ Submodule.projection_apply_mem hF.isCompl_toSubmodule.symm x

private lemma IsOrthogonallyComplemented.inner_sub_projection_of_mem
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) {u : E} (hu : u ∈ F) (x : E) :
    inner A u
      (x - F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x) = 0 :=
  inner_right_of_mem_orthogonal hu (hF.sub_projection_mem_orthogonal x)

private lemma IsOrthogonallyComplemented.inner_eq_inner_projection_of_mem
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) {u : E} (hu : u ∈ F) (x : E) :
    inner A u x =
      inner A u (F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x) := by
  have horth := hF.inner_sub_projection_of_mem hu x
  rwa [CStarModule.inner_sub_right, sub_eq_zero] at horth

private lemma IsOrthogonallyComplemented.isAdjointPair_projection
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule)
      (F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule) := by
  refine CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦ ?_
  let Q := F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule
  have h1 : inner A (Q x) y = inner A (Q x) (Q y) :=
    hF.inner_eq_inner_projection_of_mem (Submodule.projection_apply_mem hF.isCompl_toSubmodule x) y
  have h2 : inner A (Q y) x = inner A (Q y) (Q x) :=
    hF.inner_eq_inner_projection_of_mem (Submodule.projection_apply_mem hF.isCompl_toSubmodule y) x
  calc inner A (Q x) y = inner A (Q x) (Q y) := h1
    _ = star (inner A (Q y) (Q x)) := (CStarModule.star_inner _ _).symm
    _ = star (inner A (Q y) x) := by rw [h2]
    _ = inner A x (Q y) := CStarModule.star_inner _ _

private lemma sub_mem_orthogonal_of_isAdjointPair_idempotent
    {F : CStarSubmodule A E} {Q : E → E}
    (hQ : LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip Q Q)
    (hidem : ∀ x, Q (Q x) = Q x) (hrange : Set.range Q = (F : Set E)) (x : E) :
    x - Q x ∈ F.orthogonal := by
  refine sub_mem_orthogonal_of_inner_right fun u hu ↦ ?_
  have hu' : u ∈ Set.range Q := hrange.symm ▸ SetLike.mem_coe.mpr hu
  obtain ⟨v, rfl⟩ := hu'
  calc inner A (Q v) x = inner A (Q (Q v)) x := by rw [hidem v]
    _ = inner A (Q v) (Q x) := hQ.inner_eq_cstarModule (Q v) x

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
    refine ⟨Q, hF.isAdjointPair_projection, fun x ↦ ?_, ?_⟩
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
    exact ⟨Q x, hQx, x - Q x, sub_mem_orthogonal_of_isAdjointPair_idempotent hQ hidem hrange x,
      add_sub_cancel _ _⟩

end ComplementedAlgebraic

section ComplementedNormed

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E]
  [CStarModule A E]

private lemma IsOrthogonallyComplemented.isAdjointPair_subtype_projectionOnto
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := F)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip F.subtype
      (F.toSubmodule.projectionOnto F.orthogonal.toSubmodule hF.isCompl_toSubmodule) := by
  refine CStarModule.isAdjointPair_inner_iff.mpr fun u x ↦ ?_
  rw [subtype_apply, inner_coe]
  exact hF.inner_eq_inner_projection_of_mem u.property x

/-- Characterization without analytic C⋆-algebra assumptions: `F` is orthogonally complemented if
and only if its subtype inclusion `F.subtype : F → E` admits a (plain-function) C⋆-module adjoint
`P : E → F`. -/
theorem isOrthogonallyComplemented_iff_exists_adjoint_subtype {F : CStarSubmodule A E} :
    F.IsOrthogonallyComplemented ↔
      ∃ P : E → F, LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := F)).flip
        (CStarModule.innerₛₗ (A := A) (E := E)).flip F.subtype P := by
  constructor
  · intro hF
    exact ⟨F.toSubmodule.projectionOnto F.orthogonal.toSubmodule hF.isCompl_toSubmodule,
      hF.isAdjointPair_subtype_projectionOnto⟩
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
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

private lemma IsOrthogonallyComplemented.norm_projection_apply_le
    {F : CStarSubmodule A E} (hF : F.IsOrthogonallyComplemented) (x : E) :
    ‖F.toSubmodule.projection F.orthogonal.toSubmodule hF.isCompl_toSubmodule x‖ ≤ ‖x‖ := by
  simpa only [add_sub_cancel] using CStarModule.norm_le_norm_add_right_of_inner_eq_zero
    (hF.inner_sub_projection_of_mem (Submodule.projection_apply_mem hF.isCompl_toSubmodule x) x)

/-- An orthogonally complemented C⋆-submodule and its orthogonal complement form topological
complements (without assuming completeness of `E`). -/
theorem IsOrthogonallyComplemented.isTopCompl {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) : F.toSubmodule.IsTopCompl F.orthogonal.toSubmodule where
  isCompl := hF.isCompl_toSubmodule
  continuous_projection := by
    refine AddMonoidHomClass.continuous_of_bound _ 1 fun x ↦ ?_
    simpa only [one_mul] using hF.norm_projection_apply_le x

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
    (hF : F.IsOrthogonallyComplemented) (x : E) : x - hF.starProjection x ∈ F.orthogonal :=
  hF.sub_projection_mem_orthogonal x

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
  rw [coe_subtypeL]
  exact hF.isAdjointPair_subtype_projectionOnto

/-- `hF.starProjection` is self-adjoint for the `A`-valued inner product. -/
theorem IsOrthogonallyComplemented.isAdjointPair_starProjection {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (CStarModule.innerₛₗ (A := A) (E := E)).flip hF.starProjection hF.starProjection :=
  hF.isAdjointPair_projection

theorem IsOrthogonallyComplemented.orthogonalProjectionOnto_smul_coeff {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (a : A) (x : E) :
    hF.orthogonalProjectionOnto (a • x) = a • hF.orthogonalProjectionOnto x :=
  hF.isAdjointPair_subtypeL_orthogonalProjectionOnto.symm_cstarModule.map_smul_coeff_cstarModule a x

theorem IsOrthogonallyComplemented.starProjection_smul_coeff {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (a : A) (x : E) :
    hF.starProjection (a • x) = a • hF.starProjection x :=
  hF.isAdjointPair_starProjection.map_smul_coeff_cstarModule a x

theorem IsOrthogonallyComplemented.norm_starProjection_apply_le {F : CStarSubmodule A E}
    (hF : F.IsOrthogonallyComplemented) (x : E) : ‖hF.starProjection x‖ ≤ ‖x‖ :=
  hF.norm_projection_apply_le x

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
  exact (hF.eq_starProjection_of_mem_orthogonal
    (SetLike.mem_coe.mp (hrange ▸ Set.mem_range_self x))
    (sub_mem_orthogonal_of_isAdjointPair_idempotent hQ hidem hrange x)).symm

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
theorem isOrthogonallyComplemented_iff_exists_bounded_selfAdjoint_idempotent
    {F : CStarSubmodule A E} :
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
    rw [← coe_toSubmodule, ← hrange, LinearMap.coe_range, ContinuousLinearMap.coe_coe]

end ComplementedAnalytic

section ComplementedDirectSum

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

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

end ComplementedDirectSum

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

end TauCeti.CStarSubmodule
