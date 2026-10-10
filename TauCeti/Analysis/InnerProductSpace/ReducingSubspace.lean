/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Reducing subspaces for bounded operators

General `RCLike` infrastructure for invariant and reducing subspaces of bounded
operators on inner-product spaces.  This module is independent of the
Davis--Kahan theory.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ContinuousLinearMap

/-- A subspace reduces a bounded operator when it and its orthogonal complement
are invariant. -/
@[expose]
def Reduces (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  (∀ x ∈ U, A x ∈ U) ∧ (∀ x ∈ Uᗮ, A x ∈ Uᗮ)

/-- An invariant subspace of a symmetric operator is reducing. -/
theorem IsSymmetric.reduces_of_invariant {A : E →L[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : A.Reduces U := by
  refine ⟨hU, ?_⟩
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  -- states the goal as the inner-product identity the structure lemma expects.
  change ⟪u, (A : E →ₗ[𝕜] E) x⟫_𝕜 = 0
  rw [← hA u x]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hx

/-- The orthogonal projection onto a reducing subspace commutes with the
operator. -/
theorem starProjection_comp_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) :
    U.starProjection ∘L A = A ∘L U.starProjection := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.starProjection (A x) = A (U.starProjection x)
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal x
  have hApx : A (U.starProjection x) ∈ U := hU.1 _ hpx
  have hArest : A (x - U.starProjection x) ∈ Uᗮ := hU.2 _ hrest
  have hsplit : A x = A (U.starProjection x) + A (x - U.starProjection x) := by
    calc
      A x = A (U.starProjection x + (x - U.starProjection x)) := by
        congr 1
        rw [add_comm, sub_add_cancel]
      _ = A (U.starProjection x) + A (x - U.starProjection x) := map_add A _ _
  rw [hsplit, map_add,
    Submodule.starProjection_eq_self_iff.mpr hApx,
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hArest,
    add_zero]

/-- Pointwise form of `starProjection_comp_comm_of_reduces`. -/
theorem starProjection_apply_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) (x : E) :
    U.starProjection (A x) = A (U.starProjection x) := by
  have h := congrArg (fun T : E →L[𝕜] E => T x)
    (starProjection_comp_comm_of_reduces A U hU)
  simpa only [ContinuousLinearMap.comp_apply] using h

end ContinuousLinearMap

namespace LinearMap

/-- **A symmetric map that nearly reduces `Z` moves `Zᗮ` only slightly into `Z`.**

If `‖T x - Z.starProjection (T x)‖ ≤ ρ ‖x‖` for every `x ∈ Z` -- the quantitative form of
"`T` reduces `Z`" -- then for `w ⊥ Z` the part of `T w` lying in `Z` is at most `ρ ‖w‖`.
Symmetry is what lets the estimate be read on either side of the inner product.

At `ρ = 0` this is the qualitative statement: a symmetric map reducing `Z` maps `Zᗮ` into
`Zᗮ`, which is `ContinuousLinearMap.IsSymmetric.reduces_of_invariant` above in bounded
form. -/
theorem norm_starProjection_apply_le_of_mem_orthogonal
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {Z : Submodule 𝕜 E} [Z.HasOrthogonalProjection] {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hrho : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ rho * ‖x‖)
    {w : E} (hw : w ∈ Zᗮ) : ‖Z.starProjection (T w)‖ ≤ rho * ‖w‖ := by
  set z := Z.starProjection (T w) with hz
  have hzZ : z ∈ Z := Z.starProjection_apply_mem _
  have hsq : ‖z‖ ^ 2 ≤ rho * ‖w‖ * ‖z‖ := by
    have h0 : ⟪z, z⟫_𝕜 = ⟪T w, z⟫_𝕜 := by
      conv_lhs => rw [hz]
      rw [Z.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hzZ]
    have h1 : ⟪T w, z⟫_𝕜 = ⟪w, T z - Z.starProjection (T z)⟫_𝕜 := by
      rw [hT w z, inner_sub_right,
        Submodule.inner_left_of_mem_orthogonal
          (Z.starProjection_apply_mem (T z)) hw, sub_zero]
    calc ‖z‖ ^ 2 = RCLike.re ⟪z, z⟫_𝕜 := (inner_self_eq_norm_sq z).symm
      _ = RCLike.re ⟪w, T z - Z.starProjection (T z)⟫_𝕜 := by rw [h0, h1]
      _ ≤ ‖⟪w, T z - Z.starProjection (T z)⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖w‖ * ‖T z - Z.starProjection (T z)‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (rho * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hrho z hzZ) (norm_nonneg w)
      _ = rho * ‖w‖ * ‖z‖ := by ac_rfl
  rcases eq_or_ne ‖z‖ 0 with h0 | h0
  · rw [h0]
    exact mul_nonneg hrho0 (norm_nonneg w)
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using hsq) hzpos

end LinearMap

namespace Submodule

/-- A subspace admitting an orthogonal projection is complete when the ambient
space is complete. -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsComplete (U : Set E) := by
  have hclosed : IsClosed ((Uᗮ)ᗮ : Set E) := Uᗮ.isClosed_orthogonal
  rw [Submodule.orthogonal_orthogonal] at hclosed
  exact hclosed.isComplete

end Submodule

namespace TauCeti.CompleteSubspace

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete, as an instance.

`scoped` rather than global, because the search `CompleteSpace ↥U` is one that
fires on every subspace coercion and the cost of that is not worth paying in
modules that do not need it.  Activate it with

```
open scoped TauCeti.CompleteSubspace
```

**Use this one.**  It exists because the same three-line `local instance` was
written out forty-three times across `DavisKahan` and `ForTauCeti`, each under a
different name.  That is not only duplication: the instance name is part of the
*elaborated type* of every theorem whose statement compresses to a subspace, so
two modules holding private copies state provably identical theorems that the
comparator, and any exact signature comparison, reports as different.  A new
copy would put that back. -/
scoped instance instCompleteSpaceCoeOfHasOrthogonalProjection
    {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

end TauCeti.CompleteSubspace
