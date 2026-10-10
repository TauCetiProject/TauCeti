/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: a new file alongside the orthogonal-projection API.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Gluing isometries across an orthogonal decomposition

Given `A ≤ H` with an orthogonal projection, `A' ≤ H'` likewise, and isometric
equivalences `f : A ≃ₗᵢ A'` and `g : Aᗮ ≃ₗᵢ A'ᗮ`, there is a global
`H ≃ₗᵢ H'` restricting to `f` on `A` and to `g` on `Aᗮ`.  It is built pointwise,
`x ↦ f (P_A x) + g (P_{Aᗮ} x)`, and is isometric by Pythagoras because the two
images land in orthogonal subspaces.

This is the step that turns a *list* of matched summands into a single unitary,
which is what a classification theorem has to produce.  In particular it is
brick (2) of the converse of the Halmos two-projection classification: on the
four elementary Halmos summands a glued map automatically intertwines both
projections, so the whole assembly reduces to iterating this lemma.

A decomposition into more than two pieces is not of that shape — the pieces are
mutually orthogonal but none is the ambient complement of another — so
`orthogonalSupGlue` gives the companion form `(A ⊔ B) ≃ₗᵢ (A' ⊔ B')` for
orthogonal `A, B`.  Iterating it handles any finite orthogonal family, and
`orthogonalGlue` then closes off against the ambient complement.

## Main results

* `TauCeti.orthogonalGlue`: the glued isometric equivalence across `A` and `Aᗮ`.
* `TauCeti.orthogonalGlue_apply_of_mem` / `_of_mem_orthogonal`: it restricts to
  `f` and to `g`.
* `TauCeti.map_orthogonalGlue`: it carries `A` onto `A'` (and `Aᗮ` onto `A'ᗮ`).
* `TauCeti.orthogonalSupGlue`: the same for two orthogonal summands, landing in
  `A' ⊔ B'`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
/-- Orthogonality of submodules is symmetric. -/
theorem le_orthogonal_symm {K L : Submodule 𝕜 H} (h : K ≤ Lᗮ) : L ≤ Kᗮ :=
  fun y hy => (Submodule.mem_orthogonal _ _).mpr fun _u hu =>
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp (h hu) y hy)

variable {A : Submodule 𝕜 H} [A.HasOrthogonalProjection]
  [Aᗮ.HasOrthogonalProjection]
variable {A' : Submodule 𝕜 H'} [A'.HasOrthogonalProjection]
  [A'ᗮ.HasOrthogonalProjection]

/-- The underlying linear map of the glue: send `x` to `f` of its `A`-component
plus `g` of its `Aᗮ`-component. -/
noncomputable def orthogonalGlueMap (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    H →ₗ[𝕜] H' :=
  (A'.subtype ∘ₗ (f.toLinearEquiv : A →ₗ[𝕜] A') ∘ₗ
      (A.orthogonalProjectionOnto : H →ₗ[𝕜] A)) +
    (A'ᗮ.subtype ∘ₗ (g.toLinearEquiv : Aᗮ →ₗ[𝕜] A'ᗮ) ∘ₗ
      (Aᗮ.orthogonalProjectionOnto : H →ₗ[𝕜] Aᗮ))

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- The glued map splits a vector along `A ⊕ Aᗮ` and applies the two pieces
separately. -/
theorem orthogonalGlueMap_apply (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) (x : H) :
    orthogonalGlueMap f g x =
      (f (A.orthogonalProjectionOnto x) : H') +
        (g (Aᗮ.orthogonalProjectionOnto x) : H') := by
  simp [orthogonalGlueMap]

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- The glue is norm-preserving: the two components land in orthogonal
subspaces, so Pythagoras applies on both sides. -/
theorem norm_orthogonalGlueMap (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) (x : H) :
    ‖orthogonalGlueMap f g x‖ = ‖x‖ := by
  have hperp' : ⟪(f (A.orthogonalProjectionOnto x) : H'),
      (g (Aᗮ.orthogonalProjectionOnto x) : H')⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (f (A.orthogonalProjectionOnto x)).2 (g (Aᗮ.orthogonalProjectionOnto x)).2
  have hperp : ⟪(A.starProjection x), (Aᗮ.starProjection x)⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (A.starProjection_apply_mem x)
      (Aᗮ.starProjection_apply_mem x)
  have hsplit : A.starProjection x + Aᗮ.starProjection x = x := by simp
  have hsq : ‖orthogonalGlueMap f g x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [orthogonalGlueMap_apply, @norm_add_sq 𝕜, hperp']
    conv_rhs => rw [← hsplit]
    rw [@norm_add_sq 𝕜, hperp]
    -- The isometries preserve each component's norm.
    have h1 : ‖(f (A.orthogonalProjectionOnto x) : H')‖ = ‖A.starProjection x‖ := by
      calc
        ‖(f (A.orthogonalProjectionOnto x) : H')‖ =
            ‖f (A.orthogonalProjectionOnto x)‖ :=
          Submodule.norm_coe (f (A.orthogonalProjectionOnto x))
        _ = ‖A.orthogonalProjectionOnto x‖ := f.norm_map _
        _ = ‖A.starProjection x‖ := by
          simpa only [Submodule.coe_orthogonalProjectionOnto_apply] using
            (Submodule.norm_coe (A.orthogonalProjectionOnto x)).symm
    have h2 : ‖(g (Aᗮ.orthogonalProjectionOnto x) : H')‖ = ‖Aᗮ.starProjection x‖ := by
      calc
        ‖(g (Aᗮ.orthogonalProjectionOnto x) : H')‖ =
            ‖g (Aᗮ.orthogonalProjectionOnto x)‖ :=
          Submodule.norm_coe (g (Aᗮ.orthogonalProjectionOnto x))
        _ = ‖Aᗮ.orthogonalProjectionOnto x‖ := g.norm_map _
        _ = ‖Aᗮ.starProjection x‖ := by
          simpa only [Submodule.coe_orthogonalProjectionOnto_apply] using
            (Submodule.norm_coe (Aᗮ.orthogonalProjectionOnto x)).symm
    rw [h1, h2]
  have h1 : (0 : ℝ) ≤ ‖orthogonalGlueMap f g x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  nlinarith

/-- The glue as a linear isometry. -/
noncomputable def orthogonalGlueIsometry (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    H →ₗᵢ[𝕜] H' where
  toLinearMap := orthogonalGlueMap f g
  norm_map' := norm_orthogonalGlueMap f g

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- The glued isometry has the same values as the underlying glued map; only
its bundling changes. -/
theorem orthogonalGlueIsometry_apply (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ)
    (x : H) :
    orthogonalGlueIsometry f g x =
      (f (A.orthogonalProjectionOnto x) : H') +
        (g (Aᗮ.orthogonalProjectionOnto x) : H') := by
  simp [orthogonalGlueIsometry, orthogonalGlueMap]

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- On `A` the glue is `f`. -/
theorem orthogonalGlueIsometry_apply_of_mem (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) {x : H} (hx : x ∈ A) :
    orthogonalGlueIsometry f g x = (f ⟨x, hx⟩ : H') := by
  have hA : A.orthogonalProjectionOnto x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hx
  have hAperp : Aᗮ.orthogonalProjectionOnto x = 0 := by
    apply Subtype.ext
    have : Aᗮ.starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      simpa using hx
    simpa using this
  rw [orthogonalGlueIsometry_apply, hA, hAperp]
  simp

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- On `Aᗮ` the glue is `g`. -/
theorem orthogonalGlueIsometry_apply_of_mem_orthogonal (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) {x : H} (hx : x ∈ Aᗮ) :
    orthogonalGlueIsometry f g x = (g ⟨x, hx⟩ : H') := by
  have hAperp : Aᗮ.orthogonalProjectionOnto x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hx
  have hA : A.orthogonalProjectionOnto x = 0 := by
    apply Subtype.ext
    have : A.starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact hx
    simpa using this
  rw [orthogonalGlueIsometry_apply, hA, hAperp]
  simp

/-- The glue is surjective: split the target across `A'` and `A'ᗮ` and pull each
piece back. -/
theorem orthogonalGlueIsometry_surjective (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) : Function.Surjective (orthogonalGlueIsometry f g) := by
  intro y
  refine ⟨(f.symm (A'.orthogonalProjectionOnto y) : H) +
    (g.symm (A'ᗮ.orthogonalProjectionOnto y) : H), ?_⟩
  rw [map_add,
    orthogonalGlueIsometry_apply_of_mem f g (f.symm (A'.orthogonalProjectionOnto y)).2,
    orthogonalGlueIsometry_apply_of_mem_orthogonal f g
      (g.symm (A'ᗮ.orthogonalProjectionOnto y)).2]
  simp

/-- **The glued isometric equivalence.** -/
noncomputable def orthogonalGlue (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    H ≃ₗᵢ[𝕜] H' :=
  LinearIsometryEquiv.ofSurjective (orthogonalGlueIsometry f g)
    (orthogonalGlueIsometry_surjective f g)

/-- The glued equivalence has the same values as the glued isometry; only its
bundling changes. -/
@[simp] theorem orthogonalGlue_apply (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ)
    (x : H) : orthogonalGlue f g x = orthogonalGlueIsometry f g x := by
  simp [orthogonalGlue]

/-- On `A` the glued equivalence is `f`. -/
theorem orthogonalGlue_apply_of_mem (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ)
    {x : H} (hx : x ∈ A) : orthogonalGlue f g x = (f ⟨x, hx⟩ : H') :=
  orthogonalGlueIsometry_apply_of_mem f g hx

/-- On `Aᗮ` the glued equivalence is `g`. -/
theorem orthogonalGlue_apply_of_mem_orthogonal (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) {x : H} (hx : x ∈ Aᗮ) :
    orthogonalGlue f g x = (g ⟨x, hx⟩ : H') :=
  orthogonalGlueIsometry_apply_of_mem_orthogonal f g hx

/-- **The glue carries `A` onto `A'`.**  This is what a classification proof
needs: the assembled unitary matches the prescribed subspaces. -/
theorem map_orthogonalGlue (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    A.map (orthogonalGlue f g).toLinearMap = A' := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [show (orthogonalGlue f g).toLinearMap x = orthogonalGlue f g x from rfl,
      orthogonalGlue_apply_of_mem f g hx]
    exact (f ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(f.symm ⟨y, hy⟩ : H), (f.symm ⟨y, hy⟩).2, ?_⟩
    rw [show (orthogonalGlue f g).toLinearMap (f.symm ⟨y, hy⟩ : H) =
      orthogonalGlue f g (f.symm ⟨y, hy⟩ : H) from rfl,
      orthogonalGlue_apply_of_mem f g (f.symm ⟨y, hy⟩).2]
    simp

/-- The glue carries `Aᗮ` onto `A'ᗮ`. -/
theorem map_orthogonalGlue_orthogonal (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    Aᗮ.map (orthogonalGlue f g).toLinearMap = A'ᗮ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [show (orthogonalGlue f g).toLinearMap x = orthogonalGlue f g x from rfl,
      orthogonalGlue_apply_of_mem_orthogonal f g hx]
    exact (g ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(g.symm ⟨y, hy⟩ : H), (g.symm ⟨y, hy⟩).2, ?_⟩
    rw [show (orthogonalGlue f g).toLinearMap (g.symm ⟨y, hy⟩ : H) =
      orthogonalGlue f g (g.symm ⟨y, hy⟩ : H) from rfl,
      orthogonalGlue_apply_of_mem_orthogonal f g (g.symm ⟨y, hy⟩).2]
    simp

/-! ## Gluing across an orthogonal pair of summands

`orthogonalGlue` glues a subspace to its *ambient* orthogonal complement.  A
decomposition into more than two pieces is not of that shape — the pieces are
mutually orthogonal but none is the ambient complement of another — so the
companion form below glues `A` and `B` into `A ⊔ B`, and iterating it handles
any finite orthogonal family.
-/

section Sup

variable {A B : Submodule 𝕜 H} [A.HasOrthogonalProjection]
  [B.HasOrthogonalProjection]
variable {A' B' : Submodule 𝕜 H'} [A'.HasOrthogonalProjection]
  [B'.HasOrthogonalProjection]

/-- The ambient map underlying the `sup` glue.  Defined on all of `H`; only its
restriction to `A ⊔ B` is meaningful. -/
noncomputable def supGlueAmbient (f : A ≃ₗᵢ[𝕜] A') (g : B ≃ₗᵢ[𝕜] B') :
    H →ₗ[𝕜] H' :=
  (A'.subtype ∘ₗ (f.toLinearEquiv : A →ₗ[𝕜] A') ∘ₗ
      (A.orthogonalProjectionOnto : H →ₗ[𝕜] A)) +
    (B'.subtype ∘ₗ (g.toLinearEquiv : B →ₗ[𝕜] B') ∘ₗ
      (B.orthogonalProjectionOnto : H →ₗ[𝕜] B))

omit [A'.HasOrthogonalProjection] [B'.HasOrthogonalProjection] in
/-- The ambient glue of two isometries on orthogonal summands splits its
argument along `A` and `B` and applies the two pieces separately.  Unlike
`orthogonalGlueMap_apply` the two summands need not exhaust `H`. -/
theorem supGlueAmbient_apply (f : A ≃ₗᵢ[𝕜] A') (g : B ≃ₗᵢ[𝕜] B') (x : H) :
    supGlueAmbient f g x =
      (f (A.orthogonalProjectionOnto x) : H') +
        (g (B.orthogonalProjectionOnto x) : H') := by
  simp [supGlueAmbient]

omit [A'.HasOrthogonalProjection] [B'.HasOrthogonalProjection] in
/-- On `A` the ambient map is `f`; the `B`-component vanishes because `A ⊥ B`. -/
theorem supGlueAmbient_apply_of_mem_left (hAB : A ≤ Bᗮ) (f : A ≃ₗᵢ[𝕜] A')
    (g : B ≃ₗᵢ[𝕜] B') {x : H} (hx : x ∈ A) :
    supGlueAmbient f g x = (f ⟨x, hx⟩ : H') := by
  have hA : A.orthogonalProjectionOnto x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hx
  have hB : B.orthogonalProjectionOnto x = 0 := by
    apply Subtype.ext
    have : B.starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact hAB hx
    simpa using this
  rw [supGlueAmbient_apply, hA, hB]
  simp

omit [A'.HasOrthogonalProjection] [B'.HasOrthogonalProjection] in
/-- On `B` the ambient map is `g`. -/
theorem supGlueAmbient_apply_of_mem_right (hAB : A ≤ Bᗮ) (f : A ≃ₗᵢ[𝕜] A')
    (g : B ≃ₗᵢ[𝕜] B') {x : H} (hx : x ∈ B) :
    supGlueAmbient f g x = (g ⟨x, hx⟩ : H') := by
  have hBA : B ≤ Aᗮ := le_orthogonal_symm hAB
  have hB : B.orthogonalProjectionOnto x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hx
  have hA : A.orthogonalProjectionOnto x = 0 := by
    apply Subtype.ext
    have : A.starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact hBA hx
    simpa using this
  rw [supGlueAmbient_apply, hA, hB]
  simp

omit [A'.HasOrthogonalProjection] [B'.HasOrthogonalProjection] in
/-- On `A ⊔ B` the ambient map is norm-preserving. -/
theorem norm_supGlueAmbient_of_mem_sup (hAB : A ≤ Bᗮ) (hAB' : A' ≤ B'ᗮ)
    (f : A ≃ₗᵢ[𝕜] A') (g : B ≃ₗᵢ[𝕜] B') {x : H} (hx : x ∈ A ⊔ B) :
    ‖supGlueAmbient f g x‖ = ‖x‖ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, supGlueAmbient_apply_of_mem_left hAB f g ha,
    supGlueAmbient_apply_of_mem_right hAB f g hb]
  have hperp' : ⟪(f ⟨a, ha⟩ : H'), (g ⟨b, hb⟩ : H')⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (f ⟨a, ha⟩).2
      (le_orthogonal_symm hAB' (g ⟨b, hb⟩).2)
  have hperp : ⟪a, b⟫_𝕜 = 0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp (hAB ha) b hb)
  have hfa : ‖(f ⟨a, ha⟩ : H')‖ = ‖a‖ := by
    calc
      ‖(f ⟨a, ha⟩ : H')‖ = ‖f ⟨a, ha⟩‖ := Submodule.norm_coe _
      _ = ‖(⟨a, ha⟩ : A)‖ := f.norm_map _
      _ = ‖a‖ := (Submodule.norm_coe (⟨a, ha⟩ : A)).symm
  have hgb : ‖(g ⟨b, hb⟩ : H')‖ = ‖b‖ := by
    calc
      ‖(g ⟨b, hb⟩ : H')‖ = ‖g ⟨b, hb⟩‖ := Submodule.norm_coe _
      _ = ‖(⟨b, hb⟩ : B)‖ := g.norm_map _
      _ = ‖b‖ := (Submodule.norm_coe (⟨b, hb⟩ : B)).symm
  have hsq : ‖(f ⟨a, ha⟩ : H') + (g ⟨b, hb⟩ : H')‖ ^ 2 = ‖a + b‖ ^ 2 := by
    rw [@norm_add_sq 𝕜, @norm_add_sq 𝕜, hperp', hperp, hfa, hgb]
  have h1 : (0 : ℝ) ≤ ‖(f ⟨a, ha⟩ : H') + (g ⟨b, hb⟩ : H')‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖a + b‖ := norm_nonneg _
  nlinarith

omit [A'.HasOrthogonalProjection] [B'.HasOrthogonalProjection] in
/-- The ambient map sends `A ⊔ B` into `A' ⊔ B'`. -/
theorem supGlueAmbient_mem_sup (hAB : A ≤ Bᗮ) (f : A ≃ₗᵢ[𝕜] A')
    (g : B ≃ₗᵢ[𝕜] B') {x : H} (hx : x ∈ A ⊔ B) :
    supGlueAmbient f g x ∈ A' ⊔ B' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, supGlueAmbient_apply_of_mem_left hAB f g ha,
    supGlueAmbient_apply_of_mem_right hAB f g hb]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (f ⟨a, ha⟩).2)
    (Submodule.mem_sup_right (g ⟨b, hb⟩).2)

omit [A'.HasOrthogonalProjection] [B'.HasOrthogonalProjection] in
/-- Every element of `A' ⊔ B'` is hit from `A ⊔ B`. -/
theorem supGlueAmbient_surjOn (hAB : A ≤ Bᗮ) (f : A ≃ₗᵢ[𝕜] A')
    (g : B ≃ₗᵢ[𝕜] B') {y : H'} (hy : y ∈ A' ⊔ B') :
    ∃ x ∈ A ⊔ B, supGlueAmbient f g x = y := by
  obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
  refine ⟨(f.symm ⟨a', ha'⟩ : H) + (g.symm ⟨b', hb'⟩ : H),
    Submodule.add_mem _ (Submodule.mem_sup_left (f.symm ⟨a', ha'⟩).2)
      (Submodule.mem_sup_right (g.symm ⟨b', hb'⟩).2), ?_⟩
  rw [map_add, supGlueAmbient_apply_of_mem_left hAB f g (f.symm ⟨a', ha'⟩).2,
    supGlueAmbient_apply_of_mem_right hAB f g (g.symm ⟨b', hb'⟩).2]
  simp

/-- **Gluing across an orthogonal pair of summands.**  Matched isometries on two
orthogonal subspaces assemble into one on their join. -/
noncomputable def orthogonalSupGlue (hAB : A ≤ Bᗮ) (hAB' : A' ≤ B'ᗮ)
    (f : A ≃ₗᵢ[𝕜] A') (g : B ≃ₗᵢ[𝕜] B') :
    (A ⊔ B : Submodule 𝕜 H) ≃ₗᵢ[𝕜] (A' ⊔ B' : Submodule 𝕜 H') := by
  refine LinearIsometryEquiv.ofSurjective
    { toLinearMap :=
        LinearMap.codRestrict (A' ⊔ B')
          ((supGlueAmbient f g).domRestrict (A ⊔ B))
          (fun x => supGlueAmbient_mem_sup hAB f g x.2)
      norm_map' := fun x => ?_ } ?_
  · change ‖supGlueAmbient f g (x : H)‖ = ‖x‖
    rw [norm_supGlueAmbient_of_mem_sup hAB hAB' f g x.2, Submodule.norm_coe]
  · intro y
    obtain ⟨x, hx, hxy⟩ := supGlueAmbient_surjOn hAB f g y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

omit [A'.HasOrthogonalProjection] [B'.HasOrthogonalProjection] in
/-- The glue on `A ⊔ B` is the restriction of the ambient glue: its underlying
vector is computed by `supGlueAmbient`. -/
theorem coe_orthogonalSupGlue (hAB : A ≤ Bᗮ) (hAB' : A' ≤ B'ᗮ)
    (f : A ≃ₗᵢ[𝕜] A') (g : B ≃ₗᵢ[𝕜] B') (x : (A ⊔ B : Submodule 𝕜 H)) :
    (orthogonalSupGlue hAB hAB' f g x : H') = supGlueAmbient f g (x : H) := by
  rfl

end Sup

end TauCeti
