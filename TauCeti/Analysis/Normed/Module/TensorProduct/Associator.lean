/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion

/-!
# Symmetry, unit and associativity isometries of tensor norms

The linear equivalences `TensorProduct.comm`, `TensorProduct.lid`, `TensorProduct.rid` and
`TensorProduct.assoc` of algebraic tensor products preserve the projective and the injective
norms. The symmetry and scalar-unit statements for the seminorms themselves live beside their
definitions, in `TauCeti.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm` and
`TauCeti.Analysis.Normed.Module.TensorProduct.InjectiveSeminorm`. This file bundles the resulting
maps as linear isometric equivalences of `TauCeti.ProjectiveTensor` and `TauCeti.InjectiveTensor`,
proves that associativity preserves both norms, and extends the symmetry and the scalar-unit
isometries to the completed tensor products. Each isometry is
determined by its value on pure tensors, recorded as its coherence lemma: for instance
`(x ⊗ₜ y) ⊗ₜ z ↦ x ⊗ₜ (y ⊗ₜ z)` for the associativity isometry.

For the projective norm the proofs use only that it is the largest seminorm bounded on pure
tensors by the product of the norms, so they hold over any normed field. For the injective norm,
the scalar-unit isometry `𝕜 ⊗ε E ≃ E` holds over any nontrivially normed field, by evaluating the
induced operator at the identity functional of `𝕜`. Symmetry and associativity use the
description of the injective norm by pairings with functionals of norm at most one on each
factor, which relies on the Hahn–Banach theorem, so they are stated over `ℝ` and `ℂ`.

## Main declarations

* `TauCeti.ProjectiveTensor.comm`, `TauCeti.ProjectiveTensor.lid`,
  `TauCeti.ProjectiveTensor.rid` and `TauCeti.ProjectiveTensor.assoc`: the symmetry, scalar-unit
  and associativity isometries of projective tensor products, and their injective analogues in
  the namespace `TauCeti.InjectiveTensor`.
* `TauCeti.CompletedProjectiveTensor.comm` and `TauCeti.CompletedInjectiveTensor.comm`: the
  symmetry of the completed tensor products, together with the scalar-unit isometries onto the
  completion of `E`.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §§2.1, 3.1.
* V. Runde, *Lectures on Amenability*, Springer, 2002, Appendix B.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace ProjectiveTensor

section NormedField

variable {𝕜 E F G : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜 E F) in
/-- The symmetry `x ⊗ₜ y ↦ y ⊗ₜ x` of projective tensor products, an isometry. -/
noncomputable def comm : ProjectiveTensor 𝕜 E F ≃ₗᵢ[𝕜] ProjectiveTensor 𝕜 F E where
  toLinearEquiv := (linearEquiv 𝕜 E F).trans
    ((TensorProduct.comm 𝕜 E F).trans (linearEquiv 𝕜 F E).symm)
  norm_map' u := by simp [norm_def]

/-- The symmetry acts on the underlying tensor by `TensorProduct.comm`. -/
@[simp]
theorem comm_apply (u : ProjectiveTensor 𝕜 E F) :
    comm 𝕜 E F u = ⟨TensorProduct.comm 𝕜 E F u.toTensorProduct⟩ := by
  simp [comm]

/-- The symmetry sends `x ⊗ₜ y` to `y ⊗ₜ x`. -/
theorem comm_tmul (x : E) (y : F) : comm 𝕜 E F ⟨x ⊗ₜ y⟩ = ⟨y ⊗ₜ x⟩ := by
  simp

/-- The symmetry is its own inverse. -/
@[simp]
theorem comm_symm : (comm 𝕜 E F).symm = comm 𝕜 F E := by
  ext u : 1
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext
  simp

variable (𝕜 E) in
/-- The scalar-unit isometry `a ⊗ₜ x ↦ a • x` from `𝕜 ⊗π E` to `E`. -/
noncomputable def lid : ProjectiveTensor 𝕜 𝕜 E ≃ₗᵢ[𝕜] E where
  toLinearEquiv := (linearEquiv 𝕜 𝕜 E).trans (TensorProduct.lid 𝕜 E)
  norm_map' u := by simp [norm_def, TensorProduct.projectiveSeminorm_eq_norm_lid]

/-- The scalar-unit isometry acts on the underlying tensor by `TensorProduct.lid`. -/
@[simp]
theorem lid_apply (u : ProjectiveTensor 𝕜 𝕜 E) :
    lid 𝕜 E u = TensorProduct.lid 𝕜 E u.toTensorProduct := by
  simp [lid]

/-- The scalar-unit isometry sends `a ⊗ₜ x` to `a • x`. -/
theorem lid_tmul (a : 𝕜) (x : E) : lid 𝕜 E ⟨a ⊗ₜ x⟩ = a • x := by
  simp

/-- The inverse of the scalar-unit isometry sends `x` to `1 ⊗ₜ x`. -/
@[simp]
theorem lid_symm_apply (x : E) : (lid 𝕜 E).symm x = ⟨1 ⊗ₜ x⟩ :=
  (lid 𝕜 E).symm_apply_eq.2 <| by simp

variable (𝕜 E) in
/-- The scalar-unit isometry `x ⊗ₜ a ↦ a • x` from `E ⊗π 𝕜` to `E`. -/
noncomputable def rid : ProjectiveTensor 𝕜 E 𝕜 ≃ₗᵢ[𝕜] E where
  toLinearEquiv := (linearEquiv 𝕜 E 𝕜).trans (TensorProduct.rid 𝕜 E)
  norm_map' u := by simp [norm_def, TensorProduct.projectiveSeminorm_eq_norm_rid]

/-- The scalar-unit isometry acts on the underlying tensor by `TensorProduct.rid`. -/
@[simp]
theorem rid_apply (u : ProjectiveTensor 𝕜 E 𝕜) :
    rid 𝕜 E u = TensorProduct.rid 𝕜 E u.toTensorProduct := by
  simp [rid]

/-- The scalar-unit isometry sends `x ⊗ₜ a` to `a • x`. -/
theorem rid_tmul (x : E) (a : 𝕜) : rid 𝕜 E ⟨x ⊗ₜ a⟩ = a • x := by
  simp

/-- The inverse of the scalar-unit isometry sends `x` to `x ⊗ₜ 1`. -/
@[simp]
theorem rid_symm_apply (x : E) : (rid 𝕜 E).symm x = ⟨x ⊗ₜ 1⟩ :=
  (rid 𝕜 E).symm_apply_eq.2 <| by simp

/-- The rearrangement `(x ⊗ₜ y) ⊗ₜ z ↦ x ⊗ₜ (y ⊗ₜ z)` of iterated projective tensors, as a linear
equivalence; `ProjectiveTensor.assoc` shows that it is an isometry. -/
private noncomputable def assocAux :
    ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 E F) G ≃ₗ[𝕜]
      ProjectiveTensor 𝕜 E (ProjectiveTensor 𝕜 F G) :=
  (linearEquiv 𝕜 _ G).trans <|
    (TensorProduct.congr (linearEquiv 𝕜 E F) (LinearEquiv.refl 𝕜 G)).trans <|
      (TensorProduct.assoc 𝕜 E F G).trans <|
        (TensorProduct.congr (LinearEquiv.refl 𝕜 E) (linearEquiv 𝕜 F G).symm).trans
          (linearEquiv 𝕜 E _).symm

private theorem assocAux_tmul (x : E) (y : F) (z : G) :
    assocAux (𝕜 := 𝕜) ⟨⟨x ⊗ₜ y⟩ ⊗ₜ z⟩ = ⟨x ⊗ₜ ⟨y ⊗ₜ z⟩⟩ := by
  simp [assocAux]

private theorem assocAux_symm_tmul (x : E) (y : F) (z : G) :
    (assocAux (𝕜 := 𝕜)).symm ⟨x ⊗ₜ ⟨y ⊗ₜ z⟩⟩ = ⟨⟨x ⊗ₜ y⟩ ⊗ₜ z⟩ := by
  simp [assocAux]

/-- The rearrangement does not increase the projective norm: on `w ⊗ₜ z`, it is bounded by
`‖w‖ * ‖z‖` because, for fixed `z`, it is bounded on pure tensors `x ⊗ₜ y` by
`‖x‖ * (‖y‖ * ‖z‖)`. -/
private theorem norm_assocAux_le (v : ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 E F) G) :
    ‖assocAux v‖ ≤ ‖v‖ := by
  let f := (linearEquiv 𝕜 E (ProjectiveTensor 𝕜 F G)).toLinearMap ∘ₗ
    (assocAux (𝕜 := 𝕜) (E := E) (F := F) (G := G)).toLinearMap ∘ₗ
    (linearEquiv 𝕜 (ProjectiveTensor 𝕜 E F) G).symm.toLinearMap
  have key : ∀ w z, TensorProduct.projectiveSeminorm 𝕜 E (ProjectiveTensor 𝕜 F G)
      (f (w ⊗ₜ z)) ≤ 1 * (‖w‖ * ‖z‖) := fun w z ↦ by
    have := TensorProduct.apply_le_mul_projectiveSeminorm
      (p := TensorProduct.projectiveSeminorm 𝕜 E (ProjectiveTensor 𝕜 F G))
      (f := f ∘ₗ (TensorProduct.mk 𝕜 _ G).flip z ∘ₗ (linearEquiv 𝕜 E F).symm.toLinearMap)
      (norm_nonneg z) (fun x y ↦ by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          linearEquiv_symm_apply, LinearMap.flip_apply, TensorProduct.mk_apply, f,
          assocAux_tmul, linearEquiv_apply]
        calc _ ≤ ‖x‖ * ‖(⟨y ⊗ₜ z⟩ : ProjectiveTensor 𝕜 F G)‖ :=
              TensorProduct.projectiveSeminorm_tmul_le _ _
          _ ≤ ‖x‖ * (‖y‖ * ‖z‖) := by
              gcongr
              exact (norm_def _).trans_le (TensorProduct.projectiveSeminorm_tmul_le y z)
          _ = ‖z‖ * (‖x‖ * ‖y‖) := by ring) w.toTensorProduct
    simpa [norm_def, mul_comm ‖z‖] using this
  simpa [norm_def, f] using TensorProduct.apply_le_mul_projectiveSeminorm zero_le_one key
    v.toTensorProduct

/-- The inverse rearrangement does not increase the projective norm. -/
private theorem norm_assocAux_symm_le (v : ProjectiveTensor 𝕜 E (ProjectiveTensor 𝕜 F G)) :
    ‖assocAux.symm v‖ ≤ ‖v‖ := by
  let f := (linearEquiv 𝕜 (ProjectiveTensor 𝕜 E F) G).toLinearMap ∘ₗ
    (assocAux (𝕜 := 𝕜) (E := E) (F := F) (G := G)).symm.toLinearMap ∘ₗ
    (linearEquiv 𝕜 E (ProjectiveTensor 𝕜 F G)).symm.toLinearMap
  have key : ∀ x w, TensorProduct.projectiveSeminorm 𝕜 (ProjectiveTensor 𝕜 E F) G
      (f (x ⊗ₜ w)) ≤ 1 * (‖x‖ * ‖w‖) := fun x w ↦ by
    have := TensorProduct.apply_le_mul_projectiveSeminorm
      (p := TensorProduct.projectiveSeminorm 𝕜 (ProjectiveTensor 𝕜 E F) G)
      (f := f ∘ₗ TensorProduct.mk 𝕜 E _ x ∘ₗ (linearEquiv 𝕜 F G).symm.toLinearMap)
      (norm_nonneg x) (fun y z ↦ by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          linearEquiv_symm_apply, TensorProduct.mk_apply, f, assocAux_symm_tmul,
          linearEquiv_apply]
        calc _ ≤ ‖(⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 E F)‖ * ‖z‖ :=
              TensorProduct.projectiveSeminorm_tmul_le _ _
          _ ≤ (‖x‖ * ‖y‖) * ‖z‖ := by
              gcongr
              exact (norm_def _).trans_le (TensorProduct.projectiveSeminorm_tmul_le x y)
          _ = ‖x‖ * (‖y‖ * ‖z‖) := by ring) w.toTensorProduct
    simpa [norm_def] using this
  simpa [norm_def, f] using TensorProduct.apply_le_mul_projectiveSeminorm zero_le_one key
    v.toTensorProduct

variable (𝕜 E F G) in
/-- The associativity isometry `(x ⊗ₜ y) ⊗ₜ z ↦ x ⊗ₜ (y ⊗ₜ z)` of iterated projective tensor
products. -/
noncomputable def assoc :
    ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 E F) G ≃ₗᵢ[𝕜]
      ProjectiveTensor 𝕜 E (ProjectiveTensor 𝕜 F G) :=
  LinearIsometryEquiv.ofBounds assocAux norm_assocAux_le norm_assocAux_symm_le

/-- The associativity isometry sends `(x ⊗ₜ y) ⊗ₜ z` to `x ⊗ₜ (y ⊗ₜ z)`. -/
@[simp]
theorem assoc_tmul (x : E) (y : F) (z : G) :
    assoc 𝕜 E F G ⟨⟨x ⊗ₜ y⟩ ⊗ₜ z⟩ = ⟨x ⊗ₜ ⟨y ⊗ₜ z⟩⟩ := by
  simp [assoc, LinearIsometryEquiv.ofBounds, assocAux_tmul]

/-- The inverse associativity isometry sends `x ⊗ₜ (y ⊗ₜ z)` to `(x ⊗ₜ y) ⊗ₜ z`. -/
@[simp]
theorem assoc_symm_tmul (x : E) (y : F) (z : G) :
    (assoc 𝕜 E F G).symm ⟨x ⊗ₜ ⟨y ⊗ₜ z⟩⟩ = ⟨⟨x ⊗ₜ y⟩ ⊗ₜ z⟩ := by
  rw [LinearIsometryEquiv.symm_apply_eq, assoc_tmul]

end NormedField

end ProjectiveTensor

namespace InjectiveTensor

section NontriviallyNormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/-- The scalar-unit isometry `a ⊗ₜ x ↦ a • x` from `𝕜 ⊗ε E` to `E`. -/
noncomputable def lid : InjectiveTensor 𝕜 𝕜 E ≃ₗᵢ[𝕜] E where
  toLinearEquiv := (linearEquiv 𝕜 𝕜 E).trans (TensorProduct.lid 𝕜 E)
  norm_map' u := by simp [norm_def, TensorProduct.injectiveSeminorm_eq_norm_lid]

/-- The scalar-unit isometry acts on the underlying tensor by `TensorProduct.lid`. -/
@[simp]
theorem lid_apply (u : InjectiveTensor 𝕜 𝕜 E) :
    lid 𝕜 E u = TensorProduct.lid 𝕜 E u.toTensorProduct := by
  simp [lid]

/-- The scalar-unit isometry sends `a ⊗ₜ x` to `a • x`. -/
theorem lid_tmul (a : 𝕜) (x : E) : lid 𝕜 E ⟨a ⊗ₜ x⟩ = a • x := by
  simp

/-- The inverse of the scalar-unit isometry sends `x` to `1 ⊗ₜ x`. -/
@[simp]
theorem lid_symm_apply (x : E) : (lid 𝕜 E).symm x = ⟨1 ⊗ₜ x⟩ :=
  (lid 𝕜 E).symm_apply_eq.2 <| by simp

end NontriviallyNormedField

section RCLike

variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜 E F) in
/-- Over `ℝ` and `ℂ`, the symmetry `x ⊗ₜ y ↦ y ⊗ₜ x` of injective tensor products, an
isometry. -/
noncomputable def comm : InjectiveTensor 𝕜 E F ≃ₗᵢ[𝕜] InjectiveTensor 𝕜 F E where
  toLinearEquiv := (linearEquiv 𝕜 E F).trans
    ((TensorProduct.comm 𝕜 E F).trans (linearEquiv 𝕜 F E).symm)
  norm_map' u := by simp [norm_def]

/-- The symmetry acts on the underlying tensor by `TensorProduct.comm`. -/
@[simp]
theorem comm_apply (u : InjectiveTensor 𝕜 E F) :
    comm 𝕜 E F u = ⟨TensorProduct.comm 𝕜 E F u.toTensorProduct⟩ := by
  simp [comm]

/-- The symmetry sends `x ⊗ₜ y` to `y ⊗ₜ x`. -/
theorem comm_tmul (x : E) (y : F) : comm 𝕜 E F ⟨x ⊗ₜ y⟩ = ⟨y ⊗ₜ x⟩ := by
  simp

/-- The symmetry is its own inverse. -/
@[simp]
theorem comm_symm : (comm 𝕜 E F).symm = comm 𝕜 F E := by
  ext u : 1
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext
  simp

variable (𝕜 E) in
/-- Over `ℝ` and `ℂ`, the scalar-unit isometry `x ⊗ₜ a ↦ a • x` from `E ⊗ε 𝕜` to `E`. -/
noncomputable def rid : InjectiveTensor 𝕜 E 𝕜 ≃ₗᵢ[𝕜] E where
  toLinearEquiv := (linearEquiv 𝕜 E 𝕜).trans (TensorProduct.rid 𝕜 E)
  norm_map' u := by simp [norm_def, TensorProduct.injectiveSeminorm_eq_norm_rid]

/-- The scalar-unit isometry acts on the underlying tensor by `TensorProduct.rid`. -/
@[simp]
theorem rid_apply (u : InjectiveTensor 𝕜 E 𝕜) :
    rid 𝕜 E u = TensorProduct.rid 𝕜 E u.toTensorProduct := by
  simp [rid]

/-- The scalar-unit isometry sends `x ⊗ₜ a` to `a • x`. -/
theorem rid_tmul (x : E) (a : 𝕜) : rid 𝕜 E ⟨x ⊗ₜ a⟩ = a • x := by
  simp

/-- The inverse of the scalar-unit isometry sends `x` to `x ⊗ₜ 1`. -/
@[simp]
theorem rid_symm_apply (x : E) : (rid 𝕜 E).symm x = ⟨x ⊗ₜ 1⟩ :=
  (rid 𝕜 E).symm_apply_eq.2 <| by simp

/-- The rearrangement `(x ⊗ₜ y) ⊗ₜ z ↦ x ⊗ₜ (y ⊗ₜ z)` of iterated injective tensors, as a linear
equivalence; `InjectiveTensor.assoc` shows that it is an isometry. -/
private noncomputable def assocAux :
    InjectiveTensor 𝕜 (InjectiveTensor 𝕜 E F) G ≃ₗ[𝕜]
      InjectiveTensor 𝕜 E (InjectiveTensor 𝕜 F G) :=
  (linearEquiv 𝕜 _ G).trans <|
    (TensorProduct.congr (linearEquiv 𝕜 E F) (LinearEquiv.refl 𝕜 G)).trans <|
      (TensorProduct.assoc 𝕜 E F G).trans <|
        (TensorProduct.congr (LinearEquiv.refl 𝕜 E) (linearEquiv 𝕜 F G).symm).trans
          (linearEquiv 𝕜 E _).symm

private theorem assocAux_tmul (x : E) (y : F) (z : G) :
    assocAux (𝕜 := 𝕜) ⟨⟨x ⊗ₜ y⟩ ⊗ₜ z⟩ = ⟨x ⊗ₜ ⟨y ⊗ₜ z⟩⟩ := by
  simp [assocAux]

/-- The two nested contractions of `v` and of its rearrangement with functionals `f`, `g` and `h`
on the three factors agree: both are `∑ i, f (x i) * g (y i) * h (z i)` for any decomposition
`v = ∑ i, (x i ⊗ₜ y i) ⊗ₜ z i`. -/
private theorem apply_contractStrongDual_assocAux
    (v : InjectiveTensor 𝕜 (InjectiveTensor 𝕜 E F) G) (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F)
    (h : StrongDual 𝕜 G) :
    g (TensorProduct.contractStrongDual 𝕜 E F (TensorProduct.contractStrongDual 𝕜 G _
        (TensorProduct.comm 𝕜 _ G v.toTensorProduct) h).toTensorProduct f) =
      h (TensorProduct.contractStrongDual 𝕜 F G (TensorProduct.contractStrongDual 𝕜 E _
        (assocAux v).toTensorProduct f).toTensorProduct g) := by
  obtain ⟨v⟩ := v
  induction v with
  | tmul a z =>
    obtain ⟨t⟩ := a
    induction t with
    | tmul x y =>
      simp [assocAux_tmul]
      ring
    | add t t' ht ht' => simp_all [TensorProduct.add_tmul]
  | add v v' hv hv' => simp [hv, hv']

/-- The norm of `v ∈ (E ⊗ε F) ⊗ε G` is at most `C` iff all pairings of `v` with functionals of
norm at most one on the three factors are bounded by `C`. -/
private theorem norm_le_iff_forall_left {v : InjectiveTensor 𝕜 (InjectiveTensor 𝕜 E F) G} {C : ℝ}
    (hC : 0 ≤ C) :
    ‖v‖ ≤ C ↔ ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) (h : StrongDual 𝕜 G),
      ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ‖h‖ ≤ 1 →
        ‖g (TensorProduct.contractStrongDual 𝕜 E F (TensorProduct.contractStrongDual 𝕜 G _
          (TensorProduct.comm 𝕜 _ G v.toTensorProduct) h).toTensorProduct f)‖ ≤ C := by
  rw [norm_def, ← TensorProduct.injectiveSeminorm_comm,
    TensorProduct.injectiveSeminorm_le_iff_forall_norm_contractStrongDual_le hC]
  simp only [norm_def, TensorProduct.injectiveSeminorm_le_iff_forall_norm_le_one hC]
  exact ⟨fun H f g h hf hg hh ↦ H h hh f g hf hg, fun H h hh f g hf hg ↦ H f g h hf hg hh⟩

/-- The norm of `w ∈ E ⊗ε (F ⊗ε G)` is at most `C` iff all pairings of `w` with functionals of
norm at most one on the three factors are bounded by `C`. -/
private theorem norm_le_iff_forall_right {w : InjectiveTensor 𝕜 E (InjectiveTensor 𝕜 F G)} {C : ℝ}
    (hC : 0 ≤ C) :
    ‖w‖ ≤ C ↔ ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) (h : StrongDual 𝕜 G),
      ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ‖h‖ ≤ 1 →
        ‖h (TensorProduct.contractStrongDual 𝕜 F G (TensorProduct.contractStrongDual 𝕜 E _
          w.toTensorProduct f).toTensorProduct g)‖ ≤ C := by
  rw [norm_def, TensorProduct.injectiveSeminorm_le_iff_forall_norm_contractStrongDual_le hC]
  simp only [norm_def, TensorProduct.injectiveSeminorm_le_iff_forall_norm_le_one hC]
  exact ⟨fun H f g h hf hg hh ↦ H f hf g h hg hh, fun H f hf g h hg hh ↦ H f g h hf hg hh⟩

private theorem norm_assocAux (v : InjectiveTensor 𝕜 (InjectiveTensor 𝕜 E F) G) :
    ‖assocAux v‖ = ‖v‖ := by
  refine le_antisymm ((norm_le_iff_forall_right (norm_nonneg v)).2 fun f g h hf hg hh ↦ ?_)
    ((norm_le_iff_forall_left (norm_nonneg _)).2 fun f g h hf hg hh ↦ ?_)
  · rw [← apply_contractStrongDual_assocAux]
    exact (norm_le_iff_forall_left (norm_nonneg v)).1 le_rfl f g h hf hg hh
  · rw [apply_contractStrongDual_assocAux]
    exact (norm_le_iff_forall_right (norm_nonneg _)).1 le_rfl f g h hf hg hh

variable (𝕜 E F G) in
/-- Over `ℝ` and `ℂ`, the associativity isometry `(x ⊗ₜ y) ⊗ₜ z ↦ x ⊗ₜ (y ⊗ₜ z)` of iterated
injective tensor products. -/
noncomputable def assoc :
    InjectiveTensor 𝕜 (InjectiveTensor 𝕜 E F) G ≃ₗᵢ[𝕜]
      InjectiveTensor 𝕜 E (InjectiveTensor 𝕜 F G) where
  toLinearEquiv := assocAux
  norm_map' := norm_assocAux

/-- The associativity isometry sends `(x ⊗ₜ y) ⊗ₜ z` to `x ⊗ₜ (y ⊗ₜ z)`. -/
@[simp]
theorem assoc_tmul (x : E) (y : F) (z : G) :
    assoc 𝕜 E F G ⟨⟨x ⊗ₜ y⟩ ⊗ₜ z⟩ = ⟨x ⊗ₜ ⟨y ⊗ₜ z⟩⟩ := by
  simp [assoc, assocAux_tmul]

/-- The inverse associativity isometry sends `x ⊗ₜ (y ⊗ₜ z)` to `(x ⊗ₜ y) ⊗ₜ z`. -/
@[simp]
theorem assoc_symm_tmul (x : E) (y : F) (z : G) :
    (assoc 𝕜 E F G).symm ⟨x ⊗ₜ ⟨y ⊗ₜ z⟩⟩ = ⟨⟨x ⊗ₜ y⟩ ⊗ₜ z⟩ := by
  rw [LinearIsometryEquiv.symm_apply_eq, assoc_tmul]

end RCLike

end InjectiveTensor

open UniformSpace

namespace CompletedProjectiveTensor

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The symmetry `x ⊗ₜ y ↦ y ⊗ₜ x` of completed projective tensor products, an isometry. -/
noncomputable def comm : CompletedProjectiveTensor 𝕜 E F ≃ₗᵢ[𝕜] CompletedProjectiveTensor 𝕜 F E :=
  (ProjectiveTensor.comm 𝕜 E F).completion

/-- On algebraic tensors, the symmetry is `ProjectiveTensor.comm`. -/
@[simp]
theorem comm_coe (u : ProjectiveTensor 𝕜 E F) : comm 𝕜 E F u = ProjectiveTensor.comm 𝕜 E F u :=
  LinearIsometryEquiv.completion_apply_coe _ u

/-- The symmetry is its own inverse. -/
@[simp]
theorem comm_symm : (comm 𝕜 E F).symm = comm 𝕜 F E := by
  rw [comm, comm, LinearIsometryEquiv.completion_symm, ProjectiveTensor.comm_symm]

variable (𝕜 E) in
/-- The scalar-unit isometry `a ⊗ₜ x ↦ a • x` from `𝕜 ⊗̂π E` to the completion of `E`. -/
noncomputable def lid : CompletedProjectiveTensor 𝕜 𝕜 E ≃ₗᵢ[𝕜] Completion E :=
  (ProjectiveTensor.lid 𝕜 E).completion

/-- On algebraic tensors, the scalar-unit isometry is `ProjectiveTensor.lid`. -/
@[simp]
theorem lid_coe (u : ProjectiveTensor 𝕜 𝕜 E) : lid 𝕜 E u = ProjectiveTensor.lid 𝕜 E u :=
  LinearIsometryEquiv.completion_apply_coe _ u

/-- The inverse of the scalar-unit isometry sends `x` to `1 ⊗ₜ x`. -/
@[simp]
theorem lid_symm_coe (x : E) : (lid 𝕜 E).symm x = (⟨1 ⊗ₜ x⟩ : ProjectiveTensor 𝕜 𝕜 E) := by
  simp [lid]

variable (𝕜 E) in
/-- The scalar-unit isometry `x ⊗ₜ a ↦ a • x` from `E ⊗̂π 𝕜` to the completion of `E`. -/
noncomputable def rid : CompletedProjectiveTensor 𝕜 E 𝕜 ≃ₗᵢ[𝕜] Completion E :=
  (ProjectiveTensor.rid 𝕜 E).completion

/-- On algebraic tensors, the scalar-unit isometry is `ProjectiveTensor.rid`. -/
@[simp]
theorem rid_coe (u : ProjectiveTensor 𝕜 E 𝕜) : rid 𝕜 E u = ProjectiveTensor.rid 𝕜 E u :=
  LinearIsometryEquiv.completion_apply_coe _ u

/-- The inverse of the scalar-unit isometry sends `x` to `x ⊗ₜ 1`. -/
@[simp]
theorem rid_symm_coe (x : E) : (rid 𝕜 E).symm x = (⟨x ⊗ₜ 1⟩ : ProjectiveTensor 𝕜 E 𝕜) := by
  simp [rid]

end CompletedProjectiveTensor

namespace CompletedInjectiveTensor

section NontriviallyNormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/-- The scalar-unit isometry `a ⊗ₜ x ↦ a • x` from `𝕜 ⊗̂ε E` to the completion of `E`. -/
noncomputable def lid : CompletedInjectiveTensor 𝕜 𝕜 E ≃ₗᵢ[𝕜] Completion E :=
  (InjectiveTensor.lid 𝕜 E).completion

/-- On algebraic tensors, the scalar-unit isometry is `InjectiveTensor.lid`. -/
@[simp]
theorem lid_coe (u : InjectiveTensor 𝕜 𝕜 E) : lid 𝕜 E u = InjectiveTensor.lid 𝕜 E u :=
  LinearIsometryEquiv.completion_apply_coe _ u

/-- The inverse of the scalar-unit isometry sends `x` to `1 ⊗ₜ x`. -/
@[simp]
theorem lid_symm_coe (x : E) : (lid 𝕜 E).symm x = (⟨1 ⊗ₜ x⟩ : InjectiveTensor 𝕜 𝕜 E) := by
  simp [lid]

end NontriviallyNormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- Over `ℝ` and `ℂ`, the symmetry `x ⊗ₜ y ↦ y ⊗ₜ x` of completed injective tensor products, an
isometry. -/
noncomputable def comm : CompletedInjectiveTensor 𝕜 E F ≃ₗᵢ[𝕜] CompletedInjectiveTensor 𝕜 F E :=
  (InjectiveTensor.comm 𝕜 E F).completion

/-- On algebraic tensors, the symmetry is `InjectiveTensor.comm`. -/
@[simp]
theorem comm_coe (u : InjectiveTensor 𝕜 E F) : comm 𝕜 E F u = InjectiveTensor.comm 𝕜 E F u :=
  LinearIsometryEquiv.completion_apply_coe _ u

/-- The symmetry is its own inverse. -/
@[simp]
theorem comm_symm : (comm 𝕜 E F).symm = comm 𝕜 F E := by
  rw [comm, comm, LinearIsometryEquiv.completion_symm, InjectiveTensor.comm_symm]

variable (𝕜 E) in
/-- Over `ℝ` and `ℂ`, the scalar-unit isometry `x ⊗ₜ a ↦ a • x` from `E ⊗̂ε 𝕜` to the completion
of `E`. -/
noncomputable def rid : CompletedInjectiveTensor 𝕜 E 𝕜 ≃ₗᵢ[𝕜] Completion E :=
  (InjectiveTensor.rid 𝕜 E).completion

/-- On algebraic tensors, the scalar-unit isometry is `InjectiveTensor.rid`. -/
@[simp]
theorem rid_coe (u : InjectiveTensor 𝕜 E 𝕜) : rid 𝕜 E u = InjectiveTensor.rid 𝕜 E u :=
  LinearIsometryEquiv.completion_apply_coe _ u

/-- The inverse of the scalar-unit isometry sends `x` to `x ⊗ₜ 1`. -/
@[simp]
theorem rid_symm_coe (x : E) : (rid 𝕜 E).symm x = (⟨x ⊗ₜ 1⟩ : InjectiveTensor 𝕜 E 𝕜) := by
  simp [rid]

end RCLike

end CompletedInjectiveTensor

end TauCeti
