/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.Projective.Topology
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Completed projective tensor products

This file forms the separated completion of a projective tensor product and extends
seminorm-bounded multilinear maps to it.  The resulting map is characterized by its values on
pure tensors.  Tensor products of seminorm-bounded linear maps extend functorially to the
completions.

The completion is Mathlib's `UniformSpace.Completion`, applied to the canonical uniformity of the
projective topological additive group.  Consequently it simultaneously identifies points that no
defining seminorm separates and completes the resulting Hausdorff space.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {ι 𝕜 : Type*} [NormedField 𝕜]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
variable {σ : ι → Type*}

namespace ProjectiveTensorProduct

variable (p : ∀ i, SeminormFamily 𝕜 (E i) (σ i)) [Fintype ι]

/-- The translation-invariant uniformity associated to the projective tensor topology. -/
noncomputable instance instUniformSpace : UniformSpace (ProjectiveTensorProduct p) :=
  IsTopologicalAddGroup.rightUniformSpace (ProjectiveTensorProduct p)

noncomputable instance instIsUniformAddGroup :
    IsUniformAddGroup (ProjectiveTensorProduct p) :=
  isUniformAddGroup_of_addCommGroup

noncomputable instance instUniformContinuousConstSMul :
    UniformContinuousConstSMul 𝕜 (ProjectiveTensorProduct p) :=
  uniformContinuousConstSMul_of_continuousConstSMul 𝕜 (ProjectiveTensorProduct p)

end ProjectiveTensorProduct

/-- The separated completion of the algebraic tensor product with its projective topology. -/
abbrev CompletedProjectiveTensorProduct
    (p : ∀ i, SeminormFamily 𝕜 (E i) (σ i)) [Fintype ι] :=
  UniformSpace.Completion (ProjectiveTensorProduct p)

namespace CompletedProjectiveTensorProduct

open UniformSpace

variable (p : ∀ i, SeminormFamily 𝕜 (E i) (σ i)) [Fintype ι]

/-- The canonical continuous pure-tensor map into the completed projective tensor product. -/
noncomputable def tprod [∀ i, TopologicalSpace (E i)]
    (hp : ∀ i, WithSeminorms (p i)) :
    ContinuousMultilinearMap 𝕜 E (CompletedProjectiveTensorProduct p) where
  toMultilinearMap :=
    Completion.toComplL.toLinearMap.compMultilinearMap (ProjectiveTensorProduct.tprod p)
  cont := Completion.continuous_toCompl.comp (ProjectiveTensorProduct.continuous_tprod p hp)

@[simp]
theorem tprod_apply [∀ i, TopologicalSpace (E i)] (hp : ∀ i, WithSeminorms (p i))
    (x : ∀ i, E i) :
    tprod p hp x =
      (ProjectiveTensorProduct.tprod p x : CompletedProjectiveTensorProduct p) :=
  (rfl)

variable {F : Type*} [AddCommGroup F] [UniformSpace F] [Module 𝕜 F]
  [IsUniformAddGroup F] [UniformContinuousConstSMul 𝕜 F] [T0Space F] [CompleteSpace F]

/-- Extend a multilinear map satisfying projective seminorm bounds to the completed projective
tensor product.  The selected factor seminorms and the bound may depend on the target seminorm. -/
noncomputable def lift {τ : Type*} (q : SeminormFamily 𝕜 F τ) (hq : WithSeminorms q)
    (f : MultilinearMap 𝕜 E F)
    (hf : ∀ j, ∃ (s : ∀ i, Finset (σ i)) (C : NNReal),
      ∀ x, q j (f x) ≤ (C : ℝ) * ∏ i, (s i).sup (p i) (x i)) :
    CompletedProjectiveTensorProduct p →L[𝕜] F :=
  (⟨ProjectiveTensorProduct.lift p f,
    ProjectiveTensorProduct.continuous_lift p q hq f hf⟩ :
      ProjectiveTensorProduct p →L[𝕜] F).fromCompletion

/-- The extended map agrees with the original multilinear map on pure tensors. -/
@[simp]
theorem lift_tprod {τ : Type*} (q : SeminormFamily 𝕜 F τ) (hq : WithSeminorms q)
    (f : MultilinearMap 𝕜 E F)
    (hf : ∀ j, ∃ (s : ∀ i, Finset (σ i)) (C : NNReal),
      ∀ x, q j (f x) ≤ (C : ℝ) * ∏ i, (s i).sup (p i) (x i))
    (x : ∀ i, E i) :
    lift p q hq f hf (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct p) = f x := by
  simp [lift]

omit [UniformContinuousConstSMul 𝕜 F] [CompleteSpace F] in
/-- A continuous linear map from a completed projective tensor product is determined by its
values on pure tensors. -/
@[ext]
theorem continuousLinearMap_ext {g h : CompletedProjectiveTensorProduct p →L[𝕜] F}
    (hgh : ∀ x : ∀ i, E i, g (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct p) =
      h (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct p)) :
    g = h := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq g.continuous h.continuous
  | ih z =>
      let g₀ : ProjectiveTensorProduct p →ₗ[𝕜] F :=
        { toFun := fun x => g (x : CompletedProjectiveTensorProduct p)
          map_add' := by
            intro x y
            rw [Completion.coe_add, map_add]
          map_smul' := by
            intro c x
            rw [Completion.coe_smul, map_smul]
            rfl }
      let h₀ : ProjectiveTensorProduct p →ₗ[𝕜] F :=
        { toFun := fun x => h (x : CompletedProjectiveTensorProduct p)
          map_add' := by
            intro x y
            rw [Completion.coe_add, map_add]
          map_smul' := by
            intro c x
            rw [Completion.coe_smul, map_smul]
            rfl }
      have hz : g₀ = h₀ := by
        apply ProjectiveTensorProduct.linearMap_ext p
        intro x
        dsimp only [g₀, h₀]
        simpa only [LinearMap.coe_mk, AddHom.coe_mk,
          ProjectiveTensorProduct.tprod_apply] using hgh x
      exact LinearMap.congr_fun hz z

/-- The completed lift is the unique continuous linear map with the prescribed values on pure
tensors. -/
theorem lift_unique {τ : Type*} (q : SeminormFamily 𝕜 F τ) (hq : WithSeminorms q)
    (f : MultilinearMap 𝕜 E F)
    (hf : ∀ j, ∃ (s : ∀ i, Finset (σ i)) (C : NNReal),
      ∀ x, q j (f x) ≤ (C : ℝ) * ∏ i, (s i).sup (p i) (x i))
    (g : CompletedProjectiveTensorProduct p →L[𝕜] F)
    (hg : ∀ x : ∀ i, E i,
      g (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct p) = f x) :
    g = lift p q hq f hf := by
  apply continuousLinearMap_ext p
  intro x
  rw [hg]
  exact (lift_tprod p q hq f hf x).symm

variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)]
variable {τ : ι → Type*} (q : ∀ i, SeminormFamily 𝕜 (G i) (τ i))

/-- Tensor a seminorm-bounded family of linear maps and extend it to the completed projective
tensor products. -/
noncomputable def map (f : ∀ i, E i →ₗ[𝕜] G i)
    (hf : ∀ i, Seminorm.IsBounded (p i) (q i) (f i)) :
    CompletedProjectiveTensorProduct p →L[𝕜] CompletedProjectiveTensorProduct q :=
  (⟨ProjectiveTensorProduct.map p q f,
    ProjectiveTensorProduct.continuous_map p q f hf⟩ :
      ProjectiveTensorProduct p →L[𝕜] ProjectiveTensorProduct q).completion

@[simp]
theorem map_tprod (f : ∀ i, E i →ₗ[𝕜] G i)
    (hf : ∀ i, Seminorm.IsBounded (p i) (q i) (f i)) (x : ∀ i, E i) :
    map p q f hf (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct p) =
      (⟨⨂ₜ[𝕜] i, f i (x i)⟩ : ProjectiveTensorProduct q) := by
  simp [map]

/-- The completion of the identity tensor map is the identity, independently of the chosen
boundedness proof. -/
@[simp]
theorem map_id (hf : ∀ i, Seminorm.IsBounded (p i) (p i) LinearMap.id) :
    map p p (fun _ => LinearMap.id) hf = ContinuousLinearMap.id 𝕜 _ := by
  apply continuousLinearMap_ext p
  intro x
  rw [map_tprod]
  simp only [LinearMap.id_apply, ContinuousLinearMap.id_apply]

variable {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module 𝕜 (H i)]
variable {υ : ι → Type*} (r : ∀ i, SeminormFamily 𝕜 (H i) (υ i))

/-- Completed tensor maps preserve composition. -/
theorem map_comp (f : ∀ i, E i →ₗ[𝕜] G i) (g : ∀ i, G i →ₗ[𝕜] H i)
    (hf : ∀ i, Seminorm.IsBounded (p i) (q i) (f i))
    (hg : ∀ i, Seminorm.IsBounded (q i) (r i) (g i))
    (hgf : ∀ i, Seminorm.IsBounded (p i) (r i) ((g i).comp (f i))) :
    map p r (fun i => (g i).comp (f i)) hgf = (map q r g hg).comp (map p q f hf) := by
  apply continuousLinearMap_ext p
  intro x
  rw [map_tprod, ContinuousLinearMap.comp_apply, map_tprod, map_tprod]
  congr 2

end CompletedProjectiveTensorProduct

end TauCeti
