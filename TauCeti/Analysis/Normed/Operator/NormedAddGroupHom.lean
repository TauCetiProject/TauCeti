/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Comparing linear and additive operator norms

A continuous semilinear map and a bounded additive homomorphism with the same values have the
same operator norm (`ContinuousLinearMap.norm_eq_normedAddGroupHom`). When the scalar ring
homomorphism is isometric, `ContinuousLinearMap.toNormedAddGroupHom` forgets scalar linearity to
produce a `NormedAddGroupHom` with the same underlying function, operator norm, kernel, additive
group operations, identity, and composition. This lets quotient, completion, and norm-lifting
results for bounded additive homomorphisms apply directly to continuous linear operators.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

section NormEq

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ : 𝕜 →+* 𝕜₂}

/-- A continuous semilinear map and a bounded additive homomorphism with the same values have
the same operator norm. -/
theorem norm_eq_normedAddGroupHom (f : E →SL[σ] F) (g : NormedAddGroupHom E F)
    (h : ∀ x, f x = g x) : ‖f‖ = ‖g‖ := by
  rw [norm_def, NormedAddGroupHom.norm_def]
  simp only [h]

end NormEq

section ToNormedAddGroupHom

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- Forget scalar linearity of a continuous semilinear map with isometric ring homomorphism,
viewing it as a bounded additive group homomorphism. -/
def toNormedAddGroupHom (f : E →SL[σ] F) : NormedAddGroupHom E F where
  toFun := f
  map_add' := f.map_add
  bound' := ⟨‖f‖, f.le_opNorm⟩

/-- Coercing `f.toNormedAddGroupHom` to a function recovers `f`. -/
@[simp]
theorem coe_toNormedAddGroupHom (f : E →SL[σ] F) : ⇑f.toNormedAddGroupHom = f := (rfl)

/-- Applying `f.toNormedAddGroupHom` evaluates `f`. -/
theorem toNormedAddGroupHom_apply (f : E →SL[σ] F) (x : E) : f.toNormedAddGroupHom x = f x := (rfl)

/-- The underlying `AddMonoidHom` of `f.toNormedAddGroupHom` is `f.toLinearMap.toAddMonoidHom`. -/
@[simp]
theorem toAddMonoidHom_toNormedAddGroupHom (f : E →SL[σ] F) :
    f.toNormedAddGroupHom.toAddMonoidHom = f.toLinearMap.toAddMonoidHom := (rfl)

/-- `ContinuousLinearMap.toNormedAddGroupHom` is injective. -/
theorem toNormedAddGroupHom_injective :
    Function.Injective (toNormedAddGroupHom : (E →SL[σ] F) → NormedAddGroupHom E F) :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

/-- Two continuous semilinear maps have equal `NormedAddGroupHom`s if and only if they are equal. -/
@[simp]
theorem toNormedAddGroupHom_inj {f g : E →SL[σ] F} :
    f.toNormedAddGroupHom = g.toNormedAddGroupHom ↔ f = g :=
  toNormedAddGroupHom_injective.eq_iff

/-- Forgetting scalar linearity preserves the operator norm. -/
@[simp]
theorem norm_toNormedAddGroupHom (f : E →SL[σ] F) : ‖f.toNormedAddGroupHom‖ = ‖f‖ :=
  (f.norm_eq_normedAddGroupHom _ fun _ ↦ rfl).symm

/-- Forgetting scalar linearity preserves the nonnegative operator norm. -/
@[simp]
theorem nnnorm_toNormedAddGroupHom (f : E →SL[σ] F) : ‖f.toNormedAddGroupHom‖₊ = ‖f‖₊ :=
  NNReal.eq f.norm_toNormedAddGroupHom

/-- The kernel of `f.toNormedAddGroupHom` is the additive subgroup underlying `f.ker`. -/
@[simp]
theorem ker_toNormedAddGroupHom (f : E →SL[σ] F) :
    f.toNormedAddGroupHom.ker = f.ker.toAddSubgroup :=
  AddSubgroup.ext fun _ ↦ Iff.rfl

/-- `ContinuousLinearMap.toNormedAddGroupHom` maps `0` to `0`. -/
@[simp]
theorem toNormedAddGroupHom_zero : (0 : E →SL[σ] F).toNormedAddGroupHom = 0 :=
  NormedAddGroupHom.ext fun _ ↦ rfl

/-- `ContinuousLinearMap.toNormedAddGroupHom` preserves addition. -/
@[simp]
theorem toNormedAddGroupHom_add (f g : E →SL[σ] F) :
    (f + g).toNormedAddGroupHom = f.toNormedAddGroupHom + g.toNormedAddGroupHom :=
  NormedAddGroupHom.ext fun _ ↦ rfl

/-- `ContinuousLinearMap.toNormedAddGroupHom` preserves negation. -/
@[simp]
theorem toNormedAddGroupHom_neg (f : E →SL[σ] F) :
    (-f).toNormedAddGroupHom = -f.toNormedAddGroupHom :=
  NormedAddGroupHom.ext fun _ ↦ rfl

/-- `ContinuousLinearMap.toNormedAddGroupHom` preserves subtraction. -/
@[simp]
theorem toNormedAddGroupHom_sub (f g : E →SL[σ] F) :
    (f - g).toNormedAddGroupHom = f.toNormedAddGroupHom - g.toNormedAddGroupHom :=
  NormedAddGroupHom.ext fun _ ↦ rfl

/-- `ContinuousLinearMap.toNormedAddGroupHom` maps `id` to `NormedAddGroupHom.id`. -/
@[simp]
theorem toNormedAddGroupHom_id :
    (ContinuousLinearMap.id 𝕜 E).toNormedAddGroupHom = NormedAddGroupHom.id E :=
  NormedAddGroupHom.ext fun _ ↦ rfl

/-- `ContinuousLinearMap.toNormedAddGroupHom` commutes with composition. -/
@[simp]
theorem toNormedAddGroupHom_comp {𝕜₃ G : Type*} [NontriviallyNormedField 𝕜₃]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜₃ G]
    {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ σ₂₃ σ₁₃]
    [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
    (g : F →SL[σ₂₃] G) (f : E →SL[σ] F) :
    (g.comp f).toNormedAddGroupHom = g.toNormedAddGroupHom.comp f.toNormedAddGroupHom :=
  NormedAddGroupHom.ext fun _ ↦ rfl

end ToNormedAddGroupHom

end ContinuousLinearMap
