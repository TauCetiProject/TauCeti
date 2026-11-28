/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Unitization
public import TauCeti.Algebra.Algebra.Unitization

/-!
# Continuity of the canonical ring homomorphisms of the normed unitization

For a normed algebra `A` over a nontrivially normed field `𝕜`, the scalar part
`Unitization 𝕜 A →+* 𝕜` is continuous (`Unitization.continuous_fstHom`). When `A` is unital, the
splitting `Unitization 𝕜 A ≃ₐ[𝕜] A × 𝕜`, `(r, a) ↦ (r • 1 + a, r)` (`Unitization.prodAlgEquiv`), is
a homeomorphism (`Unitization.continuous_prodAlgEquiv`,
`Unitization.continuous_prodAlgEquiv_symm`), and so the lift `(r, a) ↦ r • 1 + a` of the identity
of `A` is continuous (`Unitization.continuous_lift_id`).

These are stated for the bundled ring homomorphisms, so that they can be supplied where continuity
of a bundled ring homomorphism is an argument, such as that of `TauCeti.StableComponentGroup.map`.
-/

public section

noncomputable section

namespace Unitization

section General

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The scalar part `A⁺ → 𝕜` of the unitization is continuous, stated for the bundled ring
homomorphism so that it matches the continuity argument of `TauCeti.StableComponentGroup.map`. -/
theorem continuous_fstHom :
    Continuous (Unitization.fstHom 𝕜 A : Unitization 𝕜 A →+* 𝕜) :=
  Unitization.continuous_fst

end General

section Unital

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The splitting `A⁺ ≃+* A × 𝕜`, `(r, a) ↦ (r • 1 + a, r)`, of the unitization of a unital
normed algebra is continuous. -/
theorem continuous_prodAlgEquiv :
    Continuous ((Unitization.prodAlgEquiv 𝕜 A).toRingEquiv : Unitization 𝕜 A →+* A × 𝕜) := by
  have h : ⇑((Unitization.prodAlgEquiv 𝕜 A).toRingEquiv : Unitization 𝕜 A →+* A × 𝕜) =
      fun x ↦ (algebraMap 𝕜 A x.fst + x.snd, x.fst) :=
    funext fun x ↦ Unitization.prodAlgEquiv_apply x
  rw [h]
  exact (((continuous_algebraMap 𝕜 A).comp Unitization.continuous_fst).add
    Unitization.continuous_snd).prodMk Unitization.continuous_fst

/-- The inverse `A × 𝕜 ≃+* A⁺`, `(b, r) ↦ (r, b - r • 1)`, of the splitting of the unitization of
a unital normed algebra is continuous. -/
theorem continuous_prodAlgEquiv_symm :
    Continuous ((Unitization.prodAlgEquiv 𝕜 A).toRingEquiv.symm : A × 𝕜 →+* Unitization 𝕜 A) := by
  rw [Unitization.isUniformEmbedding_addEquiv.isUniformInducing.isInducing.continuous_iff]
  have h : ⇑(Unitization.addEquiv 𝕜 A) ∘
      ⇑((Unitization.prodAlgEquiv 𝕜 A).toRingEquiv.symm : A × 𝕜 →+* Unitization 𝕜 A) =
      fun y ↦ (y.2, y.1 - algebraMap 𝕜 A y.2) :=
    funext fun y ↦ Prod.ext (by simp) (by simp)
  rw [h]
  exact _root_.continuous_snd.prodMk
    (_root_.continuous_fst.sub ((continuous_algebraMap 𝕜 A).comp _root_.continuous_snd))

/-- The map `A⁺ →+* A`, `(r, a) ↦ r • 1 + a`, the lift of the identity of a unital normed algebra
`A` to its unitization, is continuous. -/
theorem continuous_lift_id :
    Continuous (Unitization.lift (NonUnitalAlgHom.id 𝕜 A) : Unitization 𝕜 A →+* A) := by
  rw [← Unitization.fst_comp_prodAlgEquiv, ← AlgEquiv.toRingEquiv_toRingHom]
  exact _root_.continuous_fst.comp (Unitization.continuous_prodAlgEquiv 𝕜 A)

end Unital

end Unitization
