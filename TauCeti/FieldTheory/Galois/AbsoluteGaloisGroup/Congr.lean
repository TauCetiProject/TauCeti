/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

/-!
# Absolute Galois groups of isomorphic fields

A field isomorphism identifies separable closures and hence, contravariantly, their absolute
Galois groups.  This file packages that identification as an isomorphism of topological groups.
It is useful when a field is presented through a canonical completion or another isomorphic
model, while Galois-cohomological constructions are available on the standard model.

## Main definition

* `TauCeti.separableClosureRingEquivCongr`: the chosen equivalence of separable closures induced
  by a field isomorphism.
* `TauCeti.absoluteGaloisGroupCongr`: the continuous group equivalence induced by a field
  isomorphism.
-/

public noncomputable section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L]

/-- A field isomorphism induces a chosen ring equivalence of separable closures. -/
def separableClosureRingEquivCongr (e : K ≃+* L) :
    SeparableClosure L ≃+* SeparableClosure K := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] L := { e with commutes' := fun _ => rfl }
  let σ : L →ₐ[K] SeparableClosure K :=
    (Algebra.ofId K (SeparableClosure K)).comp eA.symm.toAlgHom
  exact separableClosureRingEquiv K L σ

/-- A field isomorphism `K ≃+* L` induces a contravariant continuous equivalence
`G_L ≃ₜ* G_K` of absolute Galois groups. -/
def absoluteGaloisGroupCongr (e : K ≃+* L) :
    AbsoluteGaloisGroup L ≃ₜ* AbsoluteGaloisGroup K := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] L := { e with commutes' := fun _ => rfl }
  let σ : L →ₐ[K] SeparableClosure K :=
    (Algebra.ofId K (SeparableClosure K)).comp eA.symm.toAlgHom
  have hrange : σ.fieldRange = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact IntermediateField.mem_bot.mpr ⟨e.symm y, rfl⟩
    · intro hx
      obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.mp hx
      exact ⟨e y, congrArg (algebraMap K (SeparableClosure K)) (eA.symm_apply_apply y)⟩
  let ψ := absoluteGaloisGroupEquivFixingSubgroup K L σ
  have htop : σ.fieldRange.fixingSubgroup = ⊤ := by simp [hrange]
  let f : AbsoluteGaloisGroup L →* AbsoluteGaloisGroup K :=
    σ.fieldRange.fixingSubgroup.subtype.comp ψ.toMonoidHom
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => ψ.injective (Subtype.ext h), fun g => ?_⟩
    have hg : g ∈ σ.fieldRange.fixingSubgroup := by rw [htop]; trivial
    refine ⟨ψ.symm ⟨g, hg⟩, ?_⟩
    exact congrArg Subtype.val (ψ.apply_symm_apply ⟨g, hg⟩)
  let φ := MulEquiv.ofBijective f hf
  have hcont : Continuous φ := continuous_subtype_val.comp ψ.continuous
  exact
    { φ with
      continuous_toFun := hcont
      continuous_invFun := (Continuous.homeoOfEquivCompactToT2 hcont).symm.continuous }

/-- The absolute-Galois-group equivalence induced by a field isomorphism acts by conjugation
through the chosen equivalence of separable closures. -/
theorem absoluteGaloisGroupCongr_apply (e : K ≃+* L) (g : AbsoluteGaloisGroup L)
    (x : SeparableClosure K) :
    absoluteGaloisGroupCongr e g x =
      separableClosureRingEquivCongr e
        (g ((separableClosureRingEquivCongr e).symm x)) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] L := { e with commutes' := fun _ => rfl }
  let σ : L →ₐ[K] SeparableClosure K :=
    (Algebra.ofId K (SeparableClosure K)).comp eA.symm.toAlgHom
  exact absoluteGaloisGroupEquivFixingSubgroup_apply K L σ g x

end TauCeti
