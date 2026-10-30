/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

/-!
# Absolute Galois groups of isomorphic fields

A field isomorphism identifies separable closures and hence, contravariantly, their absolute
Galois groups.  This file packages that identification as an isomorphism of topological groups.
It is useful when a field is presented through a canonical completion or another isomorphic
model, while Galois-cohomological constructions are available on the standard model.

These equivalences underlie the transport of cohomological Brauer groups along field
isomorphisms in `TauCeti.NumberTheory.ClassFieldTheory.Brauer.Congr`.

## Main definitions

* `RingEquiv.separableClosureCongr`: the chosen equivalence of separable closures induced by a
  field isomorphism.
* `RingEquiv.absoluteGaloisGroupCongr`: the continuous group equivalence induced by a field
  isomorphism.
-/

public noncomputable section

open TauCeti

namespace RingEquiv

variable {K L : Type*} [Field K] [Field L]

/-- A field isomorphism induces a chosen ring equivalence of separable closures. -/
def separableClosureCongr (e : K ≃+* L) :
    SeparableClosure L ≃+* SeparableClosure K := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] L := { e with commutes' := fun _ => rfl }
  let σ : L →ₐ[K] SeparableClosure K :=
    (Algebra.ofId K (SeparableClosure K)).comp eA.symm.toAlgHom
  exact separableClosureRingEquiv K L σ

/-- The chosen equivalence of separable closures extends `e.symm`. -/
@[simp]
theorem separableClosureCongr_algebraMap (e : K ≃+* L) (y : L) :
    e.separableClosureCongr (algebraMap L (SeparableClosure L) y) =
      algebraMap K (SeparableClosure K) (e.symm y) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact separableClosureRingEquiv_algebraMap K L _ y

/-- The inverse of the chosen equivalence of separable closures extends `e`. -/
@[simp]
theorem separableClosureCongr_symm_algebraMap (e : K ≃+* L) (x : K) :
    e.separableClosureCongr.symm (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (e x) := by
  rw [RingEquiv.symm_apply_eq, separableClosureCongr_algebraMap, e.symm_apply_apply]

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
@[simp]
theorem absoluteGaloisGroupCongr_apply (e : K ≃+* L) (g : AbsoluteGaloisGroup L)
    (x : SeparableClosure K) :
    absoluteGaloisGroupCongr e g x =
      e.separableClosureCongr (g (e.separableClosureCongr.symm x)) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] L := { e with commutes' := fun _ => rfl }
  let σ : L →ₐ[K] SeparableClosure K :=
    (Algebra.ofId K (SeparableClosure K)).comp eA.symm.toAlgHom
  exact absoluteGaloisGroupEquivFixingSubgroup_apply K L σ g x

/-- The inverse of the absolute-Galois-group equivalence induced by a field isomorphism acts by
conjugation through the inverse of the chosen equivalence of separable closures. -/
@[simp]
theorem absoluteGaloisGroupCongr_symm_apply (e : K ≃+* L) (g : AbsoluteGaloisGroup K)
    (x : SeparableClosure L) :
    (absoluteGaloisGroupCongr e).symm g x =
      e.separableClosureCongr.symm (g (e.separableClosureCongr x)) := by
  have h := absoluteGaloisGroupCongr_apply e ((absoluteGaloisGroupCongr e).symm g)
    (e.separableClosureCongr x)
  rw [ContinuousMulEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] at h
  rw [h, RingEquiv.symm_apply_apply]

/-- Restriction to identified normal subextensions commutes with field transport.
The coefficient embedding identifies the subextensions inside the chosen separable closures. -/
theorem restrictNormalHom_congr (e : K ≃+* L)
    (E : IntermediateField K (SeparableClosure K)) [Normal K E]
    (F : IntermediateField L (SeparableClosure L)) [Normal L F]
    (ι : E →+* F) (π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E))
    (hι : ∀ x : E, e.separableClosureCongr.symm (E.val x) = F.val (ι x))
    (hπ : ∀ g x, ι (π g x) = g (ι x)) (g : AbsoluteGaloisGroup L) :
    π (AlgEquiv.restrictNormalHom F g) =
      AlgEquiv.restrictNormalHom E (e.absoluteGaloisGroupCongr g) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  apply e.separableClosureCongr.symm.injective
  calc
    e.separableClosureCongr.symm (E.val (π (AlgEquiv.restrictNormalHom F g) x)) =
        F.val (ι (π (AlgEquiv.restrictNormalHom F g) x)) := hι _
    _ = F.val (AlgEquiv.restrictNormalHom F g (ι x)) := congrArg F.val (hπ _ x)
    _ = g (F.val (ι x)) := AlgEquiv.restrictNormal_commutes g F (ι x)
    _ = g (e.separableClosureCongr.symm (E.val x)) := congrArg g (hι x).symm
    _ = _ := by
      have hr : E.val (AlgEquiv.restrictNormalHom E (e.absoluteGaloisGroupCongr g) x) =
          e.absoluteGaloisGroupCongr g (E.val x) :=
        AlgEquiv.restrictNormal_commutes (e.absoluteGaloisGroupCongr g) E x
      simpa only [absoluteGaloisGroupCongr_apply, RingEquiv.symm_apply_apply,
        IntermediateField.coe_val] using (congrArg e.separableClosureCongr.symm hr).symm

end RingEquiv
