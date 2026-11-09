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

Subextensions of the chosen separable closures are transported by
`IntermediateField.separableClosureCongr`. This preserves degree, finiteness and normality.
The induced automorphism equivalence commutes with restriction from the absolute Galois
groups and identifies the corresponding fixing subgroups.

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

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L]
    (E : IntermediateField K (SeparableClosure K)) (e : K ≃+* L)

/-- Transport a subextension through the chosen identification of separable closures. -/
def separableClosureCongr : IntermediateField L (SeparableClosure L) :=
  (E.toSubfield.comap e.separableClosureCongr.toRingHom).toIntermediateField (fun r => by
    -- Unpack comap membership to apply the separable-closure algebraMap formula.
    change e.separableClosureCongr (algebraMap L (SeparableClosure L) r) ∈ E
    simp)

/-- Membership in a transported subextension is tested in the original separable closure. -/
@[simp]
theorem mem_separableClosureCongr (x : SeparableClosure L) :
    x ∈ E.separableClosureCongr e ↔ e.separableClosureCongr x ∈ E := Iff.rfl

/-- The chosen identification restricts to an isomorphism of the underlying fields. -/
def separableClosureCongrEquiv : E ≃+* E.separableClosureCongr e where
  toFun x := ⟨e.separableClosureCongr.symm x, by simp⟩
  invFun x := ⟨e.separableClosureCongr x, x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

/-- The restricted field identification acts by the inverse separable-closure map. -/
@[simp]
theorem coe_separableClosureCongrEquiv (x : E) :
    (E.separableClosureCongrEquiv e x : SeparableClosure L) =
      e.separableClosureCongr.symm x := by rfl

/-- The inverse restricted identification acts by the separable-closure map. -/
@[simp]
theorem coe_separableClosureCongrEquiv_symm (x : E.separableClosureCongr e) :
    ((E.separableClosureCongrEquiv e).symm x : SeparableClosure K) =
      e.separableClosureCongr x := by rfl

/-- The restricted identification extends the base-field isomorphism. -/
@[simp]
theorem separableClosureCongrEquiv_algebraMap (r : K) :
    E.separableClosureCongrEquiv e (algebraMap K E r) =
      algebraMap L (E.separableClosureCongr e) (e r) := by
  apply Subtype.val_injective
  simp

private theorem separableClosureCongr_algebraMap_comp :
    (algebraMap L (E.separableClosureCongr e)).comp e.toRingHom =
      (E.separableClosureCongrEquiv e).toRingHom.comp (algebraMap K E) := by
  apply RingHom.ext
  intro r
  exact (E.separableClosureCongrEquiv_algebraMap e r).symm

/-- Transport preserves and reflects inclusion of subextensions. -/
@[simp]
theorem separableClosureCongr_le_iff {E F : IntermediateField K (SeparableClosure K)} :
    E.separableClosureCongr e ≤ F.separableClosureCongr e ↔ E ≤ F := by
  constructor
  · intro h x hx
    have := h (x := e.separableClosureCongr.symm x) (by simpa using hx)
    simpa using this
  · intro h x hx
    exact h hx

/-- Refining a subextension refines its transported image. -/
theorem separableClosureCongr_mono {E F : IntermediateField K (SeparableClosure K)}
    (h : E ≤ F) : E.separableClosureCongr e ≤ F.separableClosureCongr e :=
  (separableClosureCongr_le_iff e).2 h

/-- Transport along a field isomorphism preserves the degree. -/
@[simp]
theorem finrank_separableClosureCongr :
    Module.finrank L (E.separableClosureCongr e) = Module.finrank K E :=
  (Algebra.finrank_eq_of_equiv_equiv e (E.separableClosureCongrEquiv e)
    (E.separableClosureCongr_algebraMap_comp e)).symm

/-- A finite subextension remains finite after transport. -/
instance instFiniteDimensionalSeparableClosureCongr [FiniteDimensional K E] :
    FiniteDimensional L (E.separableClosureCongr e) := by
  apply Module.finite_of_finrank_pos
  rw [finrank_separableClosureCongr]
  exact Module.finrank_pos

/-- Normality is preserved by transport along a field isomorphism. -/
instance [Normal K E] : Normal L (E.separableClosureCongr e) :=
  Normal.of_equiv_equiv (f := e) (g := E.separableClosureCongrEquiv e)
    (E.separableClosureCongr_algebraMap_comp e)

/-- A transported normal subextension is Galois, with separability inherited from the closure. -/
instance [Normal K E] : IsGalois L (E.separableClosureCongr e) where

/-- Identify automorphisms by conjugating through the restricted field identification. -/
def separableClosureCongrAutEquiv :
    (E ≃ₐ[K] E) ≃* (E.separableClosureCongr e ≃ₐ[L] E.separableClosureCongr e) where
  toFun g :=
    { toRingEquiv := (E.separableClosureCongrEquiv e).symm.trans
        (g.toRingEquiv.trans (E.separableClosureCongrEquiv e))
      commutes' r := by
        obtain ⟨r, rfl⟩ := e.surjective r
        -- Expose only composition of ring maps; keep the restricted identification opaque.
        change E.separableClosureCongrEquiv e
          (g ((E.separableClosureCongrEquiv e).symm
            (algebraMap L (E.separableClosureCongr e) (e r)))) = _
        rw [← separableClosureCongrEquiv_algebraMap, RingEquiv.symm_apply_apply,
          AlgEquiv.commutes, separableClosureCongrEquiv_algebraMap] }
  invFun g :=
    { toRingEquiv := (E.separableClosureCongrEquiv e).trans
        (g.toRingEquiv.trans (E.separableClosureCongrEquiv e).symm)
      commutes' r := by
        apply (E.separableClosureCongrEquiv e).injective
        -- Expose only composition of ring maps to cancel the inverse identification.
        change E.separableClosureCongrEquiv e
          ((E.separableClosureCongrEquiv e).symm
            (g (E.separableClosureCongrEquiv e (algebraMap K E r)))) = _
        rw [RingEquiv.apply_symm_apply, separableClosureCongrEquiv_algebraMap,
          AlgEquiv.commutes] }
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp

/-- The transported automorphism acts by conjugation through the field identification. -/
@[simp]
theorem separableClosureCongrAutEquiv_apply (g : E ≃ₐ[K] E)
    (x : E.separableClosureCongr e) :
    E.separableClosureCongrAutEquiv e g x = E.separableClosureCongrEquiv e
      (g ((E.separableClosureCongrEquiv e).symm x)) := by rfl

/-- The inverse automorphism transport acts by the reverse conjugation. -/
@[simp]
theorem separableClosureCongrAutEquiv_symm_apply
    (g : E.separableClosureCongr e ≃ₐ[L] E.separableClosureCongr e) (x : E) :
    (E.separableClosureCongrAutEquiv e).symm g x =
      (E.separableClosureCongrEquiv e).symm (g (E.separableClosureCongrEquiv e x)) := by rfl

/-- Restriction to a normal subextension commutes with transport of the absolute Galois group. -/
theorem separableClosureCongrAutEquiv_restrictNormalHom [Normal K E]
    (g : AbsoluteGaloisGroup L) :
    E.separableClosureCongrAutEquiv e
        (AlgEquiv.restrictNormalHom E (e.absoluteGaloisGroupCongr g)) =
      AlgEquiv.restrictNormalHom (E.separableClosureCongr e) g := by
  ext x
  simp [AlgEquiv.restrictNormalHom_apply]

/-- Fixing subgroups are transported by the same absolute-Galois-group equivalence. -/
theorem fixingSubgroup_separableClosureCongr [Normal K E] :
    (E.separableClosureCongr e).fixingSubgroup =
      E.fixingSubgroup.comap e.absoluteGaloisGroupCongr.toMonoidHom := by
  rw [← restrictNormalHom_ker, ← E.restrictNormalHom_ker]
  ext g
  simp only [Subgroup.mem_comap, MonoidHom.mem_ker]
  rw [← separableClosureCongrAutEquiv_restrictNormalHom]
  exact (E.separableClosureCongrAutEquiv e).map_eq_one_iff

end IntermediateField
