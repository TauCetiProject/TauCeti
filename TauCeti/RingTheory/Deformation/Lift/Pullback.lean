/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Deformation.Lift.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Pullback
import TauCeti.RingTheory.Pullback

/-!
# Gluing lifts and strict classes over coefficient pullbacks

Lifts in a fixed basis glue uniquely over a fibre product of coefficient rings. For strict
classes, one first changes basis on the surjective leg to make the lifts agree over the common
quotient. The resulting comparison for strict classes is surjective and is injective whenever strict
stabilizers lift along the surjective leg.

## Main results

* `Lift.existsUnique_map_pullback`: compatible framed lifts glue uniquely.
* `ArtinLocalAlg.existsUnique_strictKernelMap_pullback`: compatible strict-kernel elements glue
  uniquely.
* `StrictClass.exists_map_pullback`: compatible strict classes glue.
* `StrictClass.eq_of_stabilizers_lift_of_map_pullback_eq`: strict classes are determined by their
  projections when stabilizers lift along the surjective leg.

The matrix gluing uses `RingHom.pullbackGLEquiv`. For the application to deformation functors,
see B. Mazur, *Deforming Galois representations*, MSRI Publ. 16 (1989), §§1.1–1.2.
-/

public section

open CategoryTheory Limits Matrix

namespace TauCeti.Deformation

variable {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
  {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Monoid G] [TopologicalSpace G]
  {ρbar : G →* GL n k}

open ArtinLocalAlg

section Pullback

variable {A₁ A₂ B : ArtinLocalAlg Λ k} (f : A₁ ⟶ B) (g : A₂ ⟶ B)
  (hg : Function.Surjective g.hom.left.hom)

local notation "P" => ArtinLocalAlg.pullback f g hg
local notation "p₁" => pullbackFst f g hg
local notation "p₂" => pullbackSnd f g hg

-- The coefficient pullback uses the same carrier as the ring pullback. These abbreviations
-- let the matrix equivalence compute before passing to the bundled coefficient projections.
private abbrev compatibleGL :=
  ((GeneralLinearGroup.map (f.hom.left.hom : A₁.obj.left →+* B.obj.left)).comp
    (MonoidHom.fst (GL n A₁.obj.left) (GL n A₂.obj.left))).eqLocus
    ((GeneralLinearGroup.map (g.hom.left.hom : A₂.obj.left →+* B.obj.left)).comp
      (MonoidHom.snd (GL n A₁.obj.left) (GL n A₂.obj.left)))

private noncomputable abbrev pullbackGL :
    GL n (P).obj.left ≃* compatibleGL (n := n) f g :=
  RingHom.pullbackGLEquiv (f.hom.left.hom : A₁.obj.left →+* B.obj.left)
    (g.hom.left.hom : A₂.obj.left →+* B.obj.left) n

-- Record both inverse projections together using the public ring-level gluing equations.
private theorem map_pullbackGL_symm (a : compatibleGL (n := n) f g) :
    (GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left)
        ((pullbackGL f g hg).symm a),
      GeneralLinearGroup.map ((p₂).hom.left.hom : (P).obj.left →+* A₂.obj.left)
        ((pullbackGL f g hg).symm a)) = (a.val.1, a.val.2) := by
  apply Prod.ext
  · exact (GeneralLinearGroup.ext fun i j ↦
      (GeneralLinearGroup.map_apply _ i j _).trans
        (pullbackFst_hom_left_hom_apply f g hg _)).trans
      (RingHom.unitsMap_pullbackFst_pullbackGLEquiv_symm _ _ a)
  · exact (GeneralLinearGroup.ext fun i j ↦
      (GeneralLinearGroup.map_apply _ i j _).trans
        (pullbackSnd_hom_left_hom_apply f g hg _)).trans
      (RingHom.unitsMap_pullbackSnd_pullbackGLEquiv_symm _ _ a)

private theorem eq_of_map_pullbackGL_eq {a b : GL n (P).obj.left}
    (h₁ : GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) a =
      GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) b)
    (h₂ : GeneralLinearGroup.map ((p₂).hom.left.hom : (P).obj.left →+* A₂.obj.left) a =
      GeneralLinearGroup.map ((p₂).hom.left.hom : (P).obj.left →+* A₂.obj.left) b) : a = b := by
  refine GeneralLinearGroup.ext fun i j ↦ RingHom.pullback_ext
    (p := (f.hom.left.hom : A₁.obj.left →+* B.obj.left))
    (q := (g.hom.left.hom : A₂.obj.left →+* B.obj.left)) ?_ ?_
  · have hij := congrArg (fun t : GL n A₁.obj.left ↦ t i j) h₁
    simp only [GeneralLinearGroup.map_apply, AlgHom.coe_toRingHom,
      pullbackFst_hom_left_hom_apply] at hij
    exact hij
  · have hij := congrArg (fun t : GL n A₂.obj.left ↦ t i j) h₂
    simp only [GeneralLinearGroup.map_apply, AlgHom.coe_toRingHom,
      pullbackSnd_hom_left_hom_apply] at hij
    exact hij

/-- Two lifts over a coefficient fibre product agree if their projections agree. -/
theorem Lift.eq_of_map_pullback_eq {ρ σ : Lift ρbar P}
    (h₁ : ρ.map p₁ = σ.map p₁) (h₂ : ρ.map p₂ = σ.map p₂) : ρ = σ := by
  apply Lift.ext
  intro x
  apply eq_of_map_pullbackGL_eq f g hg
  · simpa only [Lift.map_apply] using congrArg (fun τ : Lift ρbar A₁ ↦ τ x) h₁
  · simpa only [Lift.map_apply] using congrArg (fun τ : Lift ρbar A₂ ↦ τ x) h₂

/-- Compatible lifts in the chosen basis glue uniquely over the coefficient fibre product. -/
theorem Lift.existsUnique_map_pullback {ρ₁ : Lift ρbar A₁} {ρ₂ : Lift ρbar A₂}
    (h : ρ₁.map f = ρ₂.map g) :
    ∃! ρ : Lift ρbar P, ρ.map p₁ = ρ₁ ∧ ρ.map p₂ = ρ₂ := by
  let pair := (ρ₁.toMonoidHom.prod ρ₂.toMonoidHom).codRestrict (compatibleGL f g) fun x ↦ by
    have hx := congrArg (fun t : Lift ρbar B ↦ t x) h
    rw [Lift.map_apply, Lift.map_apply] at hx
    exact hx
  let e := pullbackGL (n := n) f g hg
  let ρ : G →* GL n (P).obj.left := e.symm.toMonoidHom.comp pair
  have hρ (x : G) :
      (GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) (ρ x),
        GeneralLinearGroup.map ((p₂).hom.left.hom : (P).obj.left →+* A₂.obj.left) (ρ x)) =
      (ρ₁ x, ρ₂ x) := by
    exact map_pullbackGL_symm f g hg (pair x)
  have hcont : IsLocallyConstant ρ := (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦
    ((ρ₁.isLocallyConstant.prodMk ρ₂.isLocallyConstant).eventually_eq x).mono fun _ hxy ↦
      congrArg e.symm (Subtype.ext hxy)
  let t : Lift ρbar P := ⟨ρ, hcont, MonoidHom.ext fun x ↦ by
    rw [MonoidHom.comp_apply, ← map_augmentation_map p₁ (ρ x)]
    exact congrArg (GeneralLinearGroup.map (A₁.augmentation : A₁.obj.left →+* k))
      (congrArg Prod.fst (hρ x)) |>.trans (ρ₁.map_augmentation_apply x)⟩
  have ht₁ : t.map p₁ = ρ₁ := Lift.ext fun x ↦
    (Lift.map_apply p₁ t x).trans (congrArg Prod.fst (hρ x))
  have ht₂ : t.map p₂ = ρ₂ := Lift.ext fun x ↦
    (Lift.map_apply p₂ t x).trans (congrArg Prod.snd (hρ x))
  exact ⟨t, ⟨ht₁, ht₂⟩, fun σ hσ ↦
    Lift.eq_of_map_pullback_eq f g hg (hσ.1.trans ht₁.symm) (hσ.2.trans ht₂.symm)⟩

/-- Compatible matrices reducing to the identity glue uniquely to a matrix reducing to the
identity. -/
theorem ArtinLocalAlg.existsUnique_strictKernelMap_pullback {a₁ : A₁.strictKernel n}
    {a₂ : A₂.strictKernel n} (h : strictKernelMap n f a₁ = strictKernelMap n g a₂) :
    ∃! a : (P).strictKernel n, strictKernelMap n p₁ a = a₁ ∧ strictKernelMap n p₂ a = a₂ := by
  have hab : GeneralLinearGroup.map (f.hom.left.hom : A₁.obj.left →+* B.obj.left) a₁.val =
      GeneralLinearGroup.map (g.hom.left.hom : A₂.obj.left →+* B.obj.left) a₂.val := by
    simpa only [coe_strictKernelMap_apply] using congrArg Subtype.val h
  let pair : compatibleGL (n := n) f g := ⟨(a₁.val, a₂.val), hab⟩
  let b : GL n (P).obj.left := (pullbackGL f g hg).symm pair
  have hbproj :
      (GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) b,
        GeneralLinearGroup.map ((p₂).hom.left.hom : (P).obj.left →+* A₂.obj.left) b) =
      (a₁.val, a₂.val) := by
    exact map_pullbackGL_symm f g hg pair
  have hb₁ : GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) b =
      a₁.val := congrArg Prod.fst hbproj
  have hb₂ : GeneralLinearGroup.map ((p₂).hom.left.hom : (P).obj.left →+* A₂.obj.left) b =
      a₂.val := congrArg Prod.snd hbproj
  have hb : b ∈ (P).strictKernel n :=
    (map_mem_strictKernel_iff p₁).mp (hb₁.symm ▸ a₁.property)
  refine ⟨⟨b, hb⟩, ⟨Subtype.ext ((coe_strictKernelMap_apply p₁ _).trans hb₁),
    Subtype.ext ((coe_strictKernelMap_apply p₂ _).trans hb₂)⟩, ?_⟩
  intro a ha
  apply Subtype.ext
  apply eq_of_map_pullbackGL_eq f g hg
  · exact (coe_strictKernelMap_apply p₁ a).symm.trans
      ((congrArg Subtype.val ha.1).trans hb₁.symm)
  · exact (coe_strictKernelMap_apply p₂ a).symm.trans
      ((congrArg Subtype.val ha.2).trans hb₂.symm)

end Pullback

section StrictClass

variable {A₁ A₂ B : ArtinLocalAlg Λ k} (f : A₁ ⟶ B) (g : A₂ ⟶ B)
  (hg : Function.Surjective g.hom.left.hom)

/-- Compatible strict classes glue when one coefficient map is surjective. -/
theorem StrictClass.exists_map_pullback {x : StrictClass ρbar A₁} {y : StrictClass ρbar A₂}
    (h : StrictClass.map f x = StrictClass.map g y) :
    ∃ z : StrictClass ρbar (ArtinLocalAlg.pullback f g hg),
      StrictClass.map (pullbackFst f g hg) z = x ∧ StrictClass.map (pullbackSnd f g hg) z = y := by
  obtain ⟨ρ, rfl⟩ := StrictClass.mk_surjective x
  obtain ⟨σ, rfl⟩ := StrictClass.mk_surjective y
  rw [StrictClass.map_mk, StrictClass.map_mk] at h
  obtain ⟨a, ha⟩ := StrictClass.mk_eq_mk_iff.mp h.symm
  obtain ⟨b, hb⟩ := strictKernelMap_surjective g hg a
  have h' : Lift.map f ρ = Lift.map g (b • σ) := by
    rw [Lift.map_smul, hb, ha]
  obtain ⟨τ, ⟨h₁, h₂⟩, -⟩ := Lift.existsUnique_map_pullback f g hg h'
  refine ⟨StrictClass.mk τ, by rw [StrictClass.map_mk, h₁], ?_⟩
  rw [StrictClass.map_mk, h₂]
  exact (StrictClass.mk_eq_mk_iff.mpr ⟨b, rfl⟩).symm

/-- Strict classes glue uniquely if strict stabilizers of lifts on the second leg surject onto
the strict stabilizers of their images. -/
theorem StrictClass.eq_of_stabilizers_lift_of_map_pullback_eq
    (hlift : ∀ (τ : Lift ρbar A₂) (a : B.strictKernel n), a • τ.map g = τ.map g →
      ∃ b : A₂.strictKernel n, strictKernelMap n g b = a ∧ b • τ = τ)
    {x y : StrictClass ρbar (ArtinLocalAlg.pullback f g hg)}
    (h₁ : StrictClass.map (pullbackFst f g hg) x = StrictClass.map (pullbackFst f g hg) y)
    (h₂ : StrictClass.map (pullbackSnd f g hg) x = StrictClass.map (pullbackSnd f g hg) y) :
    x = y := by
  obtain ⟨ρ, rfl⟩ := StrictClass.mk_surjective x
  obtain ⟨σ, rfl⟩ := StrictClass.mk_surjective y
  simp only [StrictClass.map_mk] at h₁ h₂
  obtain ⟨a₁, ha₁⟩ := StrictClass.mk_eq_mk_iff.mp h₁
  obtain ⟨a₂, ha₂⟩ := StrictClass.mk_eq_mk_iff.mp h₂
  have compat (τ : Lift ρbar (ArtinLocalAlg.pullback f g hg)) :
      (τ.map (pullbackFst f g hg)).map f = (τ.map (pullbackSnd f g hg)).map g := by
    rw [← Lift.map_comp, pullback_condition, Lift.map_comp]
  have hleft := congrArg (Lift.map f) ha₁
  have hright := congrArg (Lift.map g) ha₂
  rw [Lift.map_smul, compat ρ, compat σ] at hleft
  rw [Lift.map_smul] at hright
  -- The discrepancy between the two conjugators stabilizes the source lift over the base.
  let u := (strictKernelMap n g a₂)⁻¹ * strictKernelMap n f a₁
  have hu : u • (ρ.map (pullbackSnd f g hg)).map g =
      (ρ.map (pullbackSnd f g hg)).map g := by
    dsimp only [u]
    rw [mul_smul, hleft, ← hright, inv_smul_smul]
  obtain ⟨b, hb, hbρ⟩ := hlift _ u hu
  have hab : strictKernelMap n f a₁ = strictKernelMap n g (a₂ * b) := by
    rw [map_mul, hb]
    simp [u]
  obtain ⟨a, ⟨ha₁', ha₂'⟩, -⟩ := existsUnique_strictKernelMap_pullback f g hg hab
  refine StrictClass.mk_eq_mk_iff.mpr ⟨a, Lift.eq_of_map_pullback_eq f g hg ?_ ?_⟩
  · rw [Lift.map_smul, ha₁', ha₁]
  · rw [Lift.map_smul, ha₂', mul_smul, hbρ, ha₂]

end StrictClass

end TauCeti.Deformation
