/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Deformation.Lift
public import TauCeti.RingTheory.Deformation.PredeformationFunctor
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Pullback
import TauCeti.RingTheory.FiberProduct.Basic

/-!
# Gluing lifts and strict classes over Artinian coefficient rings

Lifts in a fixed basis glue uniquely over a fibre product of coefficient rings. For strict
classes, one first changes basis on the surjective leg to make the lifts agree over the common
quotient. This gives Schlessinger's condition (H1). Over the residue field the strict kernel is
trivial, so the two conjugating matrices also glue, giving (H2). More generally, the comparison
is injective whenever strict stabilizers lift along the surjective leg.

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

-- The coefficient pullback has the ring-pullback carrier, but its bundled projections and
-- `GeneralLinearGroup.map` are opaque. Compare the maps through their public application equations.
private theorem map_pullbackFst :
    GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) =
      Units.map ((RingHom.pullbackFst (f.hom.left.hom : A₁.obj.left →+* B.obj.left)
        (g.hom.left.hom : A₂.obj.left →+* B.obj.left)).mapMatrix (m := n)).toMonoidHom :=
  MonoidHom.ext fun u ↦ GeneralLinearGroup.ext fun i j ↦
    (GeneralLinearGroup.map_apply _ i j u).trans
      (pullbackFst_hom_left_hom_apply f g hg _)

private theorem map_pullbackSnd :
    GeneralLinearGroup.map ((p₂).hom.left.hom : (P).obj.left →+* A₂.obj.left) =
      Units.map ((RingHom.pullbackSnd (f.hom.left.hom : A₁.obj.left →+* B.obj.left)
        (g.hom.left.hom : A₂.obj.left →+* B.obj.left)).mapMatrix (m := n)).toMonoidHom :=
  MonoidHom.ext fun u ↦ GeneralLinearGroup.ext fun i j ↦
    (GeneralLinearGroup.map_apply _ i j u).trans
      (pullbackSnd_hom_left_hom_apply f g hg _)

/-- Two lifts over a coefficient fibre product agree if their projections agree. -/
theorem Lift.eq_of_map_pullback_eq {ρ σ : Lift ρbar P}
    (h₁ : ρ.map p₁ = σ.map p₁) (h₂ : ρ.map p₂ = σ.map p₂) : ρ = σ := by
  -- The exposed coefficient-pullback carrier is the ring pullback; the bundled projections
  -- are compared through their named application equations.
  refine Lift.ext fun x ↦ GeneralLinearGroup.ext fun i j ↦ RingHom.pullback_ext
    (p := (f.hom.left.hom : A₁.obj.left →+* B.obj.left))
    (q := (g.hom.left.hom : A₂.obj.left →+* B.obj.left)) ?_ ?_
  · have hx := congrArg (fun t : Lift ρbar A₁ ↦ (t x) i j) h₁
    simp only [Lift.map_apply, GeneralLinearGroup.map_apply, AlgHom.coe_toRingHom,
      pullbackFst_hom_left_hom_apply] at hx
    exact hx
  · have hx := congrArg (fun t : Lift ρbar A₂ ↦ (t x) i j) h₂
    simp only [Lift.map_apply, GeneralLinearGroup.map_apply, AlgHom.coe_toRingHom,
      pullbackSnd_hom_left_hom_apply] at hx
    exact hx

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
  have hρ₁ (x : G) :
      GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) (ρ x) = ρ₁ x := by
    rw [map_pullbackFst f g hg]
    exact RingHom.unitsMap_pullbackFst_pullbackGLEquiv_symm _ _ (pair x)
  have hcont : IsLocallyConstant ρ := (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ by
    filter_upwards [ρ₁.isLocallyConstant.eventually_eq x, ρ₂.isLocallyConstant.eventually_eq x]
      with y hy₁ hy₂
    exact congrArg e.symm (Subtype.ext (Prod.ext hy₁ hy₂))
  let t : Lift ρbar P := ⟨ρ, hcont, MonoidHom.ext fun x ↦ by
    rw [MonoidHom.comp_apply, ← map_augmentation_map p₁ (ρ x)]
    exact congrArg (GeneralLinearGroup.map (A₁.augmentation : A₁.obj.left →+* k))
      (hρ₁ x) |>.trans (ρ₁.map_augmentation_apply x)⟩
  have ht₁ : t.map p₁ = ρ₁ := Lift.ext fun x ↦
    (Lift.map_apply p₁ t x).trans (hρ₁ x)
  have ht₂ : t.map p₂ = ρ₂ := Lift.ext fun x ↦
    (Lift.map_apply p₂ t x).trans (by
      rw [map_pullbackSnd f g hg]
      exact RingHom.unitsMap_pullbackSnd_pullbackGLEquiv_symm _ _ (pair x))
  exact ⟨t, ⟨ht₁, ht₂⟩, fun σ hσ ↦
    Lift.eq_of_map_pullback_eq f g hg (hσ.1.trans ht₁.symm) (hσ.2.trans ht₂.symm)⟩

/-- Compatible matrices reducing to the identity glue to a matrix reducing to the identity. -/
theorem ArtinLocalAlg.exists_strictKernelMap_pullback {a₁ : A₁.strictKernel n}
    {a₂ : A₂.strictKernel n} (h : strictKernelMap n f a₁ = strictKernelMap n g a₂) :
    ∃ a : (P).strictKernel n, strictKernelMap n p₁ a = a₁ ∧ strictKernelMap n p₂ a = a₂ := by
  have hab : GeneralLinearGroup.map (f.hom.left.hom : A₁.obj.left →+* B.obj.left) a₁.val =
      GeneralLinearGroup.map (g.hom.left.hom : A₂.obj.left →+* B.obj.left) a₂.val := by
    simpa only [coe_strictKernelMap_apply] using congrArg Subtype.val h
  let pair : compatibleGL (n := n) f g := ⟨(a₁.val, a₂.val), hab⟩
  let b : GL n (P).obj.left := (pullbackGL f g hg).symm pair
  have hb₁ : GeneralLinearGroup.map ((p₁).hom.left.hom : (P).obj.left →+* A₁.obj.left) b =
      a₁.val := by
    rw [map_pullbackFst f g hg]
    exact RingHom.unitsMap_pullbackFst_pullbackGLEquiv_symm _ _ pair
  have hb : b ∈ (P).strictKernel n :=
    (mem_strictKernel_iff_map_mem p₁).mpr (hb₁.symm ▸ a₁.property)
  exact ⟨⟨b, hb⟩, Subtype.ext ((coe_strictKernelMap_apply p₁ _).trans hb₁),
    Subtype.ext ((coe_strictKernelMap_apply p₂ _).trans (by
      rw [map_pullbackSnd f g hg]
      exact RingHom.unitsMap_pullbackSnd_pullbackGLEquiv_symm _ _ pair))⟩

end Pullback

variable (Λ ρbar)

/-- The framed lifting functor, equipped with its unique residue-field point. -/
def liftPredeformationFunctor (hρ : IsLocallyConstant ρbar) : PredeformationFunctor Λ k :=
  ⟨liftFunctor Λ ρbar, (inferInstance : Subsingleton (Lift ρbar (residue Λ k))),
    Lift.nonempty_residue_iff.mpr hρ⟩

/-- The functor of strict classes, equipped with its unique residue-field point. -/
def strictClassPredeformationFunctor (hρ : IsLocallyConstant ρbar) : PredeformationFunctor Λ k :=
  ⟨strictClassFunctor Λ ρbar, (inferInstance : Subsingleton (StrictClass ρbar (residue Λ k))),
    (Lift.nonempty_residue_iff.mpr hρ).map StrictClass.mk⟩

variable {Λ ρbar}

@[simp]
theorem liftPredeformationFunctor_obj (hρ : IsLocallyConstant ρbar) :
    (liftPredeformationFunctor Λ ρbar hρ).obj = liftFunctor Λ ρbar :=
  (rfl)

@[simp]
theorem strictClassPredeformationFunctor_obj (hρ : IsLocallyConstant ρbar) :
    (strictClassPredeformationFunctor Λ ρbar hρ).obj = strictClassFunctor Λ ρbar :=
  (rfl)

/-- Framed lifts satisfy the Rim–Schlessinger condition. -/
instance (hρ : IsLocallyConstant ρbar) :
    (liftPredeformationFunctor Λ ρbar hρ).IsDeformationFunctor where
  bijective_fiberProductMap := by
    intro A₁ A₂ B f g hg
    let F := liftPredeformationFunctor Λ ρbar hρ
    refine ⟨?_, ?_⟩
    · intro x y h
      obtain ⟨h₁, h₂⟩ := (F.fiberProductMap_eq_iff f g hg x y).mp h
      exact Lift.eq_of_map_pullback_eq _ _ hg h₁ h₂
    rintro ⟨⟨x, y⟩, h⟩
    obtain ⟨z, ⟨hz₁, hz₂⟩, -⟩ := Lift.existsUnique_map_pullback _ _ hg h
    exact ⟨z, (F.fiberProductMap_eq_mk_iff f g hg z x y h).mpr ⟨hz₁, hz₂⟩⟩

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
theorem StrictClass.eq_of_map_pullback_eq
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
  obtain ⟨a, ha₁', ha₂'⟩ := exists_strictKernelMap_pullback f g hg hab
  refine StrictClass.mk_eq_mk_iff.mpr ⟨a, Lift.eq_of_map_pullback_eq f g hg ?_ ?_⟩
  · rw [Lift.map_smul, ha₁', ha₁]
  · rw [Lift.map_smul, ha₂', mul_smul, hbρ, ha₂]

end StrictClass

/-- The comparison map for strict classes is surjective over any coefficient fibre product
with a surjective leg. -/
theorem strictClassPredeformationFunctor_surjective_fiberProductMap (hρ : IsLocallyConstant ρbar)
    {A₁ A₂ B : ArtinLocalAlg Λ k} (f : A₁ ⟶ B) (g : A₂ ⟶ B)
    (hg : Function.Surjective g.hom.left.hom) :
    Function.Surjective ((strictClassPredeformationFunctor Λ ρbar hρ).fiberProductMap f g hg) := by
  rintro ⟨⟨x, y⟩, h⟩
  obtain ⟨z, hz₁, hz₂⟩ := StrictClass.exists_map_pullback f g hg h
  let F := strictClassPredeformationFunctor Λ ρbar hρ
  exact ⟨z, (F.fiberProductMap_eq_mk_iff f g hg z x y h).mpr ⟨hz₁, hz₂⟩⟩

/-- Strict classes of lifts satisfy Schlessinger's condition (H1). -/
instance (hρ : IsLocallyConstant ρbar) :
    (strictClassPredeformationFunctor Λ ρbar hρ).SatisfiesH1 where
  surjective_fiberProductMap := fun _ _ _ f g hg ↦
    strictClassPredeformationFunctor_surjective_fiberProductMap hρ f g hg.surjective

/-- Strict classes of lifts satisfy Schlessinger's condition (H2). -/
instance (hρ : IsLocallyConstant ρbar) :
    (strictClassPredeformationFunctor Λ ρbar hρ).SatisfiesH2 where
  bijective_fiberProductMap A := by
    let F := strictClassPredeformationFunctor Λ ρbar hρ
    refine ⟨?_, strictClassPredeformationFunctor_surjective_fiberProductMap hρ
      (toResidue A) _ (toResidue_surjective _)⟩
    intro x y h
    obtain ⟨h₁, h₂⟩ := (F.fiberProductMap_eq_iff _ _ _ x y).mp h
    exact StrictClass.eq_of_map_pullback_eq _ _ _
      (fun _ a _ ↦ ⟨1, Subsingleton.elim _ a, one_smul _ _⟩) h₁ h₂

end TauCeti.Deformation
