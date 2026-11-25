/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import TauCeti.RingTheory.Deformation.Lift
-- Non-public: the rank-one fact `M = scalar n (det M)` is used in proofs only.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unique

/-!
# Lifts and deformations with fixed determinant

Let `ρbar : G →* GL n k` be a residual representation and `χ : G →* Λˣ` a character with values
in the coefficient ring. For an object `A` of the Artinian coefficient category `C_Λ`, write
`χ_A` for the composite of `χ` with `Λˣ → Aˣ`. The lifts of `ρbar` to `A` *with determinant `χ`*
are the lifts `ρ` with `det ρ(g) = χ_A(g)` for every `g ∈ G`. This is the actual fibre of the
determinant: no assumption is made on the characteristic of `k` relative to the rank, and the
determinant is not split off as a scalar factor, which would require `n` to be invertible in `k`.

Conjugation preserves determinants, so the strict kernel `Γ̂ₙ(A)` preserves the lifts with
determinant `χ`, and pushforward along morphisms of `C_Λ` preserves them since those morphisms
are `Λ`-algebra maps. This gives subfunctors `Lift_{ρbar,χ}` of the framed lifting functor and
`Def_{ρbar,χ}` of the deformation functor of strict classes; the strict classes with determinant
`χ` are exactly the orbits of `Γ̂ₙ(A)` on the lifts with determinant `χ`. Fixed-determinant
deformation rings represent these functors, and global deformation problems with prescribed
determinant are built from them.

Reducing the determinant equation to `k` shows that a lift with determinant `χ` can only exist
when `χ` reduces to `det ρbar`. In rank one the determinant is the representation itself, so
there is at most one lift with determinant `χ`, namely `χ_A`.

## Main definitions

* `TauCeti.Deformation.fixedDetLifts ρbar χ A`: the lifts of `ρbar` to `A` with determinant `χ`,
  as a set stable under the strict kernel `Γ̂ₙ(A)`.
* `TauCeti.Deformation.fixedDetLiftFunctor Λ ρbar χ`: the subfunctor `Lift_{ρbar,χ}` of the
  framed lifting functor.
* `TauCeti.Deformation.fixedDetStrictClassFunctor Λ ρbar χ`: the subfunctor `Def_{ρbar,χ}` of
  the deformation functor, the image of `Lift_{ρbar,χ}`.
* `TauCeti.Deformation.fixedDetStrictClassEquiv ρbar χ A`: the strict classes with determinant
  `χ` are the orbits of `Γ̂ₙ(A)` on the lifts with determinant `χ`.

## Main results

* `TauCeti.Deformation.mem_fixedDetLifts_iff_comp_eq`: `ρ` has determinant `χ` exactly when
  `det ∘ ρ = χ_A`.
* `TauCeti.Deformation.Lift.map_mem_fixedDetLifts`: pushforward preserves the determinant.
* `TauCeti.Deformation.StrictClass.mk_mem_fixedDetStrictClassFunctor_obj_iff`: a strict class
  has determinant `χ` exactly when one (equivalently every) representative does.
* `TauCeti.Deformation.det_residual_eq_of_mem_fixedDetLifts`: if a lift with determinant `χ`
  exists, then `χ` reduces to `det ρbar`. Otherwise both functors are empty:
  `TauCeti.Deformation.fixedDetLiftFunctor_eq_bot` and
  `TauCeti.Deformation.fixedDetStrictClassFunctor_eq_bot`.
* `TauCeti.Deformation.mem_fixedDetLifts_residue_iff`: over `k`, the lift `ρbar` has
  determinant `χ` exactly when `χ` reduces to `det ρbar`.
* `TauCeti.Deformation.eq_scalar_of_mem_fixedDetLifts`,
  `TauCeti.Deformation.subsingleton_fixedDetLifts` and
  `TauCeti.Deformation.nonempty_fixedDetLifts_iff`: in rank one a lift with determinant `χ` is
  `χ_A`, and there is one exactly when `χ_A` is locally constant and `χ` reduces to `ρbar`.

## References

* T. Gee, *Modularity lifting theorems*, Essent. Number Theory 1 (2022), §3.18.
* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publ. 16
  (1989), 385–437, §1.
-/

public section

open CategoryTheory Matrix

universe u v w x

namespace TauCeti.Deformation

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]
  {n : Type x} [Fintype n] [DecidableEq n] {G : Type w} [Monoid G] [TopologicalSpace G]

open ArtinLocalAlg

section Lifts

variable (ρbar : G →* GL n k) (χ : G →* Λˣ)

/-- The lifts of `ρbar` to `A` *with determinant `χ`*: those `ρ` with
`det ρ(g) = χ_A(g)` for every `g`, where `χ_A` is the image of `χ` in `Aˣ`. They form a set
stable under conjugation by the strict kernel `Γ̂ₙ(A)`. -/
def fixedDetLifts (A : ArtinLocalAlg Λ k) : SubMulAction (A.strictKernel n) (Lift ρbar A) where
  carrier := {ρ | ∀ g, GeneralLinearGroup.det (ρ g) = Units.map (algebraMap Λ A.obj.left) (χ g)}
  smul_mem' a ρ hρ g := by simpa [Lift.smul_apply, mul_inv_cancel_comm] using hρ g

variable {ρbar χ} {A B : ArtinLocalAlg Λ k}

/-- A lift has determinant `χ` exactly when `det ρ(g) = χ_A(g)` for every `g`. -/
@[simp]
theorem mem_fixedDetLifts_iff {ρ : Lift ρbar A} :
    ρ ∈ fixedDetLifts ρbar χ A ↔
      ∀ g, GeneralLinearGroup.det (ρ g) = Units.map (algebraMap Λ A.obj.left) (χ g) :=
  Iff.rfl

/-- A lift has determinant `χ` exactly when `det ∘ ρ = χ_A` as homomorphisms `G →* Aˣ`. -/
theorem mem_fixedDetLifts_iff_comp_eq {ρ : Lift ρbar A} :
    ρ ∈ fixedDetLifts ρbar χ A ↔
      GeneralLinearGroup.det.comp ρ.toMonoidHom =
        (Units.map (algebraMap Λ A.obj.left : Λ →* A.obj.left)).comp χ := by
  simp [MonoidHom.ext_iff]

/-- Pushforward along a morphism of `C_Λ` preserves the determinant `χ`. -/
theorem Lift.map_mem_fixedDetLifts (f : A ⟶ B) {ρ : Lift ρbar A}
    (hρ : ρ ∈ fixedDetLifts ρbar χ A) : Lift.map f ρ ∈ fixedDetLifts ρbar χ B := fun g ↦ by
  rw [Lift.map_apply, GeneralLinearGroup.map_det, hρ g]
  ext
  simp

/-- If a lift with determinant `χ` exists, then `χ` reduces to the determinant of `ρbar`. -/
theorem det_residual_eq_of_mem_fixedDetLifts {ρ : Lift ρbar A}
    (hρ : ρ ∈ fixedDetLifts ρbar χ A) (g : G) :
    GeneralLinearGroup.det (ρbar g) = Units.map (algebraMap Λ k) (χ g) := by
  rw [← ρ.map_augmentation_apply g, GeneralLinearGroup.map_det, hρ g]
  ext
  simp

/-- Over the residue field, the lift `ρbar` has determinant `χ` exactly when `χ` reduces to the
determinant of `ρbar`. -/
theorem mem_fixedDetLifts_residue_iff {ρ : Lift ρbar (residue Λ k)} :
    ρ ∈ fixedDetLifts ρbar χ (residue Λ k) ↔
      ∀ g, GeneralLinearGroup.det (ρbar g) = Units.map (algebraMap Λ k) (χ g) := by
  refine ⟨det_residual_eq_of_mem_fixedDetLifts, fun h g ↦ ?_⟩
  rw [← map_augmentation_residue (ρ g), ρ.map_augmentation_apply]
  exact h g

end Lifts

section Functors

variable (ρbar : G →* GL n k) (χ : G →* Λˣ)

variable (Λ) in
/-- The functor `Lift_{ρbar,χ}` of lifts with determinant `χ`, as a subfunctor of the framed
lifting functor. -/
def fixedDetLiftFunctor : Subfunctor (liftFunctor Λ ρbar) where
  obj A := (fixedDetLifts ρbar χ A : Set (Lift ρbar A))
  map f _ hρ := Lift.map_mem_fixedDetLifts f hρ

variable {ρbar χ} {A : ArtinLocalAlg Λ k}

/-- The values of `Lift_{ρbar,χ}` are the lifts with determinant `χ`. -/
@[simp]
theorem mem_fixedDetLiftFunctor_obj_iff {ρ : Lift ρbar A} :
    ρ ∈ (fixedDetLiftFunctor Λ ρbar χ).obj A ↔ ρ ∈ fixedDetLifts ρbar χ A :=
  Iff.rfl

/-- If `χ` does not reduce to the determinant of `ρbar`, the functor of lifts with determinant `χ`
is empty. -/
theorem fixedDetLiftFunctor_eq_bot
    (h : ∃ g, GeneralLinearGroup.det (ρbar g) ≠ Units.map (algebraMap Λ k) (χ g)) :
    fixedDetLiftFunctor Λ ρbar χ = ⊥ := by
  obtain ⟨g, hg⟩ := h
  refine Subfunctor.ext (funext fun A ↦ ?_)
  rw [Subfunctor.bot_obj]
  exact Set.eq_empty_of_forall_notMem fun ρ hρ ↦ hg (det_residual_eq_of_mem_fixedDetLifts hρ g)

variable (ρbar χ)

variable (Λ) in
/-- The functor `Def_{ρbar,χ}` of strict classes of lifts with determinant `χ`, as a subfunctor of
the deformation functor: the image of `Lift_{ρbar,χ}` under the quotient map to strict classes. -/
def fixedDetStrictClassFunctor : Subfunctor (strictClassFunctor Λ ρbar) :=
  (fixedDetLiftFunctor Λ ρbar χ).image (toStrictClass Λ ρbar)

variable {ρbar χ}

/-- A strict class has determinant `χ` exactly when a representative has determinant `χ`; as
conjugation preserves determinants, every representative then does. -/
@[simp]
theorem StrictClass.mk_mem_fixedDetStrictClassFunctor_obj_iff {ρ : Lift ρbar A} :
    StrictClass.mk ρ ∈ (fixedDetStrictClassFunctor Λ ρbar χ).obj A ↔
      ρ ∈ fixedDetLifts ρbar χ A := by
  refine ⟨?_, fun hρ ↦ ⟨ρ, hρ, toStrictClass_app_apply Λ ρbar A ρ⟩⟩
  rintro ⟨ρ', hρ', h⟩
  obtain ⟨a, rfl⟩ :=
    StrictClass.mk_eq_mk_iff.mp ((toStrictClass_app_apply Λ ρbar A ρ').symm.trans h)
  exact (SubMulAction.smul_mem_iff' _ a).mpr hρ'

/-- If `χ` does not reduce to the determinant of `ρbar`, the functor of strict classes with
determinant `χ` is empty. -/
theorem fixedDetStrictClassFunctor_eq_bot
    (h : ∃ g, GeneralLinearGroup.det (ρbar g) ≠ Units.map (algebraMap Λ k) (χ g)) :
    fixedDetStrictClassFunctor Λ ρbar χ = ⊥ := by
  refine Subfunctor.ext (funext fun A ↦ ?_)
  rw [fixedDetStrictClassFunctor, fixedDetLiftFunctor_eq_bot h, Subfunctor.image_obj,
    Subfunctor.bot_obj, Subfunctor.bot_obj, Set.image_empty]

variable (ρbar χ A)

/-- The strict classes with determinant `χ` are the orbits of the strict kernel `Γ̂ₙ(A)` on the
lifts with determinant `χ`. -/
noncomputable def fixedDetStrictClassEquiv :
    MulAction.orbitRel.Quotient (A.strictKernel n) (fixedDetLifts ρbar χ A) ≃
      (fixedDetStrictClassFunctor Λ ρbar χ).obj A :=
  Equiv.ofBijective
    (Quotient.lift (fun ρ ↦ ⟨StrictClass.mk ρ.val,
        StrictClass.mk_mem_fixedDetStrictClassFunctor_obj_iff.mpr ρ.property⟩)
      fun ρ ρ' h ↦ by
        obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
        exact Subtype.ext (StrictClass.mk_eq_mk_iff.mpr ⟨a, rfl⟩).symm)
    ⟨fun c c' h ↦ by
      obtain ⟨ρ, rfl⟩ := Quotient.mk''_surjective c
      obtain ⟨ρ', rfl⟩ := Quotient.mk''_surjective c'
      obtain ⟨a, ha⟩ := StrictClass.mk_eq_mk_iff.mp (congrArg Subtype.val h)
      have hρ : a • ρ = ρ' := Subtype.ext ha
      exact (Quotient.sound (MulAction.orbitRel_apply.mpr
        (MulAction.mem_orbit_iff.mpr ⟨a, hρ⟩))).symm,
     fun ⟨c, ρ, hρ, hc⟩ ↦ ⟨Quotient.mk'' ⟨ρ, hρ⟩,
      Subtype.ext ((toStrictClass_app_apply Λ ρbar A ρ).symm.trans hc)⟩⟩

@[simp]
theorem coe_fixedDetStrictClassEquiv_mk (ρ : fixedDetLifts ρbar χ A) :
    (fixedDetStrictClassEquiv ρbar χ A (Quotient.mk'' ρ)).val = StrictClass.mk ρ.val :=
  (rfl)

end Functors

section RankOne

variable {ρbar : G →* GL n k} {χ : G →* Λˣ} {A : ArtinLocalAlg Λ k} [Unique n]

/-- In rank one a lift with determinant `χ` is `χ_A`, viewed as a scalar matrix. -/
theorem eq_scalar_of_mem_fixedDetLifts {ρ : Lift ρbar A} (hρ : ρ ∈ fixedDetLifts ρbar χ A)
    (g : G) :
    ρ g = GeneralLinearGroup.scalar n (Units.map (algebraMap Λ A.obj.left) (χ g)) := by
  rw [GeneralLinearGroup.eq_scalar_det (ρ g), hρ g]

/-- In rank one there is at most one lift with determinant `χ`. -/
instance subsingleton_fixedDetLifts : Subsingleton (fixedDetLifts ρbar χ A) :=
  ⟨fun ρ ρ' ↦ Subtype.ext <| Lift.ext fun g ↦ by
    rw [eq_scalar_of_mem_fixedDetLifts ρ.property, eq_scalar_of_mem_fixedDetLifts ρ'.property]⟩

/-- In rank one a lift with determinant `χ` exists exactly when `χ_A` is continuous for the
discrete topology on `A` and `χ` reduces to `ρbar`. -/
theorem nonempty_fixedDetLifts_iff :
    Nonempty (fixedDetLifts ρbar χ A) ↔
      IsLocallyConstant ((Units.map (algebraMap Λ A.obj.left : Λ →* A.obj.left)).comp χ) ∧
        ∀ g, GeneralLinearGroup.det (ρbar g) = Units.map (algebraMap Λ k) (χ g) := by
  refine ⟨fun ⟨ρ⟩ ↦ ⟨?_, det_residual_eq_of_mem_fixedDetLifts ρ.property⟩, fun ⟨hχ, hdet⟩ ↦ ?_⟩
  · rw [← mem_fixedDetLifts_iff_comp_eq.mp ρ.property, MonoidHom.coe_comp]
    exact (ρ : Lift ρbar A).isLocallyConstant.comp _
  -- The lift is `χ_A` as a scalar matrix; it reduces to `ρbar` since in rank one a matrix is the
  -- scalar of its determinant.
  have hred : ∀ g, GeneralLinearGroup.map (A.augmentation : A.obj.left →+* k)
      (GeneralLinearGroup.scalar n (Units.map (algebraMap Λ A.obj.left) (χ g))) = ρbar g :=
    fun g ↦ by
      rw [GeneralLinearGroup.map_scalar, GeneralLinearGroup.eq_scalar_det (ρbar g), hdet g]
      congr 1
      ext
      simp
  refine ⟨⟨⟨(GeneralLinearGroup.scalar n).comp
      ((Units.map (algebraMap Λ A.obj.left : Λ →* A.obj.left)).comp χ), ?_,
      MonoidHom.ext hred⟩, fun g ↦ ?_⟩⟩
  · rw [MonoidHom.coe_comp]
    exact hχ.comp _
  · simp

end RankOne

end TauCeti.Deformation
