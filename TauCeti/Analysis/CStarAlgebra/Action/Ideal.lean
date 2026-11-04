/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Hom
public import TauCeti.Analysis.CStarAlgebra.Action.Quotient
public import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Invariant closed ideals and concrete quotient C⋆-actions

We connect two-sided ideals and C⋆-quotients `A ⧸ I` with point-norm continuous group actions
`TauCeti.CStarAction` and equivariant homomorphisms `TauCeti.CStarAction.Hom`.

Given a point-norm continuous action `α : CStarAction G A` on a (possibly nonunital) C⋆-algebra
`A`:

* Invariance of a two-sided ideal `I : TwoSidedIdeal A` is preserved under `topologicalClosure` and
  pullback along `CStarAction.Hom`; in particular, `TwoSidedIdeal.ker f.toNonUnitalStarAlgHom` is a
  closed invariant two-sided ideal for every `f : CStarAction.Hom α β`.
* Every closed invariant two-sided ideal `I` inherits a restricted point-norm continuous action
  `IsInvariant.restrictIdeal : CStarAction G I` with isometric equivariant inclusion
  `IsInvariant.idealSubtypeHom : CStarAction.Hom hI.restrictIdeal α`.
* The C⋆-quotient `A ⧸ I` carries the concrete descended point-norm continuous action
  `CStarAction.quotient : CStarAction G (A ⧸ I)` with surjective equivariant projection
  `CStarAction.quotientMkHom : CStarAction.Hom α (α.quotient I hI)` of kernel `I`, universal
  equivariant lift `CStarAction.Hom.quotientLift`, and canonical equivariant isometric
  identification `A ⧸ ker f ≃⋆ₐ[ℂ] B` for surjective `f : CStarAction.Hom α β`.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Section 2.4.
-/

public section

noncomputable section

open scoped CStarAlgebra

namespace IsInvariant

open TauCeti

variable {G A B : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}

/-- The topological closure of an invariant two-sided ideal is an invariant closed two-sided ideal.
-/
theorem topologicalClosure_ideal {I : TwoSidedIdeal A}
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    _root_.IsInvariant (fun g a => α g a) (I.topologicalClosure : Set A) := by
  simpa only [TwoSidedIdeal.coe_topologicalClosure] using hI.topologicalClosure

/-- Pulling back an invariant two-sided ideal along an equivariant homomorphism yields an invariant
two-sided ideal. -/
theorem comap_ideal {J : TwoSidedIdeal B}
    (hJ : _root_.IsInvariant (fun g b => β g b) (J : Set B)) (f : CStarAction.Hom α β) :
    _root_.IsInvariant (fun g a => α g a)
      (TwoSidedIdeal.comap f.toNonUnitalStarAlgHom J : Set A) := by
  intro g a ha
  rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, CStarAction.Hom.coe_toNonUnitalStarAlgHom] at ha ⊢
  rw [f.map_action]
  exact hJ g ha

/-- The two-sided ideal kernel of an equivariant homomorphism is invariant. -/
theorem ker (f : CStarAction.Hom α β) :
    _root_.IsInvariant (fun g a => α g a)
      (TwoSidedIdeal.ker f.toNonUnitalStarAlgHom : Set A) := by
  intro g a ha
  rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, CStarAction.Hom.coe_toNonUnitalStarAlgHom] at ha ⊢
  rw [f.map_action, ha, map_zero]

private theorem isInvariant_toNonUnitalStarSubalgebra {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    _root_.IsInvariant (fun g a => α g a) (I.toNonUnitalStarSubalgebra : Set A) :=
  fun g _ ha => I.mem_toNonUnitalStarSubalgebra.mpr (hI g (I.mem_toNonUnitalStarSubalgebra.mp ha))

/-- Restrict an automorphism from an action to a closed invariant two-sided ideal. -/
def restrictIdealEquiv {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (g : G) : I ≃⋆ₐ[ℂ] I :=
  I.toNonUnitalStarSubalgebraEquiv.trans
    (((isInvariant_toNonUnitalStarSubalgebra hI).restrictEquiv g).trans
      I.toNonUnitalStarSubalgebraEquiv.symm)

@[simp]
theorem restrictIdealEquiv_apply {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (g : G) (x : I) :
    hI.restrictIdealEquiv g x = ⟨α g x, hI.apply_mem g x.2⟩ := by
  simp [restrictIdealEquiv]

/-- Restrict a C⋆-action to a closed invariant two-sided ideal. -/
def restrictIdeal {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) : CStarAction G I :=
  (isInvariant_toNonUnitalStarSubalgebra hI).restrict.conjugate
    I.toNonUnitalStarSubalgebraEquiv.symm

@[simp]
theorem restrictIdeal_apply {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (g : G) (x : I) :
    hI.restrictIdeal g x = ⟨α g x, hI.apply_mem g x.2⟩ := by
  simp [restrictIdeal]

@[norm_cast]
theorem coe_restrictIdeal_apply {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (g : G) (x : I) :
    ((hI.restrictIdeal g x : I) : A) = α g x := by
  rw [restrictIdeal_apply]

/-- The canonical isometric inclusion `I →⋆ₙₐ[ℂ] A` of a closed invariant two-sided ideal is an
equivariant homomorphism. -/
def idealSubtypeHom {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    CStarAction.Hom hI.restrictIdeal α :=
  (isInvariant_toNonUnitalStarSubalgebra hI).subtypeHom.comp
    ⟨I.toNonUnitalStarSubalgebraEquiv.toNonUnitalStarAlgHom,
      (I.toNonUnitalStarSubalgebraEquiv.symm.isEquivariant_symm
        (CStarAction.IsEquivariant.conjugate
          (isInvariant_toNonUnitalStarSubalgebra hI).restrict
          I.toNonUnitalStarSubalgebraEquiv.symm)).apply⟩

@[simp]
theorem idealSubtypeHom_toNonUnitalStarAlgHom {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    hI.idealSubtypeHom.toNonUnitalStarAlgHom = I.starAlgHom := by
  ext x
  simp [idealSubtypeHom]

@[simp]
theorem idealSubtypeHom_apply {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (x : I) :
    hI.idealSubtypeHom x = (x : A) := by
  rw [← CStarAction.Hom.coe_toNonUnitalStarAlgHom, idealSubtypeHom_toNonUnitalStarAlgHom,
    I.starAlgHom_apply]

theorem idealSubtypeHom_injective {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Injective hI.idealSubtypeHom := by
  rw [← CStarAction.Hom.coe_toNonUnitalStarAlgHom, idealSubtypeHom_toNonUnitalStarAlgHom]
  exact I.starAlgHom_injective

theorem isometry_idealSubtypeHom {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Isometry hI.idealSubtypeHom := by
  rw [← CStarAction.Hom.coe_toNonUnitalStarAlgHom, idealSubtypeHom_toNonUnitalStarAlgHom]
  exact I.isometry_starAlgHom

end IsInvariant

namespace TauCeti.CStarAction

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

section Quotient

/-- The descended point-norm continuous C⋆-action on the quotient C⋆-algebra `A ⧸ I` by a closed
invariant two-sided ideal `I`. -/
def quotient (α : CStarAction G A) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) : CStarAction G (A ⧸ I) :=
  α.descend (TwoSidedIdeal.Quotient.mkStarAlgHom I)
    (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective I) fun g a ha => by
      have ha' : TwoSidedIdeal.Quotient.mkStarAlgHom I a = 0 := ha
      have ha0 : TwoSidedIdeal.Quotient.mk I a = 0 :=
        (TwoSidedIdeal.Quotient.mkStarAlgHom_apply I a).symm.trans ha'
      have hga : α g a ∈ I := hI g (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp ha0)
      exact (TwoSidedIdeal.Quotient.mkStarAlgHom_apply I (α g a)).trans
        (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr hga)

@[simp]
theorem quotient_mk (α : CStarAction G A) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (g : G) (a : A) :
    α.quotient I hI g (TwoSidedIdeal.Quotient.mk I a) =
      TwoSidedIdeal.Quotient.mk I (α g a) :=
  (congrArg (α.quotient I hI g) (TwoSidedIdeal.Quotient.mkStarAlgHom_apply I a).symm).trans
    ((α.descend_apply (TwoSidedIdeal.Quotient.mkStarAlgHom I) _ _ g a).trans
      (TwoSidedIdeal.Quotient.mkStarAlgHom_apply I (α g a)))

/-- The canonical quotient `⋆`-homomorphism `A →⋆ₙₐ[ℂ] A ⧸ I` is equivariant. -/
theorem isEquivariant_quotientMk (α : CStarAction G A) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    α.IsEquivariant (α.quotient I hI) (TwoSidedIdeal.Quotient.mkStarAlgHom I) :=
  α.isEquivariant_descend (TwoSidedIdeal.Quotient.mkStarAlgHom I) _ _

/-- An action on `A ⧸ I` makes the quotient projection equivariant if and only if it equals
`α.quotient I hI`. -/
theorem isEquivariant_quotientMk_iff (α : CStarAction G A) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (β : CStarAction G (A ⧸ I)) :
    α.IsEquivariant β (TwoSidedIdeal.Quotient.mkStarAlgHom I) ↔ α.quotient I hI = β :=
  α.isEquivariant_iff_descend_eq (TwoSidedIdeal.Quotient.mkStarAlgHom I) _ _ β

/-- The canonical quotient `⋆`-homomorphism `A →⋆ₙₐ[ℂ] A ⧸ I` bundled as a `CStarAction.Hom`. -/
def quotientMkHom (α : CStarAction G A) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) : Hom α (α.quotient I hI) where
  toNonUnitalStarAlgHom := TwoSidedIdeal.Quotient.mkStarAlgHom I
  map_action' g a :=
    (TwoSidedIdeal.Quotient.mkStarAlgHom_apply I (α g a)).trans
      ((α.quotient_mk I hI g a).symm.trans
        (congrArg (α.quotient I hI g) (TwoSidedIdeal.Quotient.mkStarAlgHom_apply I a).symm))

@[simp]
theorem quotientMkHom_toNonUnitalStarAlgHom (α : CStarAction G A) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (α.quotientMkHom I hI).toNonUnitalStarAlgHom = TwoSidedIdeal.Quotient.mkStarAlgHom I :=
  (rfl)

@[simp]
theorem quotientMkHom_apply (α : CStarAction G A) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (a : A) :
    α.quotientMkHom I hI a = TwoSidedIdeal.Quotient.mk I a :=
  TwoSidedIdeal.Quotient.mkStarAlgHom_apply I a

theorem quotientMkHom_surjective (α : CStarAction G A) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Surjective (α.quotientMkHom I hI) :=
  TwoSidedIdeal.Quotient.mkStarAlgHom_surjective I

theorem ker_quotientMkHom (α : CStarAction G A) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    TwoSidedIdeal.ker (α.quotientMkHom I hI).toNonUnitalStarAlgHom = I :=
  TwoSidedIdeal.Quotient.ker_mkStarAlgHom I

theorem quotientMkHom_comp_idealSubtypeHom_apply (α : CStarAction G A) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (x : I) :
    (α.quotientMkHom I hI).comp hI.idealSubtypeHom x = 0 := by
  simp [TwoSidedIdeal.Quotient.eq_zero_iff_mem]

end Quotient

namespace Hom

variable {α : CStarAction G A} {β : CStarAction G B}

/-- Descend an equivariant homomorphism `f : Hom α β` vanishing on a closed invariant ideal `I` to
an equivariant homomorphism `Hom (α.quotient I hI) β`. -/
def quotientLift (f : Hom α β) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (hf : ∀ a ∈ I, f a = 0) :
    Hom (α.quotient I hI) β where
  toNonUnitalStarAlgHom := TwoSidedIdeal.Quotient.liftStarAlgHom I f.toNonUnitalStarAlgHom hf
  map_action' g x := by
    obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective I x
    exact (congrArg (TwoSidedIdeal.Quotient.liftStarAlgHom I f.toNonUnitalStarAlgHom hf)
        (α.quotient_mk I hI g a)).trans
      ((TwoSidedIdeal.Quotient.liftStarAlgHom_mk I f.toNonUnitalStarAlgHom hf (α g a)).trans
        ((f.map_action g a).trans
          (congrArg (β g)
            (TwoSidedIdeal.Quotient.liftStarAlgHom_mk I f.toNonUnitalStarAlgHom hf a).symm)))

@[simp]
theorem quotientLift_toNonUnitalStarAlgHom (f : Hom α β) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hf : ∀ a ∈ I, f a = 0) :
    (f.quotientLift I hI hf).toNonUnitalStarAlgHom =
      TwoSidedIdeal.Quotient.liftStarAlgHom I f.toNonUnitalStarAlgHom hf :=
  (rfl)

@[simp]
theorem quotientLift_mk (f : Hom α β) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (hf : ∀ a ∈ I, f a = 0) (a : A) :
    f.quotientLift I hI hf (TwoSidedIdeal.Quotient.mk I a) = f a :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_mk I f.toNonUnitalStarAlgHom hf a

@[simp]
theorem quotientLift_comp_quotientMkHom (f : Hom α β) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (hf : ∀ a ∈ I, f a = 0) :
    (f.quotientLift I hI hf).comp (α.quotientMkHom I hI) = f := by
  ext a
  exact (Hom.comp_apply _ _ a).trans
    ((congrArg (f.quotientLift I hI hf) (α.quotientMkHom_apply I hI a)).trans
      (f.quotientLift_mk I hI hf a))

theorem quotientLift_injective_of_ker_le (f : Hom α β) {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (hf : ∀ a ∈ I, f a = 0)
    (hker : TwoSidedIdeal.ker f.toNonUnitalStarAlgHom ≤ I) :
    Function.Injective (f.quotientLift I hI hf) :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_injective_of_ker_le hf hker

theorem quotientLift_surjective_of_surjective (f : Hom α β) {I : TwoSidedIdeal A}
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hf : ∀ a ∈ I, f a = 0) (hsurj : Function.Surjective f) :
    Function.Surjective (f.quotientLift I hI hf) :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_surjective_of_surjective hf hsurj

/-- The isometric equivariant homomorphism `Hom (α.quotient (ker f) _) β` factored from
`f : Hom α β`. -/
def quotientKerHom (f : Hom α β) :
    Hom (α.quotient (TwoSidedIdeal.ker f.toNonUnitalStarAlgHom) (IsInvariant.ker f)) β :=
  f.quotientLift (TwoSidedIdeal.ker f.toNonUnitalStarAlgHom) (IsInvariant.ker f) fun _ ha =>
    (TwoSidedIdeal.mem_ker f.toNonUnitalStarAlgHom).mp ha

@[simp]
theorem quotientKerHom_mk (f : Hom α β) (a : A) :
    Hom.quotientKerHom f
      (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker f.toNonUnitalStarAlgHom) a) = f a :=
  f.quotientLift_mk _ _ _ a

theorem quotientKerHom_injective (f : Hom α β) : Function.Injective (Hom.quotientKerHom f) :=
  f.quotientLift_injective_of_ker_le _ _ le_rfl

theorem isometry_quotientKerHom (f : Hom α β) : Isometry (Hom.quotientKerHom f) :=
  NonUnitalStarAlgHom.isometry (Hom.quotientKerHom f).toNonUnitalStarAlgHom
    (quotientKerHom_injective f)

/-- For a surjective equivariant homomorphism `f : Hom α β`, the canonical isometric
`⋆`-isomorphism `A ⧸ ker f ≃⋆ₐ[ℂ] B` is equivariant. -/
theorem isEquivariant_quotientKerEquivOfSurjective (f : Hom α β) (hf : Function.Surjective f) :
    (α.quotient (TwoSidedIdeal.ker f.toNonUnitalStarAlgHom) (IsInvariant.ker f)).IsEquivariant β
      (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
        (φ := f.toNonUnitalStarAlgHom) hf).toNonUnitalStarAlgHom := by
  refine isEquivariant_iff.mpr fun g x => ?_
  obtain ⟨a, rfl⟩ :=
    TwoSidedIdeal.Quotient.mk_surjective (TwoSidedIdeal.ker f.toNonUnitalStarAlgHom) x
  exact (congrArg
      (NonUnitalStarAlgHom.quotientKerEquivOfSurjective (φ := f.toNonUnitalStarAlgHom) hf)
      (α.quotient_mk _ _ g a)).trans
    ((NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk
        (φ := f.toNonUnitalStarAlgHom) hf (α g a)).trans
      ((f.map_action g a).trans
        (congrArg (β g)
          (NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk
            (φ := f.toNonUnitalStarAlgHom) hf a).symm)))

/-- Every surjective equivariant homomorphism `f : Hom α β` identifies `β` with the concrete
quotient action `α.quotient (ker f) _` transported along `quotientKerEquivOfSurjective`. -/
theorem conjugate_quotientKerEquivOfSurjective (f : Hom α β) (hf : Function.Surjective f) :
    (α.quotient (TwoSidedIdeal.ker f.toNonUnitalStarAlgHom) (IsInvariant.ker f)).conjugate
      (NonUnitalStarAlgHom.quotientKerEquivOfSurjective (φ := f.toNonUnitalStarAlgHom) hf) = β :=
  (StarAlgEquiv.isEquivariant_iff_conjugate_eq _).mp
    (f.isEquivariant_quotientKerEquivOfSurjective hf)

end Hom

end TauCeti.CStarAction
