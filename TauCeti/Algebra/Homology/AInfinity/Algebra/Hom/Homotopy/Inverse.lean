/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Lift
import TauCeti.Algebra.Module.GradedModule.Shift

/-!
# Homotopy inverses of morphisms of A-infinity algebras

An *`A∞` homotopy equivalence* (`TauCeti.AInfinityHomotopyEquiv`) between two `A∞` algebras `A` and
`B` consists of morphisms `hom : A ⟶ B` and `inv : B ⟶ A` together with homotopies
`homotopyHomInv : id_A ⇒ inv ∘ hom` and `homotopyInvHom : id_B ⇒ hom ∘ inv`.  Its linear parts and
arity-one homotopies form a graded `TauCeti.LinearHomotopyEquiv` between the unary differentials,
and on cohomology `hom` and `inv` induce mutually inverse morphisms of nonunital algebras.

Conversely, over any commutative ring, an `A∞` morphism `f : A ⟶ B` extends to an `A∞` homotopy
equivalence with `f` as its forward map as soon as its linear part `f₁` extends to a graded
`LinearHomotopyEquiv` between the unary differentials
(`TauCeti.AInfinityHomotopyEquiv.ofLinearHomotopyEquiv`): lifting `id_B` along `f` via
`TauCeti.AInfinityHom.liftRight` produces a right homotopy inverse `g : B ⟶ A` with `id_B ⇒ f ∘ g`,
and precomposing with `f` gives a homotopy `f ∘ id_A ⇒ f ∘ (g ∘ f)` which lifts back along `f` via
`TauCeti.AInfinityHom.Homotopy.ofCompRightOfLinearHomotopyEquiv` to `id_A ⇒ g ∘ f`.

Over a field, the unary complex of every `A∞` algebra contracts onto its graded homology, so the
linear part of every quasi-isomorphism extends to a graded `LinearHomotopyEquiv`
(`TauCeti.InternalGrading.linearHomotopyEquivOfBijectiveHomologyMap`).  Every `A∞`
quasi-isomorphism over a field therefore admits an `A∞` homotopy inverse
(`TauCeti.AInfinityHom.IsQuasiIso.homotopyEquiv`, `TauCeti.AInfinityHom.IsQuasiIso.homotopyInv`),
and an `A∞` morphism over a field is a homotopy equivalence if and only if it is a
quasi-isomorphism (`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`).

## Main definitions

* `TauCeti.AInfinityHomotopyEquiv`: homotopy equivalence data between `A∞` algebras.
* `TauCeti.AInfinityHom.IsHomotopyEquiv`: predicate that an `A∞` morphism admits a two-sided
  homotopy inverse.
* `TauCeti.AInfinityHomotopyEquiv.ofLinearHomotopyEquiv`: `A∞` homotopy equivalence extending `f`
  from a graded homotopy equivalence on linear parts.
* `TauCeti.AInfinityHom.IsQuasiIso.homotopyEquiv` and
  `TauCeti.AInfinityHom.IsQuasiIso.homotopyInv`: homotopy inverse of a quasi-isomorphism over a
  field.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyEquiv`: over any commutative ring,
  `f` is an `A∞` homotopy equivalence if and only if `f₁` extends to a graded linear homotopy
  equivalence.
* `TauCeti.AInfinityHom.Homotopy.isHomotopyEquiv_iff`: homotopic `A∞` morphisms are homotopy
  equivalences together.
* `TauCeti.AInfinityHom.Homotopy.ofCompRight`: cancellation of a homotopy equivalence on the left
  of a homotopy.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: over a field, `f` is an `A∞` homotopy
  equivalence if and only if `f` is a quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Théorème 1.3.3.1.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section (1f).
-/

public section

open CategoryTheory

namespace TauCeti

universe u uR uK uA uB uC

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- The linear part of an `A∞` morphism commutes with the unary differentials. -/
theorem linearPart_comp_differential (f : AInfinityHom AA BB) :
    f.linearPart ∘ₗ AA.differential = BB.differential ∘ₗ f.linearPart :=
  LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, AInfinityAlgebra.differential_apply, f.linearPart_m_one]

/-- Under `cohomologyEquivHomology`, `cohomologyMap` corresponds to `LinearMap.homologyMap` of the
linear part. -/
theorem cohomologyEquivHomology_cohomologyMap (f : AInfinityHom AA BB) (c : AA.Cohomology) :
    BB.cohomologyEquivHomology (f.cohomologyMap c) =
      AA.differential.homologyMap f.linearPart AA.differential_comp_self_eq_zero
        BB.differential_comp_self_eq_zero f.linearPart_comp_differential
        (AA.cohomologyEquivHomology c) := by
  obtain ⟨x, hx, rfl⟩ := AA.exists_cohomologyClass_eq c
  rw [cohomologyMap_cohomologyClass, BB.cohomologyEquivHomology_cohomologyClass,
    AA.cohomologyEquivHomology_cohomologyClass]
  simp only [LinearMap.homologyπ_apply, LinearMap.homologyMap_mk]

/-- An `A∞` morphism is a quasi-isomorphism if and only if its linear part induces a bijection on
the concrete homology of the unary differentials. -/
theorem isQuasiIso_iff_bijective_homologyMap (f : AInfinityHom AA BB) :
    f.IsQuasiIso ↔
      Function.Bijective
        (AA.differential.homologyMap f.linearPart AA.differential_comp_self_eq_zero
          BB.differential_comp_self_eq_zero f.linearPart_comp_differential) := by
  have hcomp : (BB.cohomologyEquivHomology : BB.Cohomology → _) ∘ f.cohomologyMap =
      (AA.differential.homologyMap f.linearPart AA.differential_comp_self_eq_zero
        BB.differential_comp_self_eq_zero f.linearPart_comp_differential) ∘
        AA.cohomologyEquivHomology :=
    funext f.cohomologyEquivHomology_cohomologyMap
  rw [isQuasiIso_def, ← Function.Bijective.of_comp_iff' BB.cohomologyEquivHomology.bijective,
    hcomp, Function.Bijective.of_comp_iff _ AA.cohomologyEquivHomology.bijective]

end AInfinityHom

/-- A homotopy equivalence between `A∞` algebras `AA` and `BB`: morphisms `hom : AA ⟶ BB` and
`inv : BB ⟶ AA` accompanied by homotopies `id_AA ⇒ inv ∘ hom` and `id_BB ⇒ hom ∘ inv`. -/
structure AInfinityHomotopyEquiv (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) where
  /-- The forward `A∞` morphism. -/
  hom : AInfinityHom AA BB
  /-- The backward `A∞` morphism. -/
  inv : AInfinityHom BB AA
  /-- The homotopy from `id AA` to `inv ∘ hom`. -/
  homotopyHomInv : AInfinityHom.Homotopy (.id AA) (inv.comp hom)
  /-- The homotopy from `id BB` to `hom ∘ inv`. -/
  homotopyInvHom : AInfinityHom.Homotopy (.id BB) (hom.comp inv)

namespace AInfinityHomotopyEquiv

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- The identity `A∞` homotopy equivalence. -/
def refl (AA : AInfinityAlgebra R A) : AInfinityHomotopyEquiv AA AA where
  hom := .id AA
  inv := .id AA
  homotopyHomInv := AInfinityHom.Homotopy.ofEq (AInfinityHom.id_comp _).symm
  homotopyInvHom := AInfinityHom.Homotopy.ofEq (AInfinityHom.id_comp _).symm

/-- The forward morphism of `refl AA` is the identity. -/
@[simp]
theorem refl_hom (AA : AInfinityAlgebra R A) : (refl AA).hom = .id AA := (rfl)

/-- The backward morphism of `refl AA` is the identity. -/
@[simp]
theorem refl_inv (AA : AInfinityAlgebra R A) : (refl AA).inv = .id AA := (rfl)

/-- Reversing the forward and backward morphisms of an `A∞` homotopy equivalence. -/
def symm (e : AInfinityHomotopyEquiv AA BB) : AInfinityHomotopyEquiv BB AA where
  hom := e.inv
  inv := e.hom
  homotopyHomInv := e.homotopyInvHom
  homotopyInvHom := e.homotopyHomInv

/-- The forward morphism of `e.symm` is `e.inv`. -/
@[simp]
theorem symm_hom (e : AInfinityHomotopyEquiv AA BB) : e.symm.hom = e.inv := (rfl)

/-- The backward morphism of `e.symm` is `e.hom`. -/
@[simp]
theorem symm_inv (e : AInfinityHomotopyEquiv AA BB) : e.symm.inv = e.hom := (rfl)

/-- Reversing `symm` recovers the original `A∞` homotopy equivalence. -/
@[simp]
theorem symm_symm (e : AInfinityHomotopyEquiv AA BB) : e.symm.symm = e := (rfl)

/-- On cohomology, `inv` is a left inverse to `hom`. -/
@[simp]
theorem inv_cohomologyMap_comp_hom_cohomologyMap (e : AInfinityHomotopyEquiv AA BB) :
    e.inv.cohomologyMap.comp e.hom.cohomologyMap = NonUnitalAlgHom.id R AA.Cohomology := by
  rw [← AInfinityHom.cohomologyMap_comp, ← e.homotopyHomInv.cohomologyMap_eq,
    AInfinityHom.cohomologyMap_id]

/-- On cohomology, `hom` is a right inverse to `inv`. -/
@[simp]
theorem hom_cohomologyMap_comp_inv_cohomologyMap (e : AInfinityHomotopyEquiv AA BB) :
    e.hom.cohomologyMap.comp e.inv.cohomologyMap = NonUnitalAlgHom.id R BB.Cohomology :=
  e.symm.inv_cohomologyMap_comp_hom_cohomologyMap

/-- An `A∞` homotopy equivalence induces a ring equivalence of cohomology algebras. -/
noncomputable def cohomologyRingEquiv (e : AInfinityHomotopyEquiv AA BB) :
    AA.Cohomology ≃+* BB.Cohomology where
  toFun := e.hom.cohomologyMap
  invFun := e.inv.cohomologyMap
  left_inv c := NonUnitalAlgHom.congr_fun e.inv_cohomologyMap_comp_hom_cohomologyMap c
  right_inv c := NonUnitalAlgHom.congr_fun e.hom_cohomologyMap_comp_inv_cohomologyMap c
  map_mul' := map_mul e.hom.cohomologyMap
  map_add' := map_add e.hom.cohomologyMap

/-- Evaluating `e.cohomologyRingEquiv` applies `e.hom.cohomologyMap`. -/
@[simp]
theorem cohomologyRingEquiv_apply (e : AInfinityHomotopyEquiv AA BB) (c : AA.Cohomology) :
    e.cohomologyRingEquiv c = e.hom.cohomologyMap c := (rfl)

/-- Evaluating `e.cohomologyRingEquiv.symm` applies `e.inv.cohomologyMap`. -/
@[simp]
theorem cohomologyRingEquiv_symm_apply (e : AInfinityHomotopyEquiv AA BB) (c : BB.Cohomology) :
    e.cohomologyRingEquiv.symm c = e.inv.cohomologyMap c := (rfl)

/-- The forward morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_hom (e : AInfinityHomotopyEquiv AA BB) : e.hom.IsQuasiIso :=
  (AInfinityHom.isQuasiIso_def e.hom).2 e.cohomologyRingEquiv.bijective

/-- The backward morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_inv (e : AInfinityHomotopyEquiv AA BB) : e.inv.IsQuasiIso :=
  e.symm.isQuasiIso_hom

/-- The arity-one components of an `A∞` homotopy equivalence form a `LinearHomotopyEquiv` between
the unary differentials. -/
noncomputable def toLinearHomotopyEquiv (e : AInfinityHomotopyEquiv AA BB) :
    LinearHomotopyEquiv AA.differential BB.differential where
  hom := e.hom.linearPart
  inv := e.inv.linearPart
  homotopyHomInv := e.homotopyHomInv.linearHomotopy
  homotopyInvHom := e.homotopyInvHom.linearHomotopy
  dN_comp_hom := e.hom.linearPart_comp_differential.symm
  dM_comp_inv := e.inv.linearPart_comp_differential.symm
  dM_comp_homotopyHomInv_add := LinearMap.ext fun a ↦ by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      AInfinityHom.linearPart_id, AInfinityHom.linearPart_comp,
      AInfinityAlgebra.differential_apply] using (e.homotopyHomInv.linearPart_sub_linearPart a).symm
  dN_comp_homotopyInvHom_add := LinearMap.ext fun b ↦ by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      AInfinityHom.linearPart_id, AInfinityHom.linearPart_comp,
      AInfinityAlgebra.differential_apply] using (e.homotopyInvHom.linearPart_sub_linearPart b).symm

/-- The forward map of `e.toLinearHomotopyEquiv` is the linear part of `e.hom`. -/
@[simp]
theorem toLinearHomotopyEquiv_hom (e : AInfinityHomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.hom = e.hom.linearPart := (rfl)

/-- The backward map of `e.toLinearHomotopyEquiv` is the linear part of `e.inv`. -/
@[simp]
theorem toLinearHomotopyEquiv_inv (e : AInfinityHomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.inv = e.inv.linearPart := (rfl)

/-- The source homotopy of `e.toLinearHomotopyEquiv` is the linear homotopy of `e.homotopyHomInv`.
-/
@[simp]
theorem toLinearHomotopyEquiv_homotopyHomInv (e : AInfinityHomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.homotopyHomInv = e.homotopyHomInv.linearHomotopy := (rfl)

/-- The target homotopy of `e.toLinearHomotopyEquiv` is the linear homotopy of `e.homotopyInvHom`.
-/
@[simp]
theorem toLinearHomotopyEquiv_homotopyInvHom (e : AInfinityHomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.homotopyInvHom = e.homotopyInvHom.linearHomotopy := (rfl)

/-- The `LinearHomotopyEquiv` induced on arity-one components is compatible with the internal
gradings. -/
theorem isGraded_toLinearHomotopyEquiv (e : AInfinityHomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.IsGraded AA.grading.piece BB.grading.piece 1 := by
  refine ⟨e.hom.isHomogeneous_linearPart, e.inv.isHomogeneous_linearPart, ?_, ?_⟩
  · rw [toLinearHomotopyEquiv_homotopyHomInv, LinearMap.isHomogeneous_def]
    intro p a ha
    simpa only [sub_eq_add_neg] using e.homotopyHomInv.linearHomotopy_mem ha
  · rw [toLinearHomotopyEquiv_homotopyInvHom, LinearMap.isHomogeneous_def]
    intro p b hb
    simpa only [sub_eq_add_neg] using e.homotopyInvHom.linearHomotopy_mem hb

/-- **Constructive `A∞` homotopy inverse from a graded `LinearHomotopyEquiv` on linear parts**:
lifts `id BB` along `f` to obtain a right homotopy inverse `g`, then lifts the precomposed homotopy
`f ∘ id_AA ⇒ f ∘ (g ∘ f)` along `f` to obtain `id_AA ⇒ g ∘ f`. -/
noncomputable def ofLinearHomotopyEquiv
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    (f : AInfinityHom AA BB) (hf : e.hom = f.linearPart) :
    AInfinityHomotopyEquiv AA BB :=
  let g := AInfinityHom.liftRight e he hf (.id BB)
  let hR := AInfinityHom.liftRightHomotopy e he hf (.id BB)
  let hL' : AInfinityHom.Homotopy (f.comp (.id AA)) (f.comp (g.comp f)) :=
    (hR.compLeft f).cast ((AInfinityHom.id_comp f).trans f.comp_id.symm) (f.comp_assoc g f)
  { hom := f
    inv := g
    homotopyHomInv := AInfinityHom.Homotopy.ofCompRightOfLinearHomotopyEquiv e he hf hL'
    homotopyInvHom := hR }

/-- The forward morphism of `ofLinearHomotopyEquiv e he f hf` is `f`. -/
@[simp]
theorem ofLinearHomotopyEquiv_hom
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    (f : AInfinityHom AA BB) (hf : e.hom = f.linearPart) :
    (ofLinearHomotopyEquiv e he f hf).hom = f := (rfl)

end AInfinityHomotopyEquiv

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- An `A∞` morphism `f : AA ⟶ BB` is a homotopy equivalence when there exists `g : BB ⟶ AA`
with homotopies `id_AA ⇒ g ∘ f` and `id_BB ⇒ f ∘ g`. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (.id AA) (g.comp f)) ∧ Nonempty (Homotopy (.id BB) (f.comp g))

/-- `f.IsHomotopyEquiv` holds if and only if `f` is the forward morphism of an
`AInfinityHomotopyEquiv`. -/
theorem isHomotopyEquiv_iff_nonempty (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ Nonempty {e : AInfinityHomotopyEquiv AA BB // e.hom = f} :=
  ⟨fun ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ ↦ ⟨⟨⟨f, g, h₁, h₂⟩, rfl⟩⟩,
    fun ⟨⟨e, he⟩⟩ ↦ he ▸ ⟨e.inv, ⟨e.homotopyHomInv⟩, ⟨e.homotopyInvHom⟩⟩⟩

/-- Chooses an `AInfinityHomotopyEquiv` with forward map `f` from `hf : f.IsHomotopyEquiv`. -/
noncomputable def IsHomotopyEquiv.homotopyEquiv {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) : AInfinityHomotopyEquiv AA BB :=
  ((isHomotopyEquiv_iff_nonempty f).1 hf).some.1

/-- The forward morphism of `hf.homotopyEquiv` is `f`. -/
@[simp]
theorem IsHomotopyEquiv.homotopyEquiv_hom {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    hf.homotopyEquiv.hom = f :=
  ((isHomotopyEquiv_iff_nonempty f).1 hf).some.2

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso :=
  hf.homotopyEquiv_hom ▸ hf.homotopyEquiv.isQuasiIso_hom

/-- **Characterization of `A∞` homotopy equivalences over a commutative ring**: `f` is an `A∞`
homotopy equivalence if and only if its linear part extends to a graded `LinearHomotopyEquiv`
between the unary differentials. -/
theorem isHomotopyEquiv_iff_exists_linearHomotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ e : LinearHomotopyEquiv AA.differential BB.differential,
        e.IsGraded AA.grading.piece BB.grading.piece 1 ∧ e.hom = f.linearPart := by
  constructor
  · intro hf
    exact ⟨hf.homotopyEquiv.toLinearHomotopyEquiv, hf.homotopyEquiv.isGraded_toLinearHomotopyEquiv,
      congrArg linearPart hf.homotopyEquiv_hom⟩
  · rintro ⟨e, he, hf⟩
    exact (isHomotopyEquiv_iff_nonempty f).2
      ⟨⟨AInfinityHomotopyEquiv.ofLinearHomotopyEquiv e he f hf, rfl⟩⟩

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  (isHomotopyEquiv_iff_nonempty _).2 ⟨⟨AInfinityHomotopyEquiv.refl AA, rfl⟩⟩

/-- `A∞` homotopy equivalences are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨e₁, he₁, hf₁⟩ := (isHomotopyEquiv_iff_exists_linearHomotopyEquiv f).1 hf
  obtain ⟨e₂, he₂, hg₁⟩ := (isHomotopyEquiv_iff_exists_linearHomotopyEquiv g).1 hg
  exact (isHomotopyEquiv_iff_exists_linearHomotopyEquiv _).2
    ⟨e₁.trans e₂, he₁.trans he₂, by rw [LinearHomotopyEquiv.trans_hom, hg₁, hf₁, linearPart_comp]⟩

/-- Replaces the forward map of a graded `LinearHomotopyEquiv` along a degree-`-1` chain homotopy
`f₁ - g₁ = d_B ∘ k + k ∘ d_A`. -/
private def replaceForwardOfChainHomotopy
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {g₁ : A →ₗ[R] B} (hg₁_hom : LinearMap.IsHomogeneous g₁ AA.grading.piece BB.grading.piece 0)
    (hg₁ : BB.differential ∘ₗ g₁ = g₁ ∘ₗ AA.differential)
    {k : A →ₗ[R] B} (hk_hom : LinearMap.IsHomogeneous k AA.grading.piece BB.grading.piece (-1))
    (hk : e.hom - g₁ = BB.differential ∘ₗ k + k ∘ₗ AA.differential) :
    {e' : LinearHomotopyEquiv AA.differential BB.differential //
      e'.IsGraded AA.grading.piece BB.grading.piece 1 ∧ e'.hom = g₁} := by
  refine ⟨{ hom := g₁
            inv := e.inv
            homotopyHomInv := e.homotopyHomInv + e.inv ∘ₗ k
            homotopyInvHom := e.homotopyInvHom + k ∘ₗ e.inv
            dN_comp_hom := hg₁
            dM_comp_inv := e.dM_comp_inv
            dM_comp_homotopyHomInv_add := ?_
            dN_comp_homotopyInvHom_add := ?_ }, ?_, rfl⟩
  · have hik : AA.differential ∘ₗ (e.inv ∘ₗ k) + (e.inv ∘ₗ k) ∘ₗ AA.differential =
        e.inv ∘ₗ e.hom - e.inv ∘ₗ g₁ := LinearMap.ext fun a ↦ by
      have h1 := LinearMap.congr_fun e.dM_comp_inv (k a)
      have h2 := congrArg e.inv (LinearMap.congr_fun hk a)
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add,
        map_sub] at h1 h2 ⊢
      rw [h1, ← h2]
    rw [LinearMap.comp_add, LinearMap.add_comp, add_add_add_comm, e.dM_comp_homotopyHomInv_add,
      hik]
    abel
  · have hki : BB.differential ∘ₗ (k ∘ₗ e.inv) + (k ∘ₗ e.inv) ∘ₗ BB.differential =
        e.hom ∘ₗ e.inv - g₁ ∘ₗ e.inv := LinearMap.ext fun b ↦ by
      have h1 := LinearMap.congr_fun e.dM_comp_inv b
      have h2 := LinearMap.congr_fun hk (e.inv b)
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply] at h1 h2 ⊢
      rw [← h1, ← h2]
    rw [LinearMap.comp_add, LinearMap.add_comp, add_add_add_comm, e.dN_comp_homotopyInvHom_add,
      hki]
    abel
  · refine ⟨hg₁_hom, he.inv, he.homotopyHomInv.add ?_, he.homotopyInvHom.add ?_⟩
    · simpa only [add_zero] using he.inv.comp hk_hom
    · simpa only [zero_add] using hk_hom.comp he.inv

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  have hk_hom :
      LinearMap.IsHomogeneous h.linearHomotopy AA.grading.piece BB.grading.piece (-1) := by
    rw [LinearMap.isHomogeneous_def]
    intro p a ha
    simpa only [sub_eq_add_neg] using h.linearHomotopy_mem ha
  have hk : f.linearPart - g.linearPart =
      BB.differential ∘ₗ h.linearHomotopy + h.linearHomotopy ∘ₗ AA.differential :=
    LinearMap.ext fun a ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        AInfinityAlgebra.differential_apply] using h.linearPart_sub_linearPart a
  rw [isHomotopyEquiv_iff_exists_linearHomotopyEquiv,
    isHomotopyEquiv_iff_exists_linearHomotopyEquiv]
  refine ⟨fun ⟨e, he, hef⟩ ↦ ?_, fun ⟨e, he, heg⟩ ↦ ?_⟩
  · obtain ⟨e', he', he'hom⟩ := replaceForwardOfChainHomotopy e he g.isHomogeneous_linearPart
      g.linearPart_comp_differential.symm hk_hom (hef ▸ hk)
    exact ⟨e', he', he'hom⟩
  · have hk' : g.linearPart - f.linearPart =
        BB.differential ∘ₗ (-h.linearHomotopy) + (-h.linearHomotopy) ∘ₗ AA.differential := by
      rw [LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add, ← hk, neg_sub]
    obtain ⟨e', he', he'hom⟩ := replaceForwardOfChainHomotopy e he f.isHomogeneous_linearPart
      f.linearPart_comp_differential.symm hk_hom.neg (heg ▸ hk')
    exact ⟨e', he', he'hom⟩

/-- Cancels an `A∞` homotopy equivalence on the left of a homotopy. -/
noncomputable def Homotopy.ofCompRight {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv)
    {v₁ v₂ : AInfinityHom CC AA} (h : Homotopy (f.comp v₁) (f.comp v₂)) :
    Homotopy v₁ v₂ :=
  Homotopy.ofCompRightOfLinearHomotopyEquiv hf.homotopyEquiv.toLinearHomotopyEquiv
    hf.homotopyEquiv.isGraded_toLinearHomotopyEquiv
    (congrArg linearPart hf.homotopyEquiv_hom) h

/-- Postcomposing reduced transformations with an `A∞` homotopy equivalence is a quasi-isomorphism
of cochain complexes. -/
theorem IsHomotopyEquiv.quasiIso_reducedTransformationComplexCompRight
    {A' B' C' : Type u} [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    [AddCommGroup C'] [Module R C'] {AA' : AInfinityAlgebra R A'} {BB' : AInfinityAlgebra R B'}
    {CC' : AInfinityAlgebra R C'} {f : AInfinityHom AA' BB'} (hf : f.IsHomotopyEquiv)
    (v₁ v₂ : AInfinityHom CC' AA') :
    QuasiIso (reducedTransformationComplexCompRight v₁ v₂ f) :=
  quasiIso_reducedTransformationComplexCompRight_of_linearHomotopyEquiv
    hf.homotopyEquiv.toLinearHomotopyEquiv hf.homotopyEquiv.isGraded_toLinearHomotopyEquiv
    (congrArg linearPart hf.homotopyEquiv_hom) v₁ v₂

end AInfinityHom

namespace AInfinityHomotopyEquiv

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- The forward morphism of an `AInfinityHomotopyEquiv` satisfies `IsHomotopyEquiv`. -/
theorem isHomotopyEquiv_hom (e : AInfinityHomotopyEquiv AA BB) : e.hom.IsHomotopyEquiv :=
  (AInfinityHom.isHomotopyEquiv_iff_nonempty _).2 ⟨⟨e, rfl⟩⟩

/-- The backward morphism of an `AInfinityHomotopyEquiv` satisfies `IsHomotopyEquiv`. -/
theorem isHomotopyEquiv_inv (e : AInfinityHomotopyEquiv AA BB) : e.inv.IsHomotopyEquiv :=
  e.symm.isHomotopyEquiv_hom

end AInfinityHomotopyEquiv

end CommRing

/-! ### Homotopy inverses of `A∞` quasi-isomorphisms over a field -/

section Field

variable {K : Type uK} {A : Type uA} {B : Type uB} {C : Type uC}
  [Field K]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]
  {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B} {CC : AInfinityAlgebra K C}

namespace AInfinityHom

namespace IsQuasiIso

/-- **Homotopy inverse of an `A∞` quasi-isomorphism over a field**: extends `f` to an
`AInfinityHomotopyEquiv` by constructing a graded `LinearHomotopyEquiv` on the unary complexes from
`InternalGrading.linearHomotopyEquivOfBijectiveHomologyMap` and lifting `id BB` along `f`. -/
noncomputable def homotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHomotopyEquiv AA BB :=
  AInfinityHomotopyEquiv.ofLinearHomotopyEquiv
    (AA.grading.linearHomotopyEquivOfBijectiveHomologyMap BB.grading
      AA.isHomogeneous_differential AA.differential_comp_self_eq_zero
      BB.isHomogeneous_differential BB.differential_comp_self_eq_zero
      f.linearPart_comp_differential ((isQuasiIso_iff_bijective_homologyMap f).1 hf))
    (AA.grading.isGraded_linearHomotopyEquivOfBijectiveHomologyMap BB.grading
      AA.isHomogeneous_differential AA.differential_comp_self_eq_zero
      BB.isHomogeneous_differential BB.differential_comp_self_eq_zero
      f.isHomogeneous_linearPart f.linearPart_comp_differential
      ((isQuasiIso_iff_bijective_homologyMap f).1 hf))
    f
    (AA.grading.linearHomotopyEquivOfBijectiveHomologyMap_hom BB.grading
      AA.isHomogeneous_differential AA.differential_comp_self_eq_zero
      BB.isHomogeneous_differential BB.differential_comp_self_eq_zero
      f.linearPart_comp_differential ((isQuasiIso_iff_bijective_homologyMap f).1 hf))

/-- The forward morphism of `hf.homotopyEquiv` is `f`. -/
@[simp]
theorem homotopyEquiv_hom {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyEquiv.hom = f := (rfl)

/-- A chosen homotopy inverse `BB ⟶ AA` of an `A∞` quasi-isomorphism `f : AA ⟶ BB` over a field. -/
noncomputable def homotopyInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHom BB AA :=
  hf.homotopyEquiv.inv

/-- The homotopy `id AA ⇒ homotopyInv ∘ f`. -/
noncomputable def homotopyHomInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (.id AA) (hf.homotopyInv.comp f) :=
  hf.homotopyEquiv.homotopyHomInv

/-- The homotopy `id BB ⇒ f ∘ homotopyInv`. -/
noncomputable def homotopyInvHom {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (.id BB) (f.comp hf.homotopyInv) :=
  hf.homotopyEquiv.homotopyInvHom

/-- The homotopy inverse of a quasi-isomorphism is itself a quasi-isomorphism. -/
theorem isQuasiIso_homotopyInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInv.IsQuasiIso :=
  hf.homotopyEquiv.isQuasiIso_inv

/-- On cohomology, `hf.homotopyInv` induces the inverse algebra morphism `hf.cohomologyMapInv`. -/
@[simp]
theorem cohomologyMap_homotopyInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInv.cohomologyMap = hf.cohomologyMapInv := by
  ext c
  have h1 := NonUnitalAlgHom.congr_fun hf.cohomologyMap_comp_cohomologyMapInv c
  have h2 := NonUnitalAlgHom.congr_fun
    hf.homotopyEquiv.inv_cohomologyMap_comp_hom_cohomologyMap (hf.cohomologyMapInv c)
  simp only [NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.coe_id, id_eq,
    homotopyEquiv_hom] at h1 h2
  exact (congrArg hf.homotopyInv.cohomologyMap h1).symm.trans h2

/-- Every `A∞` quasi-isomorphism over a field is a homotopy equivalence. -/
theorem isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) : f.IsHomotopyEquiv :=
  hf.homotopyEquiv_hom ▸ hf.homotopyEquiv.isHomotopyEquiv_hom

/-- Over a field, homotopies cancel on the left along any `A∞` quasi-isomorphism. -/
noncomputable def homotopyOfCompRight {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)
    {v₁ v₂ : AInfinityHom CC AA} (h : Homotopy (f.comp v₁) (f.comp v₂)) :
    Homotopy v₁ v₂ :=
  Homotopy.ofCompRight hf.isHomotopyEquiv h

/-- Over a field, postcomposing reduced transformations with any `A∞` quasi-isomorphism is a
quasi-isomorphism of cochain complexes. -/
theorem quasiIso_reducedTransformationComplexCompRight
    {A' B' C' : Type u} [AddCommGroup A'] [Module K A'] [AddCommGroup B'] [Module K B']
    [AddCommGroup C'] [Module K C'] {AA' : AInfinityAlgebra K A'} {BB' : AInfinityAlgebra K B'}
    {CC' : AInfinityAlgebra K C'} {f : AInfinityHom AA' BB'} (hf : f.IsQuasiIso)
    (v₁ v₂ : AInfinityHom CC' AA') :
    QuasiIso (AInfinityHom.reducedTransformationComplexCompRight v₁ v₂ f) :=
  hf.isHomotopyEquiv.quasiIso_reducedTransformationComplexCompRight v₁ v₂

end IsQuasiIso

/-- **Whitehead theorem for `A∞` algebras over a field**: an `A∞` morphism over a field is a
homotopy equivalence if and only if it is a quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end AInfinityHom

end Field

end TauCeti
