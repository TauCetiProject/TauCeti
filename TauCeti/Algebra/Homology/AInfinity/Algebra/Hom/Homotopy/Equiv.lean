/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
public import TauCeti.Algebra.Homology.Contraction.Linear.HomotopyEquiv

/-!
# Homotopy equivalences of A-infinity algebras

Let `f : AA ⟶ BB` be a morphism of `A∞` algebras over a commutative ring `R`.  A *homotopy
equivalence* (`TauCeti.AInfinityHom.HomotopyEquiv`) equips `f` with an `A∞` morphism `g : BB ⟶ AA`
and homotopies `g ∘ f ⇒ id_AA` and `f ∘ g ⇒ id_BB`.  We also define the corresponding predicate
`TauCeti.AInfinityHom.IsHomotopyEquiv` on morphisms, construct homotopies directly from their
suspended Taylor components (`TauCeti.AInfinityHom.Homotopy.ofTaylor`), project any `A∞` homotopy
equivalence to a homogeneous degree-`(-1)` linear chain-homotopy equivalence between the unary
complexes (`TauCeti.AInfinityHom.HomotopyEquiv.toLinearHomotopyEquiv`), and record that every `A∞`
isomorphism is a homotopy equivalence and every `A∞` homotopy equivalence is a quasi-isomorphism.

The converse lifting from linear chain-homotopy equivalences, closure of `A∞` homotopy equivalences
under composition, two-out-of-three, and the Whitehead theorem over a field are established in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Inverse`.

## Main definitions

* `TauCeti.AInfinityHom.Homotopy.ofTaylor`: construct an `A∞` homotopy from its suspended Taylor
  components.
* `TauCeti.AInfinityHom.HomotopyEquiv`: a bundled two-sided `A∞` homotopy equivalence between `A∞`
  algebras.
* `TauCeti.AInfinityHom.IsHomotopyEquiv`: predicate that an `A∞` morphism admits a two-sided `A∞`
  homotopy inverse.
* `TauCeti.AInfinityHom.HomotopyEquiv.refl`, `TauCeti.AInfinityHom.HomotopyEquiv.symm`, and
  `TauCeti.AInfinityHom.HomotopyEquiv.ofLinearPartBijective`: basic constructors and symmetry.
* `TauCeti.AInfinityHom.HomotopyEquiv.toLinearHomotopyEquiv`: underlying linear chain-homotopy
  equivalence between the unary complexes `(A, m₁)` and `(B, m₁)`.

## Main results

* `TauCeti.AInfinityHom.HomotopyEquiv.isHomogeneous_toLinearHomotopyEquiv`: the underlying linear
  chain-homotopy equivalence is homogeneous with homotopy degree `-1`.
* `TauCeti.AInfinityHom.IsIso.isHomotopyEquiv`: every `A∞` isomorphism is a homotopy equivalence.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.isQuasiIso`: every `A∞` homotopy equivalence is a
  quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Section 1.3.
-/

public section

namespace TauCeti

universe uR uA uB

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-! ### Taylor construction and linear-part lemmas for homotopies -/

/-- The linear part of an `A∞` morphism intertwines the unary differentials. -/
theorem differential_comp_linearPart (f : AInfinityHom AA BB) :
    BB.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ AA.differential :=
  LinearMap.ext fun a ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AInfinityAlgebra.differential_apply,
      AInfinityAlgebra.differential_apply, f.linearPart_m_one]

namespace Homotopy

variable {f g : AInfinityHom AA BB}

/-- Construct an `A∞` homotopy from `f` to `g` from its suspended Taylor components `h`, which have
degree `-1` for the suspended gradings and satisfy the suspended component equation against
`gradedCoderivAlong`. -/
noncomputable def ofTaylor (h : ReducedTensorWords R A →ₗ[R] B)
    (hh : LinearMap.IsHomogeneous h (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    (he : f.taylor - g.taylor =
      BB.taylor ∘ₗ
        ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h +
        h ∘ₗ AA.barDifferential) :
    Homotopy f g :=
  ofCoderivation
    (ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h)
    (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
      f.isCoalgHom_barMap g.isCoalgHom_barMap h)
    (ReducedTensorWords.isHomogeneous_gradedCoderivAlong f.isHomogeneous_barMap
      g.isHomogeneous_barMap hh)
    (by rwa [ReducedTensorWords.letter_comp_gradedCoderivAlong])

@[simp]
theorem barHomotopy_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh he) :
    (ofTaylor (f := f) (g := g) h hh he).barHomotopy =
      ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h := by
  rw [ofTaylor, barHomotopy_ofCoderivation]

@[simp]
theorem taylor_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh he) :
    (ofTaylor (f := f) (g := g) h hh he).taylor = h := by
  rw [taylor_def, barHomotopy_ofTaylor, ReducedTensorWords.letter_comp_gradedCoderivAlong]

@[simp]
theorem linearHomotopy_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh he) :
    (ofTaylor (f := f) (g := g) h hh he).linearHomotopy =
      h ∘ₗ ReducedTensorWords.ofLetter R A := by
  ext a
  rw [linearHomotopy_apply, taylor_ofTaylor, LinearMap.comp_apply]

/-- The arity-one component of an `A∞` homotopy is homogeneous of degree `-1`. -/
theorem isHomogeneous_linearHomotopy (h : Homotopy f g) :
    LinearMap.IsHomogeneous h.linearHomotopy AA.grading.piece BB.grading.piece (-1) :=
  LinearMap.isHomogeneous_def.2 fun p _ ha ↦ by
    simpa only [sub_eq_add_neg] using h.linearHomotopy_mem ha

/-- Linear-map form of `Homotopy.linearPart_sub_linearPart`. -/
theorem differential_comp_linearHomotopy_add (h : Homotopy f g) :
    BB.differential ∘ₗ h.linearHomotopy + h.linearHomotopy ∘ₗ AA.differential =
      f.linearPart - g.linearPart :=
  LinearMap.ext fun a ↦ by
    rw [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply,
      h.linearPart_sub_linearPart]

end Homotopy

/-! ### Bundled homotopy equivalences and the `IsHomotopyEquiv` predicate -/

/-- A two-sided `A∞` homotopy equivalence between `AA` and `BB`: forward and inverse `A∞`
morphisms equipped with homotopies `inv ∘ hom ⇒ id` and `hom ∘ inv ⇒ id`. -/
structure HomotopyEquiv (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) where
  /-- The forward `A∞` morphism. -/
  hom : AInfinityHom AA BB
  /-- The homotopy-inverse `A∞` morphism. -/
  inv : AInfinityHom BB AA
  /-- The homotopy from `inv ∘ hom` to the identity on `AA`. -/
  homotopyInvHomId : Homotopy (inv.comp hom) (AInfinityHom.id AA)
  /-- The homotopy from `hom ∘ inv` to the identity on `BB`. -/
  homotopyHomInvId : Homotopy (hom.comp inv) (AInfinityHom.id BB)

/-- An `A∞` morphism is a **homotopy equivalence** when it admits an `A∞` morphism inverse up to
homotopy on both sides. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
      Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB))

/-- Restatement of `IsHomotopyEquiv` for callers outside this module. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
          Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB)) :=
  Iff.rfl

/-- An `A∞` morphism is a homotopy equivalence if and only if it is the forward morphism of a
bundled `HomotopyEquiv`. -/
theorem isHomotopyEquiv_iff_exists_homotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ e : HomotopyEquiv AA BB, e.hom = f := by
  constructor
  · rintro ⟨g, ⟨hA⟩, ⟨hB⟩⟩
    exact ⟨⟨f, g, hA, hB⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e.inv, ⟨e.homotopyInvHomId⟩, ⟨e.homotopyHomInvId⟩⟩

namespace HomotopyEquiv

/-- The identity `A∞` homotopy equivalence. -/
protected def refl (AA : AInfinityAlgebra R A) : HomotopyEquiv AA AA where
  hom := AInfinityHom.id AA
  inv := AInfinityHom.id AA
  homotopyInvHomId := by rw [comp_id]; exact Homotopy.refl _
  homotopyHomInvId := by rw [comp_id]; exact Homotopy.refl _

@[simp]
theorem hom_refl (AA : AInfinityAlgebra R A) : (HomotopyEquiv.refl AA).hom = AInfinityHom.id AA :=
  (rfl)

@[simp]
theorem inv_refl (AA : AInfinityAlgebra R A) : (HomotopyEquiv.refl AA).inv = AInfinityHom.id AA :=
  (rfl)

/-- Swap the forward and inverse morphisms of an `A∞` homotopy equivalence. -/
def symm (e : HomotopyEquiv AA BB) : HomotopyEquiv BB AA where
  hom := e.inv
  inv := e.hom
  homotopyInvHomId := e.homotopyHomInvId
  homotopyHomInvId := e.homotopyInvHomId

@[simp] theorem hom_symm (e : HomotopyEquiv AA BB) : e.symm.hom = e.inv := (rfl)
@[simp] theorem inv_symm (e : HomotopyEquiv AA BB) : e.symm.inv = e.hom := (rfl)

/-- An `A∞` morphism with bijective linear part upgrades to an `A∞` homotopy equivalence with zero
homotopies. -/
noncomputable def ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : HomotopyEquiv AA BB where
  hom := f
  inv := f.inverse hf
  homotopyInvHomId := by rw [f.inverse_comp_cancel hf]; exact Homotopy.refl _
  homotopyHomInvId := by rw [f.comp_inverse_cancel hf]; exact Homotopy.refl _

@[simp]
theorem hom_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) :
    (ofLinearPartBijective f hf).hom = f := (rfl)

@[simp]
theorem inv_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) :
    (ofLinearPartBijective f hf).inv = f.inverse hf := (rfl)

/-- The arity-one components of an `A∞` homotopy equivalence form a linear chain-homotopy
equivalence between the unary complexes. -/
noncomputable def toLinearHomotopyEquiv (e : HomotopyEquiv AA BB) :
    LinearHomotopyEquiv AA.differential BB.differential where
  hom := e.hom.linearPart
  inv := e.inv.linearPart
  homotopyInvHom := e.homotopyInvHomId.linearHomotopy
  homotopyHomInv := e.homotopyHomInvId.linearHomotopy
  dN_comp_hom := e.hom.differential_comp_linearPart
  dM_comp_inv := e.inv.differential_comp_linearPart
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    rw [e.homotopyInvHomId.differential_comp_linearHomotopy_add, linearPart_comp, linearPart_id]
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    rw [e.homotopyHomInvId.differential_comp_linearHomotopy_add, linearPart_comp, linearPart_id]

@[simp]
theorem hom_toLinearHomotopyEquiv (e : HomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.hom = e.hom.linearPart := (rfl)

@[simp]
theorem inv_toLinearHomotopyEquiv (e : HomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.inv = e.inv.linearPart := (rfl)

@[simp]
theorem homotopyInvHom_toLinearHomotopyEquiv (e : HomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.homotopyInvHom = e.homotopyInvHomId.linearHomotopy := (rfl)

@[simp]
theorem homotopyHomInv_toLinearHomotopyEquiv (e : HomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.homotopyHomInv = e.homotopyHomInvId.linearHomotopy := (rfl)

/-- The underlying linear chain-homotopy equivalence of an `A∞` homotopy equivalence is homogeneous
with homotopy degree `-1`. -/
theorem isHomogeneous_toLinearHomotopyEquiv (e : HomotopyEquiv AA BB) :
    e.toLinearHomotopyEquiv.IsHomogeneous AA.grading.piece BB.grading.piece (-1) :=
  ⟨e.hom.isHomogeneous_linearPart, e.inv.isHomogeneous_linearPart,
    e.homotopyInvHomId.isHomogeneous_linearHomotopy,
    e.homotopyHomInvId.isHomogeneous_linearHomotopy⟩

/-- The forward morphism of an `A∞` homotopy equivalence is a homotopy equivalence. -/
theorem isHomotopyEquiv_hom (e : HomotopyEquiv AA BB) : e.hom.IsHomotopyEquiv :=
  ⟨e.inv, ⟨e.homotopyInvHomId⟩, ⟨e.homotopyHomInvId⟩⟩

/-- The inverse morphism of an `A∞` homotopy equivalence is a homotopy equivalence. -/
theorem isHomotopyEquiv_inv (e : HomotopyEquiv AA BB) : e.inv.IsHomotopyEquiv :=
  e.symm.isHomotopyEquiv_hom

/-- The forward morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_hom (e : HomotopyEquiv AA BB) : e.hom.IsQuasiIso := by
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · have h := DFunLike.congr_fun e.homotopyInvHomId.cohomologyMap_eq x
    simpa only [cohomologyMap_comp, NonUnitalAlgHom.comp_apply, cohomologyMap_id,
      NonUnitalAlgHom.coe_id, id_eq] using h
  · have h := DFunLike.congr_fun e.homotopyHomInvId.cohomologyMap_eq y
    simpa only [cohomologyMap_comp, NonUnitalAlgHom.comp_apply, cohomologyMap_id,
      NonUnitalAlgHom.coe_id, id_eq] using h

/-- The inverse morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_inv (e : HomotopyEquiv AA BB) : e.inv.IsQuasiIso :=
  e.symm.isQuasiIso_hom

end HomotopyEquiv

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  (HomotopyEquiv.refl AA).isHomotopyEquiv_hom

/-- Every `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (h : f.IsIso) : f.IsHomotopyEquiv :=
  (HomotopyEquiv.ofLinearPartBijective f h.linearPart_bijective).isHomotopyEquiv_hom

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (h : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 h
  exact e.isQuasiIso_hom

end AInfinityHom

end TauCeti
