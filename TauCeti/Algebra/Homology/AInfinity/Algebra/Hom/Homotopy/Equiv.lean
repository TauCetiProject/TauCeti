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

`TauCeti.AInfinityHom.HomotopyEquiv` bundles a two-sided `A∞` homotopy equivalence between `AA`
and `BB`, with unbundled predicate `TauCeti.AInfinityHom.IsHomotopyEquiv`.  We also construct
homotopies from Taylor components (`Homotopy.ofTaylor`), project to linear chain-homotopy
equivalences (`HomotopyEquiv.toLinearHomotopyEquiv`), and show that `A∞` isomorphisms are homotopy
equivalences and homotopy equivalences are quasi-isomorphisms.

## Main definitions

* `TauCeti.AInfinityHom.Homotopy.ofTaylor`, `TauCeti.AInfinityHom.HomotopyEquiv`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv`.
* `TauCeti.AInfinityHom.HomotopyEquiv.refl`, `symm`, `ofLinearPartBijective`,
  `toLinearHomotopyEquiv`.

## Main results

* `TauCeti.AInfinityHom.HomotopyEquiv.isHomogeneous_toLinearHomotopyEquiv`,
  `TauCeti.AInfinityHom.IsIso.isHomotopyEquiv`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv.isQuasiIso`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Université Paris 7 (2003), Section 1.3.
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
    simp only [LinearMap.comp_apply, AInfinityAlgebra.differential_apply, f.linearPart_m_one]

namespace Homotopy
open ReducedTensorWords
variable {f g : AInfinityHom AA BB}

section OfTaylor
variable (h : ReducedTensorWords R A →ₗ[R] B)
  (hh : LinearMap.IsHomogeneous h (gradedPiece (AA.grading.shift 1))
    (BB.grading.shift 1).piece (-1))
  (he : f.taylor - g.taylor =
    BB.taylor ∘ₗ gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h +
      h ∘ₗ AA.barDifferential)

/-- Construct an `A∞` homotopy from `f` to `g` from its suspended Taylor components `h`. -/
noncomputable def ofTaylor : Homotopy f g :=
  ofCoderivation (gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h)
    (isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
      f.isCoalgHom_barMap g.isCoalgHom_barMap h)
    (isHomogeneous_gradedCoderivAlong f.isHomogeneous_barMap g.isHomogeneous_barMap hh)
    (by rwa [letter_comp_gradedCoderivAlong])
@[simp] theorem barHomotopy_ofTaylor :
    (ofTaylor (f := f) (g := g) h hh he).barHomotopy =
      gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h := by
  rw [ofTaylor, barHomotopy_ofCoderivation]
@[simp] theorem taylor_ofTaylor : (ofTaylor (f := f) (g := g) h hh he).taylor = h := by
  rw [taylor_def, barHomotopy_ofTaylor, letter_comp_gradedCoderivAlong]
@[simp] theorem linearHomotopy_ofTaylor :
    (ofTaylor (f := f) (g := g) h hh he).linearHomotopy = h ∘ₗ ofLetter R A :=
  LinearMap.ext fun a ↦ by rw [linearHomotopy_apply, taylor_ofTaylor, LinearMap.comp_apply]
end OfTaylor

/-- The arity-one component of an `A∞` homotopy is homogeneous of degree `-1`. -/
theorem isHomogeneous_linearHomotopy (h : Homotopy f g) :
    LinearMap.IsHomogeneous h.linearHomotopy AA.grading.piece BB.grading.piece (-1) :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
    simpa only [sub_eq_add_neg] using h.linearHomotopy_mem ha
/-- Linear-map form of `Homotopy.linearPart_sub_linearPart`. -/
theorem differential_comp_linearHomotopy_add (h : Homotopy f g) :
    BB.differential ∘ₗ h.linearHomotopy + h.linearHomotopy ∘ₗ AA.differential =
      f.linearPart - g.linearPart :=
  LinearMap.ext fun a ↦ by
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      AInfinityAlgebra.differential_apply, h.linearPart_sub_linearPart]
end Homotopy

/-! ### Bundled homotopy equivalences and the `IsHomotopyEquiv` predicate -/

/-- A two-sided `A∞` homotopy equivalence between `AA` and `BB`. -/
structure HomotopyEquiv (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) where
  /-- The forward `A∞` morphism. -/
  hom : AInfinityHom AA BB
  /-- The homotopy-inverse `A∞` morphism. -/
  inv : AInfinityHom BB AA
  /-- The homotopy from `inv ∘ hom` to the identity on `AA`. -/
  homotopyInvHomId : Homotopy (inv.comp hom) (AInfinityHom.id AA)
  /-- The homotopy from `hom ∘ inv` to the identity on `BB`. -/
  homotopyHomInvId : Homotopy (hom.comp inv) (AInfinityHom.id BB)

/-- An `A∞` morphism is a **homotopy equivalence** when it has a two-sided homotopy inverse. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
      Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB))

/-- Restatement of `IsHomotopyEquiv` for callers outside this module. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
          Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB)) := Iff.rfl

/-- An `A∞` morphism is a homotopy equivalence iff it is the forward morphism of a
`HomotopyEquiv`. -/
theorem isHomotopyEquiv_iff_exists_homotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ e : HomotopyEquiv AA BB, e.hom = f :=
  ⟨fun ⟨g, ⟨hA⟩, ⟨hB⟩⟩ ↦ ⟨⟨f, g, hA, hB⟩, rfl⟩,
    fun ⟨e, he⟩ ↦ he ▸ ⟨e.inv, ⟨e.homotopyInvHomId⟩, ⟨e.homotopyHomInvId⟩⟩⟩

namespace HomotopyEquiv
/-- The identity `A∞` homotopy equivalence. -/
@[expose, simps hom inv]
protected def refl (AA : AInfinityAlgebra R A) : HomotopyEquiv AA AA where
  hom := AInfinityHom.id AA; inv := AInfinityHom.id AA
  homotopyInvHomId := by rw [comp_id]; exact Homotopy.refl _
  homotopyHomInvId := by rw [comp_id]; exact Homotopy.refl _

/-- An `A∞` morphism with bijective linear part upgrades to an `A∞` homotopy equivalence. -/
@[expose, simps hom inv]
noncomputable def ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : HomotopyEquiv AA BB where
  hom := f; inv := f.inverse hf
  homotopyInvHomId := by rw [f.inverse_comp_cancel hf]; exact Homotopy.refl _
  homotopyHomInvId := by rw [f.comp_inverse_cancel hf]; exact Homotopy.refl _

variable (e : HomotopyEquiv AA BB)

/-- Swap the forward and inverse morphisms of an `A∞` homotopy equivalence. -/
@[expose, simps hom inv]
def symm : HomotopyEquiv BB AA where
  hom := e.inv; inv := e.hom
  homotopyInvHomId := e.homotopyHomInvId; homotopyHomInvId := e.homotopyInvHomId

/-- The arity-one components of an `A∞` homotopy equivalence form a linear chain-homotopy
equivalence between the unary complexes. -/
@[expose, simps -fullyApplied]
noncomputable def toLinearHomotopyEquiv : LinearHomotopyEquiv AA.differential BB.differential where
  hom := e.hom.linearPart; inv := e.inv.linearPart
  homotopyInvHom := e.homotopyInvHomId.linearHomotopy
  homotopyHomInv := e.homotopyHomInvId.linearHomotopy
  dN_comp_hom := e.hom.differential_comp_linearPart
  dM_comp_inv := e.inv.differential_comp_linearPart
  dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM := by
    rw [e.homotopyInvHomId.differential_comp_linearHomotopy_add, linearPart_comp, linearPart_id]
  dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN := by
    rw [e.homotopyHomInvId.differential_comp_linearHomotopy_add, linearPart_comp, linearPart_id]

/-- The underlying linear chain-homotopy equivalence is homogeneous with homotopy degree `-1`. -/
theorem isHomogeneous_toLinearHomotopyEquiv :
    e.toLinearHomotopyEquiv.IsHomogeneous AA.grading.piece BB.grading.piece (-1) :=
  ⟨e.hom.isHomogeneous_linearPart, e.inv.isHomogeneous_linearPart,
    e.homotopyInvHomId.isHomogeneous_linearHomotopy,
    e.homotopyHomInvId.isHomogeneous_linearHomotopy⟩
/-- The forward morphism of an `A∞` homotopy equivalence is a homotopy equivalence. -/
theorem isHomotopyEquiv_hom : e.hom.IsHomotopyEquiv :=
  ⟨e.inv, ⟨e.homotopyInvHomId⟩, ⟨e.homotopyHomInvId⟩⟩
/-- The inverse morphism of an `A∞` homotopy equivalence is a homotopy equivalence. -/
theorem isHomotopyEquiv_inv : e.inv.IsHomotopyEquiv := e.symm.isHomotopyEquiv_hom
/-- The forward morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_hom : e.hom.IsQuasiIso :=
  e.hom.isQuasiIso_def.2 <| Function.bijective_iff_has_inverse.2 ⟨e.inv.cohomologyMap,
    fun x ↦ by simpa only [cohomologyMap_comp, NonUnitalAlgHom.comp_apply, cohomologyMap_id,
      NonUnitalAlgHom.coe_id, id_eq] using DFunLike.congr_fun e.homotopyInvHomId.cohomologyMap_eq x,
    fun y ↦ by simpa only [cohomologyMap_comp, NonUnitalAlgHom.comp_apply, cohomologyMap_id,
      NonUnitalAlgHom.coe_id, id_eq] using DFunLike.congr_fun e.homotopyHomInvId.cohomologyMap_eq y⟩
/-- The inverse morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_inv : e.inv.IsQuasiIso := e.symm.isQuasiIso_hom
end HomotopyEquiv

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp] theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).IsHomotopyEquiv := (HomotopyEquiv.refl AA).isHomotopyEquiv_hom
/-- Every `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (h : f.IsIso) : f.IsHomotopyEquiv :=
  (HomotopyEquiv.ofLinearPartBijective f h.linearPart_bijective).isHomotopyEquiv_hom
/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (h : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 h; exact e.isQuasiIso_hom
end AInfinityHom

end TauCeti
