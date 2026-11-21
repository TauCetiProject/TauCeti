/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
import Mathlib.Tactic.Abel

/-!
# Bundled A-infinity homotopy equivalences and linear chain-homotopy inverses

Defines bundled two-sided `A∞` homotopy equivalences (`TauCeti.AInfinityHom.HomotopyEquiv`) and
homogeneous chain-homotopy inverse data (`TauCeti.AInfinityHom.LinearHomotopyInverse`) for the
arity-one component of an `A∞` morphism, together with reflexivity, symmetry, composition, and
transport along `A∞` homotopies.

## Main definitions

* `TauCeti.AInfinityHom.HomotopyEquiv`: bundled two-sided `A∞` homotopy equivalence.
* `TauCeti.AInfinityHom.LinearHomotopyInverse`: homogeneous chain-homotopy inverse data for `f₁`.
* `TauCeti.AInfinityHom.HomotopyEquiv.linearHomotopyInverse`: linear inverse of a `HomotopyEquiv`.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.comp`: composition of linear inverse data.
* `TauCeti.AInfinityHom.Homotopy.linearHomotopyInverse`: transport along an `A∞` homotopy.

## Main results

* `TauCeti.AInfinityHom.HomotopyEquiv.isQuasiIso_hom`: every `HomotopyEquiv` is a quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Section 1.3.
-/

public section
namespace TauCeti
universe uR uA uB uC
namespace AInfinityHom
variable {R : Type uR} [CommRing R]

/-- A two-sided `A∞` homotopy equivalence between `AA` and `BB`: a pair of `A∞` morphisms `hom` and
`inv` together with homotopies from `inv ∘ hom` and `hom ∘ inv` to the respective identities. -/
@[ext] structure HomotopyEquiv {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) where
  /-- The forward `A∞` morphism. -/
  hom : AInfinityHom AA BB
  /-- The inverse `A∞` morphism up to homotopy. -/
  inv : AInfinityHom BB AA
  /-- Homotopy from `inv ∘ hom` to the identity of `AA`. -/
  homotopyInvCompHom : Homotopy (inv.comp hom) (AInfinityHom.id AA)
  /-- Homotopy from `hom ∘ inv` to the identity of `BB`. -/
  homotopyHomCompInv : Homotopy (hom.comp inv) (AInfinityHom.id BB)

namespace HomotopyEquiv
section Refl
variable {A : Type uA} [AddCommGroup A] [Module R A] (AA : AInfinityAlgebra R A)

/-- The identity `A∞` homotopy equivalence. -/
@[refl] def refl : HomotopyEquiv AA AA :=
  ⟨.id AA, .id AA, .ofEq (comp_id _), .ofEq (comp_id _)⟩

@[simp] theorem refl_hom : (refl AA).hom = AInfinityHom.id AA := (rfl)
@[simp] theorem refl_inv : (refl AA).inv = AInfinityHom.id AA := (rfl)
@[simp] theorem barHomotopy_refl_homotopyInvCompHom :
    (refl AA).homotopyInvCompHom.barHomotopy = 0 := Homotopy.barHomotopy_ofEq _
@[simp] theorem barHomotopy_refl_homotopyHomCompInv :
    (refl AA).homotopyHomCompInv.barHomotopy = 0 := Homotopy.barHomotopy_ofEq _
end Refl
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

section Symm
variable (e : HomotopyEquiv AA BB)

/-- Symmetry of `A∞` homotopy equivalences, exchanging `hom` and `inv`. -/
@[symm] def symm : HomotopyEquiv BB AA :=
  ⟨e.inv, e.hom, e.homotopyHomCompInv, e.homotopyInvCompHom⟩

@[simp] theorem symm_hom : e.symm.hom = e.inv := (rfl)
@[simp] theorem symm_inv : e.symm.inv = e.hom := (rfl)
@[simp] theorem symm_symm : e.symm.symm = e := (rfl)
@[simp] theorem barHomotopy_symm_homotopyInvCompHom :
    e.symm.homotopyInvCompHom.barHomotopy = e.homotopyHomCompInv.barHomotopy := (rfl)
@[simp] theorem barHomotopy_symm_homotopyHomCompInv :
    e.symm.homotopyHomCompInv.barHomotopy = e.homotopyInvCompHom.barHomotopy := (rfl)

/-- The forward morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_hom : e.hom.IsQuasiIso :=
  (isQuasiIso_def _).2 <| Function.bijective_iff_has_inverse.2 ⟨e.inv.cohomologyMap,
    fun c ↦ DFunLike.congr_fun (cohomologyMap_comp e.inv e.hom ▸
      cohomologyMap_id AA ▸ e.homotopyInvCompHom.cohomologyMap_eq) c,
    fun c ↦ DFunLike.congr_fun (cohomologyMap_comp e.hom e.inv ▸
      cohomologyMap_id BB ▸ e.homotopyHomCompInv.cohomologyMap_eq) c⟩

/-- The inverse morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_inv : e.inv.IsQuasiIso := e.symm.isQuasiIso_hom
end Symm

section Bijective
variable (f : AInfinityHom AA BB) (hf : Function.Bijective f.linearPart)

/-- An `A∞` morphism with bijective linear part packaged as a `HomotopyEquiv`. -/
noncomputable def ofLinearPartBijective : HomotopyEquiv AA BB :=
  ⟨f, f.inverse hf, .ofEq (f.inverse_comp_cancel hf), .ofEq (f.comp_inverse_cancel hf)⟩

@[simp] theorem ofLinearPartBijective_hom : (ofLinearPartBijective f hf).hom = f := (rfl)
@[simp] theorem ofLinearPartBijective_inv :
    (ofLinearPartBijective f hf).inv = f.inverse hf := (rfl)
end Bijective
end HomotopyEquiv

/-- Homogeneous chain-homotopy inverse data for the linear part `f₁` of `f : AA ⟶ BB`. -/
@[ext] structure LinearHomotopyInverse {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
    (f : AInfinityHom AA BB) where
  /-- The chain-level homotopy inverse of `f.linearPart`. -/
  inv : B →ₗ[R] A
  /-- The left chain homotopy witnessing `inv ∘ f₁ - id = d_A ∘ h_A + h_A ∘ d_A`. -/
  homotopyLeft : A →ₗ[R] A
  /-- The right chain homotopy witnessing `f₁ ∘ inv - id = d_B ∘ h_B + h_B ∘ d_B`. -/
  homotopyRight : B →ₗ[R] B
  /-- `inv` is homogeneous of internal degree `0`. -/
  isHomogeneous_inv : LinearMap.IsHomogeneous inv BB.grading.piece AA.grading.piece 0
  /-- `inv` is a chain map intertwining `BB.differential` and `AA.differential`. -/
  differential_comp_inv : AA.differential ∘ₗ inv = inv ∘ₗ BB.differential
  /-- `homotopyLeft` is homogeneous of internal degree `-1`. -/
  isHomogeneous_homotopyLeft :
    LinearMap.IsHomogeneous homotopyLeft AA.grading.piece AA.grading.piece (-1)
  /-- The left chain-homotopy equation `inv ∘ f₁ - id = d_A ∘ h_A + h_A ∘ d_A`. -/
  inv_comp_linearPart_sub_id : inv ∘ₗ f.linearPart - LinearMap.id =
    AA.differential ∘ₗ homotopyLeft + homotopyLeft ∘ₗ AA.differential
  /-- `homotopyRight` is homogeneous of internal degree `-1`. -/
  isHomogeneous_homotopyRight :
    LinearMap.IsHomogeneous homotopyRight BB.grading.piece BB.grading.piece (-1)
  /-- The right chain-homotopy equation `f₁ ∘ inv - id = d_B ∘ h_B + h_B ∘ d_B`. -/
  linearPart_comp_inv_sub_id : f.linearPart ∘ₗ inv - LinearMap.id =
    BB.differential ∘ₗ homotopyRight + homotopyRight ∘ₗ BB.differential

namespace HomotopyEquiv
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} (e : HomotopyEquiv AA BB)

/-- The linear chain-homotopy inverse data of the arity-one maps of a `HomotopyEquiv`. -/
noncomputable def linearHomotopyInverse : LinearHomotopyInverse e.hom where
  inv := e.inv.linearPart
  homotopyLeft := e.homotopyInvCompHom.linearHomotopy
  homotopyRight := e.homotopyHomCompInv.linearHomotopy
  isHomogeneous_inv := e.inv.isHomogeneous_linearPart
  differential_comp_inv := e.inv.differential_comp_linearPart
  isHomogeneous_homotopyLeft := e.homotopyInvCompHom.isHomogeneous_linearHomotopy
  inv_comp_linearPart_sub_id := by simpa only [linearPart_comp, linearPart_id] using
    e.homotopyInvCompHom.linearPart_sub_linearPart_eq
  isHomogeneous_homotopyRight := e.homotopyHomCompInv.isHomogeneous_linearHomotopy
  linearPart_comp_inv_sub_id := by simpa only [linearPart_comp, linearPart_id] using
    e.homotopyHomCompInv.linearPart_sub_linearPart_eq

@[simp] theorem linearHomotopyInverse_inv : e.linearHomotopyInverse.inv = e.inv.linearPart := (rfl)
@[simp] theorem linearHomotopyInverse_homotopyLeft :
    e.linearHomotopyInverse.homotopyLeft = e.homotopyInvCompHom.linearHomotopy := (rfl)
@[simp] theorem linearHomotopyInverse_homotopyRight :
    e.linearHomotopyInverse.homotopyRight = e.homotopyHomCompInv.linearHomotopy := (rfl)
end HomotopyEquiv

namespace LinearHomotopyInverse
section Refl
variable {A : Type uA} [AddCommGroup A] [Module R A] (AA : AInfinityAlgebra R A)

/-- Linear chain-homotopy inverse data for the identity `A∞` morphism. -/
noncomputable def refl : LinearHomotopyInverse (AInfinityHom.id AA) :=
  (HomotopyEquiv.refl AA).linearHomotopyInverse

@[simp] theorem refl_inv : (refl AA).inv = LinearMap.id := linearPart_id AA
@[simp] theorem refl_homotopyLeft : (refl AA).homotopyLeft = 0 := Homotopy.linearHomotopy_ofEq _
@[simp] theorem refl_homotopyRight : (refl AA).homotopyRight = 0 := Homotopy.linearHomotopy_ofEq _
end Refl

section Comp
variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}
  {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
  (Lg : LinearHomotopyInverse g) (Lf : LinearHomotopyInverse f)

/-- Composition of linear chain-homotopy inverse data along composable `A∞` morphisms. -/
noncomputable def comp : LinearHomotopyInverse (g.comp f) where
  inv := Lf.inv ∘ₗ Lg.inv
  homotopyLeft := Lf.inv ∘ₗ Lg.homotopyLeft ∘ₗ f.linearPart + Lf.homotopyLeft
  homotopyRight := g.linearPart ∘ₗ Lf.homotopyRight ∘ₗ Lg.inv + Lg.homotopyRight
  isHomogeneous_inv := add_zero (0 : ℤ) ▸ Lf.isHomogeneous_inv.comp Lg.isHomogeneous_inv
  differential_comp_inv := by
    rw [← LinearMap.comp_assoc, Lf.differential_comp_inv, LinearMap.comp_assoc,
      Lg.differential_comp_inv, LinearMap.comp_assoc]
  isHomogeneous_homotopyLeft := LinearMap.IsHomogeneous.add
    (add_zero (-1 : ℤ) ▸ Lf.isHomogeneous_inv.comp
      (zero_add (-1 : ℤ) ▸ Lg.isHomogeneous_homotopyLeft.comp f.isHomogeneous_linearPart))
    Lf.isHomogeneous_homotopyLeft
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    have hg := congrArg Lf.inv (LinearMap.congr_fun Lg.inv_comp_linearPart_sub_id (f.linearPart a))
    have hf := LinearMap.congr_fun Lf.inv_comp_linearPart_sub_id a
    have hd₁ := LinearMap.congr_fun Lf.differential_comp_inv (Lg.homotopyLeft (f.linearPart a))
    have hd₂ := LinearMap.congr_fun f.differential_comp_linearPart a
    simp only [linearPart_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add] at hg hf hd₁ hd₂ ⊢
    rw [← sub_add_sub_cancel _ (Lf.inv (f.linearPart a)) a, hg, hf, hd₁, ← hd₂]; abel
  isHomogeneous_homotopyRight := LinearMap.IsHomogeneous.add
    (add_zero (-1 : ℤ) ▸ g.isHomogeneous_linearPart.comp
      (zero_add (-1 : ℤ) ▸ Lf.isHomogeneous_homotopyRight.comp Lg.isHomogeneous_inv))
    Lg.isHomogeneous_homotopyRight
  linearPart_comp_inv_sub_id := LinearMap.ext fun c ↦ by
    have hf := congrArg g.linearPart (LinearMap.congr_fun Lf.linearPart_comp_inv_sub_id (Lg.inv c))
    have hg := LinearMap.congr_fun Lg.linearPart_comp_inv_sub_id c
    have hd₁ := LinearMap.congr_fun g.differential_comp_linearPart (Lf.homotopyRight (Lg.inv c))
    have hd₂ := LinearMap.congr_fun Lg.differential_comp_inv c
    simp only [linearPart_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add] at hf hg hd₁ hd₂ ⊢
    rw [← sub_add_sub_cancel _ (g.linearPart (Lg.inv c)) c, hf, hg, hd₁, hd₂]; abel

@[simp] theorem comp_inv : (Lg.comp Lf).inv = Lf.inv ∘ₗ Lg.inv := (rfl)
@[simp] theorem comp_homotopyLeft :
    (Lg.comp Lf).homotopyLeft = Lf.inv ∘ₗ Lg.homotopyLeft ∘ₗ f.linearPart + Lf.homotopyLeft := (rfl)
@[simp] theorem comp_homotopyRight : (Lg.comp Lf).homotopyRight =
    g.linearPart ∘ₗ Lf.homotopyRight ∘ₗ Lg.inv + Lg.homotopyRight := (rfl)
end Comp

private noncomputable def ofChainHomotopy {A : Type uA} {B : Type uB} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] {AA : AInfinityAlgebra R A}
    {BB : AInfinityAlgebra R B} {f f' : AInfinityHom AA BB} (k : A →ₗ[R] B)
    (hk : LinearMap.IsHomogeneous k AA.grading.piece BB.grading.piece (-1))
    (heq : f.linearPart - f'.linearPart = BB.differential ∘ₗ k + k ∘ₗ AA.differential)
    (L : LinearHomotopyInverse f) : LinearHomotopyInverse f' where
  inv := L.inv
  homotopyLeft := L.homotopyLeft - L.inv ∘ₗ k
  homotopyRight := L.homotopyRight - k ∘ₗ L.inv
  isHomogeneous_inv := L.isHomogeneous_inv
  differential_comp_inv := L.differential_comp_inv
  isHomogeneous_homotopyLeft :=
    L.isHomogeneous_homotopyLeft.sub (add_zero (-1 : ℤ) ▸ L.isHomogeneous_inv.comp hk)
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    have ha := LinearMap.congr_fun L.inv_comp_linearPart_sub_id a
    have hd := LinearMap.congr_fun L.differential_comp_inv (k a)
    simp only [eq_sub_of_add_eq' (sub_eq_iff_eq_add.1 heq).symm, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_add] at ha hd ⊢
    rw [sub_right_comm, ha, ← hd]; abel
  isHomogeneous_homotopyRight :=
    L.isHomogeneous_homotopyRight.sub (zero_add (-1 : ℤ) ▸ hk.comp L.isHomogeneous_inv)
  linearPart_comp_inv_sub_id := LinearMap.ext fun b ↦ by
    have hb := LinearMap.congr_fun L.linearPart_comp_inv_sub_id b
    have hd := LinearMap.congr_fun L.differential_comp_inv b
    simp only [eq_sub_of_add_eq' (sub_eq_iff_eq_add.1 heq).symm, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub] at hb hd ⊢
    rw [sub_right_comm, hb, hd]; abel
end LinearHomotopyInverse

namespace Homotopy
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {f f' : AInfinityHom AA BB}
  (h : Homotopy f f')

/-- Transport `LinearHomotopyInverse` data forward along an `A∞` homotopy `Homotopy f f'`. -/
noncomputable def linearHomotopyInverse (L : LinearHomotopyInverse f) : LinearHomotopyInverse f' :=
  LinearHomotopyInverse.ofChainHomotopy h.linearHomotopy h.isHomogeneous_linearHomotopy
    h.linearPart_sub_linearPart_eq L

@[simp] theorem linearHomotopyInverse_inv (L : LinearHomotopyInverse f) :
    (h.linearHomotopyInverse L).inv = L.inv := (rfl)
@[simp] theorem linearHomotopyInverse_homotopyLeft (L : LinearHomotopyInverse f) :
    (h.linearHomotopyInverse L).homotopyLeft = L.homotopyLeft - L.inv ∘ₗ h.linearHomotopy := (rfl)
@[simp] theorem linearHomotopyInverse_homotopyRight (L : LinearHomotopyInverse f) :
    (h.linearHomotopyInverse L).homotopyRight = L.homotopyRight - h.linearHomotopy ∘ₗ L.inv := (rfl)

/-- Transport `LinearHomotopyInverse` data backward along an `A∞` homotopy `Homotopy f f'`. -/
noncomputable def linearHomotopyInverseSymm (L : LinearHomotopyInverse f') :
    LinearHomotopyInverse f :=
  LinearHomotopyInverse.ofChainHomotopy (-h.linearHomotopy) h.isHomogeneous_linearHomotopy.neg
    (by rw [← neg_sub, h.linearPart_sub_linearPart_eq, neg_add, LinearMap.comp_neg,
      LinearMap.neg_comp]) L

@[simp] theorem linearHomotopyInverseSymm_inv (L : LinearHomotopyInverse f') :
    (h.linearHomotopyInverseSymm L).inv = L.inv := (rfl)
@[simp] theorem linearHomotopyInverseSymm_homotopyLeft (L : LinearHomotopyInverse f') :
    (h.linearHomotopyInverseSymm L).homotopyLeft =
      L.homotopyLeft + L.inv ∘ₗ h.linearHomotopy := by
  rw [← sub_neg_eq_add, ← LinearMap.comp_neg]; rfl
@[simp] theorem linearHomotopyInverseSymm_homotopyRight (L : LinearHomotopyInverse f') :
    (h.linearHomotopyInverseSymm L).homotopyRight =
      L.homotopyRight + h.linearHomotopy ∘ₗ L.inv := by
  rw [← sub_neg_eq_add, ← LinearMap.neg_comp]; rfl
end Homotopy
end AInfinityHom
end TauCeti
