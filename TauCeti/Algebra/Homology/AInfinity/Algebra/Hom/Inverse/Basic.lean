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

An `A∞` morphism `f : A ⟶ B` over a commutative ring `R` need not admit a homotopy inverse merely
because it induces an isomorphism on cohomology: already for complexes with `mₙ = 0` (`n ≥ 2`),
quasi-isomorphisms invert up to homotopy only when they admit chain-homotopy inverses.

This file defines bundled two-sided `A∞` homotopy equivalences
(`TauCeti.AInfinityHom.HomotopyEquiv`) together with the arity-one chain-homotopy inverse data
(`TauCeti.AInfinityHom.LinearHomotopyInverse`) that characterizes homotopy invertibility over an
arbitrary commutative ring.  Reading off arity-one components extracts
`LinearHomotopyInverse e.hom` from any `e : HomotopyEquiv AA BB`, and `LinearHomotopyInverse`
composes along morphisms and transports in both directions along `A∞` homotopies.

Lifting `LinearHomotopyInverse f` back to a right `A∞` homotopy inverse is carried out in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Right`, upgraded to a two-sided
`HomotopyEquiv` in `TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Vogt`, and specialized to
quasi-isomorphisms over a field in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.QuasiIso`.

## Main definitions

* `TauCeti.AInfinityHom.HomotopyEquiv`: a bundled two-sided `A∞` homotopy equivalence between two
  `A∞` algebras.
* `TauCeti.AInfinityHom.LinearHomotopyInverse`: homogeneous chain-homotopy inverse data for the
  linear part `f₁` of an `A∞` morphism `f`.
* `TauCeti.AInfinityHom.HomotopyEquiv.linearHomotopyInverse`: arity-one `LinearHomotopyInverse` data
  of a bundled `A∞` homotopy equivalence.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.comp`: composition of linear chain-homotopy inverse
  data along composable `A∞` morphisms.
* `TauCeti.AInfinityHom.Homotopy.linearHomotopyInverse` and
  `TauCeti.AInfinityHom.Homotopy.linearHomotopyInverseSymm`: transport of `LinearHomotopyInverse`
  data along an `A∞` homotopy.

## Main results

* `TauCeti.AInfinityHom.HomotopyEquiv.isQuasiIso_hom` and
  `TauCeti.AInfinityHom.HomotopyEquiv.isQuasiIso_inv`: both directions of an `A∞` homotopy
  equivalence are quasi-isomorphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Section 1.3.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

variable {R : Type uR} [CommRing R]

/-- A two-sided `A∞` homotopy equivalence between `AA` and `BB`: a pair of `A∞` morphisms `hom` and
`inv` together with homotopies from `inv ∘ hom` and `hom ∘ inv` to the respective identities. -/
@[ext]
structure HomotopyEquiv {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A]
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

section Single

variable {A : Type uA} [AddCommGroup A] [Module R A]

/-- The identity `A∞` homotopy equivalence. -/
@[refl]
def refl (AA : AInfinityAlgebra R A) : HomotopyEquiv AA AA where
  hom := AInfinityHom.id AA
  inv := AInfinityHom.id AA
  homotopyInvCompHom := Homotopy.ofEq (comp_id _)
  homotopyHomCompInv := Homotopy.ofEq (comp_id _)

@[simp]
theorem refl_hom (AA : AInfinityAlgebra R A) : (refl AA).hom = AInfinityHom.id AA := (rfl)

@[simp]
theorem refl_inv (AA : AInfinityAlgebra R A) : (refl AA).inv = AInfinityHom.id AA := (rfl)

@[simp]
theorem barHomotopy_refl_homotopyInvCompHom (AA : AInfinityAlgebra R A) :
    (refl AA).homotopyInvCompHom.barHomotopy = 0 :=
  Homotopy.barHomotopy_ofEq _

@[simp]
theorem barHomotopy_refl_homotopyHomCompInv (AA : AInfinityAlgebra R A) :
    (refl AA).homotopyHomCompInv.barHomotopy = 0 :=
  Homotopy.barHomotopy_ofEq _

end Single

section Pair

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- Symmetry of `A∞` homotopy equivalences, exchanging `hom` and `inv`. -/
@[symm]
def symm (e : HomotopyEquiv AA BB) : HomotopyEquiv BB AA where
  hom := e.inv
  inv := e.hom
  homotopyInvCompHom := e.homotopyHomCompInv
  homotopyHomCompInv := e.homotopyInvCompHom

@[simp]
theorem symm_hom (e : HomotopyEquiv AA BB) : e.symm.hom = e.inv := (rfl)

@[simp]
theorem symm_inv (e : HomotopyEquiv AA BB) : e.symm.inv = e.hom := (rfl)

@[simp]
theorem barHomotopy_symm_homotopyInvCompHom (e : HomotopyEquiv AA BB) :
    e.symm.homotopyInvCompHom.barHomotopy = e.homotopyHomCompInv.barHomotopy := (rfl)

@[simp]
theorem barHomotopy_symm_homotopyHomCompInv (e : HomotopyEquiv AA BB) :
    e.symm.homotopyHomCompInv.barHomotopy = e.homotopyInvCompHom.barHomotopy := (rfl)

@[simp]
theorem symm_symm (e : HomotopyEquiv AA BB) : e.symm.symm = e := (rfl)

/-- An `A∞` morphism with bijective linear part packaged as a `HomotopyEquiv` with zero
homotopies. -/
noncomputable def ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : HomotopyEquiv AA BB where
  hom := f
  inv := f.inverse hf
  homotopyInvCompHom := Homotopy.ofEq (f.inverse_comp_cancel hf)
  homotopyHomCompInv := Homotopy.ofEq (f.comp_inverse_cancel hf)

@[simp]
theorem ofLinearPartBijective_hom (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : (ofLinearPartBijective f hf).hom = f := (rfl)

@[simp]
theorem ofLinearPartBijective_inv (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) :
    (ofLinearPartBijective f hf).inv = f.inverse hf := (rfl)

/-- The forward morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_hom (e : HomotopyEquiv AA BB) : e.hom.IsQuasiIso := by
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.cohomologyMap, fun c ↦ ?_, fun c ↦ ?_⟩
  · have h := e.homotopyInvCompHom.cohomologyMap_eq
    rw [cohomologyMap_comp, cohomologyMap_id] at h
    exact DFunLike.congr_fun h c
  · have h := e.homotopyHomCompInv.cohomologyMap_eq
    rw [cohomologyMap_comp, cohomologyMap_id] at h
    exact DFunLike.congr_fun h c

/-- The inverse morphism of an `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_inv (e : HomotopyEquiv AA BB) : e.inv.IsQuasiIso :=
  e.symm.isQuasiIso_hom

end Pair

end HomotopyEquiv

/-- Homogeneous chain-homotopy inverse data for the linear part `f₁` of an `A∞` morphism
`f : AA ⟶ BB`: a degree-zero chain map `inv : B →ₗ[R] A` together with degree-`-1` chain
homotopies `homotopyLeft` and `homotopyRight` bounding `inv ∘ f₁ - id` and `f₁ ∘ inv - id`. -/
@[ext]
structure LinearHomotopyInverse {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
    (f : AInfinityHom AA BB) where
  /-- The chain-level homotopy inverse of `f.linearPart`. -/
  inv : B →ₗ[R] A
  /-- The left chain homotopy witnessing `inv ∘ f₁ - id = d_A ∘ h_A + h_A ∘ d_A`. -/
  homotopyLeft : A →ₗ[R] A
  /-- The right chain homotopy witnessing `f₁ ∘ inv - id = d_B ∘ h_B + h_B ∘ d_B`. -/
  homotopyRight : B →ₗ[R] B
  /-- `inv` preserves internal degree. -/
  isHomogeneous_inv : LinearMap.IsHomogeneous inv BB.grading.piece AA.grading.piece 0
  /-- `inv` intertwines the unary differentials. -/
  differential_comp_inv : AA.differential ∘ₗ inv = inv ∘ₗ BB.differential
  /-- `homotopyLeft` has internal degree `-1`. -/
  isHomogeneous_homotopyLeft :
    LinearMap.IsHomogeneous homotopyLeft AA.grading.piece AA.grading.piece (-1)
  /-- Left chain-homotopy equation `inv ∘ f₁ - id = d_A ∘ homotopyLeft + homotopyLeft ∘ d_A`. -/
  inv_comp_linearPart_sub_id :
    inv ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ homotopyLeft + homotopyLeft ∘ₗ AA.differential
  /-- `homotopyRight` has internal degree `-1`. -/
  isHomogeneous_homotopyRight :
    LinearMap.IsHomogeneous homotopyRight BB.grading.piece BB.grading.piece (-1)
  /-- Right chain-homotopy equation `f₁ ∘ inv - id = d_B ∘ homotopyRight + homotopyRight ∘ d_B`. -/
  linearPart_comp_inv_sub_id :
    f.linearPart ∘ₗ inv - LinearMap.id =
      BB.differential ∘ₗ homotopyRight + homotopyRight ∘ₗ BB.differential

namespace HomotopyEquiv

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- The linear chain-homotopy inverse data of the underlying arity-one maps of an `A∞` homotopy
equivalence. -/
noncomputable def linearHomotopyInverse (e : HomotopyEquiv AA BB) :
    LinearHomotopyInverse e.hom where
  inv := e.inv.linearPart
  homotopyLeft := e.homotopyInvCompHom.linearHomotopy
  homotopyRight := e.homotopyHomCompInv.linearHomotopy
  isHomogeneous_inv := e.inv.isHomogeneous_linearPart
  differential_comp_inv := e.inv.differential_comp_linearPart
  isHomogeneous_homotopyLeft := e.homotopyInvCompHom.isHomogeneous_linearHomotopy
  inv_comp_linearPart_sub_id := by
    simpa only [linearPart_comp, linearPart_id] using
      e.homotopyInvCompHom.linearPart_sub_linearPart_eq
  isHomogeneous_homotopyRight := e.homotopyHomCompInv.isHomogeneous_linearHomotopy
  linearPart_comp_inv_sub_id := by
    simpa only [linearPart_comp, linearPart_id] using
      e.homotopyHomCompInv.linearPart_sub_linearPart_eq

@[simp]
theorem linearHomotopyInverse_inv (e : HomotopyEquiv AA BB) :
    e.linearHomotopyInverse.inv = e.inv.linearPart := (rfl)

@[simp]
theorem linearHomotopyInverse_homotopyLeft (e : HomotopyEquiv AA BB) :
    e.linearHomotopyInverse.homotopyLeft = e.homotopyInvCompHom.linearHomotopy := (rfl)

@[simp]
theorem linearHomotopyInverse_homotopyRight (e : HomotopyEquiv AA BB) :
    e.linearHomotopyInverse.homotopyRight = e.homotopyHomCompInv.linearHomotopy := (rfl)

end HomotopyEquiv

namespace LinearHomotopyInverse

section Single

variable {A : Type uA} [AddCommGroup A] [Module R A]

/-- Linear chain-homotopy inverse data for the identity `A∞` morphism. -/
noncomputable def refl (AA : AInfinityAlgebra R A) :
    LinearHomotopyInverse (AInfinityHom.id AA) :=
  (HomotopyEquiv.refl AA).linearHomotopyInverse

@[simp]
theorem refl_inv (AA : AInfinityAlgebra R A) : (refl AA).inv = LinearMap.id :=
  linearPart_id AA

@[simp]
theorem refl_homotopyLeft (AA : AInfinityAlgebra R A) : (refl AA).homotopyLeft = 0 :=
  Homotopy.linearHomotopy_ofEq _

@[simp]
theorem refl_homotopyRight (AA : AInfinityAlgebra R A) : (refl AA).homotopyRight = 0 :=
  Homotopy.linearHomotopy_ofEq _

end Single

section Comp

variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

private theorem comp_inv_comp_linearPart_sub_id {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (Lg : LinearHomotopyInverse g) (Lf : LinearHomotopyInverse f) :
    (Lf.inv ∘ₗ Lg.inv) ∘ₗ (g.comp f).linearPart - LinearMap.id =
      AA.differential ∘ₗ (Lf.inv ∘ₗ Lg.homotopyLeft ∘ₗ f.linearPart + Lf.homotopyLeft) +
        (Lf.inv ∘ₗ Lg.homotopyLeft ∘ₗ f.linearPart + Lf.homotopyLeft) ∘ₗ AA.differential := by
  ext a
  have hg := congrArg Lf.inv (LinearMap.congr_fun Lg.inv_comp_linearPart_sub_id (f.linearPart a))
  have hf := LinearMap.congr_fun Lf.inv_comp_linearPart_sub_id a
  have hd₁ := LinearMap.congr_fun Lf.differential_comp_inv (Lg.homotopyLeft (f.linearPart a))
  have hd₂ := LinearMap.congr_fun f.differential_comp_linearPart a
  simp only [linearPart_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub, map_add] at hg hf hd₁ hd₂ ⊢
  rw [← sub_add_sub_cancel (Lf.inv (Lg.inv (g.linearPart (f.linearPart a))))
    (Lf.inv (f.linearPart a)) a, hg, hf, hd₁, ← hd₂]
  abel

private theorem comp_linearPart_comp_inv_sub_id {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (Lg : LinearHomotopyInverse g) (Lf : LinearHomotopyInverse f) :
    (g.comp f).linearPart ∘ₗ (Lf.inv ∘ₗ Lg.inv) - LinearMap.id =
      CC.differential ∘ₗ (g.linearPart ∘ₗ Lf.homotopyRight ∘ₗ Lg.inv + Lg.homotopyRight) +
        (g.linearPart ∘ₗ Lf.homotopyRight ∘ₗ Lg.inv + Lg.homotopyRight) ∘ₗ CC.differential := by
  ext c
  have hf := congrArg g.linearPart (LinearMap.congr_fun Lf.linearPart_comp_inv_sub_id (Lg.inv c))
  have hg := LinearMap.congr_fun Lg.linearPart_comp_inv_sub_id c
  have hd₁ := LinearMap.congr_fun g.differential_comp_linearPart (Lf.homotopyRight (Lg.inv c))
  have hd₂ := LinearMap.congr_fun Lg.differential_comp_inv c
  simp only [linearPart_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub, map_add] at hf hg hd₁ hd₂ ⊢
  rw [← sub_add_sub_cancel (g.linearPart (f.linearPart (Lf.inv (Lg.inv c))))
    (g.linearPart (Lg.inv c)) c, hf, hg, hd₁, hd₂]
  abel

/-- Composition of linear chain-homotopy inverse data along composable `A∞` morphisms. -/
noncomputable def comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (Lg : LinearHomotopyInverse g) (Lf : LinearHomotopyInverse f) :
    LinearHomotopyInverse (g.comp f) where
  inv := Lf.inv ∘ₗ Lg.inv
  homotopyLeft := Lf.inv ∘ₗ Lg.homotopyLeft ∘ₗ f.linearPart + Lf.homotopyLeft
  homotopyRight := g.linearPart ∘ₗ Lf.homotopyRight ∘ₗ Lg.inv + Lg.homotopyRight
  isHomogeneous_inv := by
    simpa only [add_zero] using Lf.isHomogeneous_inv.comp Lg.isHomogeneous_inv
  differential_comp_inv := by
    rw [← LinearMap.comp_assoc, Lf.differential_comp_inv, LinearMap.comp_assoc,
      Lg.differential_comp_inv, LinearMap.comp_assoc]
  isHomogeneous_homotopyLeft := by
    have h₁ : LinearMap.IsHomogeneous (Lf.inv ∘ₗ Lg.homotopyLeft ∘ₗ f.linearPart)
        AA.grading.piece AA.grading.piece (-1) := by
      simpa only [add_zero, zero_add] using
        Lf.isHomogeneous_inv.comp (Lg.isHomogeneous_homotopyLeft.comp f.isHomogeneous_linearPart)
    exact h₁.add Lf.isHomogeneous_homotopyLeft
  inv_comp_linearPart_sub_id := comp_inv_comp_linearPart_sub_id Lg Lf
  isHomogeneous_homotopyRight := by
    have h₁ : LinearMap.IsHomogeneous (g.linearPart ∘ₗ Lf.homotopyRight ∘ₗ Lg.inv)
        CC.grading.piece CC.grading.piece (-1) := by
      simpa only [add_zero, zero_add] using
        g.isHomogeneous_linearPart.comp (Lf.isHomogeneous_homotopyRight.comp Lg.isHomogeneous_inv)
    exact h₁.add Lg.isHomogeneous_homotopyRight
  linearPart_comp_inv_sub_id := comp_linearPart_comp_inv_sub_id Lg Lf

@[simp]
theorem comp_inv {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (Lg : LinearHomotopyInverse g) (Lf : LinearHomotopyInverse f) :
    (Lg.comp Lf).inv = Lf.inv ∘ₗ Lg.inv := (rfl)

@[simp]
theorem comp_homotopyLeft {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (Lg : LinearHomotopyInverse g) (Lf : LinearHomotopyInverse f) :
    (Lg.comp Lf).homotopyLeft =
      Lf.inv ∘ₗ Lg.homotopyLeft ∘ₗ f.linearPart + Lf.homotopyLeft := (rfl)

@[simp]
theorem comp_homotopyRight {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (Lg : LinearHomotopyInverse g) (Lf : LinearHomotopyInverse f) :
    (Lg.comp Lf).homotopyRight =
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
  isHomogeneous_homotopyLeft := by
    have hk' : LinearMap.IsHomogeneous (L.inv ∘ₗ k) AA.grading.piece AA.grading.piece (-1) := by
      simpa only [add_zero] using L.isHomogeneous_inv.comp hk
    exact L.isHomogeneous_homotopyLeft.sub hk'
  inv_comp_linearPart_sub_id := by
    have hf' : f'.linearPart = f.linearPart - (BB.differential ∘ₗ k + k ∘ₗ AA.differential) :=
      eq_sub_of_add_eq' (sub_eq_iff_eq_add.1 heq).symm
    ext a
    have ha := LinearMap.congr_fun L.inv_comp_linearPart_sub_id a
    have hd := LinearMap.congr_fun L.differential_comp_inv (k a)
    simp only [hf', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add] at ha hd ⊢
    rw [sub_right_comm, ha, ← hd]
    abel
  isHomogeneous_homotopyRight := by
    have hk' : LinearMap.IsHomogeneous (k ∘ₗ L.inv) BB.grading.piece BB.grading.piece (-1) := by
      simpa only [zero_add] using hk.comp L.isHomogeneous_inv
    exact L.isHomogeneous_homotopyRight.sub hk'
  linearPart_comp_inv_sub_id := by
    have hf' : f'.linearPart = f.linearPart - (BB.differential ∘ₗ k + k ∘ₗ AA.differential) :=
      eq_sub_of_add_eq' (sub_eq_iff_eq_add.1 heq).symm
    ext b
    have hb := LinearMap.congr_fun L.linearPart_comp_inv_sub_id b
    have hd := LinearMap.congr_fun L.differential_comp_inv b
    simp only [hf', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub] at hb hd ⊢
    rw [sub_right_comm, hb, hd]
    abel

end LinearHomotopyInverse

namespace Homotopy

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {f f' : AInfinityHom AA BB}

/-- Transport `LinearHomotopyInverse` data forward along an `A∞` homotopy `Homotopy f f'`. -/
noncomputable def linearHomotopyInverse (h : Homotopy f f') (L : LinearHomotopyInverse f) :
    LinearHomotopyInverse f' :=
  LinearHomotopyInverse.ofChainHomotopy h.linearHomotopy h.isHomogeneous_linearHomotopy
    h.linearPart_sub_linearPart_eq L

@[simp]
theorem linearHomotopyInverse_inv (h : Homotopy f f') (L : LinearHomotopyInverse f) :
    (h.linearHomotopyInverse L).inv = L.inv := (rfl)

@[simp]
theorem linearHomotopyInverse_homotopyLeft (h : Homotopy f f') (L : LinearHomotopyInverse f) :
    (h.linearHomotopyInverse L).homotopyLeft = L.homotopyLeft - L.inv ∘ₗ h.linearHomotopy := (rfl)

@[simp]
theorem linearHomotopyInverse_homotopyRight (h : Homotopy f f') (L : LinearHomotopyInverse f) :
    (h.linearHomotopyInverse L).homotopyRight = L.homotopyRight - h.linearHomotopy ∘ₗ L.inv :=
  (rfl)

/-- Transport `LinearHomotopyInverse` data backward along an `A∞` homotopy `Homotopy f f'`. -/
noncomputable def linearHomotopyInverseSymm (h : Homotopy f f') (L : LinearHomotopyInverse f') :
    LinearHomotopyInverse f :=
  LinearHomotopyInverse.ofChainHomotopy (-h.linearHomotopy)
    (by simpa only [neg_one_smul R] using h.isHomogeneous_linearHomotopy.smul (-1 : R))
    (by rw [← neg_sub, h.linearPart_sub_linearPart_eq, neg_add, LinearMap.comp_neg,
      LinearMap.neg_comp]) L

@[simp]
theorem linearHomotopyInverseSymm_inv (h : Homotopy f f') (L : LinearHomotopyInverse f') :
    (h.linearHomotopyInverseSymm L).inv = L.inv := (rfl)

end Homotopy

end AInfinityHom

end TauCeti
