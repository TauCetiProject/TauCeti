/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.LazardRing.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Deformations with a fixed special-fibre coordinate

Fix a formal group law `F₀` over `k` and a coefficient homomorphism `π : A →+* k`.
A `FormalGroupLift π F₀` is a commutative formal group law over `A` whose reduction is
exactly `F₀`. The kernel of coefficient reduction on formal coordinates acts on these
lifts. Its orbit set, `FormalGroupDeformation π F₀`, identifies lifts by coordinate
changes reducing to `X`, not by all strict coordinate changes. In particular, the
linear coefficient need only reduce to one; it need not equal one in `A`.

Base change along commuting triangles defines `formalGroupDeformationFunctor` on
rings over `k`. Restriction to complete local rings with their specified residue maps
is the fixed-residue-coordinate deformation functor. No existence of lifts, rigidity,
or representability is assumed: lifts are constructed when the coefficient map splits,
and the value at the residue ring itself has exactly one element. The equivalence
`FormalGroupLift.classifyingMapEquiv` identifies lifts with the fibre of coefficient
reduction on ring homomorphisms from the Lazard ring, naturally in the coefficient ring.

This is the coordinate description of deformations used in J. Lubin and J. Tate,
*Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math. France 94 (1966).
Here the special fibre is fixed by equality, rather than by a separate marking
isomorphism; no comparison with arbitrary marked special fibres is asserted.
-/

public section

noncomputable section

namespace TauCeti

variable {A B C k : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing k]

/-- A commutative lift of `F₀` with its special-fibre coordinate fixed. -/
@[ext]
structure FormalGroupLift (π : A →+* k) (F₀ : FormalGroup k) where
  /-- The formal group law before reduction. -/
  formalGroup : FormalGroup A
  /-- The lifted law is commutative. -/
  isComm : formalGroup.IsComm
  /-- Reduction agrees with the specified law in the specified coordinate. -/
  map_eq : formalGroup.map π = F₀

attribute [instance] FormalGroupLift.isComm

namespace FormalGroupLift

variable {π : A →+* k} {ρ : B →+* k} {τ : C →+* k} {F₀ : FormalGroup k}

/-- Coordinates reducing to the identity act on lifts without changing the special fibre. -/
instance : MulAction (FormalCoordinate.map π).ker (FormalGroupLift π F₀) where
  smul φ F :=
    { formalGroup := φ.val • F.formalGroup
      isComm := inferInstance
      map_eq := by
        rw [FormalGroup.map_smul, MonoidHom.mem_ker.mp φ.property, one_smul, F.map_eq] }
  one_smul F := FormalGroupLift.ext (one_smul (FormalCoordinate A) F.formalGroup)
  mul_smul φ ψ F := FormalGroupLift.ext (mul_smul φ.val ψ.val F.formalGroup)

/-- The action on lifts is the usual change of coordinate on the underlying law. -/
@[simp]
theorem formalGroup_smul (φ : (FormalCoordinate.map π).ker) (F : FormalGroupLift π F₀) :
    (φ • F).formalGroup = φ.val • F.formalGroup := (rfl)

/-- Base change of a lift along a homomorphism commuting with reduction. -/
def map (F : FormalGroupLift π F₀) (f : A →+* B) (hf : ρ.comp f = π) :
    FormalGroupLift ρ F₀ where
  formalGroup := F.formalGroup.map f
  isComm := inferInstance
  map_eq := by rw [FormalGroup.map_comp, hf, F.map_eq]

/-- Base change applies the coefficient homomorphism to the lifted formal group law. -/
@[simp]
theorem formalGroup_map (F : FormalGroupLift π F₀) (f : A →+* B) (hf : ρ.comp f = π) :
    (F.map f hf).formalGroup = F.formalGroup.map f := (rfl)

/-- Base change of lifts commutes with coordinate changes reducing to the identity. -/
@[simp]
theorem map_smul (φ : (FormalCoordinate.map π).ker) (F : FormalGroupLift π F₀)
    (f : A →+* B) (hf : ρ.comp f = π) :
    (φ • F).map f hf =
      (⟨FormalCoordinate.map f φ.val, by
        apply MonoidHom.mem_ker.mpr
        rw [← FormalCoordinate.map_comp, hf, MonoidHom.mem_ker.mp φ.property]⟩ :
        (FormalCoordinate.map ρ).ker) • F.map f hf := by
  ext
  simp only [formalGroup_map, formalGroup_smul, FormalGroup.map_smul]

/-- Base change by the identity fixes a lift. -/
@[simp]
theorem map_id (F : FormalGroupLift π F₀) (h : π.comp (RingHom.id A) = π) :
    F.map (RingHom.id A) h = F := by ext; simp

/-- Successive base changes of lifts agree with their composite. -/
@[simp]
theorem map_comp (F : FormalGroupLift π F₀) (f : A →+* B) (hf : ρ.comp f = π)
    (g : B →+* C) (hg : τ.comp g = ρ) :
    (F.map f hf).map g hg = F.map (g.comp f) (by rw [← RingHom.comp_assoc, hg, hf]) := by
  ext
  simp

/-- A section of the coefficient map constructs a lift of every commutative law. -/
def ofSection (F₀ : FormalGroup k) [F₀.IsComm] (π : A →+* k) (s : k →+* A)
    (hs : π.comp s = RingHom.id k) : FormalGroupLift π F₀ where
  formalGroup := F₀.map s
  isComm := inferInstance
  map_eq := by rw [FormalGroup.map_comp, hs, FormalGroup.map_id]

/-- The split lift is coefficient extension along the section. -/
@[simp]
theorem formalGroup_ofSection (F₀ : FormalGroup k) [F₀.IsComm] (π : A →+* k)
    (s : k →+* A) (hs : π.comp s = RingHom.id k) :
    (ofSection F₀ π s hs).formalGroup = F₀.map s := (rfl)

/-- Over the identity coefficient map, a lift has no free coefficients. -/
instance : Subsingleton (FormalGroupLift (RingHom.id k) F₀) where
  allEq F G := by
    apply FormalGroupLift.ext
    simpa using F.map_eq.trans G.map_eq.symm

/-- Lifts of a commutative special fibre correspond to classifying maps from the Lazard
ring with the prescribed reduction. This describes the framed deformation problem before
quotienting by changes of coordinate. -/
def classifyingMapEquiv (π : A →+* k) (F₀ : FormalGroup k) [F₀.IsComm] :
    FormalGroupLift π F₀ ≃
      {f : LazardRing →+* A // π.comp f = LazardRing.lift ⟨F₀, inferInstance⟩} where
  toFun F := ⟨LazardRing.lift ⟨F.formalGroup, inferInstance⟩, by
    apply LazardRing.hom_ext
    rw [← FormalGroup.map_comp, LazardRing.map_lift, LazardRing.map_lift, F.map_eq]⟩
  invFun f :=
    { formalGroup := LazardRing.formalGroup.map f.val
      isComm := inferInstance
      map_eq := by rw [FormalGroup.map_comp, f.property, LazardRing.map_lift] }
  left_inv F := FormalGroupLift.ext (LazardRing.map_lift _)
  right_inv f := Subtype.ext (LazardRing.hom_ext (by simp))

/-- The classifying map of a lift classifies its underlying formal group law. -/
@[simp]
theorem classifyingMapEquiv_apply_coe (π : A →+* k) (F₀ : FormalGroup k) [F₀.IsComm]
    (F : FormalGroupLift π F₀) :
    (classifyingMapEquiv π F₀ F).val = LazardRing.lift ⟨F.formalGroup, inferInstance⟩ := (rfl)

/-- The lift attached to a classifying map is the base change of the universal law. -/
@[simp]
theorem formalGroup_classifyingMapEquiv_symm (π : A →+* k) (F₀ : FormalGroup k) [F₀.IsComm]
    (f : {f : LazardRing →+* A // π.comp f = LazardRing.lift ⟨F₀, inferInstance⟩}) :
    ((classifyingMapEquiv π F₀).symm f).formalGroup = LazardRing.formalGroup.map f.val := (rfl)

/-- The classifying-map description of lifts is natural in the coefficient ring. -/
theorem classifyingMapEquiv_map [F₀.IsComm] (F : FormalGroupLift π F₀)
    (f : A →+* B) (hf : ρ.comp f = π) :
    (classifyingMapEquiv ρ F₀ (F.map f hf)).val =
      f.comp (classifyingMapEquiv π F₀ F).val := by
  simpa only [classifyingMapEquiv_apply_coe, formalGroup_map] using
    LazardRing.lift_map F.formalGroup f

end FormalGroupLift

/-- Deformations in a fixed special-fibre coordinate: commutative lifts modulo coordinate
changes whose entire reduction is `X`. -/
abbrev FormalGroupDeformation (π : A →+* k) (F₀ : FormalGroup k) :=
  MulAction.orbitRel.Quotient (FormalCoordinate.map π).ker (FormalGroupLift π F₀)

namespace FormalGroupDeformation

variable {π : A →+* k} {ρ : B →+* k} {τ : C →+* k} {F₀ : FormalGroup k}

/-- Two lifts define the same deformation exactly when a coordinate reducing to the
identity carries the first law to the second. -/
theorem mk_eq_mk_iff (F G : FormalGroupLift π F₀) :
    (⟦F⟧ : FormalGroupDeformation π F₀) = ⟦G⟧ ↔
      ∃ φ : FormalCoordinate A, FormalCoordinate.map π φ = 1 ∧
        φ • F.formalGroup = G.formalGroup := by
  rw [eq_comm, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ.val, MonoidHom.mem_ker.mp φ.property, congrArg FormalGroupLift.formalGroup hφ⟩
  · rintro ⟨φ, hφ, hFG⟩
    exact ⟨⟨φ, MonoidHom.mem_ker.mpr hφ⟩, FormalGroupLift.ext hFG⟩

/-- Base change of deformation classes along a commuting triangle of coefficient maps. -/
def map (f : A →+* B) (hf : ρ.comp f = π) :
    FormalGroupDeformation π F₀ → FormalGroupDeformation ρ F₀ :=
  Quotient.map (fun F => F.map f hf) fun F G h => by
    obtain ⟨φ, rfl⟩ := MulAction.mem_orbit_iff.mp h
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨_, (FormalGroupLift.map_smul φ G f hf).symm⟩

/-- Base change on a representative is coefficient extension of that lift. -/
@[simp]
theorem map_mk (f : A →+* B) (hf : ρ.comp f = π) (F : FormalGroupLift π F₀) :
    map f hf ⟦F⟧ = ⟦F.map f hf⟧ := (rfl)

/-- Base change by the identity fixes a deformation. -/
@[simp]
theorem map_id (h : π.comp (RingHom.id A) = π) (x : FormalGroupDeformation π F₀) :
    map (RingHom.id A) h x = x := by
  exact Quotient.inductionOn x fun F => congrArg Quotient.mk'' (FormalGroupLift.map_id F h)

/-- Successive base changes of deformation classes agree with their composite. -/
@[simp]
theorem map_comp (f : A →+* B) (hf : ρ.comp f = π) (g : B →+* C)
    (hg : τ.comp g = ρ) (x : FormalGroupDeformation π F₀) :
    map g hg (map f hf x) = map (g.comp f) (by rw [← RingHom.comp_assoc, hg, hf]) x := by
  exact Quotient.inductionOn x fun F =>
    congrArg Quotient.mk'' (FormalGroupLift.map_comp F f hf g hg)

/-- A split coefficient map admits a deformation of each commutative special fibre. -/
theorem nonempty_of_section (F₀ : FormalGroup k) [F₀.IsComm] (π : A →+* k)
    (s : k →+* A) (hs : π.comp s = RingHom.id k) :
    Nonempty (FormalGroupDeformation π F₀) :=
  ⟨⟦FormalGroupLift.ofSection F₀ π s hs⟧⟩

/-- The deformation set evaluated at its own special fibre consists of one element. -/
instance [F₀.IsComm] : Unique (FormalGroupDeformation (RingHom.id k) F₀) where
  default := ⟦FormalGroupLift.ofSection F₀ (RingHom.id k) (RingHom.id k) (by ext; rfl)⟧
  uniq _ := Subsingleton.elim _ _

end FormalGroupDeformation

open CategoryTheory

universe u

/-- The fixed-special-fibre deformation functor on commutative rings over `k`.
Its maps extend coefficients, and its values quotient only by coordinates reducing to `X`.
The body is exposed so that its values compute to the concrete deformation sets, allowing
its maps to be applied to deformation classes without transporting along type equalities. -/
@[expose]
def formalGroupDeformationFunctor {k : Type u} [CommRing k] (F₀ : FormalGroup k) :
    Over (CommRingCat.of k) ⥤ Type u where
  obj A := FormalGroupDeformation A.hom.hom F₀
  map f := ↾(FormalGroupDeformation.map f.left.hom (congrArg CommRingCat.Hom.hom f.w))
  map_id A := by
    ext x
    exact FormalGroupDeformation.map_id _ x
  map_comp f g := by
    ext x
    exact (FormalGroupDeformation.map_comp _ _ _ _ x).symm

/-- The value of the deformation functor is the specified orbit set of lifts. -/
@[simp]
theorem formalGroupDeformationFunctor_obj {k : Type u} [CommRing k] (F₀ : FormalGroup k)
    (A : Over (CommRingCat.of k)) :
    (formalGroupDeformationFunctor F₀).obj A = FormalGroupDeformation A.hom.hom F₀ := (rfl)

/-- The deformation functor acts by the base-change map on deformation classes. -/
@[simp]
theorem formalGroupDeformationFunctor_map {k : Type u} [CommRing k] (F₀ : FormalGroup k)
    {A B : Over (CommRingCat.of k)} (f : A ⟶ B) :
    (formalGroupDeformationFunctor F₀).map f =
      ↾(FormalGroupDeformation.map f.left.hom (congrArg CommRingCat.Hom.hom f.w)) := (rfl)

end TauCeti
