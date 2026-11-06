/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import TauCeti.AlgebraicGeometry.Rigidity.Relative
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf

/-!
# Pointed morphisms, uniqueness of group laws, and commutativity of proper flat group schemes

Let `S` be an arbitrary scheme. As consequences of the relative rigidity lemma
(`TauCeti.AlgebraicGeometry.eq_snd_comp_lift_comp_of_flat`), this file establishes the fundamental
rigidity properties of proper, flat, geometrically integral monoid and group schemes `A` over `S`
satisfying `A.hom_* 𝒪_A = 𝒪_S` (for instance abelian schemes and elliptic curves over `S`):

1. **Pointed morphisms are homomorphisms**
   (`TauCeti.AlgebraicGeometry.isMonHom_of_one_hom_of_flat`):
   for any separated, locally of finite type group scheme `B` over `S`, a morphism `f : A ⟶ B` over
   `S` sending the identity section of `A` to that of `B` is automatically a homomorphism of monoid
   schemes (`IsMonHom f`). The defect `(x, y) ↦ f(xy) / (f(x) f(y))` vanishes on `A ×_S {1}`, hence
   depends only on `y` by the relative rigidity lemma, and vanishes on `{1} ×_S A`.
2. **Uniqueness of the group and monoid structure**
   (`TauCeti.AlgebraicGeometry.monObj_eq_of_one_eq_of_flat` and
   `TauCeti.AlgebraicGeometry.grpObj_eq_of_one_eq_of_flat`): applying the pointed-morphism theorem
   to the identity morphism `𝟙 G` shows that a proper, flat, geometrically integral scheme `G` over
   `S` with `G.hom_* 𝒪_G = 𝒪_S` admits at most one group-scheme structure (and at most one
   monoid-scheme structure once a group-scheme structure exists) having a prescribed identity
   section.
3. **Commutativity over an arbitrary base**
   (`TauCeti.AlgebraicGeometry.isCommMonObj_of_isProper_of_flat`): applying the pointed-morphism
   theorem to the inversion morphism `ι[G] : G ⟶ G` shows that `ι[G]` is a monoid homomorphism,
   whence `G` is commutative (`CategoryTheory.GrpObj.isCommMonObj_of_isMonHom_inv`). This extends
   `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` (due in Mathlib to Andrew
   Yang and Christian Merten in `Mathlib.AlgebraicGeometry.Group.Abelian`) from fields to arbitrary
   base schemes `S`.

Over a field `K`, flatness and `A.hom_* 𝒪_A = 𝒪_{Spec K}` hold automatically, recovering
`TauCeti.AlgebraicGeometry.isMonHom_of_one_hom` together with uniqueness of monoid and group
structures over `Spec K`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isMonHom_of_one_hom_of_flat`: pointed morphisms out of a proper, flat,
  geometrically integral monoid scheme `A` over `S` with `A.hom_* 𝒪_A = 𝒪_S` into a separated
  locally finite type group scheme `B` over `S` are homomorphisms.
* `TauCeti.AlgebraicGeometry.monObj_eq_of_one_eq_of_flat` and
  `TauCeti.AlgebraicGeometry.grpObj_eq_of_one_eq_of_flat`: uniqueness of monoid and group structures
  with a prescribed identity section over `S`.
* `TauCeti.AlgebraicGeometry.isCommMonObj_of_isProper_of_flat`: every proper, flat, geometrically
  integral group scheme `G` over `S` with `G.hom_* 𝒪_G = 𝒪_S` is commutative.
* `TauCeti.AlgebraicGeometry.commGrpHomOfOneHom` and
  `TauCeti.AlgebraicGeometry.commGrpHomEquivPointed`: homomorphisms in `CommGrp (Over S)` are
  equivalent to identity-preserving morphisms in `Over S`.
* `TauCeti.AlgebraicGeometry.isMonHom_of_one_hom`,
  `TauCeti.AlgebraicGeometry.monObj_eq_of_one_eq`, and
  `TauCeti.AlgebraicGeometry.grpObj_eq_of_one_eq`: specializations over a field `K`.

## References

* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, Proposition 6.1 and Corollary
  6.4.
* D. Mumford, *Abelian Varieties*, Section 4, Corollaries 1–2 to the rigidity lemma.
* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1, Lemma 2.
* J. S. Milne, *Abelian Varieties*, Corollary 1.2.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Theorem 2.5.1.
* [The Stacks Project, Tag 0BF6](https://stacks.math.columbia.edu/tag/0BF6) and
  [Tag 0BFD](https://stacks.math.columbia.edu/tag/0BFD).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

section Relative

variable {S : Scheme.{u}}

/-- **Pointed morphisms out of proper flat geometrically integral monoid schemes are
homomorphisms.** Let `A` be a monoid scheme over `S` whose structure morphism is proper, flat, and
geometrically integral with `A.hom_* 𝒪_A = 𝒪_S`, and let `B` be a separated locally finite type
group scheme over `S`. Every morphism `f : A ⟶ B` over `S` carrying the identity section of `A` to
that of `B` is a homomorphism of monoid schemes. -/
theorem isMonHom_of_one_hom_of_flat {A B : Over S} [MonObj A] [GrpObj B]
    [IsProper A.hom] [Flat A.hom] [GeometricallyIntegral A.hom]
    (hA : ∀ V : S.affineOpens, IsIso (A.hom.app V))
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  -- The defect `h (x, y) = f (x y) / (f x * f y)` in the group of morphisms `A ×_S A ⟶ B`.
  let h : A ⊗ A ⟶ B := (μ ≫ f) / ((fst _ _ ≫ f) * (snd _ _ ≫ f))
  have key {W : Over S} (a b : W ⟶ A) :
      lift a b ≫ h = ((a * b) ≫ f) / ((a ≫ f) * (b ≫ f)) := by
    simp only [h, GrpObj.comp_div, comp_mul, ← Category.assoc, ← Hom.mul_def,
      lift_fst, lift_snd]
  have hf₁ (X : Over S) : (1 : X ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  have H := eq_snd_comp_lift_comp_of_flat hA h η η η (by
    rw [key]
    simp only [← Hom.one_def, Category.id_comp, hf₁, _root_.mul_one, div_self'])
  rw [key] at H
  simp only [← Hom.one_def, Category.id_comp, hf₁, comp_one, _root_.one_mul, div_self'] at H
  refine ⟨hf, ?_⟩
  rw [← lift_fst_comp_snd_comp, ← Hom.mul_def]
  exact div_eq_one.mp H

/-- **Uniqueness of the monoid structure for a given identity section.** Let `G` be a proper, flat,
geometrically integral scheme over `S` with `G.hom_* 𝒪_G = 𝒪_S`. If `m` is a monoid-object
structure on `G` and `g` is a group-object structure on `G` having the same identity section, then
`m = g.toMonObj`. -/
theorem monObj_eq_of_one_eq_of_flat {G : Over S}
    [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
    (hG : ∀ V : S.affineOpens, IsIso (G.hom.app V))
    (m : MonObj G) (g : GrpObj G) (hone : m.one = g.one) :
    m = g.toMonObj := by
  have hid : @IsMonHom _ _ _ G G m g.toMonObj (𝟙 G) :=
    @isMonHom_of_one_hom_of_flat S G G m g _ _ _ hG _ _ (𝟙 G) (by rw [Category.comp_id]; exact hone)
  apply MonObj.ext
  have hmul := @IsMonHom.mul_hom _ _ _ G G m g.toMonObj (𝟙 G) hid
  simpa only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id] using hmul

/-- **Uniqueness of the group structure for a given identity section.** Let `G` be a proper, flat,
geometrically integral scheme over `S` with `G.hom_* 𝒪_G = 𝒪_S`. Any two group-object structures on
`G` having the same identity section are equal. -/
theorem grpObj_eq_of_one_eq_of_flat {G : Over S}
    [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
    (hG : ∀ V : S.affineOpens, IsIso (G.hom.app V))
    (g₁ g₂ : GrpObj G) (hone : g₁.one = g₂.one) :
    g₁ = g₂ :=
  GrpObj.ext _ _ (monObj_eq_of_one_eq_of_flat hG g₁.toMonObj g₂ hone)

/-- **Abelian schemes are commutative.** Every proper, flat, geometrically integral group scheme `G`
over an arbitrary base scheme `S` satisfying `G.hom_* 𝒪_G = 𝒪_S` is commutative. -/
theorem isCommMonObj_of_isProper_of_flat (G : Over S) [GrpObj G]
    [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
    (hG : ∀ V : S.affineOpens, IsIso (G.hom.app V)) :
    IsCommMonObj G :=
  have : IsMonHom ι[G] := isMonHom_of_one_hom_of_flat hG ι[G] GrpObj.one_inv
  GrpObj.isCommMonObj_of_isMonHom_inv G

/-- Construct a morphism in `CommGrp (Over S)` from a pointed morphism `f : A.X ⟶ B.X` over `S`,
when `A` is proper, flat, and geometrically integral over `S` with `A.X.hom_* 𝒪_{A.X} = 𝒪_S` and
`B` is separated and locally of finite type over `S`. -/
noncomputable def commGrpHomOfOneHom {A B : CommGrp (Over S)}
    [IsProper A.X.hom] [Flat A.X.hom] [GeometricallyIntegral A.X.hom]
    (hA : ∀ V : S.affineOpens, IsIso (A.X.hom.app V))
    [IsSeparated B.X.hom] [LocallyOfFiniteType B.X.hom]
    (f : A.X ⟶ B.X) (hf : η[A.X] ≫ f = η[B.X]) : A ⟶ B :=
  have : IsMonHom f := isMonHom_of_one_hom_of_flat hA f hf
  CommGrp.homMk f

@[simp]
theorem commGrpHomOfOneHom_hom_hom_hom {A B : CommGrp (Over S)}
    [IsProper A.X.hom] [Flat A.X.hom] [GeometricallyIntegral A.X.hom]
    (hA : ∀ V : S.affineOpens, IsIso (A.X.hom.app V))
    [IsSeparated B.X.hom] [LocallyOfFiniteType B.X.hom]
    (f : A.X ⟶ B.X) (hf : η[A.X] ≫ f = η[B.X]) :
    (commGrpHomOfOneHom hA f hf).hom.hom.hom = f :=
  have : IsMonHom f := isMonHom_of_one_hom_of_flat hA f hf
  CommGrp.homMk_hom_hom_hom f

/-- For `A, B : CommGrp (Over S)` with `A` proper, flat, and geometrically integral over `S`
satisfying `A.X.hom_* 𝒪_{A.X} = 𝒪_S` and `B` separated and locally of finite type over `S`,
homomorphisms `A ⟶ B` in `CommGrp (Over S)` are equivalent to identity-preserving morphisms
`A.X ⟶ B.X` in `Over S`. -/
noncomputable def commGrpHomEquivPointed (A B : CommGrp (Over S))
    [IsProper A.X.hom] [Flat A.X.hom] [GeometricallyIntegral A.X.hom]
    (hA : ∀ V : S.affineOpens, IsIso (A.X.hom.app V))
    [IsSeparated B.X.hom] [LocallyOfFiniteType B.X.hom] :
    (A ⟶ B) ≃ {f : A.X ⟶ B.X // η[A.X] ≫ f = η[B.X]} where
  toFun F := ⟨F.hom.hom.hom, IsMonHom.one_hom F.hom.hom.hom⟩
  invFun f := commGrpHomOfOneHom hA f.1 f.2
  left_inv _ := CommGrp.hom_ext _ _ (commGrpHomOfOneHom_hom_hom_hom hA _ _)
  right_inv _ := Subtype.ext (commGrpHomOfOneHom_hom_hom_hom hA _ _)

end Relative

section Field

variable {K : Type u} [Field K]

/-- A morphism of monoid schemes over a field `K` from a proper geometrically integral source to a
separated locally finite type group scheme is a homomorphism if it preserves the identity. -/
theorem isMonHom_of_one_hom {A B : Over (Spec (.of K))} [MonObj A] [GrpObj B]
    [IsProper A.hom] [GeometricallyIntegral A.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f :=
  isMonHom_of_one_hom_of_flat
    (fun V ↦ A.hom.isIso_app_of_universallyClosed_of_geometricallyIntegral V) f hf

/-- Over a field `K`, a proper geometrically integral scheme admits at most one monoid-scheme
structure having the same identity section as a group-scheme structure on it. -/
theorem monObj_eq_of_one_eq {G : Over (Spec (.of K))}
    [IsProper G.hom] [GeometricallyIntegral G.hom]
    (m : MonObj G) (g : GrpObj G) (hone : m.one = g.one) :
    m = g.toMonObj :=
  monObj_eq_of_one_eq_of_flat
    (fun V ↦ G.hom.isIso_app_of_universallyClosed_of_geometricallyIntegral V) m g hone

/-- Over a field `K`, a proper geometrically integral scheme admits at most one group-scheme
structure with a prescribed identity section. -/
theorem grpObj_eq_of_one_eq {G : Over (Spec (.of K))}
    [IsProper G.hom] [GeometricallyIntegral G.hom]
    (g₁ g₂ : GrpObj G) (hone : g₁.one = g₂.one) :
    g₁ = g₂ :=
  GrpObj.ext _ _ (monObj_eq_of_one_eq g₁.toMonObj g₂ hone)

end Field

end AlgebraicGeometry

end TauCeti
