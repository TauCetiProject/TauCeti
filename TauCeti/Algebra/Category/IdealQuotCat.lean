/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.LinearAlgebra.Quotient.ScalarMap

/-!
# The category of quotients of a module by ideals

Let `M` be a module over a commutative ring `R`. Mazur and Rubin's category `Quot_R(M)` has one
object for each ideal `I` of `R`, standing for the quotient `M ⧸ I M`, and its morphisms
`M ⧸ I M → M ⧸ J M` are the maps given by multiplication by a scalar `r` with `r I ⊆ J`
(`Ideal.smulMapQ`). A morphism is the induced map, not the scalar: different scalars acting by the
same map give the same morphism, and composition multiplies the scalars.

In Mazur and Rubin's theory of Kolyvagin systems `M` is a Galois representation `T` with
coefficients in `R`. Local conditions on `T` propagate to the quotients `T ⧸ I T` along this
category, and a Selmer structure is cartesian when its local conditions are compatible with the
injective morphisms. Over a local ring with maximal ideal `𝔪 = (ϖ)` these include the maps
`ϖ ^ (j - i) : T ⧸ 𝔪 ^ i T → T ⧸ 𝔪 ^ j T` for free `T` (`Ideal.injective_smulMapQ_pow`). The
functor to representations records that the morphisms are equivariant for an action on `T` by
`R`-linear maps.

## Main definitions

* `TauCeti.IdealQuotCat R M`: the category `Quot_R(M)`, whose objects are the ideals of `R`.
* `TauCeti.IdealQuotCat.scalarHom`: the morphism `M ⧸ I M → M ⧸ J M` given by a scalar `r` with
  `r I ⊆ J`.
* `TauCeti.IdealQuotCat.toModuleCat`: the faithful functor `I ↦ M ⧸ I M` to `R`-modules.
* `TauCeti.IdealQuotCat.toRep`: for a representation `ρ` of a monoid `G` on `M`, the faithful
  functor `I ↦ M ⧸ I M` to representations of `G`; the morphisms of `Quot_R(M)` are
  `G`-equivariant.

## Main results

* `TauCeti.IdealQuotCat.exists_eq_scalarHom`: every morphism is given by a scalar.
* `TauCeti.IdealQuotCat.scalarHom_comp_scalarHom`: `r` followed by `s` is `s * r`.
* `TauCeti.IdealQuotCat.scalarHom_one`: the scalar `1` gives the identity.

## References

* B. Mazur and K. Rubin, *Kolyvagin systems*, Mem. Amer. Math. Soc. 168 (2004), no. 799,
  Example 1.1.3 and Definition 1.1.4.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

/-- **The category of quotients of a module.** Mazur and Rubin's `Quot_R(M)` for a module `M`
over a commutative ring `R`: an object is an ideal `I` of `R`, standing for the quotient
`M ⧸ I M`, and the morphisms are given by multiplication by scalars (`TauCeti.IdealQuotCat.Hom`).
-/
structure IdealQuotCat (R : Type u) [Semiring R] (M : Type v) where
  /-- The ideal `I` of an object, which stands for the quotient `M ⧸ I M`. -/
  ideal : Ideal R

namespace IdealQuotCat

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A morphism `I ⟶ J` of `Quot_R(M)`: an `R`-linear map `M ⧸ I M → M ⧸ J M` that is
multiplication by some scalar `r` with `r I ⊆ J`. -/
@[ext]
structure Hom (X Y : IdealQuotCat R M) where
  /-- The underlying linear map `M ⧸ I M → M ⧸ J M`. -/
  hom : M ⧸ X.ideal • (⊤ : Submodule R M) →ₗ[R] M ⧸ Y.ideal • (⊤ : Submodule R M)
  exists_eq_smulMapQ' :
    ∃ (r : R) (h : X.ideal ≤ Y.ideal.colon {r}), hom = Ideal.smulMapQ M r h

instance : Category (IdealQuotCat R M) where
  Hom := Hom
  id X := ⟨LinearMap.id, 1, fun a ha ↦ by simpa using ha, (Ideal.smulMapQ_one_self _).symm⟩
  comp f g := ⟨g.hom ∘ₗ f.hom, by
    obtain ⟨r, hr, hf⟩ := f.exists_eq_smulMapQ'
    obtain ⟨s, hs, hg⟩ := g.exists_eq_smulMapQ'
    exact ⟨s * r, _, by rw [hf, hg, Ideal.smulMapQ_comp_smulMapQ]⟩⟩

variable {X Y Z : IdealQuotCat R M}

@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
theorem hom_id (X : IdealQuotCat R M) : (𝟙 X : X ⟶ X).hom = LinearMap.id :=
  (rfl)

@[simp]
theorem hom_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom ∘ₗ f.hom :=
  (rfl)

/-- The morphism `M ⧸ I M → M ⧸ J M` of `Quot_R(M)` given by multiplication by `r`, for
`r I ⊆ J`. -/
def scalarHom (r : R) (h : X.ideal ≤ Y.ideal.colon {r}) : X ⟶ Y :=
  ⟨Ideal.smulMapQ M r h, r, h, rfl⟩

@[simp]
theorem hom_scalarHom (r : R) (h : X.ideal ≤ Y.ideal.colon {r}) :
    (scalarHom r h).hom = Ideal.smulMapQ M r h :=
  (rfl)

/-- Every morphism of `Quot_R(M)` is multiplication by a scalar. -/
theorem exists_eq_scalarHom (f : X ⟶ Y) :
    ∃ (r : R) (h : X.ideal ≤ Y.ideal.colon {r}), f = scalarHom r h := by
  obtain ⟨r, h, hf⟩ := f.exists_eq_smulMapQ'
  exact ⟨r, h, hom_ext hf⟩

/-- Multiplication by `r` followed by multiplication by `s` is multiplication by `s * r`. -/
@[simp]
theorem scalarHom_comp_scalarHom {r s : R} (hr : X.ideal ≤ Y.ideal.colon {r})
    (hs : Y.ideal ≤ Z.ideal.colon {s}) :
    scalarHom r hr ≫ scalarHom s hs = scalarHom (s * r) (Ideal.le_colon_singleton_mul hr hs) :=
  hom_ext (Ideal.smulMapQ_comp_smulMapQ hr hs)

/-- Multiplication by `1` is the identity morphism. -/
@[simp]
theorem scalarHom_one (h : X.ideal ≤ X.ideal.colon {1}) : scalarHom (1 : R) h = 𝟙 X :=
  hom_ext (Ideal.smulMapQ_one_self h)

variable (R M) in
/-- The functor `Quot_R(M) ⥤ ModuleCat R` sending an ideal `I` to the quotient `M ⧸ I M`. -/
@[expose, simps]
def toModuleCat : IdealQuotCat R M ⥤ ModuleCat.{v} R where
  obj X := ModuleCat.of R (M ⧸ X.ideal • (⊤ : Submodule R M))
  map f := ModuleCat.ofHom f.hom

instance : (toModuleCat R M).Faithful where
  map_injective h := hom_ext (ModuleCat.hom_ext_iff.mp h)

section Rep

variable {G : Type*} [Monoid G] (ρ : Representation R G M)

/-- The functor `Quot_R(M) ⥤ Rep R G` sending an ideal `I` to the representation of `G` on
`M ⧸ I M` induced by `ρ`. That it is a functor says that the morphisms of `Quot_R(M)` are
`G`-equivariant. -/
@[expose] def toRep : IdealQuotCat R M ⥤ Rep.{v} R G where
  obj X := Rep.of (ρ.quotient (X.ideal • ⊤) fun g ↦ Submodule.smul_top_le_comap_smul_top _ (ρ g))
  map {X Y} f := Rep.ofHom <| f.hom.intertwiningMap_of_isIntertwiningMap _ _ fun g x ↦ by
    obtain ⟨r, h, hf⟩ := f.exists_eq_smulMapQ'
    induction x using Submodule.Quotient.induction_on with | H x => ?_
    simp [hf]

@[simp]
theorem toRep_obj_ρ_apply_mk (X : IdealQuotCat R M) (g : G) (x : M) :
    ((toRep ρ).obj X).ρ g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
  (rfl)

@[simp]
theorem toRep_map_hom_apply (f : X ⟶ Y) (x : M ⧸ X.ideal • (⊤ : Submodule R M)) :
    ((toRep ρ).map f).hom x = f.hom x :=
  (rfl)

instance : (toRep ρ).Faithful where
  map_injective {X Y _ _} h := hom_ext <| LinearMap.ext fun x ↦
    congrArg (fun φ : (toRep ρ).obj X ⟶ (toRep ρ).obj Y ↦ φ.hom x) h

end Rep

end IdealQuotCat

end TauCeti
