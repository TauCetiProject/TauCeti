/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.FiniteType
import TauCeti.Algebra.AlgebraicGroup.FiniteTypeCommHopfAlgCat
import TauCeti.Algebra.HopfAlgebra.Quotient

/-!
# Hopf-ideal quotients of finite-type commutative Hopf algebras

This file packages the quotient of a finite-type commutative Hopf algebra by a Hopf ideal
as another object of `FiniteTypeCommHopfAlgCat`. The Hopf algebra structure and quotient
bialgebra morphism are supplied by `TauCeti.Algebra.HopfAlgebra.Quotient`; the only extra
ingredient here is that finite type descends along the surjective quotient algebra map.

This is a small Layer 3 prerequisite for the reductive-groups roadmap target
"Hopf ideals ↔ closed subgroup schemes": once closed subgroup schemes are represented by
Hopf ideals on coordinate rings, their quotient coordinate Hopf algebras should remain in
the finite-type coordinate-Hopf-algebra category.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotient`: the quotient object in `CommHopfAlgCat`.
* `TauCeti.FiniteTypeCommHopfAlgCat.quotient`: the quotient object in
  `FiniteTypeCommHopfAlgCat`.
* `TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient`: the quotient morphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_ker`: its kernel characterization.
* `TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient`: the induced morphism out of a quotient.

## References

The quotient Hopf algebra construction follows `TauCeti.Algebra.HopfAlgebra.Quotient`,
which cites Sweedler, *Hopf Algebras*, Chapter 4, and Waterhouse, *Introduction to Affine
Group Schemes*, §16. The finite-type descent is Mathlib's
`Algebra.FiniteType.quotient`.
-/

namespace TauCeti

universe u v

namespace CommHopfAlgCat

open CategoryTheory
open _root_.CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The quotient of a commutative Hopf algebra by a Hopf ideal, as a bundled commutative
Hopf algebra. -/
noncomputable abbrev quotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    _root_.CommHopfAlgCat.{v} R :=
  _root_.CommHopfAlgCat.of R (H ⧸ I.toIdeal)

/-- The quotient morphism `H ⟶ H ⧸ I` in `CommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    H ⟶ quotient H I :=
  _root_.CommHopfAlgCat.ofHom (Bialgebra.Quotient.mkBialgHom I.toIdeal)

/-- The quotient morphism has the expected underlying bialgebra morphism. -/
@[simp]
lemma hom_mkQuotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    (mkQuotient H I).hom = Bialgebra.Quotient.mkBialgHom I.toIdeal :=
  _root_.CommHopfAlgCat.hom_ofHom _

/-- Deprecated compatibility alias for `hom_mkQuotient`. -/
@[deprecated hom_mkQuotient (since := "2026-06-22")]
alias toBialgHom_mkQuotient := hom_mkQuotient

/-- The quotient morphism sends an element to its quotient class. -/
@[simp]
lemma mkQuotient_apply (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) (h : H) :
    (mkQuotient H I).hom h = Ideal.Quotient.mkₐ R I.toIdeal h := by
  rw [hom_mkQuotient, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- The kernel of the quotient morphism is the Hopf ideal being quotiented by. -/
lemma mkQuotient_ker (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    RingHom.ker (mkQuotient H I).hom.toAlgHom.toRingHom = I.toIdeal := by
  rw [hom_mkQuotient]
  exact Ideal.Quotient.mkₐ_ker (R₁ := R) I.toIdeal

/-- An element maps to zero in the quotient exactly when it belongs to the Hopf ideal. -/
@[simp]
lemma mkQuotient_eq_zero_iff (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) (h : H) :
    (mkQuotient H I).hom h = 0 ↔ h ∈ I.toIdeal := by
  rw [mkQuotient_apply]
  exact Ideal.Quotient.eq_zero_iff_mem

variable {H K : _root_.CommHopfAlgCat.{v} R}

/-- A morphism of commutative Hopf algebras out of `H` which kills a Hopf ideal factors
through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) : quotient H I ⟶ K :=
  _root_.CommHopfAlgCat.ofHom (HopfIdeal.liftBialgHom I f.hom hf)

/-- The quotient lift has the expected underlying bialgebra morphism. -/
@[simp]
lemma hom_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) :
    (liftQuotient I f hf).hom = HopfIdeal.liftBialgHom I f.hom hf :=
  _root_.CommHopfAlgCat.hom_ofHom _

/-- Deprecated compatibility alias for `hom_liftQuotient`. -/
@[deprecated hom_liftQuotient (since := "2026-06-22")]
alias toBialgHom_liftQuotient := hom_liftQuotient

/-- The quotient lift evaluates on quotient classes as the original morphism. -/
@[simp]
lemma liftQuotient_mk (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) (h : H) :
    (liftQuotient I f hf).hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
      f.hom h :=
  HopfIdeal.liftBialgHom_mk I f.hom hf h

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma mkQuotient_comp_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  ext h
  exact BialgHom.congr_fun
    (HopfIdeal.liftBialgHom_comp_mkBialgHom I f.hom hf) h

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  calc
    g.hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
        (mkQuotient H I ≫ g).hom h := by
      rw [_root_.CommHopfAlgCat.comp_apply, mkQuotient_apply]
    _ = f.hom h := by rw [hg]
    _ = (liftQuotient I f hf).hom (Ideal.Quotient.mkₐ R I.toIdeal h) :=
      (liftQuotient_mk I f hf h).symm

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- The quotient of a finite-type commutative Hopf algebra by a Hopf ideal, as a bundled
finite-type commutative Hopf algebra. -/
noncomputable abbrev quotient (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  ⟨CommHopfAlgCat.quotient H.obj I, inferInstanceAs (Algebra.FiniteType R (H ⧸ I.toIdeal))⟩

/-- The quotient morphism `H ⟶ H ⧸ I` in `FiniteTypeCommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) : H ⟶ quotient H I :=
  ObjectProperty.homMk (CommHopfAlgCat.mkQuotient H.obj I)

/-- The finite-type quotient morphism forgets to the `CommHopfAlgCat` quotient morphism. -/
@[simp]
lemma forget₂_commHopfAlgCat_map_mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
      (mkQuotient H I) = CommHopfAlgCat.mkQuotient H.obj I :=
  rfl

/-- The kernel of the finite-type quotient morphism is the Hopf ideal being quotiented by. -/
lemma mkQuotient_ker (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    RingHom.ker (toBialgHom (mkQuotient H I)).toAlgHom.toRingHom = I.toIdeal :=
  CommHopfAlgCat.mkQuotient_ker H.obj I

/-- An element maps to zero in the finite-type quotient exactly when it belongs to the Hopf
ideal. -/
@[simp]
lemma mkQuotient_eq_zero_iff (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) (h : H) : toBialgHom (mkQuotient H I) h = 0 ↔ h ∈ I.toIdeal :=
  CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I h

variable {H K : FiniteTypeCommHopfAlgCat.{u, v} R}

/-- A morphism of finite-type commutative Hopf algebras out of `H` which kills a Hopf ideal
factors through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) : quotient H I ⟶ K :=
  ObjectProperty.homMk (CommHopfAlgCat.liftQuotient I f.hom hf)

/-- The finite-type quotient lift forgets to the `CommHopfAlgCat` quotient lift. -/
@[simp]
lemma forget₂_commHopfAlgCat_map_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
      (liftQuotient I f hf) = CommHopfAlgCat.liftQuotient I f.hom hf :=
  rfl

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma mkQuotient_comp_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient I f.hom hf

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  have hg' : _root_.CommHopfAlgCat.ofHom (Bialgebra.Quotient.mkBialgHom I.toIdeal) ≫ g.hom =
      f.hom :=
    congrArg
      (fun φ => (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
        (_root_.CommHopfAlgCat.{v} R)).map φ) hg
  exact CommHopfAlgCat.liftQuotient_unique (H := _root_.CommHopfAlgCat.of R H) I f.hom hf
    g.hom hg'

end FiniteTypeCommHopfAlgCat

end TauCeti
