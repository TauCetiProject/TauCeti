/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
* `TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient`: the induced morphism out of a quotient.

## References

The quotient Hopf algebra construction follows `TauCeti.Algebra.HopfAlgebra.Quotient`,
which cites Sweedler, *Hopf Algebras*, Chapter 4, and Waterhouse, *Introduction to Affine
Group Schemes*, §16. The finite-type descent is Mathlib's
`Algebra.FiniteType.of_surjective`.
-/

namespace TauCeti

universe u v

namespace CommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- The quotient of a commutative Hopf algebra by a Hopf ideal, as a bundled commutative
Hopf algebra. -/
noncomputable abbrev quotient (H : CommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    CommHopfAlgCat.{u, v} R :=
  of R (H ⧸ I.toIdeal)

/-- The quotient morphism `H ⟶ H ⧸ I` in `CommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : CommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    H ⟶ quotient H I :=
  ofHom (HopfIdeal.mkBialgHom I)

/-- The quotient morphism has the expected underlying bialgebra morphism. -/
@[simp]
lemma toBialgHom_mkQuotient (H : CommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    toBialgHom (mkQuotient H I) = HopfIdeal.mkBialgHom I :=
  rfl

/-- The quotient morphism sends an element to its quotient class. -/
@[simp]
lemma mkQuotient_apply (H : CommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) (h : H) :
    toBialgHom (mkQuotient H I) h = Ideal.Quotient.mkₐ R I.toIdeal h :=
  rfl

variable {H K : CommHopfAlgCat.{u, v} R}

/-- A morphism of commutative Hopf algebras out of `H` which kills a Hopf ideal factors
through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) : quotient H I ⟶ K :=
  ofHom (HopfIdeal.liftBialgHom I (toBialgHom f) hf)

/-- The quotient lift has the expected underlying bialgebra morphism. -/
@[simp]
lemma toBialgHom_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    toBialgHom (liftQuotient I f hf) = HopfIdeal.liftBialgHom I (toBialgHom f) hf :=
  rfl

/-- The quotient lift evaluates on quotient classes as the original morphism. -/
@[simp]
lemma liftQuotient_mk (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) (h : H) :
    toBialgHom (liftQuotient I f hf) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      toBialgHom f h :=
  HopfIdeal.liftBialgHom_mk I (toBialgHom f) hf h

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma liftQuotient_comp_mkQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  ext h
  exact BialgHom.congr_fun
    (HopfIdeal.liftBialgHom_comp_mkBialgHom I (toBialgHom f) hf) h

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  calc
    toBialgHom g (Ideal.Quotient.mkₐ R I.toIdeal h) =
        toBialgHom (mkQuotient H I ≫ g) h := rfl
    _ = toBialgHom f h := by rw [hg]
    _ = toBialgHom (liftQuotient I f hf) (Ideal.Quotient.mkₐ R I.toIdeal h) :=
      (liftQuotient_mk I f hf h).symm

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- The quotient of a finite-type commutative Hopf algebra by a Hopf ideal, as a bundled
finite-type commutative Hopf algebra. -/
noncomputable abbrev quotient (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  of R (H ⧸ I.toIdeal)

/-- The quotient morphism `H ⟶ H ⧸ I` in `FiniteTypeCommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) : H ⟶ quotient H I :=
  ofHom (HopfIdeal.mkBialgHom I)

/-- The quotient morphism has the expected underlying bialgebra morphism. -/
@[simp]
lemma toBialgHom_mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) : toBialgHom (mkQuotient H I) = HopfIdeal.mkBialgHom I :=
  rfl

/-- The quotient morphism sends an element to its quotient class. -/
@[simp]
lemma mkQuotient_apply (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) (h : H) :
    toBialgHom (mkQuotient H I) h = Ideal.Quotient.mkₐ R I.toIdeal h :=
  rfl

variable {H K : FiniteTypeCommHopfAlgCat.{u, v} R}

/-- A morphism of finite-type commutative Hopf algebras out of `H` which kills a Hopf ideal
factors through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) : quotient H I ⟶ K :=
  ofHom (HopfIdeal.liftBialgHom I (toBialgHom f) hf)

/-- The quotient lift has the expected underlying bialgebra morphism. -/
@[simp]
lemma toBialgHom_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    toBialgHom (liftQuotient I f hf) = HopfIdeal.liftBialgHom I (toBialgHom f) hf :=
  rfl

/-- The quotient lift evaluates on quotient classes as the original morphism. -/
@[simp]
lemma liftQuotient_mk (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) (h : H) :
    toBialgHom (liftQuotient I f hf) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      toBialgHom f h :=
  HopfIdeal.liftBialgHom_mk I (toBialgHom f) hf h

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma liftQuotient_comp_mkQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (CommHopfAlgCat.{u, v} R)).map_injective
  exact CommHopfAlgCat.liftQuotient_comp_mkQuotient I f.hom hf

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (CommHopfAlgCat.{u, v} R)).map_injective
  have hg' : CommHopfAlgCat.ofHom (HopfIdeal.mkBialgHom I) ≫ g.hom = f.hom :=
    congrArg
      (fun φ => (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
        (CommHopfAlgCat.{u, v} R)).map φ) hg
  exact CommHopfAlgCat.liftQuotient_unique (H := CommHopfAlgCat.of R H) I f.hom hf
    g.hom hg'

end FiniteTypeCommHopfAlgCat

end TauCeti
