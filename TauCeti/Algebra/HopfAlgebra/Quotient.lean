/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.Bialgebra.Quotient
import TauCeti.Algebra.HopfAlgebra.HopfIdeal

/-!
# The quotient Hopf algebra of a Hopf ideal

For a Hopf algebra `H` over a commutative ring `R` and a Hopf ideal `I` of `H`, Mathlib equips the
quotient ring `H ⧸ I` with the structure of a Hopf algebra over `R`, descending the
comultiplication, counit and antipode from `H` (see
`Mathlib.RingTheory.{Coalgebra,Bialgebra,HopfAlgebra}.Quotient`). Mathlib's instances fire on an
`Ideal` once it is known to be two-sided, a coideal, and antipode-stable. The **bridge** turning a
`TauCeti.HopfIdeal` into those Mathlib hypotheses lives in `TauCeti.Algebra.HopfAlgebra.HopfIdeal`
(`HopfIdeal.instIsCoideal`, `HopfIdeal.instIsHopfIdeal`), so that Mathlib's
`Coalgebra`/`Bialgebra`/`HopfAlgebra` instances apply to `H ⧸ I.toIdeal`. On top of that bridge this
file provides the part Mathlib lacks: the **universal property** `liftBialgHom` of the quotient
bialgebra.

This is the Layer 3 milestone "the quotient Hopf algebra `A/I`" of the reductive-groups
roadmap: closed subgroup schemes of an affine group scheme are represented on coordinate
rings by exactly these quotient Hopf algebras, and the three Hopf-ideal closure conditions
(`comul (I) ⊆ I ⊗ H + H ⊗ I`, `counit (I) = 0`, `S(I) ⊆ I`) are precisely what is needed for
the structure maps to descend.

## Main definitions

* `TauCeti.HopfIdeal.liftBialgHom`: the specialization to the underlying ideal of a Hopf ideal of
  the generic bialgebra-quotient universal property `Bialgebra.Quotient.liftBialgHom` (which needs
  only a two-sided coideal, not an antipode, and lives in `TauCeti.Algebra.Bialgebra.Quotient`),
  namely the bialgebra morphism induced from a bialgebra morphism which kills the Hopf ideal,
  together with its computation and uniqueness lemmas.

The quotient coalgebra/bialgebra/Hopf-algebra structure maps, the quotient bialgebra morphism, and
the commutative-case antipode algebra homomorphism are themselves Mathlib's
`Bialgebra.Quotient.comulAlgHom`, `Bialgebra.Quotient.counitAlgHom`,
`Bialgebra.Quotient.mkBialgHom`, `HopfAlgebra.antipode`, and `HopfAlgebra.antipodeAlgHom`; the older
TauCeti names for them are retained as deprecated wrappers.

## References

This follows the standard construction of the quotient Hopf algebra; see Sweedler,
*Hopf Algebras*, Chapter 4, and Waterhouse, *Introduction to Affine Group Schemes*, §16. It
builds on the `TauCeti.HopfIdeal` API and Mathlib's quotient Hopf-algebra machinery
(`Mathlib.RingTheory.HopfAlgebra.Quotient`, due to Robert Hawkins), the algebra-quotient lift
`Ideal.Quotient.liftₐ`, and `HopfAlgebra.antipodeAlgHom` from
`Mathlib.RingTheory.HopfAlgebra.Convolution`, due to Yaël Dillies, Michał Mrugała and Yunzhou Xie.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfIdeal

universe u v

variable {R : Type u} {H : Type v}
variable [CommRing R]

section Ring

variable [Ring H] [HopfAlgebra R H]

variable (I : HopfIdeal R H)

/-- Mathlib's quotient coalgebra structure on `H ⧸ I`, recovered via `inferInstance` from the
bridge instance `HopfIdeal.instIsCoideal`. -/
@[deprecated "Mathlib provides this quotient instance; use `inferInstance`" (since := "2026-06-19")]
noncomputable abbrev instCoalgebraQuotient (I : HopfIdeal R H) : Coalgebra R (H ⧸ I.toIdeal) :=
  inferInstance

/-- Mathlib's quotient bialgebra structure on `H ⧸ I`, recovered via `inferInstance` from the
bridge instance `HopfIdeal.instIsHopfIdeal`. -/
@[deprecated "Mathlib provides this quotient instance; use `inferInstance`" (since := "2026-06-19")]
noncomputable abbrev instBialgebraQuotient (I : HopfIdeal R H) : Bialgebra R (H ⧸ I.toIdeal) :=
  inferInstance

/-- Mathlib's quotient Hopf-algebra structure on `H ⧸ I`, recovered via `inferInstance` from
the bridge instance `HopfIdeal.instIsHopfIdeal`. -/
@[deprecated "Mathlib provides this quotient instance; use `inferInstance`" (since := "2026-06-19")]
noncomputable abbrev instHopfAlgebraQuotient (I : HopfIdeal R H) : HopfAlgebra R (H ⧸ I.toIdeal) :=
  inferInstance

/-- The comultiplication of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
@[deprecated Bialgebra.Quotient.comulAlgHom (since := "2026-06-19")]
noncomputable def quotientComulAlgHom :
    (H ⧸ I.toIdeal) →ₐ[R] (H ⧸ I.toIdeal) ⊗[R] (H ⧸ I.toIdeal) :=
  Bialgebra.Quotient.comulAlgHom I.toIdeal

/-- The counit of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
@[deprecated Bialgebra.Quotient.counitAlgHom (since := "2026-06-19")]
noncomputable def quotientCounitAlgHom : (H ⧸ I.toIdeal) →ₐ[R] R :=
  Bialgebra.Quotient.counitAlgHom I.toIdeal

/-- The comultiplication on the quotient, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.comul_mk (since := "2026-06-19")]
theorem comul_mk (h : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h)
      = TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
        (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Coalgebra.comul h) := by
  rw [Ideal.Quotient.mkₐ_eq_mk]
  exact Bialgebra.Quotient.comul_mk I.toIdeal h

/-- The counit on the quotient, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.counit_mk (since := "2026-06-19")]
theorem counit_mk (h : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h := by
  rw [Ideal.Quotient.mkₐ_eq_mk]
  exact Bialgebra.Quotient.counit_mk I.toIdeal h

/-- The descended comultiplication, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.comul_mk (since := "2026-06-19")]
theorem quotientComulAlgHom_mk (h : H) :
    quotientComulAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h)
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal)
        (Ideal.Quotient.mkₐ R I.toIdeal) (Coalgebra.comul h) := by
  rw [quotientComulAlgHom, Ideal.Quotient.mkₐ_eq_mk]
  refine (Bialgebra.Quotient.comul_mk I.toIdeal h).trans ?_
  exact (LinearMap.congr_fun
    (Algebra.TensorProduct.toLinearMap_map (Ideal.Quotient.mkₐ R I.toIdeal)
      (Ideal.Quotient.mkₐ R I.toIdeal)) _).symm

/-- The descended counit, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.counit_mk (since := "2026-06-19")]
theorem quotientCounitAlgHom_mk (h : H) :
    quotientCounitAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h := by
  rw [quotientCounitAlgHom, Ideal.Quotient.mkₐ_eq_mk]
  exact Bialgebra.Quotient.counit_mk I.toIdeal h

/-- The antipode of the quotient, as an `R`-linear map descended from `H`. -/
@[deprecated "Use `HopfAlgebra.antipode R` on the quotient instead." (since := "2026-06-19")]
noncomputable def quotientAntipodeLinearMap : (H ⧸ I.toIdeal) →ₗ[R] H ⧸ I.toIdeal :=
  HopfAlgebra.antipode R

/-- The antipode on the quotient, evaluated on a quotient class. -/
@[deprecated HopfAlgebra.Quotient.antipode_mk (since := "2026-06-19")]
theorem antipode_mk (h : H) :
    HopfAlgebra.antipode R (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  rw [Ideal.Quotient.mkₐ_eq_mk]
  exact HopfAlgebra.Quotient.antipode_mk I.toIdeal h

/-- The descended antipode linear map, evaluated on a quotient class. -/
@[deprecated HopfAlgebra.Quotient.antipode_mk (since := "2026-06-19")]
theorem quotientAntipodeLinearMap_mk (h : H) :
    quotientAntipodeLinearMap I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  rw [quotientAntipodeLinearMap, Ideal.Quotient.mkₐ_eq_mk]
  exact HopfAlgebra.Quotient.antipode_mk I.toIdeal h

/-- The quotient map `H →ₐ[R] H ⧸ I` as a bialgebra morphism: it is an algebra homomorphism
respecting the counit and comultiplication by construction. -/
@[deprecated Bialgebra.Quotient.mkBialgHom (since := "2026-06-19")]
noncomputable def mkBialgHom : H →ₐc[R] H ⧸ I.toIdeal :=
  Bialgebra.Quotient.mkBialgHom I.toIdeal

/-- The quotient bialgebra morphism, evaluated on an element of `H`. -/
@[deprecated Bialgebra.Quotient.mkBialgHom_apply (since := "2026-06-19")]
theorem mkBialgHom_apply (h : H) : mkBialgHom I h = Ideal.Quotient.mkₐ R I.toIdeal h := by
  rw [mkBialgHom, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk]

variable {K : Type*} [Semiring K] [Bialgebra R K]

/-- A bialgebra morphism out of `H` which kills a Hopf ideal factors through the quotient
bialgebra.

This is the specialization to `I.toIdeal` of the general bialgebra-quotient universal property
`Bialgebra.Quotient.liftBialgHom`, which only needs a two-sided coideal. -/
noncomputable def liftBialgHom (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ I.toIdeal →ₐc[R] K :=
  Bialgebra.Quotient.liftBialgHom I.toIdeal f hf

/-- The quotient lift, evaluated on a quotient class. -/
@[simp]
theorem liftBialgHom_mk (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    liftBialgHom I f hf (Ideal.Quotient.mkₐ R I.toIdeal h) = f h :=
  Bialgebra.Quotient.liftBialgHom_mk I.toIdeal f hf h

/-- The quotient lift composed with the quotient map is the original bialgebra morphism. -/
@[simp]
theorem liftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (liftBialgHom I f hf).comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) = f :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom I.toIdeal f hf

/-- A bialgebra morphism out of the quotient is determined by its precomposition with the
quotient map. -/
theorem liftBialgHom_unique (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (g : H ⧸ I.toIdeal →ₐc[R] K)
    (hg : g.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) = f) :
    g = liftBialgHom I f hf :=
  Bialgebra.Quotient.liftBialgHom_unique I.toIdeal f hf g hg

end Ring

section CommRing

variable [CommRing H] [HopfAlgebra R H]
variable (I : HopfIdeal R H)

/-- The antipode of the quotient, as an `R`-algebra homomorphism descended from `H` (valid since
`H` is commutative, where the antipode is an algebra homomorphism). -/
@[deprecated HopfAlgebra.antipodeAlgHom (since := "2026-06-19")]
noncomputable def quotientAntipodeAlgHom : (H ⧸ I.toIdeal) →ₐ[R] H ⧸ I.toIdeal :=
  HopfAlgebra.antipodeAlgHom R (H ⧸ I.toIdeal)

/-- The descended antipode algebra homomorphism, evaluated on a quotient class. -/
@[deprecated HopfAlgebra.Quotient.antipode_mk (since := "2026-06-19")]
theorem quotientAntipodeAlgHom_mk (h : H) :
    quotientAntipodeAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  rw [quotientAntipodeAlgHom]
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  exact HopfAlgebra.Quotient.antipode_mk I.toIdeal h

end CommRing

end HopfIdeal

end TauCeti
