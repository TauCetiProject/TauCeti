/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.AffinePoint.Basic
public import TauCeti.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Complex points of a product semigroup

A splitting of an additive commutative monoid as a product identifies its complex points
with pairs of complex points of the factors. Restriction to each factor gives the forward
map; the inverse multiplies the two monomial values. This is a homeomorphism for arbitrary
finite monomial generating families, and supplies the affine charts of products of toric fans.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open Multiplicative

namespace TauCeti.Toric.AffineSemigroupComplexPoint

variable {S T U : Type*} [AddCommMonoid S] [AddCommMonoid T] [AddCommMonoid U]

/-- A splitting of a semigroup identifies its complex points with pairs of points of the
two factors, by restriction of multiplicative characters. -/
noncomputable def prodEquiv (e : S ≃+ T × U) :
    AffineSemigroupComplexPoint S ≃
      AffineSemigroupComplexPoint T × AffineSemigroupComplexPoint U :=
  (MonoidAlgebra.lift ℂ ℂ (Multiplicative S)).symm.trans <|
    (MulEquiv.monoidHomCongrLeft e.toMultiplicative).toEquiv.trans <|
      (MulEquiv.monoidHomCongrLeft (MulEquiv.prodMultiplicative T U)).toEquiv.trans <|
        MonoidHom.coprodEquiv.symm.toEquiv.trans <|
          Equiv.prodCongr (MonoidAlgebra.lift ℂ ℂ (Multiplicative T))
            (MonoidAlgebra.lift ℂ ℂ (Multiplicative U))

/-- The inverse product identification multiplies the values on the factor monomials. -/
@[simp]
theorem prodEquiv_symm_apply_single (e : S ≃+ T × U)
    (p : AffineSemigroupComplexPoint T × AffineSemigroupComplexPoint U) (s : S) :
    (prodEquiv e).symm p (MonoidAlgebra.single (ofAdd s) 1) =
      p.1 (MonoidAlgebra.single (ofAdd (e s).1) 1) *
        p.2 (MonoidAlgebra.single (ofAdd (e s).2) 1) := by
  simp [prodEquiv, MonoidAlgebra.lift_symm_apply]

/-- Restriction to the first factor reads its monomial values. -/
@[simp]
theorem prodEquiv_fst_apply_single (e : S ≃+ T × U)
    (x : AffineSemigroupComplexPoint S) (t : T) :
    (prodEquiv e x).1 (MonoidAlgebra.single (ofAdd t) 1) =
      x (MonoidAlgebra.single (ofAdd (e.symm (t, 0))) 1) := by
  have h := prodEquiv_symm_apply_single e (prodEquiv e x) (e.symm (t, 0))
  simpa [← MonoidAlgebra.one_def] using h.symm

/-- Restriction to the second factor reads its monomial values. -/
@[simp]
theorem prodEquiv_snd_apply_single (e : S ≃+ T × U)
    (x : AffineSemigroupComplexPoint S) (u : U) :
    (prodEquiv e x).2 (MonoidAlgebra.single (ofAdd u) 1) =
      x (MonoidAlgebra.single (ofAdd (e.symm (0, u))) 1) := by
  have h := prodEquiv_symm_apply_single e (prodEquiv e x) (e.symm (0, u))
  simpa [← MonoidAlgebra.one_def] using h.symm

/-- The product identification is a homeomorphism for any finite monomial generating
families on the three semigroups. -/
noncomputable def prodHomeomorph (e : S ≃+ T × U) {r rT rU : ℕ}
    (g : AddGeneratingFamily S r) (gT : AddGeneratingFamily T rT)
    (gU : AddGeneratingFamily U rU) :
    letI := affinePointTopology g
    letI := affinePointTopology gT
    letI := affinePointTopology gU
    AffineSemigroupComplexPoint S ≃ₜ
      AffineSemigroupComplexPoint T × AffineSemigroupComplexPoint U := by
  letI := affinePointTopology g
  letI := affinePointTopology gT
  letI := affinePointTopology gU
  have hforward : Continuous (prodEquiv e) := by
    exact ((continuous_iff_forall_continuous_apply_single gT _).2 fun t ↦ by
        exact (continuous_apply_single g (e.symm (t, 0))).congr
          fun x ↦ (prodEquiv_fst_apply_single e x t).symm).prodMk
      ((continuous_iff_forall_continuous_apply_single gU _).2 fun u ↦ by
        exact (continuous_apply_single g (e.symm (0, u))).congr
          fun x ↦ (prodEquiv_snd_apply_single e x u).symm)
  have hbackward : Continuous (prodEquiv e).symm := by
    apply (continuous_iff_forall_continuous_apply_single g _).2
    intro s
    simp only [prodEquiv_symm_apply_single]
    exact ((continuous_apply_single gT _).comp continuous_fst).mul
      ((continuous_apply_single gU _).comp continuous_snd)
  exact ⟨prodEquiv e, hforward, hbackward⟩

@[simp]
theorem coe_prodHomeomorph (e : S ≃+ T × U) {r rT rU : ℕ}
    (g : AddGeneratingFamily S r) (gT : AddGeneratingFamily T rT)
    (gU : AddGeneratingFamily U rU) :
    ⇑(prodHomeomorph e g gT gU) = prodEquiv e := (rfl)

@[simp]
theorem coe_prodHomeomorph_symm (e : S ≃+ T × U) {r rT rU : ℕ}
    (g : AddGeneratingFamily S r) (gT : AddGeneratingFamily T rT)
    (gU : AddGeneratingFamily U rU) :
    letI := affinePointTopology g
    letI := affinePointTopology gT
    letI := affinePointTopology gU
    ⇑(prodHomeomorph e g gT gU).symm = (prodEquiv e).symm := (rfl)

end TauCeti.Toric.AffineSemigroupComplexPoint
