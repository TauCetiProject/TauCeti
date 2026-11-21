/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation.Coaction
public import TauCeti.AlgebraicGeometry.Quotient.ComoduleAlgebra

/-!
# The conjugation quotient `Conj_H = H // H`

Let `H = Spec O(H)` be an affine group over a commutative ring `R`, acting on itself by
conjugation (`TauCeti.HopfAlgebra.conjugationComoduleAlgebra`). Its **conjugation quotient** is the
affine quotient `Conj_H = H // H = Spec O(H)^H` of this action
(`TauCeti.HopfAlgebra.conjugationQuotient`), and the quotient morphism
`χ_H : H ⟶ Conj_H` (`TauCeti.HopfAlgebra.conjugationQuotientMap`) is induced by the inclusion of
the conjugation-invariant functions `TauCeti.HopfAlgebra.conjugationInvariants`.

The quotient morphism is invariant under conjugation
(`TauCeti.HopfAlgebra.conjugationCoact_conjugationQuotientMap`). On points with values in any
commutative `R`-algebra `K'`, in particular any field over the base, this says
`χ_H(g h g⁻¹) = χ_H(h)` for `g, h ∈ H(K')`
(`TauCeti.HopfAlgebra.comp_val_conjugationInvariants_conj`), so `χ_H` is constant on
`H(K')`-conjugacy classes. Every conjugation-invariant morphism from `H` to an affine scheme
factors uniquely through `χ_H`
(`TauCeti.HopfAlgebra.existsUnique_conjugationQuotientMap_comp_eq`).

For `H` connected reductive over a field, `Conj_H(K)` for algebraically closed `K` is the set of
semisimple conjugacy classes, and for `H = GL_n` the map `χ_H` is the characteristic polynomial;
these statements are not proved here.

## Main declarations

* `TauCeti.HopfAlgebra.conjugationQuotient`: the conjugation quotient `Conj_H = H // H`.
* `TauCeti.HopfAlgebra.conjugationQuotientMap`: the quotient morphism `χ_H : H ⟶ Conj_H`.
* `TauCeti.HopfAlgebra.conjugationCoact_conjugationQuotientMap`: `χ_H` is conjugation invariant.
* `TauCeti.HopfAlgebra.existsUnique_conjugationQuotientMap_comp_eq`: the affine-target universal
  property of `χ_H`.

## References

* R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS **25** (1965),
  §6.
* G. Böckle, M. Harris, C. Khare, J. A. Thorne, arXiv:1609.03491v2, §3 (the paragraph before
  Proposition 3.2, and Proposition 3.2).
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u

variable (R : Type*) (H : Type u) [CommRing R] [CommRing H] [_root_.HopfAlgebra R H]

/-- The **conjugation quotient** `Conj_H = H // H = Spec O(H)^H` of an affine group `H`: the
affine quotient of `H` by its conjugation action on itself. -/
noncomputable abbrev conjugationQuotient : Scheme.{u} :=
  letI := conjugationComoduleAlgebra (R := R) (H := H)
  ComoduleAlgebra.AffineQuotient.quotient R H H

/-- The quotient morphism `χ_H : H ⟶ Conj_H` of the conjugation action, induced by the inclusion
of the conjugation-invariant functions. -/
noncomputable def conjugationQuotientMap : Spec (CommRingCat.of H) ⟶ conjugationQuotient R H :=
  letI := conjugationComoduleAlgebra (R := R) (H := H)
  ComoduleAlgebra.AffineQuotient.projection R H H

/-- The quotient morphism `χ_H` is the affine-quotient morphism of the conjugation action. -/
theorem conjugationQuotientMap_def :
    conjugationQuotientMap R H =
      letI := conjugationComoduleAlgebra (R := R) (H := H)
      ComoduleAlgebra.AffineQuotient.projection R H H :=
  (rfl)

/-- The coordinate ring of `Conj_H` is the ring of conjugation-invariant functions. -/
theorem conjugationQuotient_eq :
    conjugationQuotient R H = Spec (CommRingCat.of (conjugationInvariants R H)) := by
  rw [conjugationInvariants_def]

/-- **The quotient morphism `χ_H` is conjugation invariant**: composing it with the conjugation
action `Spec (H ⊗[R] H) ⟶ H` or with the projection `Spec (H ⊗[R] H) ⟶ H` gives the same
morphism. -/
@[reassoc]
theorem conjugationCoact_conjugationQuotientMap :
    Spec.map (CommRingCat.ofHom (conjugationCoactAlgHom R H).toRingHom) ≫
        conjugationQuotientMap R H =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : H →+* H ⊗[R] H)) ≫
        conjugationQuotientMap R H := by
  let := conjugationComoduleAlgebra (R := R) (H := H)
  rw [conjugationQuotientMap_def, ← conjugationComoduleAlgebra_coactAlgHom]
  exact ComoduleAlgebra.AffineQuotient.act_projection R H H

variable {R H}

/-- **`χ_H` is a categorical quotient in affine schemes**: every conjugation-invariant morphism
from `H` to an affine scheme factors uniquely through `χ_H`. -/
theorem existsUnique_conjugationQuotientMap_comp_eq {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of H) ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom (conjugationCoactAlgHom R H).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : H →+* H ⊗[R] H)) ≫ f) :
    ∃! g : conjugationQuotient R H ⟶ Y, conjugationQuotientMap R H ≫ g = f := by
  let := conjugationComoduleAlgebra (R := R) (H := H)
  rw [conjugationQuotientMap_def]
  rw [← conjugationComoduleAlgebra_coactAlgHom] at hf
  exact ComoduleAlgebra.AffineQuotient.existsUnique_desc f hf

end TauCeti.HopfAlgebra
