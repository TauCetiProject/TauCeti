/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate

/-!
# Base change squares of Hopf spectra from coordinate squares

Let `R → S` be a ring map, `f : H' ⟶ H` a morphism of commutative Hopf algebras over `R` and
`g : A' ⟶ A` one over `S`, and let `b : S ⊗ H ≅ A`, `b' : S ⊗ H' ≅ A'` identify the scalar
extensions. If the coordinate square `(S ⊗ f) ≫ b = b' ≫ g` commutes, then the square of group
schemes over `S` formed by the base change of `Spec f`, the comparisons
`hopfSpecBaseChangeGrpIso` followed by `Spec b⁻¹`, and `Spec g` commutes
(`TauCeti.AffineGroupSchemeCat.baseChange_map_hopfSpec_comp_baseChangeIso_hom`). This turns the
naturality in the base ring of an isomorphism of coordinate Hopf algebras into the naturality of
the isomorphism of group schemes.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.AffineGroupSchemeCat

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- **A coordinate square gives a group-scheme square.** If `(S ⊗ f) ≫ b = b' ≫ g`, then base
change of `Spec f` followed by the comparison of `Spec (S ⊗ H')` with `Spec A'` is the comparison
of `Spec (S ⊗ H)` with `Spec A` followed by `Spec g`. -/
@[reassoc]
theorem baseChange_map_hopfSpec_comp_baseChangeIso_hom {H H' : CommHopfAlgCat.{u} R}
    {A A' : CommHopfAlgCat.{u} S} (f : H' ⟶ H) (g : A' ⟶ A)
    (b : CommHopfAlgCat.baseChange (K := S) H ≅ A) (b' : CommHopfAlgCat.baseChange (K := S) H' ≅ A')
    (h : CommHopfAlgCat.baseChangeMap (K := S) f ≫ b.hom = b'.hom ≫ g) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          ((hopfSpec (CommRingCat.of R)).map f.op) ≫
        (hopfSpecBaseChangeGrpIso H' ≪≫ (hopfSpec (CommRingCat.of S)).mapIso b'.symm.op).hom =
      (hopfSpecBaseChangeGrpIso H ≪≫ (hopfSpec (CommRingCat.of S)).mapIso b.symm.op).hom ≫
        (hopfSpec (CommRingCat.of S)).map g.op := by
  have h' : b'.inv ≫ CommHopfAlgCat.baseChangeMap (K := S) f = g ≫ b.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom]
  rw [← Category.assoc, hopfSpecBaseChangeGrpIso_hom_naturality, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h']

end TauCeti.AffineGroupSchemeCat
