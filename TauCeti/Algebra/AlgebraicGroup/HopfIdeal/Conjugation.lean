/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Comap

/-!
# Conjugation of closed subgroup schemes

A rational point of an affine group conjugates its closed subgroup schemes. In Hopf coordinates,
closed subgroups are represented contravariantly by Hopf ideals, so conjugating an ideal means
taking its inverse image under the coordinate automorphism of point conjugation.

This file makes that operation a group action on Hopf ideals. It proves the order and membership
characterizations and checks its geometric meaning on points: pulling a point back by the inner
automorphism identifies the points cut out by an ideal with those cut out by its conjugate.

The action is the basic language needed for conjugacy theorems for Borel subgroups and maximal
tori.

A rational point `g` normalizes the closed subgroup `N` cut out by `I` when conjugation by `g`
maps `I` into itself; every rational point normalizes a normal closed subgroup. Conjugation by a
normalizing point then restricts to an endomorphism of `N`, whose coordinate map is the bialgebra
endomorphism of `H ⧸ I` induced by point conjugation. This is how normalizing points act on the
characters of `N`.

## Main declarations

* `TauCeti.HopfIdeal.conjugate`: the Hopf ideal of the conjugated closed subgroup.
* `TauCeti.HopfIdeal.instMulAction`: rational points act on Hopf ideals by conjugation.
* `TauCeti.HopfIdeal.IsNormal.le_conjugate`: rational points normalize a normal closed subgroup.
* `TauCeti.HopfIdeal.quotientPointConjugation`: conjugation by a normalizing point, restricted to
  the subgroup, as a bialgebra endomorphism of its coordinate algebra.
* `TauCeti.CommHopfAlgCat.mapDomain_pointConjugation_mem_conjugate_iff`: the pointwise
  interpretation of the conjugated ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 3.5 and 17.a.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]

/-- The Hopf ideal cutting out the conjugate of a closed subgroup by a rational point.

If `I` cuts out `K` and `g` is an `R`-valued point, this ideal cuts out `gKg⁻¹`. Since coordinate
maps are contravariant, it is the inverse image of `I` under the coordinate automorphism of
`x ↦ gxg⁻¹`. -/
noncomputable def conjugate (I : HopfIdeal R H) (g : WithConv (H →ₐ[R] R)) : HopfIdeal R H :=
  I.comapOfSurjective (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
    (by
      simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
        EquivLike.surjective (HopfAlgebra.pointConjugationBialgEquiv g))

/-- Conjugation is the inverse image under the bialgebra automorphism of point conjugation.

This is the public interface lemma for `conjugate`: the definition's body is not exposed
outside this module, so downstream files cannot unfold it and rewrite with this instead. -/
theorem conjugate_eq_comapOfSurjective (I : HopfIdeal R H)
    (g : WithConv (H →ₐ[R] R)) :
    I.conjugate g =
      I.comapOfSurjective (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
        (by
          simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective (HopfAlgebra.pointConjugationBialgEquiv g)) := by
  rfl

/-- Membership in a conjugated Hopf ideal is tested after applying the coordinate
automorphism of point conjugation. -/
@[simp]
theorem mem_conjugate {I : HopfIdeal R H} {g : WithConv (H →ₐ[R] R)} {x : H} :
    x ∈ I.conjugate g ↔ HopfAlgebra.pointConjugationAlgHom g x ∈ I := by
  rw [conjugate, mem_comapOfSurjective]
  rw [← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  rfl

/-- Conjugation by the identity point fixes every Hopf ideal. -/
@[simp]
theorem conjugate_one (I : HopfIdeal R H) :
    I.conjugate (1 : WithConv (H →ₐ[R] R)) = I := by
  ext x
  rw [mem_conjugate, HopfAlgebra.pointConjugationAlgHom_one, AlgHom.id_apply]

/-- Successive conjugations are conjugation by the product of the points. -/
theorem conjugate_mul (I : HopfIdeal R H) (g h : WithConv (H →ₐ[R] R)) :
    I.conjugate (g * h) = (I.conjugate h).conjugate g := by
  ext x
  rw [mem_conjugate, mem_conjugate, mem_conjugate,
    HopfAlgebra.pointConjugationAlgHom_mul, AlgHom.comp_apply]

/-- Conjugating by a point and then by its inverse recovers the original Hopf ideal. -/
@[simp]
theorem conjugate_inv_conjugate (I : HopfIdeal R H) (g : WithConv (H →ₐ[R] R)) :
    (I.conjugate g).conjugate g⁻¹ = I := by
  rw [← conjugate_mul, inv_mul_cancel, conjugate_one]

/-- Conjugating by the inverse point and then by the point recovers the original Hopf ideal. -/
@[simp]
theorem conjugate_conjugate_inv (I : HopfIdeal R H) (g : WithConv (H →ₐ[R] R)) :
    (I.conjugate g⁻¹).conjugate g = I := by
  rw [← conjugate_mul, mul_inv_cancel, conjugate_one]

/-- Conjugation is monotone on Hopf ideals. -/
theorem conjugate_mono (g : WithConv (H →ₐ[R] R)) {I J : HopfIdeal R H} (h : I ≤ J) :
    I.conjugate g ≤ J.conjugate g := by
  intro x hx
  exact mem_conjugate.mpr (h (mem_conjugate.mp hx))

/-- If a conjugated point annihilates `J` and the kernel of the original point is contained in
`I`, then conjugating `J` by the inverse point gives an ideal contained in `I`. -/
theorem conjugate_inv_le_of_mem_quotientPointsSubgroup
    {A : Type w} [CommRing A] [Algebra R A]
    (I J : HopfIdeal R H) (g : WithConv (H →ₐ[R] R))
    (π : H →ₐ[R] A) (hker : ∀ x, π x = 0 → x ∈ I)
    (hmem : WithConv.toConv (π.comp (HopfAlgebra.pointConjugationAlgHom g)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of R H) J
        (CommAlgCat.of R A)) :
    J.conjugate g⁻¹ ≤ I := by
  have hle : J ≤ I.conjugate g := by
    intro x hx
    rw [mem_conjugate]
    exact hker _ ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hmem x hx)
  simpa using conjugate_mono g⁻¹ hle

/-- If the conjugated generic point of the quotient by `I` belongs to the subgroup defined by
`J`, then `J.conjugate g⁻¹ ≤ I`. -/
theorem conjugate_inv_le_of_mem_quotientPointsSubgroup_mkQuotient
    (I J : HopfIdeal R H) (g : WithConv (H →ₐ[R] R))
    (hmem : WithConv.toConv (((CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of R H) I).hom : H →ₐ[R]
        (CommHopfAlgCat.quotient (CommHopfAlgCat.of R H) I)).comp
        (HopfAlgebra.pointConjugationAlgHom g)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of R H) J
        (CommAlgCat.of R (CommHopfAlgCat.quotient (CommHopfAlgCat.of R H) I))) :
    J.conjugate g⁻¹ ≤ I := by
  exact conjugate_inv_le_of_mem_quotientPointsSubgroup I J g
    ((CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of R H) I).hom : H →ₐ[R]
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of R H) I))
    (by
      intro x hx
      rw [BialgHom.coe_toAlgHom] at hx
      exact HopfIdeal.mem_toIdeal.mp
        ((CommHopfAlgCat.mkQuotient_eq_zero_iff (CommHopfAlgCat.of R H) I x).mp hx)) hmem

/-- Conjugation preserves and reflects containment of Hopf ideals. -/
@[simp]
theorem conjugate_le_conjugate_iff (I J : HopfIdeal R H)
    (g : WithConv (H →ₐ[R] R)) : I.conjugate g ≤ J.conjugate g ↔ I ≤ J := by
  constructor
  · intro h
    have h' := conjugate_mono g⁻¹ h
    simpa using h'
  · exact conjugate_mono g

/-- Conjugation preserves and reflects equality of Hopf ideals. -/
@[simp]
theorem conjugate_eq_conjugate_iff (I J : HopfIdeal R H)
    (g : WithConv (H →ₐ[R] R)) : I.conjugate g = J.conjugate g ↔ I = J := by
  constructor
  · intro h
    have h' := congrArg (fun K : HopfIdeal R H => K.conjugate g⁻¹) h
    simpa using h'
  · rintro rfl
    rfl

/-- Rational points act on Hopf ideals by conjugating the represented closed subgroup. -/
noncomputable instance instMulAction :
    MulAction (WithConv (H →ₐ[R] R)) (HopfIdeal R H) where
  smul g I := I.conjugate g
  one_smul := conjugate_one
  mul_smul g h I := conjugate_mul I g h

/-- The rational-point action on Hopf ideals is conjugation. -/
@[simp]
theorem smul_eq_conjugate (g : WithConv (H →ₐ[R] R)) (I : HopfIdeal R H) :
    g • I = I.conjugate g :=
  rfl

/-- Every rational point normalizes a normal closed subgroup: conjugation by it maps the defining
ideal into itself. -/
theorem IsNormal.le_conjugate {I : HopfIdeal R H} (hI : I.IsNormal)
    (g : WithConv (H →ₐ[R] R)) : I ≤ I.conjugate g := by
  -- Conjugation by `g` pulls back as the universal conjugation followed by evaluation at `g` in
  -- the conjugating variable, and that evaluation keeps `H ⊗ I` inside `I`.
  let f := Algebra.TensorProduct.productMap
    (AlgHom.mapValue (H := H) (Algebra.ofId R H) g).ofConv (AlgHom.id R H)
  have hconj : HopfAlgebra.pointConjugationAlgHom g =
      f.comp (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) := by
    apply WithConv.toConv_injective
    rw [HopfAlgebra.toConv_pointConjugationAlgHom, HopfAlgebra.productMap_comp_conjugationAlgHom,
      WithConv.toConv_ofConv]
  have hker : rightTensorIdeal (R := R) (H := H) I.toIdeal ≤ I.toIdeal.comap f.toRingHom := by
    rw [rightTensorIdeal_le_iff]
    intro y hy
    simpa [f] using hy
  intro x hx
  rw [mem_conjugate, hconj, AlgHom.comp_apply, ← mem_toIdeal]
  exact hker (hI.conjugation_mem hx)

/-- Conjugation by a rational point `g` normalizing the closed subgroup `N` cut out by `I`,
restricted to `N`. This is the bialgebra endomorphism of `H ⧸ I` induced by the coordinate map of
`x ↦ g x g⁻¹`. -/
noncomputable def quotientPointConjugation (I : HopfIdeal R H) (g : WithConv (H →ₐ[R] R))
    (hg : I ≤ I.conjugate g) : H ⧸ I.toIdeal →ₐc[R] H ⧸ I.toIdeal :=
  Bialgebra.Quotient.liftBialgHom I.toIdeal
    ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom)
    (fun x hx ↦ by
      rw [RingHom.mem_ker]
      simpa [← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom, Ideal.Quotient.eq_zero_iff_mem]
        using mem_conjugate.mp (hg hx))

/-- Restricted conjugation sends the class of `x` to the class of its conjugate. -/
@[simp]
theorem quotientPointConjugation_mk (I : HopfIdeal R H) (g : WithConv (H →ₐ[R] R))
    (hg : I ≤ I.conjugate g) (x : H) :
    I.quotientPointConjugation g hg (Ideal.Quotient.mk I.toIdeal x) =
      Ideal.Quotient.mk I.toIdeal (HopfAlgebra.pointConjugationAlgHom g x) := by
  rw [quotientPointConjugation, Bialgebra.Quotient.liftBialgHom_mk]
  simp [← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]

/-- Restricted conjugation by the identity point is the identity. -/
@[simp]
theorem quotientPointConjugation_one (I : HopfIdeal R H) (h : I ≤ I.conjugate 1) :
    I.quotientPointConjugation 1 h = BialgHom.id R (H ⧸ I.toIdeal) := by
  ext q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- Restricted conjugations compose in the order forced by contravariance. -/
theorem quotientPointConjugation_mul (I : HopfIdeal R H) (g h : WithConv (H →ₐ[R] R))
    (hg : I ≤ I.conjugate g) (hh : I ≤ I.conjugate h) (hgh : I ≤ I.conjugate (g * h)) :
    I.quotientPointConjugation (g * h) hgh =
      (I.quotientPointConjugation h hh).comp (I.quotientPointConjugation g hg) := by
  ext q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [HopfAlgebra.pointConjugationAlgHom_mul]

end HopfIdeal

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]

/-- Point conjugation identifies the subgroup cut out by a Hopf ideal with the subgroup cut out
by its conjugate. -/
theorem mapDomain_pointConjugation_mem_conjugate_iff
    (I : HopfIdeal R H) (g : WithConv (H →ₐ[R] R))
    (A : CommAlgCat.{w} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    AlgHom.mapDomain (A := A) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom x ∈
        quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) (I.conjugate g) A ↔
      x ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I A := by
  have hinj : Function.Injective
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom := by
    simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
      EquivLike.injective (HopfAlgebra.pointConjugationBialgEquiv g)
  have hsurj : Function.Surjective
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom := by
    simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
      EquivLike.surjective (HopfAlgebra.pointConjugationBialgEquiv g)
  have he : BialgEquiv.ofBijective
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom ⟨hinj, hsurj⟩ =
      HopfAlgebra.pointConjugationBialgEquiv g := by
    ext z
    simp only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.ofBijective_apply, BialgHom.coe_coe]
  have h := mapDomainMulEquiv_mem_quotientPointsSubgroup_comapOfSurjective_iff
    (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom hinj hsurj I A x
  rw [he, AlgHom.mapDomainMulEquiv_apply, ← BialgEquiv.toBialgHom_eq_coe] at h
  rw [HopfIdeal.conjugate_eq_comapOfSurjective]
  exact h

/-- In explicit pointwise terms, conjugating a point by `g` carries the points of `I` exactly
onto the points of the conjugated ideal. -/
theorem pointConjugation_mem_conjugate_iff
    (I : HopfIdeal R H) (g : WithConv (H →ₐ[R] R))
    (A : CommAlgCat.{w} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    AlgHom.mapValue (H := H) (Algebra.ofId R A) g * x *
          (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ ∈
        quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) (I.conjugate g) A ↔
      x ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I A := by
  rw [← HopfAlgebra.mapDomain_pointConjugationBialgEquiv]
  exact mapDomain_pointConjugation_mem_conjugate_iff I g A x

end CommHopfAlgCat

end TauCeti
