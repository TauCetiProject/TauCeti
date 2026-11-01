/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import TauCeti.AlgebraicGeometry.Descent.Contraction
public import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Contraction descent tested on geometric fibres

A morphism out of a contraction descends if it is constant on every geometric fibre.
Here constancy means that the image in the target has at most one underlying point; the
scheme-theoretic factorization is a conclusion, not an additional hypothesis.

For any scheme morphism `c : X ⟶ Y`, constancy on its set-theoretic fibres is equivalent to
constancy after pulling back to an algebraic closure of each residue field of `Y`. Equivalently,
one can test all algebraically closed field-valued points of `Y`. This uses the surjectivity
of a geometric fibre onto the corresponding set-theoretic fibre, and needs no finiteness or
reducedness hypotheses.

If `c` is universally closed and surjective, and `𝒪_Y → c_*𝒪_X` is an isomorphism, this
criterion gives unique descent of morphisms, including morphisms over a base. These are the
geometric-fibre versions of `Scheme.Hom.existsUnique_comp_eq_of_universallyClosed`.
They apply to contractions of rational tails and bridges; no separatedness of the target is
needed. Compatibility of the descended morphism with base change is the commutative-square
identity `Scheme.Hom.descOfIsQuotientMap_of_commSq`.

## References

* The Stacks Project, Tags 0E7B and 0E8A, for contractions and stabilization of nodal curves.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}} (c : X ⟶ Y) (h : X ⟶ Z)

/-- A map is constant on the fibres of `c` exactly when its restriction to each geometric
fibre, formed with an algebraic closure of the residue field, has at most one image point. -/
theorem factorsThrough_iff_subsingleton_range_geometricFiber :
    Function.FactorsThrough h c ↔ ∀ y : Y,
      (Set.range (pullback.fst c (Y.fromSpecAlgebraicClosure y) ≫ h)).Subsingleton := by
  have hr (y : Y) :
      Set.range (pullback.fst c (Y.fromSpecAlgebraicClosure y) ≫ h) =
        h '' (c ⁻¹' {y}) := by
    rw [comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst,
      Scheme.range_fromSpecAlgebraicClosure]
  simp_rw [hr]
  constructor
  · intro hh y
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hh (ha.trans hb.symm)
  · intro hh a b hab
    exact hh (c a) ⟨a, rfl, rfl⟩ ⟨b, hab.symm, rfl⟩

/-- Constancy on fibres can equivalently be tested after pullback along all algebraically
closed field-valued points. Only the underlying image in `Z` is required to have at most one
point. -/
theorem factorsThrough_iff_forall_isAlgClosed_subsingleton_range :
    Function.FactorsThrough h c ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ Y),
        (Set.range (pullback.fst c y ≫ h)).Subsingleton := by
  constructor
  · intro hh K _ _ y
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    apply hh
    have he := congrArg (fun f : pullback c y ⟶ Y ↦ f a) (pullback.condition (f := c) (g := y))
    have he' := congrArg (fun f : pullback c y ⟶ Y ↦ f b) (pullback.condition (f := c) (g := y))
    exact he.trans ((congrArg y (Subsingleton.elim _ _)).trans he'.symm)
  · intro hh
    exact (c.factorsThrough_iff_subsingleton_range_geometricFiber h).mpr
      fun y ↦ hh _ (Y.fromSpecAlgebraicClosure y)

variable [hclosed : UniversallyClosed c] [hsurj : Surjective c]
  (hc : ∀ U, IsIso (c.app U))

include hc hclosed hsurj

/-- **Geometric-fibre criterion for contraction descent.** For a universally closed surjective
`c` with `𝒪_Y ≅ c_*𝒪_X`, a morphism descends uniquely exactly when it is constant on each
geometric fibre. Proper contractions are a special case. -/
theorem existsUnique_comp_eq_iff_subsingleton_range_geometricFiber :
    (∃! g : Y ⟶ Z, c ≫ g = h) ↔ ∀ y : Y,
      (Set.range (pullback.fst c (Y.fromSpecAlgebraicClosure y) ≫ h)).Subsingleton := by
  rw [← c.factorsThrough_iff_subsingleton_range_geometricFiber h]
  constructor
  · rintro ⟨g, rfl, -⟩ a b hab
    exact congrArg g hab
  · intro hh
    exact c.existsUnique_comp_eq_of_universallyClosed hc h hh

/-- **Contraction descent over a base.** A morphism over `S` constant on every geometric fibre
of a universally closed surjective contraction factors uniquely as a morphism over `S`.
The structure-sheaf isomorphism is required only for this contraction, not universally. -/
theorem existsUnique_comp_eq_over_of_subsingleton_range_geometricFiber
    {S : Scheme.{u}} (p : Y ⟶ S) (q : Z ⟶ S) (e : h ≫ q = c ≫ p)
    (hh : ∀ y : Y,
      (Set.range (pullback.fst c (Y.fromSpecAlgebraicClosure y) ≫ h)).Subsingleton) :
    ∃! g : Y ⟶ Z, c ≫ g = h ∧ g ≫ q = p := by
  have hf := (c.factorsThrough_iff_subsingleton_range_geometricFiber h).mpr hh
  let hquot := c.isClosedMap.isQuotientMap c.continuous c.surjective
  refine ⟨c.descOfIsQuotientMap hquot hc h hf,
    ⟨c.comp_descOfIsQuotientMap hquot hc h hf,
      c.descOfIsQuotientMap_comp_eq hquot hc h hf e⟩, ?_⟩
  exact fun _ hg ↦ c.eq_descOfIsQuotientMap hquot hc h hf hg.1

end AlgebraicGeometry.Scheme.Hom
