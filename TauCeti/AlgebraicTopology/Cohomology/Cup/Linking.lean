/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.GroupTheory.Torsion
public import TauCeti.Algebra.Category.ModuleCat.RatAddCircle
public import TauCeti.AlgebraicTopology.Cohomology.Bockstein
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker

/-!
# The torsion linking pairing of integral cohomology

Let `X` be a space, write `Hⁿ(X; ℤ)` for its integral cohomology `TopCat.integralCohomology` and
`Hⁿ(X; ℚ/ℤ)` for its cohomology with values in the rational circle `ℚ/ℤ = AddCircle (1 : ℚ)`, and
let `β : Hᵖ(X; ℚ/ℤ) ⟶ Hᵖ⁺¹(X; ℤ)` be the Bockstein homomorphism of the coefficient sequence
`0 ⟶ ℤ ⟶ ℚ ⟶ ℚ/ℤ ⟶ 0` (`ModuleCat.ratAddCircleShortComplex`). For an integral homology class
`z ∈ Hₙ(X; ℤ)` and `p + q = n`, the **torsion linking pairing** against `z`
(`TopCat.torsionLinkingPairing`) is the biadditive map

`Tors Hᵖ⁺¹(X; ℤ) × Tors H^q(X; ℤ) ⟶ ℚ/ℤ`,   `(α, b) ↦ ⟨u ⌣ b, z⟩`   for any `u` with `β u = α`,

where `u ⌣ b ∈ Hⁿ(X; ℚ/ℤ)` is the cup product along the action of `ℤ` on `ℚ/ℤ` and `⟨-, z⟩` is the
Kronecker pairing. For a closed connected oriented `n`-manifold and `z` its fundamental class, this
is the Bockstein description of the linking form on the torsion of its homology, transported along
Poincaré duality (Conway–Friedl–Herrmann, Section 2).

Two facts make this well defined, both resting on the fact that `Hᵏ(X; ℚ)` has no torsion, since
multiplication by a nonzero integer is bijective on it
(`TopCat.eq_zero_of_isOfFinAddOrder_singularCohomology_rat`):

* every torsion class `α` is a Bockstein: its image in `Hᵖ⁺¹(X; ℚ)` is torsion, hence zero, so
  `α` lies in the image of `β` by exactness of the coefficient sequence
  (`TopCat.exists_singularCohomologyBockstein_eq_of_mem_torsion`);
* the product `u ⌣ b` does not depend on the choice of `u` when `b` is torsion: two choices differ
  by the reduction of a rational class `r`, and `r ⌣ b ∈ Hⁿ(X; ℚ)` is torsion, hence zero
  (`TopCat.singularCup_eq_of_singularCohomologyBockstein_eq`).

The pairing is natural in the space (`TopCat.torsionLinkingPairing_naturality`).

## Main definitions and results

* `TopCat.torsionLinkingPairing`: the torsion linking pairing against an integral homology class,
  with `TopCat.torsionLinkingPairing_apply` its value through any Bockstein lift.
* `TopCat.exists_singularCohomologyBockstein_eq_of_mem_torsion`: a torsion class of integral
  cohomology is the Bockstein of a class with values in `ℚ/ℤ`.
* `TopCat.singularCup_eq_of_singularCohomologyBockstein_eq`: classes with values in `ℚ/ℤ` with the
  same Bockstein have the same cup product with a torsion integral class.
* `TopCat.torsionLinkingPairing_naturality`: naturality along continuous maps.

## References

* A. Conway, S. Friedl and G. Herrmann, *Linking forms revisited*, Pure Appl. Math. Q. 12 (2016),
  Section 2.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.E (Bockstein homomorphisms).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology TauCeti ModuleCat

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace TopCat

variable {X : TopCat.{0}}

/-- **Torsion integral classes are Bocksteins**: a torsion class `α ∈ Hᵖ⁺¹(X; ℤ)` is the Bockstein
`β u` of a class `u ∈ Hᵖ(X; ℚ/ℤ)`, for the coefficient sequence `0 ⟶ ℤ ⟶ ℚ ⟶ ℚ/ℤ ⟶ 0`. -/
theorem exists_singularCohomologyBockstein_eq_of_mem_torsion {p : ℕ}
    {α : X.integralCohomology (p + 1)}
    (hα : α ∈ AddCommGroup.torsion (X.integralCohomology (p + 1))) :
    ∃ u : X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        (ModuleCat.of ℤ (AddCircle (1 : ℚ))) p,
      X.singularCohomologyBockstein (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        ratAddCircleShortComplex_shortExact p (p + 1) rfl u = α := by
  -- The image of `α` in `Hᵖ⁺¹(X; ℚ)` is torsion, hence zero.
  exact (ShortComplex.moduleCat_exact_iff _).1 (X.singularCohomology_exact_coefficient₁
    (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ ratAddCircleShortComplex_shortExact p (p + 1) rfl) α <|
    eq_zero_of_isOfFinAddOrder_singularCohomology_rat <| (AddCommGroup.mem_torsion _).1 <|
      AddSubgroup.mem_comap.1 <|
        AddCommGroup.le_comap_torsion (ModuleCat.Hom.hom _).toAddMonoidHom hα

/-- **The cup product with a torsion class only sees the Bockstein**: if `u, u' ∈ Hᵖ(X; ℚ/ℤ)` have
the same Bockstein in `Hᵖ⁺¹(X; ℤ)` and `b ∈ H^q(X; ℤ)` is torsion, then `u ⌣ b = u' ⌣ b` in
`Hⁿ(X; ℚ/ℤ)`, `p + q = n`, the cup products being taken along the action of `ℤ` on `ℚ/ℤ`. -/
theorem singularCup_eq_of_singularCohomologyBockstein_eq {p q n : ℕ} (h : p + q = n)
    {u u' : X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (AddCircle (1 : ℚ))) p}
    (hu : X.singularCohomologyBockstein (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        ratAddCircleShortComplex_shortExact p (p + 1) rfl u =
      X.singularCohomologyBockstein (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        ratAddCircleShortComplex_shortExact p (p + 1) rfl u')
    {b : X.integralCohomology q} (hb : b ∈ AddCommGroup.torsion (X.integralCohomology q)) :
    X.singularCup ℤ integralCoeffComul (ρ_ (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).hom p q n h u b =
      X.singularCup ℤ integralCoeffComul (ρ_ (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).hom p q n h u'
        b := by
  -- `u - u'` is the reduction of a rational class `r`, by exactness of the coefficient sequence.
  obtain ⟨r, hr⟩ := (ShortComplex.moduleCat_exact_iff _).1 (X.singularCohomology_exact_coefficient₃
    (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ ratAddCircleShortComplex_shortExact p (p + 1) rfl) (u - u')
    (by rw [map_sub, hu, sub_self])
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub]
  dsimp only at hr
  -- The reduction of `r` cupped with `b` is the reduction of the rational class `r ⌣ b`.
  rw [← hr, singularCup_homologyMap_linearYonedaObjMap_left,
    MonoidalCategory.rightUnitor_naturality, ← homologyMap_linearYonedaObjMap_singularCup]
  suffices hz : X.singularCup ℤ integralCoeffComul (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h r b = 0 by
    rw [hz, map_zero]
  -- `r ⌣ b` is torsion, hence zero.
  exact eq_zero_of_isOfFinAddOrder_singularCohomology_rat <| (AddCommGroup.mem_torsion _).1 <|
    AddSubgroup.mem_comap.1 <| AddCommGroup.le_comap_torsion (X.singularCup ℤ integralCoeffComul
      (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h r).toAddMonoidHom hb

/-- The value `⟨u ⌣ b, z⟩` of the torsion linking pairing, for the chosen Bockstein lift `u` of
`α`. -/
private def torsionLinkingValue (p q n : ℕ) (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X)
    (α : AddCommGroup.torsion (X.integralCohomology (p + 1))) (b : X.integralCohomology q) :
    AddCircle (1 : ℚ) :=
  (X.singularKronecker ℤ n (X.singularCup ℤ integralCoeffComul
    (ρ_ (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).hom p q n h
    (exists_singularCohomologyBockstein_eq_of_mem_torsion α.property).choose b)).hom z

/-- The value of the torsion linking pairing can be computed with any Bockstein lift. -/
private lemma torsionLinkingValue_eq (p q n : ℕ) (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X)
    (α : AddCommGroup.torsion (X.integralCohomology (p + 1))) {b : X.integralCohomology q}
    (hb : b ∈ AddCommGroup.torsion (X.integralCohomology q))
    (u : X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (AddCircle (1 : ℚ))) p)
    (hu : X.singularCohomologyBockstein (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      ratAddCircleShortComplex_shortExact p (p + 1) rfl u = α) :
    torsionLinkingValue p q n h z α b =
      (X.singularKronecker ℤ n (X.singularCup ℤ integralCoeffComul
        (ρ_ (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).hom p q n h u b)).hom z := by
  rw [torsionLinkingValue, singularCup_eq_of_singularCohomologyBockstein_eq h (u' := u) _ hb]
  rw [(exists_singularCohomologyBockstein_eq_of_mem_torsion α.property).choose_spec, hu]

/-- **The torsion linking pairing** of the integral cohomology of `X` against an integral homology
class `z ∈ Hₙ(X; ℤ)`, for `p + q = n`: the biadditive map
`Tors Hᵖ⁺¹(X; ℤ) × Tors H^q(X; ℤ) ⟶ ℚ/ℤ` sending `(α, b)` to `⟨u ⌣ b, z⟩` for any
`u ∈ Hᵖ(X; ℚ/ℤ)` whose Bockstein is `α` (`TopCat.torsionLinkingPairing_apply`). -/
def torsionLinkingPairing (p q n : ℕ) (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X) :
    AddCommGroup.torsion (X.integralCohomology (p + 1)) →+
      AddCommGroup.torsion (X.integralCohomology q) →+ AddCircle (1 : ℚ) :=
  AddMonoidHom.mk'
    (fun α ↦ AddMonoidHom.mk' (fun b ↦ torsionLinkingValue p q n h z α b) (fun b b' ↦ by
      rw [torsionLinkingValue, torsionLinkingValue, torsionLinkingValue]
      simp only [AddSubgroup.coe_add, map_add, ModuleCat.hom_add, LinearMap.add_apply]))
    (fun α α' ↦ AddMonoidHom.ext fun b ↦ by
      -- Compute all three values with the sum of the chosen lifts of `α` and `α'`.
      obtain ⟨u, hu⟩ := exists_singularCohomologyBockstein_eq_of_mem_torsion α.property
      obtain ⟨u', hu'⟩ := exists_singularCohomologyBockstein_eq_of_mem_torsion α'.property
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [torsionLinkingValue_eq p q n h z _ b.property (u + u')
          (by rw [map_add, hu, hu', AddSubgroup.coe_add]),
        torsionLinkingValue_eq p q n h z α b.property u hu,
        torsionLinkingValue_eq p q n h z α' b.property u' hu']
      simp only [map_add, ModuleCat.hom_add, LinearMap.add_apply])

/-- **The value of the torsion linking pairing**: if `u ∈ Hᵖ(X; ℚ/ℤ)` has Bockstein `α`, then the
torsion linking pairing of `α` and `b` against `z` is `⟨u ⌣ b, z⟩`. -/
theorem torsionLinkingPairing_apply (p q n : ℕ) (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X)
    (α : AddCommGroup.torsion (X.integralCohomology (p + 1)))
    (b : AddCommGroup.torsion (X.integralCohomology q))
    (u : X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (AddCircle (1 : ℚ))) p)
    (hu : X.singularCohomologyBockstein (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      ratAddCircleShortComplex_shortExact p (p + 1) rfl u = α) :
    X.torsionLinkingPairing p q n h z α b =
      (X.singularKronecker ℤ n (X.singularCup ℤ integralCoeffComul
        (ρ_ (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).hom p q n h u b)).hom z :=
  torsionLinkingValue_eq p q n h z α b.property u hu

/-- **Naturality of the torsion linking pairing**: for a continuous map `f : X ⟶ Y`, the pairing
of the pullbacks `f^* α` and `f^* b` against `z` is the pairing of `α` and `b` against `f_* z`. -/
theorem torsionLinkingPairing_naturality {Y : TopCat.{0}} (f : X ⟶ Y) (p q n : ℕ) (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X)
    (α : AddCommGroup.torsion (Y.integralCohomology (p + 1)))
    (b : AddCommGroup.torsion (Y.integralCohomology q)) :
    X.torsionLinkingPairing p q n h z
        ⟨TopCat.singularCohomologyMap f (p + 1) α, AddSubgroup.mem_comap.1 <|
          AddCommGroup.le_comap_torsion (TopCat.singularCohomologyMap f (p + 1)).hom.toAddMonoidHom
            α.property⟩
        ⟨TopCat.singularCohomologyMap f q b, AddSubgroup.mem_comap.1 <|
          AddCommGroup.le_comap_torsion (TopCat.singularCohomologyMap f q).hom.toAddMonoidHom
            b.property⟩ =
      Y.torsionLinkingPairing p q n h
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map f z) α b := by
  obtain ⟨u, hu⟩ := exists_singularCohomologyBockstein_eq_of_mem_torsion α.property
  rw [Y.torsionLinkingPairing_apply p q n h _ α b u hu,
    X.torsionLinkingPairing_apply p q n h z _ _ (TopCat.singularCohomologyMap f p u) (by
      rw [← ConcreteCategory.comp_apply, ← singularCohomologyBockstein_naturality
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ ratAddCircleShortComplex_shortExact f p (p + 1) rfl,
        ConcreteCategory.comp_apply, hu])]
  -- Pull the cup product back along `f`, then push the homology class forward.
  refine (congrArg (fun c : X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (AddCircle (1 : ℚ))) n ↦ (X.singularKronecker ℤ n c).hom z)
    (singularCup_naturality f ℤ integralCoeffComul (ρ_ (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).hom
      p q n h u (b : Y.integralCohomology q))).trans ?_
  rw [singularKronecker_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]

end TopCat
