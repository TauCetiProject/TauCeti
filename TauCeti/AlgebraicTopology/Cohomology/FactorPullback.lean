/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Slant
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Classes on a product pulled back from a factor

Let `X` be a path-connected space whose singular homology `Hₚ(X; k)` is projective in every
degree, over a commutative ring `k`, for instance the circle `S¹` over `ℤ`. For every space `Y`, a
class `φ ∈ Hⁿ(X × Y; k, M)` is pulled back along the projection `pr₂ : X × Y ⟶ Y` exactly when its
slant products `φ / x ∈ H^q(Y; k, M)` by all homology classes `x ∈ Hₚ(X; k)` of positive degree
`p` vanish (`TopCat.exists_singularCohomologyMap_snd_eq_iff`). Indeed a pulled-back class has no
such slant products (`TopCat.singularSlant_singularCohomologyMap_snd_eq_zero`); conversely, if
`b` is the slant product of `φ` by the class of a point, `φ - pr₂^* b` has vanishing slant
products by `H₀(X; k) = k [pt]` as well, and slant products by the homology of `X` detect the
cohomology of `X × Y` (`TopCat.eq_zero_of_forall_singularSlant_eq_zero`). For `X = S¹` the slant
product by the fundamental class is the coordinate of `φ` in the summand
`H¹(S¹) ⊗ Hⁿ⁻¹(Y) ≅ Hⁿ⁻¹(Y)` of the Künneth decomposition (`TopCat.singularCohomologyKunnethIso`),
the quotient of `Hⁿ(S¹ × Y)` by the pulled-back classes.

Over any commutative ring, a monomorphism of coefficients `g : M ⟶ N` is injective on
`H⁰(Y; k, -)` and on `H¹(Y; k, -)` for every space `Y`
(`TopCat.singularCohomology_coefficient_injective_zero`,
`TopCat.singularCohomology_coefficient_injective_of_projective_homology_lt`), since `H₀(Y; k)` is
free. The slant
products of a class of degree `n ≤ 2` by classes of positive degree lie in these groups, and
slant products commute with `g` (`TopCat.singularSlant_homologyMap_linearYonedaObjMap`). Hence in
degrees `n ≤ 2` a class on `X × Y` whose image under `g` is pulled back from `Y` is itself pulled
back from `Y` (`TopCat.exists_singularCohomologyMap_snd_eq_of_coefficient`). For `X = S¹`, `n = 2`
and `g : ℤ ⟶ ℝ`: an integral class `l ∈ H²(S¹ × Y; ℤ)` whose real image is pulled back from `Y` is
the pullback of an integral class of `Y`, torsion included. The bound `n ≤ 2` is sharp: for a
nonzero torsion class `t ∈ H²(Y; ℤ)` and the generator `u ∈ H¹(S¹; ℤ)`, the cross product
`u × t ∈ H³(S¹ × Y; ℤ)` has real image zero but slant product `t` by the fundamental class of
`S¹`, so it is not pulled back from `Y`.

On a product `S¹ × Y` this turns a real statement about a first Chern class, for instance that
the curvature form of a connection is pulled back from `Y`, into the integral statement that the
Chern class itself, torsion included, is pulled back from `Y`.

## Main results

* `TopCat.exists_singularCohomologyMap_snd_eq_iff`: a class on `X × Y` is pulled back from `Y`
  exactly when its slant products by the positive-degree homology of `X` vanish.
* `TopCat.exists_singularCohomologyMap_snd_eq_of_coefficient`: in degrees `n ≤ 2`, a class whose
  image under an injective coefficient map is pulled back from `Y` is pulled back from `Y`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 and Section 3.B (the Künneth formula), Section 3.1 (universal coefficients).
* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TopCat

variable {k : Type w} [CommRing k] (X Y : TopCat.{w}) (M : ModuleCat.{w} k)

/-- **Classes pulled back from the second factor**: let `X` be path-connected with projective
singular homology `Hₚ(X; k)` in every degree. A class `φ ∈ Hⁿ(X × Y; k, M)` is the pullback
`pr₂^* b` of a class `b` of `Y` if and only if its slant products `φ / x` by all classes
`x ∈ Hₚ(X; k)` of positive degree `p` vanish. There is no hypothesis on `Y`. -/
theorem exists_singularCohomologyMap_snd_eq_iff [PathConnectedSpace X]
    [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)] {n : ℕ}
    (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k M n) :
    (∃ b, TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b = φ) ↔
      ∀ p q (h : p + q = n), p ≠ 0 → ∀ x, singularSlant k M X Y (𝟙 _) p q n h x φ = 0 := by
  constructor
  · rintro ⟨b, rfl⟩ p q h hp x
    exact singularSlant_singularCohomologyMap_snd_eq_zero M X Y _ p q n h hp x b
  intro hφ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  -- the class `[x₀] ∈ H₀(X; k)` of a point spans `H₀(X; k)`
  let x₁ := TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)
  have hx (x : ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
      x = (X.singularHomology₀ε (𝟙_ (ModuleCat.{w} k)) x : k) • x₁ :=
    TauCeti.singularHomology₀_eq_smul_singularHomology₀Section x₀ x
  let z := ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).liftCycles
    ((toSSet.obj X).ιChainComplex (toSSetObj₀Equiv.symm x₀)) 0 (by simp) (by simp) (1 : k)
  have hx₁ : x₁ = ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ 0 z := by
    change TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k) = _
    rw [TauCeti.singularHomology₀Section_def, SSet.ιHomology₀_def]
    -- the class of the vertex is the composite `liftCycles ≫ homologyπ` applied to `1`
    rfl
  -- `b` is the slant product `φ / [x₀]`, with its coefficients changed along the unitor
  -- `e : C(Y; k ⊗ k) ≅ C(Y; k)`
  let e := ((SSet.chainComplexFunctor _).mapIso (λ_ (𝟙_ (ModuleCat.{w} k)))).app (toSSet.obj Y)
  let β := singularSlant k M X Y (𝟙 _) 0 n n (zero_add n) x₁ φ
  let b := homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map e.hom.op) n β
  have hb : singularSlant k M X Y (𝟙 _) 0 n n (zero_add n) x₁
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b) = β := by
    rw [hx₁, singularSlant_homologyπ_singularCohomologyMap_snd M X Y (𝟙 _) n z
      (toSSetObj₀Equiv.symm x₀) (1 : k) (ConcreteCategory.congr_hom
        (HomologicalComplex.liftCycles_i ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k)))
          ((toSSet.obj X).ιChainComplex (toSSetObj₀Equiv.symm x₀)) 0 (by simp) (by simp)) (1 : k))
      (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (fun s ↦ by simp [ModuleCat.MonoidalCategory.leftUnitor_inv_apply]) b]
    exact Iso.hom_inv_id_apply ((homologyFunctor _ _ n).mapIso
      ((TauCeti.ChainComplex.linearYonedaFunctor k M).mapIso e.op)) β
  -- `φ - pr₂^* b` has no slant products, so it vanishes
  refine ⟨b, (sub_eq_zero.1 ?_).symm⟩
  refine eq_zero_of_forall_singularSlant_eq_zero M X Y _ fun p q h x ↦ ?_
  rcases p with _ | p
  · obtain rfl : q = n := by omega
    rw [hx x, map_smul, LinearMap.smul_apply, map_sub, hb, sub_self, smul_zero]
  · rw [map_sub, hφ _ _ h p.succ_ne_zero, zero_sub, neg_eq_zero]
    exact singularSlant_singularCohomologyMap_snd_eq_zero M X Y _ _ _ n h p.succ_ne_zero x b

/-- **Pulled-back classes in degree at most two descend along injective coefficient maps**: over
a commutative ring `k`, for instance `ℤ`, let `X` be path-connected with projective singular
homology `Hₚ(X; k)`, for instance `X = S¹`, and let `g : M ⟶ N` be a monomorphism of coefficient
modules. If `n ≤ 2` and the image of `φ ∈ Hⁿ(X × Y; k, M)` under `g` is pulled back from `Y`, then
so is `φ`. For `X = S¹`, `n = 2` and `g : ℤ ⟶ ℝ`: an integral class on `S¹ × Y` whose real image is
pulled back from `Y` is the pullback of an integral class of `Y`. The slant products of `φ` by
classes of positive degree lie in `H⁰(Y; k, M)` and `H¹(Y; k, M)`, on which `g` is injective since
`H₀(Y; k)` is free; in degree `3` torsion classes of `H²(Y; k, M)` give counterexamples. -/
theorem exists_singularCohomologyMap_snd_eq_of_coefficient [PathConnectedSpace X]
    [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)] {N : ModuleCat.{w} k} (g : M ⟶ N) [Mono g] {n : ℕ}
    (hn : n ≤ 2)
    (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k M n)
    (hφ : ∃ b, TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b =
      homologyMap (((toSSet.obj (X ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n φ) :
    ∃ b, TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b = φ := by
  have hY : ∀ j < 1, Projective (((singularHomologyFunctor (ModuleCat.{w} k) j).obj
      (𝟙_ (ModuleCat.{w} k))).obj Y) := fun j hj ↦ by
    obtain rfl : j = 0 := by omega
    exact Projective.of_iso (Y.singularHomology₀Iso _).symm inferInstance
  rw [exists_singularCohomologyMap_snd_eq_iff] at hφ ⊢
  intro p q h hp x
  have hgx := hφ p q h hp x
  rw [singularSlant_homologyMap_linearYonedaObjMap] at hgx
  -- the slant product lies in degree `q = n - p ≤ 1`
  rcases q with _ | _ | q
  · exact singularCohomology_coefficient_injective_zero Y k g (hgx.trans (map_zero _).symm)
  · exact singularCohomology_coefficient_injective_of_projective_homology_lt Y (𝟙_ _) 1 hY g
      (hgx.trans (map_zero _).symm)
  · omega

end TopCat
