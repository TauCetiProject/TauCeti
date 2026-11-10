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

Over a hereditary ring such as `ℤ`, a monomorphism of coefficients `g : M ⟶ N` is injective on
`H⁰(Y; k, -)` and on `H¹(Y; k, -)` for every space `Y`
(`TopCat.singularCohomology_coefficient_injective_zero`,
`TopCat.singularCohomology_coefficient_injective_succ`), since `H₀(Y; k)` is free. The slant
products of a class of degree `n ≤ 2` by classes of positive degree lie in these groups, and
slant products commute with `g` (`TopCat.singularSlant_coefficient_naturality`). Hence in degrees
`n ≤ 2` a class on `X × Y` whose image under `g` is pulled back from `Y` is itself pulled back from
`Y` (`TopCat.exists_singularCohomologyMap_snd_eq_of_coefficient`). For `X = S¹`, `n = 2` and
`g : ℤ ⟶ ℝ`: an integral class `l ∈ H²(S¹ × Y; ℤ)` whose real image is pulled back from `Y` is
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

/-- On a path-connected space, the zeroth homology `H₀(X; k)` is spanned by the class of the
singular `0`-cycle of any point `x₀`, with coefficient `1`: every class `x` is `ε(x) • [x₀]` for
the augmentation `ε`. -/
private lemma exists_cycles_zero_forall_eq_smul [PathConnectedSpace X] (x₀ : X) :
    ∃ z : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).cycles 0,
      ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).iCycles 0 z =
        (toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{w} k)) (toSSetObj₀Equiv.symm x₀) 1 ∧
      ∃ x₁ : ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj (𝟙_ (ModuleCat.{w} k))).obj X,
        x₁ = ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ 0 z ∧
        ∀ x, x = (X.singularHomology₀ε (𝟙_ (ModuleCat.{w} k)) x : k) • x₁ := by
  let C := (toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))
  let z := C.liftCycles ((toSSet.obj X).ιChainComplex (toSSetObj₀Equiv.symm x₀)) 0
    (by simp) (by simp) (1 : k)
  let x₁ : ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj (𝟙_ (ModuleCat.{w} k))).obj X :=
    C.homologyπ 0 z
  refine ⟨z, (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (C.liftCycles_i _ _ _ _) _), x₁, rfl, fun x ↦ ?_⟩
  -- the augmentation is injective on a path-connected space and sends `[x₀]` to `1`
  apply (ConcreteCategory.bijective_of_isIso (X.singularHomology₀ε (𝟙_ (ModuleCat.{w} k)))).1
  rw [(X.singularHomology₀ε (𝟙_ (ModuleCat.{w} k))).hom.map_smul]
  refine (mul_one _).symm.trans (congrArg (_ * ·) ?_)
  exact (ConcreteCategory.congr_hom (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
    (toSSet.obj X) (𝟙_ (ModuleCat.{w} k)) (toSSetObj₀Equiv.symm x₀)) (1 : k)).symm

/-- Changing the coefficients of `β ∈ Hⁿ(Y; k, M)` along `k ⊗ k ⟶ k` and then back along
`k ⟶ k ⊗ k`, the two halves of the unitor `k ⊗ k ≅ k`, returns `β`. -/
private lemma homologyMap_leftUnitor_inv_homologyMap_leftUnitor_hom {n : ℕ}
    (β : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
      (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app
        (toSSet.obj Y)).op) n
      (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
        (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app
          (toSSet.obj Y)).op) n β) = β := by
  have hc : ((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app
      (toSSet.obj Y) ≫ ((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app
        (toSSet.obj Y) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id]
    simp
  have hcomp := ConcreteCategory.congr_hom (homologyMap_comp
    ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
      (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (toSSet.obj Y)).op)
    ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
      (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app
        (toSSet.obj Y)).op) n) β
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, hc, op_id, CategoryTheory.Functor.map_id,
    homologyMap_id] at hcomp
  exact hcomp.symm

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
  obtain ⟨z, hz, x₁, hx₁, hx⟩ := exists_cycles_zero_forall_eq_smul (k := k) X x₀
  -- `b` is the slant product `φ / [x₀]`, with its coefficients changed along `k ⊗ k ⟶ k`
  let β := singularSlant k M X Y (𝟙 _) 0 n n (zero_add n)
    (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ 0 z) φ
  let b := homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
    (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app
      (toSSet.obj Y)).op) n β
  have hb : singularSlant k M X Y (𝟙 _) 0 n n (zero_add n)
      (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ 0 z)
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b) = β :=
    (singularSlant_homologyπ_singularCohomologyMap_snd M X Y (𝟙 _) n z
      (toSSetObj₀Equiv.symm x₀) (1 : k) hz (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (fun s ↦ by simp [ModuleCat.MonoidalCategory.leftUnitor_inv_apply]) b).trans
      (homologyMap_leftUnitor_inv_homologyMap_leftUnitor_hom Y M β)
  -- `φ - pr₂^* b` has no slant products, so it vanishes
  refine ⟨b, (sub_eq_zero.1 ?_).symm⟩
  refine eq_zero_of_forall_singularSlant_eq_zero M X Y _ fun p q h x ↦ ?_
  rcases p with _ | p
  · obtain rfl : q = n := by omega
    rw [hx x, map_smul, LinearMap.smul_apply, map_sub, hx₁, hb, sub_self, smul_zero]
  · rw [map_sub, hφ _ _ h p.succ_ne_zero, zero_sub, neg_eq_zero]
    exact singularSlant_singularCohomologyMap_snd_eq_zero M X Y _ _ _ n h p.succ_ne_zero x b

/-- **Pulled-back classes in degree at most two descend along injective coefficient maps**: over
a hereditary commutative ring `k` such as `ℤ`, let `X` be path-connected with projective singular
homology `Hₚ(X; k)`, for instance `X = S¹`, and let `g : M ⟶ N` be a monomorphism of coefficient
modules. If `n ≤ 2` and the image of `φ ∈ Hⁿ(X × Y; k, M)` under `g` is pulled back from `Y`, then
so is `φ`. For `X = S¹`, `n = 2` and `g : ℤ ⟶ ℝ`: an integral class on `S¹ × Y` whose real image is
pulled back from `Y` is the pullback of an integral class of `Y`. The slant products of `φ` by
classes of positive degree lie in `H⁰(Y; k, M)` and `H¹(Y; k, M)`, on which `g` is injective since
`H₀(Y; k)` is free; in degree `3` torsion classes of `H²(Y; k, M)` give counterexamples. -/
theorem exists_singularCohomologyMap_snd_eq_of_coefficient
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] [PathConnectedSpace X]
    [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)] {N : ModuleCat.{w} k} (g : M ⟶ N) [Mono g] {n : ℕ}
    (hn : n ≤ 2)
    (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k M n)
    (hφ : ∃ b, TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b =
      homologyMap (((toSSet.obj (X ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n φ) :
    ∃ b, TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b = φ := by
  have : Projective (((singularHomologyFunctor (ModuleCat.{w} k) 0).obj
      (𝟙_ (ModuleCat.{w} k))).obj Y) :=
    Projective.of_iso (Y.singularHomology₀Iso _).symm inferInstance
  rw [exists_singularCohomologyMap_snd_eq_iff] at hφ ⊢
  intro p q h hp x
  have hgx := hφ p q h hp x
  rw [singularSlant_coefficient_naturality] at hgx
  -- the slant product lies in degree `q = n - p ≤ 1`
  rcases q with _ | _ | q
  · exact singularCohomology_coefficient_injective_zero Y k g (hgx.trans (map_zero _).symm)
  · exact singularCohomology_coefficient_injective_succ Y (𝟙_ _) 0 g
      (hgx.trans (map_zero _).symm)
  · omega

end TopCat
