/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Values
import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Data.ZMod.Four

/-!
# Mod `2` cup squares of degree-one classes

For a class `w ∈ H¹(X; 𝔽₂)` the cup square `w ⌣ w ∈ H²(X; 𝔽₂)` is the obstruction to lifting `w`
to a class with coefficients in `ℤ/4`: it is the Bockstein image `Sq¹ w` of `w` for the extension
`0 ⟶ ℤ/2 ⟶ ℤ/4 ⟶ ℤ/2 ⟶ 0`. This file proves the half of this statement needed to detect nonzero
squares, at the level of cochains. If `φ` is a mod `2` cocycle with values `a` on the singular
`1`-simplices and `φ ⌣ φ = δψ`, where `ψ` has values `b`, then the `ℤ/4`-valued cochain with
values `ι a + 2 ι b` is a cocycle reducing to `φ` modulo `2`; here `ι` lifts residues modulo `2`
to `{0, 1} ⊆ ℤ/4` (`ZMod.cast`). On a `2`-simplex with edges `e₀₁, e₀₂, e₁₂` this is the carry
identity `ι a(e₀₁) + ι a(e₁₂) = ι a(e₀₂) + 2 ι (a(e₀₁) a(e₁₂))` in `ℤ/4` for a mod `2` cocycle
`a` (`ZMod.cast_add_two_mul_cast_sub_mul`), the identity which, for group cohomology, turns a
character to `𝔽₂` with vanishing cup square into a character to `ℤ/4`.

A degree-one class with values in `ℤ/4` evaluates on integral homology through the Kronecker map,
which is injective in degree one for every space, since `H₀(X; ℤ)` is free. If every class of
`H₁(X; ℤ)` has order at most `2`, the values of a `ℤ/4`-class on `H₁(X; ℤ)` are killed by `2`, so
they lie in `{0, 2}` and reduce to `0` modulo `2`: the reduction `H¹(X; ℤ/4) ⟶ H¹(X; ℤ/2)` is zero.
Combining the two, on such a space a class `w ∈ H¹(X; 𝔽₂)` with `w ⌣ w = 0` vanishes
(`TopCat.eq_zero_of_singularCup_self_eq_zero`). For real projective space `RPᴺ`, `N ≥ 2`, where
`H₁(RPᴺ; ℤ) = ℤ/2`, this says that the generator of `H¹(RPᴺ; 𝔽₂)` has nonzero square.

The mod `2` cohomology here is that of `TauCeti.lsCupLength`: chain and cochain coefficients
`𝟙_ (ModuleCat (ZMod 2))`, with the unitors as diagonal and multiplication. The `ℤ/4` and the
integral computations use integral chains. The two are compared through the values of cochains on
singular simplices (`TauCeti.cochainValuesEquiv`), which both describe; on values, the mod `2` cup
square is computed by `TopCat.cochainValuesEquiv_cupCochain_one_one`.

## Main results

* `TopCat.eq_zero_of_singularCup_self_eq_zero`: if every class of `H₁(X; ℤ)` is killed by `2`, a
  class of `H¹(X; 𝔽₂)` with zero square is zero.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.E (the Bockstein homomorphism) and Section 4.L, the identity `Sq¹ = β` and
  `Sq¹ w = w²` for `w` of degree one.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial TauCeti

universe w

namespace TopCat

/- Integral cochains are taken with the `ℤ`-linear structure `ModuleCat.instLinear` of
`ModuleCat ℤ`, the one the universal coefficient theorem is stated with for a general ring, rather
than the structure `Linear.preadditiveIntLinear` of an arbitrary preadditive category. -/
attribute [local instance high] ModuleCat.instLinear

/-- The lifts `ι a + 2 ι x` to `ℤ/4` of the values of a mod `2` cocycle `a` and of a mod `2`
cochain `x` with `δx = a ⌣ a` form a `ℤ/4`-cocycle, where `ι : ℤ/2 → ℤ/4` is `ZMod.cast`: on a
`2`-simplex, `a + b + c = 0` and `c a = x + y + z` for the values on its faces `δ₀, δ₁, δ₂` give
`(ι a + 2 ι x) - (ι b + 2 ι y) + (ι c + 2 ι z) = 0`. This is the carry identity
`ZMod.cast_add_two_mul_cast_sub_mul` for the edges `δ₂` and `δ₀`, whose sum is `δ₁`. -/
private lemma zmod_four_cocycle (a b c x y z : ZMod 2) (h₁ : a + b + c = 0)
    (h₂ : c * a = x + y + z) :
    ((ZMod.cast a : ZMod 4) + 2 * ZMod.cast x) - ((ZMod.cast b : ZMod 4) + 2 * ZMod.cast y) +
      ((ZMod.cast c : ZMod 4) + 2 * ZMod.cast z) = 0 := by
  have hb : b = c + a := by linear_combination (norm := (ring_nf; reduce_mod_char)) h₁
  have hy : y = z + x - c * a := by linear_combination (norm := (ring_nf; reduce_mod_char)) -h₂
  rw [hb, hy, ZMod.cast_add_two_mul_cast_sub_mul]
  ring

/-- The reduction `ℤ/4 ⟶ ℤ/2`, as a morphism of abelian groups. -/
private abbrev zmodFourToTwo : ModuleCat.of ℤ (ZMod 4) ⟶ ModuleCat.of ℤ (ZMod 2) :=
  ModuleCat.ofHom (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toIntLinearMap

/-- If every class of `H₁(X; ℤ)` is killed by `2`, the reduction `H¹(X; ℤ/4) ⟶ H¹(X; ℤ/2)` is
zero: through the Kronecker map, which is injective in degree one, a `ℤ/4`-class is a morphism
`H₁(X; ℤ) ⟶ ℤ/4` with values in `{0, 2}`. -/
private lemma homologyMap_zmodFourToTwo_eq_zero (X : TopCat.{0})
    (h2 : ∀ x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj X,
      2 • x = 0)
    (α : X.singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ (ZMod 4)) 1) :
    HomologicalComplex.homologyMap
      (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObjMap ℤ zmodFourToTwo) 1 α
        = 0 := by
  have hK := X.singularKronecker_bijective_of_projective_homology_lt (R := ModuleCat.of ℤ ℤ)
    (ModuleCat.of ℤ (ZMod 2)) 1 fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ _)
  refine hK.1 (((X.singularKronecker_coefficient_naturality ℤ zmodFourToTwo 1 α).trans ?_).trans
    (map_zero _).symm)
  ext x
  rw [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  have hx : 2 • X.singularKronecker ℤ 1 α x = 0 := by rw [← map_nsmul, h2, map_zero]
  generalize X.singularKronecker ℤ 1 α x = y at hx ⊢
  revert y
  decide

/-- The mod `2` cochain complex of `X`, with chain and cochain coefficients
`𝟙_ (ModuleCat (ZMod 2))`. Since `𝟙_ (ModuleCat (ZMod 2))` is `ModuleCat.of (ZMod 2) (ZMod 2)` by
definition, this complex unfolds to the `linearYonedaObj` of the chain complex of `toSSet.obj X`
with coefficients `ModuleCat.of (ZMod 2) (ZMod 2)`. The lemmas below use this unfolding to apply
`cochainValuesEquiv` (through `modTwoValues`) and `cochainValuesEquiv_linearYonedaObj_d_zero_one`
and `_d_one_two` to its cochains, as `TopCat.cochainValuesEquiv_cupCochain_one_one` does. -/
private abbrev modTwoCochains (X : TopCat.{0}) : CochainComplex (ModuleCat (ZMod 2)) ℕ :=
  X.singularCochainComplex (𝟙_ (ModuleCat.{0} (ZMod 2))) (ZMod 2) (𝟙_ (ModuleCat (ZMod 2)))

/-- The values of a mod `2` cochain on the singular simplices of `X`. -/
private abbrev modTwoValues (X : TopCat.{0}) (n : ℕ) :=
  cochainValuesEquiv (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) (toSSet.obj X) n

/-- A mod `2` cocycle has values summing to `0` over the faces of every `2`-simplex. -/
private lemma modTwoValues_cocycle (X : TopCat.{0}) (φ : (modTwoCochains X).cycles 1)
    (σ : (toSSet.obj X) _⦋2⦌) :
    modTwoValues X 1 ((modTwoCochains X).iCycles 1 φ) ((toSSet.obj X).δ 0 σ) +
        modTwoValues X 1 ((modTwoCochains X).iCycles 1 φ) ((toSSet.obj X).δ 1 σ) +
      modTwoValues X 1 ((modTwoCochains X).iCycles 1 φ) ((toSSet.obj X).δ 2 σ) = 0 := by
  have h : modTwoValues X 2 ((modTwoCochains X).d 1 2 ((modTwoCochains X).iCycles 1 φ)) σ = _ :=
    cochainValuesEquiv_linearYonedaObj_d_one_two (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) _ _ σ
  rw [(modTwoCochains X).moduleCat_d_iCycles_apply, CharTwo.sub_eq_add] at h
  rw [← h]
  exact congrFun (map_zero (modTwoValues X 2)) σ

/-- If `δψ = φ ⌣ φ` for mod `2` cochains, the values of `ψ` on the faces of a `2`-simplex sum to
the product of the values of `φ` on its edges from vertex `0` to `1` and from `1` to `2`. -/
private lemma modTwoValues_cup_self (X : TopCat.{0}) (φ : (modTwoCochains X).cycles 1)
    (ψ : (modTwoCochains X).X 1)
    (hψ : (modTwoCochains X).toCycles 1 2 ψ =
      TauCeti.ChainComplex.cupCycles (ZMod 2) (X.alexanderWhitneyDiagonal (λ_ _).inv) (λ_ _).hom
        1 1 2 rfl φ φ)
    (σ : (toSSet.obj X) _⦋2⦌) :
    modTwoValues X 1 ((modTwoCochains X).iCycles 1 φ) ((toSSet.obj X).δ 2 σ) *
        modTwoValues X 1 ((modTwoCochains X).iCycles 1 φ) ((toSSet.obj X).δ 0 σ) =
      modTwoValues X 1 ψ ((toSSet.obj X).δ 0 σ) + modTwoValues X 1 ψ ((toSSet.obj X).δ 1 σ) +
        modTwoValues X 1 ψ ((toSSet.obj X).δ 2 σ) := by
  have h := congrArg ((modTwoCochains X).iCycles 2) hψ
  rw [(modTwoCochains X).moduleCat_iCycles_toCycles_apply,
    TauCeti.ChainComplex.iCycles_cupCycles] at h
  calc _ = modTwoValues X 2 ((modTwoCochains X).d 1 2 ψ) σ := by
        rw [h]
        exact (cochainValuesEquiv_cupCochain_one_one X _ _ _ σ).symm
    _ = _ := (cochainValuesEquiv_linearYonedaObj_d_one_two (ZMod 2)
          (ModuleCat.of (ZMod 2) (ZMod 2)) _ ψ σ).trans (by rw [CharTwo.sub_eq_add])

/-- **The `ℤ/4` lift.** If every class of `H₁(X; ℤ)` is killed by `2`, and the values `f` of a mod
`2` cocycle satisfy `f ⌣ f = δg` on every `2`-simplex, then `f` is the coboundary of a function `e`
on the vertices. The cochain with values `ι f + 2 ι g` in `ℤ/4`, where `ι` is `ZMod.cast`, is a
cocycle reducing to `f`, and the reduction `H¹(X; ℤ/4) ⟶ H¹(X; ℤ/2)` is zero. -/
private lemma exists_sub_eq_of_mul_eq (X : TopCat.{0})
    (h2 : ∀ x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj X,
      2 • x = 0)
    (f g : (toSSet.obj X) _⦋1⦌ → ZMod 2)
    (hf : ∀ σ, f ((toSSet.obj X).δ 0 σ) + f ((toSSet.obj X).δ 1 σ) + f ((toSSet.obj X).δ 2 σ) = 0)
    (hg : ∀ σ, f ((toSSet.obj X).δ 2 σ) * f ((toSSet.obj X).δ 0 σ) =
      g ((toSSet.obj X).δ 0 σ) + g ((toSSet.obj X).δ 1 σ) + g ((toSSet.obj X).δ 2 σ)) :
    ∃ e : (toSSet.obj X) _⦋0⦌ → ZMod 2,
      ∀ τ, e ((toSSet.obj X).δ 0 τ) - e ((toSSet.obj X).δ 1 τ) = f τ := by
  let K := toSSet.obj X
  -- The `ℤ/4`-cocycle `Θ` with values `ι f + 2 ι g` on integral chains, `ι` being `ZMod.cast`.
  let v : K _⦋1⦌ → ZMod 4 := fun τ ↦ (ZMod.cast (f τ) : ZMod 4) + 2 * ZMod.cast (g τ)
  -- `singularCochainComplex` unfolds to the `linearYonedaObj` of the integral chain complex of
  -- `K`, which `cochainValuesEquiv` and `linearYonedaObjMap` below are applied to directly.
  let Z := X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ (ZMod 4))
  let Θ : Z.X 1 := (cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) K 1).symm v
  have hΘ : Z.d 1 2 Θ = 0 := by
    refine (cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) K 2).map_eq_zero_iff.1
      (funext fun σ ↦ ?_)
    rw [cochainValuesEquiv_linearYonedaObj_d_one_two]
    simp only [Θ, K, LinearEquiv.apply_symm_apply, Pi.zero_apply]
    exact zmod_four_cocycle _ _ _ _ _ _ (hf σ) (hg σ)
  -- The reduction of `Θ` modulo `2` is the coboundary of a `0`-cochain `η`.
  have hβ := homologyMap_zmodFourToTwo_eq_zero X h2
    (Z.homologyπ 1 (Z.moduleCatCyclesMk Θ 2 (by simp) hΘ))
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk] at hβ
  obtain ⟨η, hη⟩ :=
    (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _ (m := 0) (by simp) _).1 hβ
  have hη' := congrArg
    (((K.chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ (ModuleCat.of ℤ (ZMod 2))).iCycles
      1).hom hη
  rw [HomologicalComplex.moduleCat_iCycles_toCycles_apply,
    HomologicalComplex.iCycles_moduleCatCyclesMk] at hη'
  refine ⟨cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 2)) K 0 η, fun τ ↦ ?_⟩
  have hv : cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 2)) K 1 (Θ ≫ zmodFourToTwo) τ = f τ := by
    rw [cochainValuesEquiv_apply, ModuleCat.comp_apply, ← cochainValuesEquiv_apply,
      LinearEquiv.apply_symm_apply]
    exact ZMod.cast_cast_add_two_mul_cast _ _
  rw [← cochainValuesEquiv_linearYonedaObj_d_zero_one, hη',
    ChainComplex.linearYonedaObjMap_f_hom_apply, hv]

/-- A mod `2` cocycle whose values are the coboundary of a function `e` on the vertices has zero
class. -/
private lemma homologyπ_eq_zero_of_sub_eq (X : TopCat.{0}) (φ : (modTwoCochains X).cycles 1)
    (e : (toSSet.obj X) _⦋0⦌ → ZMod 2)
    (he : ∀ τ, e ((toSSet.obj X).δ 0 τ) - e ((toSSet.obj X).δ 1 τ) =
      modTwoValues X 1 ((modTwoCochains X).iCycles 1 φ) τ) :
    (modTwoCochains X).homologyπ 1 φ = 0 := by
  let η : (modTwoCochains X).X 0 := (modTwoValues X 0).symm e
  have hφ : (modTwoCochains X).toCycles 0 1 η = φ := by
    apply (modTwoCochains X).moduleCat_iCycles_injective
    rw [(modTwoCochains X).moduleCat_iCycles_toCycles_apply]
    apply (modTwoValues X 1).injective
    funext τ
    refine (cochainValuesEquiv_linearYonedaObj_d_zero_one (ZMod 2)
      (ModuleCat.of (ZMod 2) (ZMod 2)) _ η τ).trans ?_
    simp only [η, LinearEquiv.apply_symm_apply]
    exact he τ
  rw [← hφ, ← ModuleCat.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
  simp

/-- **A mod `2` class of degree one with zero square vanishes when `H₁(X; ℤ)` is `2`-torsion.**
If every class of `H₁(X; ℤ)` is killed by `2`, then every class `w ∈ H¹(X; 𝔽₂)` with
`w ⌣ w = 0` is zero. For instance, on real projective space `RPᴺ`, `N ≥ 2`, the nonzero class of
`H¹(RPᴺ; 𝔽₂)` has nonzero square. -/
theorem eq_zero_of_singularCup_self_eq_zero (X : TopCat.{0})
    (h2 : ∀ x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj X,
      2 • x = 0)
    {w : X.singularCohomology (𝟙_ (ModuleCat.{0} (ZMod 2))) (ZMod 2) (𝟙_ (ModuleCat (ZMod 2))) 1}
    (hw : X.singularCup (ZMod 2) (λ_ _).inv (λ_ _).hom 1 1 2 rfl w w = 0) : w = 0 := by
  -- Represent `w` by a cocycle `φ`, and write `φ ⌣ φ = δψ`.
  obtain ⟨φ, rfl⟩ := (modTwoCochains X).moduleCat_homologyπ_surjective 1 w
  rw [singularCup_homologyπ] at hw
  obtain ⟨ψ, hψ⟩ := ((modTwoCochains X).moduleCat_homologyπ_eq_zero_iff (m := 1) (by simp) _).1 hw
  -- On values, `φ` lifts to a `ℤ/4`-cocycle, so it is a coboundary.
  obtain ⟨e, he⟩ := exists_sub_eq_of_mul_eq X h2 _ _ (modTwoValues_cocycle X φ)
    (modTwoValues_cup_self X φ ψ hψ)
  exact homologyπ_eq_zero_of_sub_eq X φ e he

end TopCat
