/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic

/-!
# Values of cup products of ring-valued singular cochains

For a commutative ring `k`, a singular cochain with coefficients `𝟙_ (ModuleCat k)` is determined
by its values in `k` on singular simplices (`TauCeti.cochainValuesEquiv`). This file computes the
cup product along the unitors in these terms: `φ ⌣ ψ` takes a simplex to the product of the values
of `φ` on its front face and of `ψ` on its back face, the cup product of Hatcher, Section 3.2.

## Main results

* `TopCat.cochainValuesEquiv_cupCochain`: the cup product of a `p`-cochain and a `q`-cochain on
  a singular `(p + q)`-simplex.
* `TopCat.cochainValuesEquiv_cupCochain_one_one`: the cup product of two `1`-cochains on a
  singular `2`-simplex, through its faces `δ₂` and `δ₀`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial TauCeti

universe w

namespace TopCat

variable {k : Type w} [CommRing k] (X : TopCat.{w})

/-- **The cup product of two cochains on a simplex**: with values in a commutative ring `k`, the
cup product of a `p`-cochain `φ` and a `q`-cochain `ψ` takes a singular `(p + q)`-simplex `σ` to
`φ` of the front `p`-face of `σ` times `ψ` of its back `q`-face. -/
lemma cochainValuesEquiv_cupCochain (p q n : ℕ) (h : p + q = n)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X p ⟶ 𝟙_ (ModuleCat.{w} k))
    (ψ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X q ⟶ 𝟙_ (ModuleCat.{w} k))
    (σ : (toSSet.obj X) _⦋n⦌) :
    cochainValuesEquiv k (ModuleCat.of k k) (toSSet.obj X) n
        (TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal (λ_ _).inv) (λ_ _).hom
          p q n h φ ψ) σ =
      cochainValuesEquiv k (ModuleCat.of k k) (toSSet.obj X) p φ
          ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) *
        cochainValuesEquiv k (ModuleCat.of k k) (toSSet.obj X) q ψ
          ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  rw [cochainValuesEquiv_apply, ← ModuleCat.comp_apply,
    ιChainComplex_cupCochain_alexanderWhitneyDiagonal]
  -- `simp` does not unfold this composite through the unit object `𝟙_ (ModuleCat k)`, so the
  -- composite and the unitors are rewritten explicitly first.
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  simp

/-- The cup product of two `1`-cochains with values in a commutative ring takes a `2`-simplex `σ`
to the product of the values on its edges `δ₂ σ` (from vertex `0` to `1`) and `δ₀ σ` (from `1`
to `2`). -/
lemma cochainValuesEquiv_cupCochain_one_one
    (φ ψ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X 1 ⟶ 𝟙_ (ModuleCat.{w} k))
    (σ : (toSSet.obj X) _⦋2⦌) :
    cochainValuesEquiv k (ModuleCat.of k k) (toSSet.obj X) 2
        (TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal (λ_ _).inv) (λ_ _).hom
          1 1 2 rfl φ ψ) σ =
      cochainValuesEquiv k (ModuleCat.of k k) (toSSet.obj X) 1 φ ((toSSet.obj X).δ 2 σ) *
        cochainValuesEquiv k (ModuleCat.of k k) (toSSet.obj X) 1 ψ ((toSSet.obj X).δ 0 σ) := by
  have h₀ : SimplexCategory.subinterval (n := 2) 0 1 (by omega) = SimplexCategory.δ 2 := by
    ext i; fin_cases i <;> rfl
  have h₁ : SimplexCategory.subinterval (n := 2) 1 1 (by omega) = SimplexCategory.δ 0 := by
    ext i; fin_cases i <;> rfl
  rw [cochainValuesEquiv_cupCochain, h₀, h₁, SimplicialObject.δ_def, SimplicialObject.δ_def]

end TopCat
