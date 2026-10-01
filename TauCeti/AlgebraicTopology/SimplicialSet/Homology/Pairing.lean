/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Coefficient pairings on simplicial chains

Let `C` be a preadditive monoidal category with `w`-small coproducts, and let `M` be an object of
`C` such that `M ⊗ -` preserves `w`-small coproducts (for instance, any object of a closed
monoidal category such as `ModuleCat k`).  The simplicial chains `Cₙ(X; S)` of a simplicial set
`X` are the coproduct of one copy of `S` for each `n`-simplex, so `M ⊗ Cₙ(X; S)` is the coproduct
of one copy of `M ⊗ S` for each `n`-simplex.  A pairing `μ : M ⊗ S ⟶ P` of coefficient objects
therefore induces, simplex by simplex, a chain map `X.chainComplexPairing μ` from the complex
`M ⊗ C(X; S)` to `C(X; P)`.  It is natural in `X`.

This is how the coefficients of a cochain act on chains in the cap product: capping with a cochain
`φ : Cₚ(X; R) ⟶ M` produces an element of `M ⊗ C_q(X; S)`, which the pairing turns into a chain
with coefficients in `P`.

## Main definitions and results

* `SSet.chainComplexPairing`: the chain map `M ⊗ C(X; S) ⟶ C(X; P)` induced by `μ`.
* `SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f`: its value on the summand of a simplex.
* `SSet.chainComplexPairing_naturality`: it is natural in the simplicial set.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [MonoidalCategory C] {M S P : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- `M ⊗ Cₙ(X; S)` is the coproduct of the objects `M ⊗ S`, one for each `n`-simplex of `X`, with
inclusions `M ◁ X.ιChainComplex x`. -/
private def isColimitTensorLeftChainComplexXCofan (X : SSet.{w}) (n : ℕ) :
    IsColimit (Cofan.mk (M ⊗ (X.chainComplex S).X n) fun x : X _⦋n⦌ ↦ M ◁ X.ιChainComplex x) :=
  isColimitCofanMkObjOfIsColimit (tensorLeft M) _ _ (X.isColimitChainComplexXCofan S n)

/-- Two morphisms out of `M ⊗ Cₙ(X; S)` agree as soon as they agree on the summand `M ⊗ S` of each
`n`-simplex of `X`. -/
lemma whiskerLeft_chainComplex_hom_ext {X : SSet.{w}} {n : ℕ} {T : C}
    {f g : M ⊗ (X.chainComplex S).X n ⟶ T}
    (h : ∀ x : X _⦋n⦌, (M ◁ X.ιChainComplex x) ≫ f = (M ◁ X.ιChainComplex x) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitTensorLeftChainComplexXCofan X n) _ _ h

/-- The degree-`n` component of `SSet.chainComplexPairing`. -/
private def chainComplexPairingX (X : SSet.{w}) (μ : M ⊗ S ⟶ P) (n : ℕ) :
    M ⊗ (X.chainComplex S).X n ⟶ (X.chainComplex P).X n :=
  Cofan.IsColimit.desc (isColimitTensorLeftChainComplexXCofan X n) fun x ↦ μ ≫ X.ιChainComplex x

@[reassoc]
private lemma whiskerLeft_ιChainComplex_chainComplexPairingX (X : SSet.{w}) (μ : M ⊗ S ⟶ P)
    {n : ℕ} (x : X _⦋n⦌) :
    (M ◁ X.ιChainComplex x) ≫ chainComplexPairingX X μ n = μ ≫ X.ιChainComplex x :=
  Cofan.IsColimit.fac (isColimitTensorLeftChainComplexXCofan X n) _ x

variable [MonoidalPreadditive C]

/-- **The chain map induced by a coefficient pairing** `μ : M ⊗ S ⟶ P`: the chain map
`M ⊗ C(X; S) ⟶ C(X; P)` which sends the summand `M ⊗ S` of a simplex `x` to the summand `P` of `x`
through `μ` (`SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f`). -/
def chainComplexPairing (X : SSet.{w}) (μ : M ⊗ S ⟶ P) :
    ((tensorLeft M).mapHomologicalComplex _).obj (X.chainComplex S) ⟶ X.chainComplex P where
  f n := chainComplexPairingX X μ n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    refine whiskerLeft_chainComplex_hom_ext fun x ↦ ?_
    dsimp
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ιChainComplex_d,
      whiskerLeft_ιChainComplex_chainComplexPairingX_assoc, ιChainComplex_d, Preadditive.comp_sum,
      whiskerLeft_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    -- whiskering by `M` is the additive functor `tensorLeft M`, so it commutes with `ℤ`-scaling
    have hz : M ◁ (((-1 : ℤ) ^ (k : ℕ)) • X.ιChainComplex (R := S) (X.δ k x)) =
        ((-1 : ℤ) ^ (k : ℕ)) • (M ◁ X.ιChainComplex (X.δ k x)) :=
      (tensorLeft M).map_zsmul
    rw [hz, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      whiskerLeft_ιChainComplex_chainComplexPairingX]

/-- The chain map induced by a coefficient pairing `μ` sends the summand `M ⊗ S` of a simplex `x`
to the summand `P` of `x` through `μ`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ιChainComplex_chainComplexPairing_f (X : SSet.{w}) (μ : M ⊗ S ⟶ P) {n : ℕ}
    (x : X _⦋n⦌) :
    (M ◁ X.ιChainComplex x) ≫ (X.chainComplexPairing μ).f n = μ ≫ X.ιChainComplex x :=
  whiskerLeft_ιChainComplex_chainComplexPairingX X μ x

/-- The chain map induced by a coefficient pairing is natural in the simplicial set. -/
@[reassoc]
lemma chainComplexPairing_naturality {X Y : SSet.{w}} (f : X ⟶ Y) (μ : M ⊗ S ⟶ P) :
    ((tensorLeft M).mapHomologicalComplex _).map (chainComplexMap f S) ≫
        Y.chainComplexPairing μ =
      X.chainComplexPairing μ ≫ chainComplexMap f P := by
  ext n : 1
  refine whiskerLeft_chainComplex_hom_ext fun x ↦ ?_
  simp [← MonoidalCategory.whiskerLeft_comp_assoc]

end SSet
