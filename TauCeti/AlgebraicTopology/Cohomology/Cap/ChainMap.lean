/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.ChainMap
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Pushforward

/-!
# The relative cap product with a cocycle as a chain map

For a topological pair `P = (X, Z)`, a continuous map `p₀ : X ⟶ Y` and a relative cocycle `φ` of
degree `n` with coefficients in a commutative ring `K`, capping a relative chain with `φ` and
pushing forward along `p₀`, `x ↦ (-1)^(n p) p₀_*(x ⌢ φ)` in degree `n + p`, is a chain map from the
relative singular chains of `P` to the singular chains of `Y` placed `n` degrees higher
(`TopPair.pushforwardCapChainMap`, an instance of `TauCeti.ChainComplex.capChainMap`). On homology
it is `(-1)^(n p)` times the map `TopPair.pushforwardCap`, `x ↦ p₀_*(x ⌢ [φ])`
(`TopPair.homologyMap_pushforwardCapChainMap_comp_extendHomologyIso_hom`).

So this chain map is a quasi-isomorphism exactly when the relative homology of `P` vanishes below
`n` and `TopPair.pushforwardCap` is an isomorphism in every degree
(`TopPair.quasiIso_pushforwardCapChainMap_iff`). For the Thom pair `(E, E₀)` of a vector bundle,
its projection and a cocycle representing a Thom class, both hold by the Thom isomorphism in
homology (`TauCeti.isIso_homologyThomMap`), so the chain map is a quasi-isomorphism: a chain-level
form of the Thom isomorphism.

## Main definitions

* `TopPair.pushforwardCapChainMap`: the chain map `x ↦ (-1)^(n p) p₀_*(x ⌢ φ)` from the relative
  singular chains of `P` to the singular chains of `Y` shifted up by `n`.

## Main results

* `TopPair.pushforwardCapChainMap_f`: its component in degree `n + p`.
* `TopPair.homologyMap_pushforwardCapChainMap_comp_extendHomologyIso_hom`: on homology it is
  `(-1)^(n p)` times `TopPair.pushforwardCap` of the class of `φ`.
* `TopPair.quasiIso_pushforwardCapChainMap_iff`: it is a quasi-isomorphism if and only if the
  relative homology of `P` vanishes below `n` and `TopPair.pushforwardCap` of the class of `φ` is
  an isomorphism in every degree.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.3.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits MonoidalCategory HomologicalComplex

universe w

namespace TopPair

variable {K : Type w} [CommRing K] (P : TopPair.{w}) {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y)
  (A : ModuleCat.{w} K)

/-- **The relative cap product with a cocycle, pushed forward, as a chain map.** For a relative
cocycle `φ` of degree `n` of a pair `P = (X, Z)` with coefficients in `K` and a map `p₀ : X ⟶ Y`,
the chain map from the relative singular chains of `P` with coefficients in `A` to the singular
chains of `Y` placed `n` degrees higher, which in degree `n + p` is `x ↦ (-1)^(n p) p₀_*(x ⌢ φ)`.
The cap product pairs the values of `φ` with `A` through the left unitor `K ⊗ A ≅ A`, as in
`TopPair.pushforwardCap`. -/
def pushforwardCapChainMap (n : ℕ)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles n) :
    P.singularChainComplex A ⟶
      ((TopCat.toSSet.obj Y).chainComplex A).extend (ComplexShape.embeddingDownNatAdd n) :=
  TauCeti.ChainComplex.capChainMap K (P.alexanderWhitneyDiagonal (λ_ A).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) A) n φ

/-- In degree `m = n + p`, the chain map `TopPair.pushforwardCapChainMap` is `(-1)^(n p)` times the
cap product with `φ` followed by the push-forward along `p₀`, then the identification of the
shifted chains of `Y` in degree `m` with `Cₚ(Y; A)`. -/
theorem pushforwardCapChainMap_f (n p m : ℕ) (h : n + p = m)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles n) :
    (P.pushforwardCapChainMap p₀ A n φ).f m =
      (((-1 : ℤ) ^ (n * p)) • TauCeti.ChainComplex.capChain K
        (P.alexanderWhitneyDiagonal (λ_ A).inv)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
          SSet.chainComplexMap (TopCat.toSSet.map p₀) A) n p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles n φ)) ≫
        (((TopCat.toSSet.obj Y).chainComplex A).extendXIso (ComplexShape.embeddingDownNatAdd n)
          (by simp; omega)).inv :=
  TauCeti.ChainComplex.capChainMap_f _ _ n p m (by omega) φ

/-- `TopPair.pushforwardCap` is the cap product along the relative Alexander–Whitney diagonal and
the coefficient pairing followed by the push-forward along `p₀`. -/
private theorem pushforwardCap_eq_cap (n p m : ℕ) (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.pushforwardCap p₀ A n p m h u =
      TauCeti.ChainComplex.cap K (P.alexanderWhitneyDiagonal (λ_ A).inv)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
          SSet.chainComplexMap (TopCat.toSSet.map p₀) A) n p m h u := by
  -- naturality of the cap product along the push-forward of its output
  have := TauCeti.ChainComplex.cap_naturality (k := K) (P.alexanderWhitneyDiagonal (λ_ A).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) A) (P.alexanderWhitneyDiagonal (λ_ A).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) (𝟙 _) (𝟙 _) (𝟙 _)
    (SSet.chainComplexMap (TopCat.toSSet.map p₀) A) (by simp) (by simp) n p m h u
  simp only [op_id, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    Category.id_comp] at this
  rw [pushforwardCap_apply, singularCap_def, ← this]
  -- the identity of the relative cochains induces the identity on cohomology
  exact congrArg (fun v ↦ TauCeti.ChainComplex.cap K _ _ n p m h v ≫ _)
    (ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_id _ n) u).symm

/-- **On homology, `TopPair.pushforwardCapChainMap` is `TopPair.pushforwardCap`**, up to sign: in
degree `m = n + p`, followed by the identification of the homology of the shifted chains of `Y`
with `Hₚ(Y; A)`, it is `(-1)^(n p)` times `x ↦ p₀_*(x ⌢ [φ])`. -/
theorem homologyMap_pushforwardCapChainMap_comp_extendHomologyIso_hom (n p m : ℕ)
    (h : n + p = m)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles n) :
    homologyMap (P.pushforwardCapChainMap p₀ A n φ) m ≫
        (((TopCat.toSSet.obj Y).chainComplex A).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd n) (by simp; omega)).hom =
      ((-1 : ℤ) ^ (n * p)) • P.pushforwardCap p₀ A n p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ n φ) := by
  rw [pushforwardCap_eq_cap]
  exact TauCeti.ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom _ _ n p m
    (by omega) φ

/-- **When the pushed-forward cap product with a cocycle is a quasi-isomorphism.** The chain map
`TopPair.pushforwardCapChainMap` of a relative cocycle `φ` of degree `n` is a quasi-isomorphism if
and only if the relative homology of `P` with coefficients in `A` vanishes below `n` and
`x ↦ p₀_*(x ⌢ [φ])` is an isomorphism `H_{n + p}(P; A) ≅ Hₚ(Y; A)` for every `p`. -/
theorem quasiIso_pushforwardCapChainMap_iff (n : ℕ)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles n) :
    QuasiIso (P.pushforwardCapChainMap p₀ A n φ) ↔ (∀ m < n, IsZero (P.singularHomology A m)) ∧
      ∀ p, IsIso (P.pushforwardCap p₀ A n p (n + p) rfl
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ n φ)) := by
  simp only [pushforwardCap_eq_cap]
  exact TauCeti.ChainComplex.quasiIso_capChainMap_iff _ _ n φ

end TopPair
