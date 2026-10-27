/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Pontryagin.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.TopologicalSimplex

/-!
# Exterior powers of the first homology of a commutative topological monoid

Let `G` be a monoid object of `TopCat`, for instance a topological monoid, and `k` a commutative
ring. The Pontryagin product on the singular homology of `G` with coefficients in `k`
(`TopCat.pontryaginProduct`) is here a bilinear map `Hₚ(G; k) → H_q(G; k) → Hₙ(G; k)`
(`TopCat.pontryaginMul`), associative and natural in morphisms of monoid objects, and graded
commutative when `G` is commutative.

When `G` is commutative, the Pontryagin square of every class of degree one vanishes
(`TopCat.pontryaginMul_self_eq_zero`). Graded commutativity alone only shows that this square has
order two; the vanishing holds already for chains. The shuffle product of two singular
`1`-simplices `σ` and `τ` is `(s₁ σ, s₀ τ) - (s₀ σ, s₁ τ)`
(`TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_one_one`), and multiplying the two
components pointwise in a commutative `G` makes the product of a `1`-chain with itself cancel term
by term.

Consequently the iterated Pontryagin product of `n` classes of degree one
(`TopCat.pontryaginMultilinear`), with the class of the identity point as the empty product, is
alternating (`TopCat.pontryaginAlternatingMap`), and induces a linear
map `⋀ⁿ H₁(G; k) → Hₙ(G; k)` (`TopCat.pontryaginExteriorPower`), natural in morphisms of
commutative monoid objects (`TopCat.pontryaginExteriorPower_naturality`), such as continuous
homomorphisms of tori. For the torus `(S¹)ⁿ` and `k = ℤ` these maps are isomorphisms, the
description of the homology of a torus as an exterior algebra; this file only constructs them.

## Main definitions

* `TopCat.pontryaginMul`: the Pontryagin product as a bilinear map.
* `TopCat.pontryaginMultilinear`: the iterated Pontryagin product of classes of degree one.
* `TopCat.pontryaginAlternatingMap`: the same, as an alternating map, for commutative `G`.
* `TopCat.pontryaginExteriorPower`: the induced map `⋀ⁿ H₁(G; k) → Hₙ(G; k)`.

## Main results

* `TopCat.pontryaginMul_assoc`, `TopCat.pontryaginMul_comm`: associativity and graded
  commutativity.
* `TopCat.pontryaginMul_self_eq_zero`: the square of a class of degree one vanishes.
* `TopCat.singularHomologyFunctor_map_pontryaginMul`,
  `TopCat.singularHomologyFunctor_map_pontryaginMultilinear`,
  `TopCat.pontryaginExteriorPower_naturality`: naturality in morphisms of monoid objects.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.C, the Pontryagin product on the homology of an H-space.
* S. Eilenberg and S. Mac Lane, *On the groups `H(Π, n)`, I*, Ann. of Math. 58 (1953), for the
  shuffle product.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits AlgebraicTopology HomologicalComplex MonObj
open TensorProduct Simplicial

universe u

namespace TopCat

variable (k : Type u) [CommRing k] (G : TopCat.{u}) [MonObj G]

/-- **The Pontryagin product** on the singular homology of a monoid object `G` of `TopCat` with
coefficients in a commutative ring `k`, as a bilinear map `Hₚ(G; k) → H_q(G; k) → Hₙ(G; k)` for
`p + q = n`. -/
def pontryaginMul (p q n : ℕ) (h : p + q = n) :
    ((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).obj G →ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj G →ₗ[k]
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).obj G :=
  TensorProduct.curry (pontryaginProduct G (𝟙_ (ModuleCat.{u} k)) p q n h).hom

variable {k G}

/-- The bilinear Pontryagin product of `a` and `b` is the Pontryagin product of `a ⊗ b`. -/
lemma pontryaginMul_apply (p q n : ℕ) (h : p + q = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).obj G)
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj G) :
    pontryaginMul k G p q n h a b = pontryaginProduct G (𝟙_ (ModuleCat.{u} k)) p q n h (a ⊗ₜ b) :=
  (rfl)

/-- **Associativity of the Pontryagin product**: `(a · b) · c = a · (b · c)`. -/
theorem pontryaginMul_assoc (p q r pq qr n : ℕ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).obj G)
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj G)
    (c : ((singularHomologyFunctor (ModuleCat.{u} k) r).obj (𝟙_ _)).obj G) :
    pontryaginMul k G pq r n hn (pontryaginMul k G p q pq hpq a b) c =
      pontryaginMul k G p qr n hn' a (pontryaginMul k G q r qr hqr b c) := by
  have := congrArg (fun f ↦ f ((a ⊗ₜ b) ⊗ₜ c))
    (pontryaginProduct_assoc G (𝟙_ (ModuleCat.{u} k)) p q r pq qr n hpq hqr hn hn')
  simp only [CategoryTheory.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply] at this
  exact this

/-- **Graded commutativity of the Pontryagin product**: for a commutative monoid object `G`,
`a · b = (-1)^(p * q) b · a` for `a ∈ Hₚ(G; k)` and `b ∈ H_q(G; k)`. -/
theorem pontryaginMul_comm [IsCommMonObj G] (p q n : ℕ) (h : p + q = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).obj G)
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj G) :
    pontryaginMul k G p q n h a b =
      ((-1 : ℤ) ^ (p * q)) • pontryaginMul k G q p n (by omega) b a := by
  have := congrArg (fun f ↦ f (a ⊗ₜ b))
    (pontryaginProduct_comm G (𝟙_ (ModuleCat.{u} k)) p q n h)
  simpa [pontryaginMul_apply] using this

/-- **Naturality of the Pontryagin product**: a morphism of monoid objects `f : G ⟶ G'` satisfies
`f_* (a · b) = f_* a · f_* b`. -/
theorem singularHomologyFunctor_map_pontryaginMul {G' : TopCat.{u}} [MonObj G'] (f : G ⟶ G')
    [IsMonHom f] (p q n : ℕ) (h : p + q = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).obj G)
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj G) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map f
        (pontryaginMul k G p q n h a b) =
      pontryaginMul k G' p q n h
        (((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).map f a)
        (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).map f b) :=
  (congrArg (fun g ↦ g (a ⊗ₜ b))
    (pontryaginProduct_naturality f (𝟙_ (ModuleCat.{u} k)) p q n h)).symm

section Square

/-! ### The square of a class of degree one -/

variable (k G) in
/-- The chain map inducing the Pontryagin product: the shuffle map followed by the
multiplications of `k` and of `G`. -/
private abbrev pontryaginChainMap :
    (toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)) ⊗
        (toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)) ⟶
      (toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)) :=
  shuffle G G (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) ≫
    ((SSet.chainComplexFunctor (ModuleCat.{u} k)).map μ[𝟙_ (ModuleCat.{u} k)]).app
      (toSSet.obj (G ⊗ G)) ≫
    SSet.chainComplexMap (toSSet.map μ[G]) (𝟙_ (ModuleCat.{u} k))

variable (G) in
/-- The pointwise product of two singular `2`-simplices of `G`. -/
private abbrev simplexMul (x y : (toSSet.obj G) _⦋2⦌) : (toSSet.obj G) _⦋2⦌ :=
  (toSSet.map μ[G]).app _ ((Functor.LaxMonoidal.μ toSSet G G).app _
    ((x, y) : (toSSet.obj G ⊗ toSSet.obj G) _⦋2⦌))

private lemma simplexMul_comm [IsCommMonObj G] (x y : (toSSet.obj G) _⦋2⦌) :
    simplexMul G x y = simplexMul G y x := by
  refine TauCeti.TopCat.simplexMap_injective (ContinuousMap.ext fun p ↦ ?_)
  simp only [TauCeti.TopCat.simplexMap_app, ContinuousMap.comp_apply]
  rw [TauCeti.TopCat.simplexMap_μ_apply, TauCeti.TopCat.simplexMap_μ_apply]
  exact congrArg (fun f : G ⊗ G ⟶ G ↦ f
    ((TauCeti.TopCat.simplexMap y p, TauCeti.TopCat.simplexMap x p) : G ⊗ G))
    (IsCommMonObj.mul_comm G)

/-- The chain-level Pontryagin product of two singular `1`-simplices `σ` and `τ` is
`s₁ σ · s₀ τ - s₀ σ · s₁ τ`. -/
private lemma pontryaginChainMap_simplex (σ τ : (toSSet.obj G) _⦋1⦌) :
    (ιTensorObj ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)))
        ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))) 1 1 2 rfl ≫
        (pontryaginChainMap k G).f 2)
      ((toSSet.obj G).ιChainComplex (R := 𝟙_ (ModuleCat.{u} k)) σ 1 ⊗ₜ
        (toSSet.obj G).ιChainComplex (R := 𝟙_ (ModuleCat.{u} k)) τ 1) =
      (toSSet.obj G).ιChainComplex (R := 𝟙_ (ModuleCat.{u} k))
          (simplexMul G ((toSSet.obj G).σ 1 σ) ((toSSet.obj G).σ 0 τ)) 1 -
        (toSSet.obj G).ιChainComplex (R := 𝟙_ (ModuleCat.{u} k))
          (simplexMul G ((toSSet.obj G).σ 0 σ) ((toSSet.obj G).σ 1 τ)) 1 := by
  have h : ((toSSet.obj G).ιChainComplex (R := 𝟙_ (ModuleCat.{u} k)) σ ⊗ₘ
      (toSSet.obj G).ιChainComplex (R := 𝟙_ (ModuleCat.{u} k)) τ) ≫
      ιTensorObj ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)))
        ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))) 1 1 2 rfl ≫
      (pontryaginChainMap k G).f 2 =
      μ[𝟙_ (ModuleCat.{u} k)] ≫ ((toSSet.obj G).ιChainComplex
          (simplexMul G ((toSSet.obj G).σ 1 σ) ((toSSet.obj G).σ 0 τ)) -
        (toSSet.obj G).ιChainComplex
          (simplexMul G ((toSSet.obj G).σ 0 σ) ((toSSet.obj G).σ 1 τ))) := by
    simp only [HomologicalComplex.comp_f,
      ιChainComplex_tensorHom_ιChainComplex_shuffle_f_one_one_assoc, Preadditive.sub_comp,
      TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc, SSet.ι_chainComplexMap_f,
      Preadditive.comp_sub]
  -- evaluate both sides at `1 ⊗ 1`, which the multiplication of `k` sends to `1`
  rw [← ModuleCat.MonoidalCategory.tensorHom_tmul, ← CategoryTheory.comp_apply, h]
  simp

/-- For commutative `G`, the chain-level Pontryagin product of a `1`-chain with itself vanishes. -/
private lemma pontryaginChainMap_self [IsCommMonObj G]
    (c : ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))).X 1) :
    (ιTensorObj ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)))
        ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))) 1 1 2 rfl ≫
        (pontryaginChainMap k G).f 2) (c ⊗ₜ c) = 0 := by
  -- the chain-level product on `1`-chains, read on the singular chains with coefficients in `k`,
  -- where the element-level interface applies
  let B : ((TauCeti.singularChains k).obj G).X 1 →ₗ[k] ((TauCeti.singularChains k).obj G).X 1 →ₗ[k]
      ((TauCeti.singularChains k).obj G).X 2 :=
    TensorProduct.curry (ιTensorObj ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)))
      ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))) 1 1 2 rfl ≫
        (pontryaginChainMap k G).f 2).hom
  have hB (σ τ : (toSSet.obj G) _⦋1⦌) : B (TauCeti.simplexChain σ 1) (TauCeti.simplexChain τ 1) =
      TauCeti.simplexChain (simplexMul G ((toSSet.obj G).σ 1 σ) ((toSSet.obj G).σ 0 τ)) 1 -
        TauCeti.simplexChain (simplexMul G ((toSSet.obj G).σ 0 σ) ((toSSet.obj G).σ 1 τ)) 1 :=
    pontryaginChainMap_simplex σ τ
  -- `B` is antisymmetric, as it is on pairs of simplices by commutativity of `G`
  have hanti : B + B.flip = 0 :=
    TauCeti.singularChains_linearMap_ext fun σ ↦ TauCeti.singularChains_linearMap_ext fun τ ↦ by
      simp only [LinearMap.add_apply, LinearMap.flip_apply, LinearMap.zero_apply, hB]
      rw [simplexMul_comm ((toSSet.obj G).σ 1 σ), simplexMul_comm ((toSSet.obj G).σ 0 σ)]
      abel
  -- and it vanishes on the diagonal of each simplex, hence on the whole diagonal
  have hdiag (d : ((TauCeti.singularChains k).obj G).X 1) : B d d = 0 := by
    obtain ⟨f, rfl⟩ := (TauCeti.singularChainsLinearEquivFinsupp k G 1).symm.surjective d
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      have h := LinearMap.congr_fun₂ hanti
        ((TauCeti.singularChainsLinearEquivFinsupp k G 1).symm f)
        ((TauCeti.singularChainsLinearEquivFinsupp k G 1).symm g)
      simp only [LinearMap.add_apply, LinearMap.flip_apply, LinearMap.zero_apply] at h
      simp only [map_add, LinearMap.add_apply, hf, hg, zero_add, add_zero]
      rw [add_comm, h]
    | single σ a =>
      rw [TauCeti.singularChainsLinearEquivFinsupp_symm_single, TauCeti.simplexChain_eq_smul,
        map_smul, map_smul, LinearMap.smul_apply, hB, simplexMul_comm ((toSSet.obj G).σ 1 σ),
        sub_self, smul_zero, smul_zero]
  exact hdiag c

/-- **The Pontryagin square of a class of degree one vanishes** in the homology of a commutative
monoid object `G` of `TopCat`, with coefficients in any commutative ring. -/
theorem pontryaginMul_self_eq_zero [IsCommMonObj G]
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G) :
    pontryaginMul k G 1 1 2 rfl a a = 0 := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))).homologyπ 1)) a
  -- the square of the class of a cycle is the class of a cycle which vanishes already as a chain
  have key : (cyclesCross _ _ 1 1 2 rfl ≫ cyclesMap (pontryaginChainMap k G) 2) (z ⊗ₜ z) = 0 := by
    have hc : cyclesCross _ _ 1 1 2 rfl ≫
        (((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))) ⊗
          ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k)))).iCycles 2 =
        (iCycles _ 1 ⊗ₘ iCycles _ 1) ≫ ιTensorObj _ _ 1 1 2 rfl :=
      cyclesCross_iCycles _ _ 1 1 2 rfl
    refine (ModuleCat.mono_iff_injective (iCycles _ 2)).1 inferInstance ?_
    rw [map_zero, ← CategoryTheory.comp_apply, Category.assoc, cyclesMap_i, reassoc_of% hc,
      CategoryTheory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]
    exact pontryaginChainMap_self _
  calc pontryaginMul k G 1 1 2 rfl _ _ =
      ((((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))).homologyπ 1 ⊗ₘ
        ((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))).homologyπ 1) ≫
          pontryaginProduct G (𝟙_ (ModuleCat.{u} k)) 1 1 2 rfl) (z ⊗ₜ z) := (rfl)
    _ = 0 := by
      rw [homologyπ_tensorHom_pontryaginProduct, ← Category.assoc]
      exact (congrArg (((toSSet.obj G).chainComplex (𝟙_ (ModuleCat.{u} k))).homologyπ 2).hom
        key).trans (map_zero _)

end Square

section Multilinear

/-! ### Iterated products of classes of degree one -/

variable (k G) in
/-- The iterated Pontryagin product `a₀ · (a₁ · (⋯ · aₙ₋₁))` of `n` classes of degree one, a
multilinear map `H₁(G; k)ⁿ → Hₙ(G; k)`; the empty product is the class of the identity point
of `G`. -/
def pontryaginMultilinear (n : ℕ) : MultilinearMap k
    (fun _ : Fin n ↦ ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G)
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).obj G) :=
  match n with
  | 0 => MultilinearMap.constOfIsEmpty k _
      (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{u} k)) (η[G] PUnit.unit) (1 : k))
  | n + 1 => LinearMap.uncurryLeft
      { toFun := fun x ↦ (pontryaginMul k G 1 n (n + 1) (Nat.add_comm 1 n) x).compMultilinearMap
          (pontryaginMultilinear n)
        map_add' := fun x y ↦ by rw [map_add, LinearMap.add_compMultilinearMap]
        map_smul' := fun c x ↦ by rw [map_smul, LinearMap.smul_compMultilinearMap]; rfl }

/-- The empty Pontryagin product is the class of the identity point. -/
@[simp]
theorem pontryaginMultilinear_zero_apply
    (v : Fin 0 → ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G) :
    pontryaginMultilinear k G 0 v =
      TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{u} k)) (η[G] PUnit.unit) (1 : k) :=
  (rfl)

/-- The iterated Pontryagin product of `n + 1` classes is the product of the first one with the
iterated product of the others. -/
theorem pontryaginMultilinear_succ_apply (n : ℕ)
    (v : Fin (n + 1) → ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G) :
    pontryaginMultilinear k G (n + 1) v =
      pontryaginMul k G 1 n (n + 1) (Nat.add_comm 1 n) (v 0)
        (pontryaginMultilinear k G n (Fin.tail v)) :=
  (rfl)

/-- **Naturality of the iterated Pontryagin product** in morphisms of monoid objects. -/
theorem singularHomologyFunctor_map_pontryaginMultilinear {G' : TopCat.{u}} [MonObj G']
    (f : G ⟶ G') [IsMonHom f] (n : ℕ)
    (v : Fin n → ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map f
        (pontryaginMultilinear k G n v) =
      pontryaginMultilinear k G' n
        (fun i ↦ ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).map f (v i)) := by
  induction n with
  | zero =>
    rw [pontryaginMultilinear_zero_apply, pontryaginMultilinear_zero_apply,
      ← CategoryTheory.comp_apply, TauCeti.singularHomology₀Section_naturality]
    exact congrArg (fun x ↦ TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{u} k)) x (1 : k))
      (congrArg (fun g ↦ g PUnit.unit) (IsMonHom.one_hom f))
  | succ n ih =>
    rw [pontryaginMultilinear_succ_apply, pontryaginMultilinear_succ_apply,
      singularHomologyFunctor_map_pontryaginMul, ih]
    rfl

end Multilinear

section Alternating

/-! ### Exterior powers -/

variable [IsCommMonObj G]

/-- The Pontryagin product of a class of degree one with an iterated product of classes of degree
one containing it vanishes. -/
private lemma pontryaginMul_pontryaginMultilinear_eq_zero (n : ℕ)
    (w : Fin n → ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G)
    (j : Fin n) :
    pontryaginMul k G 1 n (n + 1) (Nat.add_comm 1 n) (w j) (pontryaginMultilinear k G n w) = 0 := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [pontryaginMultilinear_succ_apply]
    cases j using Fin.cases with
    | zero =>
      -- `a · (a · b) = (a · a) · b = 0`
      rw [← pontryaginMul_assoc 1 1 n 2 (n + 1) (n + 1 + 1) rfl (Nat.add_comm 1 n) (by omega),
        pontryaginMul_self_eq_zero, map_zero, LinearMap.zero_apply]
    | succ j =>
      -- `a · (c · b) = -(c · (a · b))`, and `a · b = 0` as `a` occurs in `b`
      rw [← pontryaginMul_assoc 1 1 n 2 (n + 1) (n + 1 + 1) rfl (Nat.add_comm 1 n) (by omega),
        pontryaginMul_comm 1 1 2 rfl, map_zsmul, LinearMap.smul_apply,
        pontryaginMul_assoc 1 1 n 2 (n + 1) (n + 1 + 1) rfl (Nat.add_comm 1 n) (by omega)
          (by omega)]
      exact (congrArg _ ((congrArg _ (ih (Fin.tail w) j)).trans (map_zero _))).trans (smul_zero _)

/-- An iterated Pontryagin product of classes of degree one with a repeated factor vanishes. -/
private lemma pontryaginMultilinear_eq_zero_of_eq (n : ℕ)
    (v : Fin n → ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G)
    {i j : Fin n} (hv : v i = v j) (hij : i ≠ j) :
    pontryaginMultilinear k G n v = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [pontryaginMultilinear_succ_apply]
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => rw [hv]; exact pontryaginMul_pontryaginMultilinear_eq_zero _ (Fin.tail v) j
    | succ i =>
      cases j using Fin.cases with
      | zero => rw [← hv]; exact pontryaginMul_pontryaginMultilinear_eq_zero _ (Fin.tail v) i
      | succ j =>
        rw [ih (Fin.tail v) hv (fun h ↦ hij (congrArg Fin.succ h)), map_zero]

variable (k G) in
/-- For a commutative monoid object `G`, the iterated Pontryagin product of `n` classes of degree
one, as an alternating map `H₁(G; k)ⁿ → Hₙ(G; k)`. -/
def pontryaginAlternatingMap (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G [⋀^Fin n]→ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).obj G where
  __ := pontryaginMultilinear k G n
  map_eq_zero_of_eq' v _ _ hv hij := pontryaginMultilinear_eq_zero_of_eq n v hv hij

@[simp]
theorem pontryaginAlternatingMap_apply (n : ℕ)
    (v : Fin n → ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G) :
    pontryaginAlternatingMap k G n v = pontryaginMultilinear k G n v :=
  (rfl)

variable (k G) in
/-- For a commutative monoid object `G`, the linear map `⋀ⁿ H₁(G; k) → Hₙ(G; k)` induced by the
Pontryagin product, sending `a₀ ∧ ⋯ ∧ aₙ₋₁` to `a₀ · (a₁ · (⋯ · aₙ₋₁))`. -/
def pontryaginExteriorPower (n : ℕ) :
    ⋀[k]^n (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G) →ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).obj G :=
  exteriorPower.alternatingMapLinearEquiv (pontryaginAlternatingMap k G n)

@[simp]
theorem pontryaginExteriorPower_ιMulti (n : ℕ)
    (v : Fin n → ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj G) :
    pontryaginExteriorPower k G n (exteriorPower.ιMulti k n v) = pontryaginMultilinear k G n v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- **Naturality of the exterior power map**: for a morphism `f : G ⟶ G'` of commutative monoid
objects, `f_* ∘ Φ_G = Φ_G' ∘ ⋀ⁿ f_*`, where `Φ` is `TopCat.pontryaginExteriorPower`. -/
theorem pontryaginExteriorPower_naturality {G' : TopCat.{u}} [MonObj G'] [IsCommMonObj G']
    (f : G ⟶ G') [IsMonHom f] (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map f).hom ∘ₗ
        pontryaginExteriorPower k G n =
      pontryaginExteriorPower k G' n ∘ₗ
        exteriorPower.map n
          (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).map f).hom :=
  exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ by
    simp [singularHomologyFunctor_map_pontryaginMultilinear, Function.comp_def])

end Alternating

end TopCat

end

end
