/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.AlexanderWhitney
public import TauCeti.AlgebraicTopology.SimplicialSet.Shuffle

/-!
# The Eilenberg–Zilber theorem

For simplicial sets `K` and `L`, the Alexander–Whitney map
`C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)` and the shuffle map back are mutually inverse chain homotopy
equivalences (`SSet.eilenbergZilberHomotopyEquiv`).  Neither composite is the identity on
unnormalized chains.  Already for a `1`-simplex `x` of `K` and a vertex `y` of `L`, the
Alexander–Whitney map followed by the shuffle map sends the summand of the `1`-simplex `(x, s₀ y)`
of `K × L` to itself plus the summand of the degenerate `1`-simplex `(s₀ x₀, s₀ y)`, where `x₀` is
the initial vertex of `x`.  Both homotopies come from the method of acyclic models.

For `shuffle ∘ AW ≃ id` (`SSet.alexanderWhitneyShuffleHomotopy`) the statement used is
`SSet.prodChainComplexHomotopy`.  Let `φ` and `ψ` be families of chain maps
`C(K × L; T) ⟶ C(K × L; T')`, natural in maps `K ⟶ K'` and `L ⟶ L'`, which agree in degree zero.
Then `φ` and `ψ` are chain homotopic, through a homotopy natural in `K` and `L`
(`SSet.prodChainComplexHomotopy_hom_naturality`).  An `n`-simplex `(x, y)` of `K × L` is the image
of the diagonal `n`-simplex of the model `Δ[n] × Δ[n]` under the map classifying `(x, y)`, so by
naturality the homotopy is determined by its values on these diagonal simplices.  These values are
built by induction on `n`: the chain that the homotopy must bound on the model is a cycle by the
inductive hypothesis, and the cone from the vertex `(0, 0)` of `Δ[n] × Δ[n]`
(`SSet.stdSimplex.prodConeChain`) bounds it, because this cone is a contracting homotopy in
positive degrees.

For `AW ∘ shuffle ≃ id` (`SSet.shuffleAlexanderWhitneyHomotopy`) the statement used is the same
one for families of chain maps `C(K; R) ⊗ C(L; S) ⟶ C(K; R') ⊗ C(L; S')`
(`SSet.tensorChainComplexHomotopy`).  Here the summand of a `p`-simplex `x` of `K` and a
`q`-simplex `y` of `L` is the image of the summand of the pair of top simplices of the models
`Δ[p]` and `Δ[q]`, so there is one model for each bidegree.  The bounding chains on the models come
from the contracting homotopy `c ⊗ 1 + e ⊗ c` of `C(Δ[p]; R') ⊗ C(Δ[q]; S')` in positive degrees
(`SSet.stdSimplex.tensorConeChain`).  Here `c` is the cone from the vertex `0` on either factor
(`SSet.stdSimplex.coneChain`), and `e` collapses the vertices of `Δ[p]` onto the vertex `0`
(`SSet.stdSimplex.constZeroChain`).

## Main definitions and results

* `SSet.prodChainComplexHomotopy`: two natural families of chain maps on the simplicial chains of
  products which agree in degree zero are chain homotopic.
* `SSet.prodChainComplexHomotopy_hom_naturality`: the homotopy is natural in both simplicial sets.
* `SSet.alexanderWhitney_shuffle_f_zero`: the Alexander–Whitney map followed by the shuffle map is
  the identity in degree zero.
* `SSet.alexanderWhitneyShuffleHomotopy`: the Alexander–Whitney map followed by the shuffle map is
  chain homotopic to the identity.
* `SSet.stdSimplex.tensorConeChain`: the contracting homotopy of `C(Δ[a]; R) ⊗ C(Δ[b]; S)` in
  positive degrees, with `SSet.stdSimplex.tensorConeChain_d` its boundary formula.
* `SSet.tensorChainComplexHomotopy`: two natural families of chain maps on tensor products of
  simplicial chains which agree in degree zero are chain homotopic, and
  `SSet.tensorChainComplexHomotopy_hom_naturality`: the homotopy is natural.
* `SSet.shuffle_alexanderWhitney_f_zero`: the shuffle map followed by the Alexander–Whitney map is
  the identity in degree zero.
* `SSet.shuffleAlexanderWhitneyHomotopy`: the shuffle map followed by the Alexander–Whitney map is
  chain homotopic to the identity.
* `SSet.eilenbergZilberHomotopyEquiv`: the Alexander–Whitney map is a chain homotopy equivalence
  with homotopy inverse the shuffle map.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Sections 8.5 and 8.6.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex
open TauCeti.SSet (chainComplexMap_f_comp chainComplexMap_f_comp_assoc)

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section AcyclicModels

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] {T T' : C}

/-- The diagonal `n`-simplex of `Δ[n] × Δ[n]`, whose image under the map classifying a simplex
`(x, y)` of `K × L` is `(x, y)`. -/
private def diag (n : ℕ) : ((Δ[n] : SSet.{w}) ⊗ Δ[n]) _⦋n⦌ :=
  (yonedaEquiv (𝟙 _), yonedaEquiv (𝟙 _))

private lemma ιChainComplex_diag_chainComplexMap_f {K L : SSet.{w}} {n : ℕ}
    (x : (K ⊗ L) _⦋n⦌) :
    ((Δ[n] : SSet.{w}) ⊗ Δ[n]).ιChainComplex (R := T) (diag n) ≫
        (chainComplexMap (yonedaEquiv.symm x.1 ⊗ₘ yonedaEquiv.symm x.2) T).f n =
      (K ⊗ L).ιChainComplex x := by
  rw [ι_chainComplexMap_f]
  -- the two components of the image of the diagonal simplex are, by definition, the images of
  -- `𝟙` under the maps classifying `x.1` and `x.2`
  exact congrArg _ (Prod.ext (yonedaEquiv_symm_app_id x.1) (yonedaEquiv_symm_app_id x.2))

/-- The summand of a `p`-simplex `x` of `K` is the image of the summand of the top simplex of the
model `Δ[p]` under the map classifying `x`. -/
private lemma ιChainComplex_id_chainComplexMap_f {K : SSet.{w}} {p : ℕ} (x : K _⦋p⦌) :
    (Δ[p] : SSet.{w}).ιChainComplex (R := T) (yonedaEquiv (𝟙 _)) ≫
        (chainComplexMap (yonedaEquiv.symm x) T).f p = K.ιChainComplex x := by
  rw [ι_chainComplexMap_f, yonedaEquiv_symm_app_id]

/-- A natural family of maps between the simplicial chains of products is determined by its values
on the diagonal simplices of the models: on the summand of an `n`-simplex `(x, y)` of `K × L` it is
the image of its value on the diagonal `n`-simplex of `Δ[n] × Δ[n]` under the map classifying
`(x, y)`. -/
private lemma ιChainComplex_comp_eq_diag {n m : ℕ}
    (u : ∀ K L : SSet.{w}, ((K ⊗ L).chainComplex T).X n ⟶ ((K ⊗ L).chainComplex T').X m)
    (hu : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
      (chainComplexMap (f ⊗ₘ g) T).f n ≫ u K' L' = u K L ≫ (chainComplexMap (f ⊗ₘ g) T').f m)
    {K L : SSet.{w}} (x : (K ⊗ L) _⦋n⦌) :
    (K ⊗ L).ιChainComplex x ≫ u K L =
      ((Δ[n] : SSet.{w}) ⊗ Δ[n]).ιChainComplex (diag n) ≫ u _ _ ≫
        (chainComplexMap (yonedaEquiv.symm x.1 ⊗ₘ yonedaEquiv.symm x.2) T').f m := by
  rw [← ιChainComplex_diag_chainComplexMap_f x, Category.assoc, hu]

/-- The natural extension of a chain `c` of `Δ[n] × Δ[n]` of degree `n + 1`: the map raising the
degree of the simplicial chains of `K × L` by one which sends the summand of an `n`-simplex
`(x, y)` to the image of `c` under the map `Δ[n] × Δ[n] ⟶ K × L` classifying `(x, y)`. -/
private def extend {n : ℕ} (c : T ⟶ (((Δ[n] : SSet.{w}) ⊗ Δ[n]).chainComplex T').X (n + 1))
    (K L : SSet.{w}) :
    ((K ⊗ L).chainComplex T).X n ⟶ ((K ⊗ L).chainComplex T').X (n + 1) :=
  Cofan.IsColimit.desc ((K ⊗ L).isColimitChainComplexXCofan T n) fun x ↦
    c ≫ (chainComplexMap (yonedaEquiv.symm x.1 ⊗ₘ yonedaEquiv.symm x.2) T').f (n + 1)

@[reassoc]
private lemma ιChainComplex_extend {n : ℕ}
    (c : T ⟶ (((Δ[n] : SSet.{w}) ⊗ Δ[n]).chainComplex T').X (n + 1)) {K L : SSet.{w}}
    (x : (K ⊗ L) _⦋n⦌) :
    (K ⊗ L).ιChainComplex x ≫ extend c K L =
      c ≫ (chainComplexMap (yonedaEquiv.symm x.1 ⊗ₘ yonedaEquiv.symm x.2) T').f (n + 1) :=
  Cofan.IsColimit.fac _ _ x

@[reassoc]
private lemma chainComplexMap_f_extend {n : ℕ}
    (c : T ⟶ (((Δ[n] : SSet.{w}) ⊗ Δ[n]).chainComplex T').X (n + 1)) {K K' L L' : SSet.{w}}
    (f : K ⟶ K') (g : L ⟶ L') :
    (chainComplexMap (f ⊗ₘ g) T).f n ≫ extend c K' L' =
      extend c K L ≫ (chainComplexMap (f ⊗ₘ g) T').f (n + 1) := by
  ext x
  simp only [ι_chainComplexMap_f_assoc, ιChainComplex_extend, ιChainComplex_extend_assoc,
    chainComplexMap_f_comp, tensorHom_comp_tensorHom, yonedaEquiv_symm_comp]
  -- a tensor product of maps acts on the components of a simplex of a product separately
  rfl

private lemma extend_zero {n : ℕ} (K L : SSet.{w}) :
    extend (0 : T ⟶ (((Δ[n] : SSet.{w}) ⊗ Δ[n]).chainComplex T').X (n + 1)) K L = 0 := by
  ext x
  rw [ιChainComplex_extend, zero_comp, comp_zero]

variable (θ : ∀ K L : SSet.{w}, (K ⊗ L).chainComplex T ⟶ (K ⊗ L).chainComplex T')

/-- The values of the homotopy on the diagonal simplices of the models `Δ[n] × Δ[n]`, defined by
induction on `n`.  In degree zero it vanishes.  In degree `n + 1`, it is the cone from `(0, 0)` on
the chain `θ (ι) - h (∂ ι)`, where `ι` is the diagonal `(n + 1)`-simplex and `h` is the natural
extension of the value in degree `n`. -/
private def modelHom : (n : ℕ) → (T ⟶ (((Δ[n] : SSet.{w}) ⊗ Δ[n]).chainComplex T').X (n + 1))
  | 0 => 0
  | n + 1 =>
      ((Δ[n + 1] : SSet.{w}) ⊗ Δ[n + 1]).ιChainComplex (diag (n + 1)) ≫
        ((θ (Δ[n + 1]) (Δ[n + 1])).f (n + 1) -
          (((Δ[n + 1] : SSet.{w}) ⊗ Δ[n + 1]).chainComplex T).d (n + 1) n ≫
            extend (modelHom n) (Δ[n + 1]) (Δ[n + 1])) ≫
        stdSimplex.prodConeChain (n + 1) (n + 1) T' (n + 1)

variable {θ}

variable (hθ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
  chainComplexMap (f ⊗ₘ g) T ≫ θ K' L' = θ K L ≫ chainComplexMap (f ⊗ₘ g) T')
include hθ

/-- The inductive step: if the extension `h` of the model value in degree `n` satisfies
`∂ h ∂ = ∂ θ` in degree `n`, then the extension of the model value in degree `n + 1` satisfies
`∂ h = θ - h ∂` in degree `n + 1`. -/
private lemma extend_modelHom_succ_d (n : ℕ)
    (hcyc : ∀ K L : SSet.{w}, ((K ⊗ L).chainComplex T).d (n + 1) n ≫
        extend (modelHom θ n) K L ≫ ((K ⊗ L).chainComplex T').d (n + 1) n =
      ((K ⊗ L).chainComplex T).d (n + 1) n ≫ (θ K L).f n)
    (K L : SSet.{w}) :
    extend (modelHom θ (n + 1)) K L ≫ ((K ⊗ L).chainComplex T').d (n + 2) (n + 1) =
      (θ K L).f (n + 1) - ((K ⊗ L).chainComplex T).d (n + 1) n ≫ extend (modelHom θ n) K L := by
  -- the map `θ - h ∂` raising degrees by one is natural
  have hnat : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
      (chainComplexMap (f ⊗ₘ g) T).f (n + 1) ≫ ((θ K' L').f (n + 1) -
          ((K' ⊗ L').chainComplex T).d (n + 1) n ≫ extend (modelHom θ n) K' L') =
        ((θ K L).f (n + 1) - ((K ⊗ L).chainComplex T).d (n + 1) n ≫ extend (modelHom θ n) K L) ≫
          (chainComplexMap (f ⊗ₘ g) T').f (n + 1) := fun _ _ _ _ f g ↦ by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      ← chainComplexMap_f_extend, Hom.comm_assoc, ← HomologicalComplex.comp_f, hθ]
  -- on the model, the chain `(θ - h ∂) (ι)` is a cycle, so the cone on it bounds it
  have hmodel : modelHom θ (n + 1) ≫
      (((Δ[n + 1] : SSet.{w}) ⊗ Δ[n + 1]).chainComplex T').d (n + 2) (n + 1) =
        ((Δ[n + 1] : SSet.{w}) ⊗ Δ[n + 1]).ιChainComplex (diag (n + 1)) ≫
          ((θ (Δ[n + 1]) (Δ[n + 1])).f (n + 1) -
            (((Δ[n + 1] : SSet.{w}) ⊗ Δ[n + 1]).chainComplex T).d (n + 1) n ≫
              extend (modelHom θ n) (Δ[n + 1]) (Δ[n + 1])) := by
    have hcyc' : ((θ (Δ[n + 1]) (Δ[n + 1])).f (n + 1) -
        (((Δ[n + 1] : SSet.{w}) ⊗ Δ[n + 1]).chainComplex T).d (n + 1) n ≫
          extend (modelHom θ n) (Δ[n + 1]) (Δ[n + 1])) ≫
        (((Δ[n + 1] : SSet.{w}) ⊗ Δ[n + 1]).chainComplex T').d (n + 1) n = 0 := by
      simp only [Preadditive.sub_comp, Category.assoc, Hom.comm, hcyc, sub_self]
    simp only [modelHom, Category.assoc, stdSimplex.prodConeChain_d, Preadditive.comp_sub,
      Category.comp_id, reassoc_of% hcyc', zero_comp, sub_zero]
  -- by naturality, the identity on a simplex `(x, y)` is the image of the identity on the model
  ext x
  rw [ιChainComplex_extend_assoc, Hom.comm, reassoc_of% hmodel,
    ιChainComplex_comp_eq_diag (fun K L ↦ (θ K L).f (n + 1) -
      ((K ⊗ L).chainComplex T).d (n + 1) n ≫ extend (modelHom θ n) K L) hnat]

variable (h₀ : ∀ K L : SSet.{w}, (θ K L).f 0 = 0)
include h₀

/-- The extension `h` of the model values satisfies `∂ h = θ - h ∂` in every positive degree. -/
private lemma extend_modelHom_succ_d' (n : ℕ) (K L : SSet.{w}) :
    extend (modelHom θ (n + 1)) K L ≫ ((K ⊗ L).chainComplex T').d (n + 2) (n + 1) =
      (θ K L).f (n + 1) - ((K ⊗ L).chainComplex T).d (n + 1) n ≫ extend (modelHom θ n) K L := by
  induction n generalizing K L with
  | zero =>
    refine extend_modelHom_succ_d hθ 0 (fun K L ↦ ?_) K L
    rw [modelHom, extend_zero, zero_comp, comp_zero, h₀, comp_zero]
  | succ n ih =>
    refine extend_modelHom_succ_d hθ (n + 1) (fun K L ↦ ?_) K L
    rw [ih, Preadditive.comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp, sub_zero]

end AcyclicModels

section Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] {T T' : C}
  (φ ψ : ∀ K L : SSet.{w}, (K ⊗ L).chainComplex T ⟶ (K ⊗ L).chainComplex T')
  (hφ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
    chainComplexMap (f ⊗ₘ g) T ≫ φ K' L' = φ K L ≫ chainComplexMap (f ⊗ₘ g) T')
  (hψ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
    chainComplexMap (f ⊗ₘ g) T ≫ ψ K' L' = ψ K L ≫ chainComplexMap (f ⊗ₘ g) T')
  (h₀ : ∀ K L : SSet.{w}, (φ K L).f 0 = (ψ K L).f 0)

/-- **Acyclic models for products of simplicial sets.**  Two families `φ` and `ψ` of chain maps
`C(K × L; T) ⟶ C(K × L; T')` on the simplicial chains of products, natural in both simplicial sets
and equal in degree zero, are chain homotopic.  The homotopy is natural in `K` and `L`
(`SSet.prodChainComplexHomotopy_hom_naturality`). -/
def prodChainComplexHomotopy (K L : SSet.{w}) : Homotopy (φ K L) (ψ K L) where
  hom i j :=
    if h : i + 1 = j then
      extend (modelHom (fun K L ↦ φ K L - ψ K L) i) K L ≫ eqToHom (congrArg _ h)
    else 0
  zero _ _ h := dite_eq_right_iff.mpr fun h' ↦ absurd h' h
  comm i := by
    have hθ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
        chainComplexMap (f ⊗ₘ g) T ≫ (φ K' L' - ψ K' L') =
          (φ K L - ψ K L) ≫ chainComplexMap (f ⊗ₘ g) T' := fun _ _ _ _ f g ↦ by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, hφ, hψ]
    have h₀' : ∀ K L : SSet.{w}, (φ K L - ψ K L).f 0 = 0 := fun K L ↦ by
      rw [HomologicalComplex.sub_f_apply, h₀, sub_self]
    cases i with
    | zero =>
      simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, ↓reduceDIte,
        eqToHom_refl, Category.comp_id]
      rw [modelHom, extend_zero, zero_comp, zero_add, zero_add, h₀]
    | succ n =>
      simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, ↓reduceDIte,
        eqToHom_refl, Category.comp_id]
      rw [extend_modelHom_succ_d' hθ h₀' n K L, HomologicalComplex.sub_f_apply]
      abel

/-- The homotopy of `SSet.prodChainComplexHomotopy` is natural in both simplicial sets. -/
@[reassoc]
lemma prodChainComplexHomotopy_hom_naturality {K K' L L' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L')
    (i j : ℕ) :
    (chainComplexMap (f ⊗ₘ g) T).f i ≫ (prodChainComplexHomotopy φ ψ hφ hψ h₀ K' L').hom i j =
      (prodChainComplexHomotopy φ ψ hφ hψ h₀ K L).hom i j ≫ (chainComplexMap (f ⊗ₘ g) T').f j := by
  simp only [prodChainComplexHomotopy]
  split_ifs with h
  · subst h
    simp only [eqToHom_refl, Category.comp_id]
    exact chainComplexMap_f_extend _ f g
  · rw [comp_zero, zero_comp]

end Homotopy

section EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L : SSet.{w}) (R S : C)

/-- In degree zero, the Alexander–Whitney map followed by the shuffle map is the identity: both
maps send the summand of a vertex `(x, y)` to the summand of `x` tensored with that of `y`, and
back. -/
@[reassoc (attr := simp)]
lemma alexanderWhitney_shuffle_f_zero :
    (alexanderWhitney K L R S).f 0 ≫ (shuffle K L R S).f 0 = 𝟙 _ := by
  ext x
  rw [ιChainComplex_alexanderWhitney_f_assoc, Fin.sum_univ_one, Category.comp_id]
  simp only [Fin.val_zero, Nat.sub_zero, TauCeti.SimplexCategory.subinterval_zero_eq_id, op_id,
    Functor.map_id_apply, Category.assoc]
  exact ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero K L R S x.1 x.2

/-- **The Eilenberg–Zilber homotopy** `shuffle ∘ AW ≃ id`: the Alexander–Whitney map
`C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)` followed by the shuffle map is chain homotopic to the
identity of `C(K × L; R ⊗ S)`.  The homotopy is the one given by acyclic models,
`SSet.prodChainComplexHomotopy`, and so is natural in `K` and `L`. -/
def alexanderWhitneyShuffleHomotopy :
    Homotopy (alexanderWhitney K L R S ≫ shuffle K L R S) (𝟙 _) :=
  prodChainComplexHomotopy (fun K L ↦ alexanderWhitney K L R S ≫ shuffle K L R S)
    (fun _ _ ↦ 𝟙 _)
    (fun _ _ _ _ f g ↦ by
      rw [alexanderWhitney_naturality_assoc, shuffle_naturality, Category.assoc])
    (fun _ _ _ _ _ _ ↦ by rw [Category.comp_id, Category.id_comp])
    (fun _ _ ↦ by simp) K L

end EilenbergZilber

namespace stdSimplex

section TensorCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] (a b : ℕ) (R S : C)

/-- The summands of `SSet.stdSimplex.tensorConeChain`. -/
private def tensorConeSummand : (r s n : ℕ) → r + s = n →
    (((Δ[a] : SSet.{w}).chainComplex R).X r ⊗ ((Δ[b] : SSet.{w}).chainComplex S).X s ⟶
      ((Δ[a] : SSet.{w}).chainComplex R ⊗ (Δ[b] : SSet.{w}).chainComplex S).X (n + 1))
  | 0, s, n, h =>
      (coneChain a R 0 ▷ _) ≫ ιTensorObj _ _ 1 s (n + 1) (by omega) +
        (constZeroChain a R ⊗ₘ coneChain b S s) ≫ ιTensorObj _ _ 0 (s + 1) (n + 1) (by omega)
  | r + 1, s, n, h =>
      (coneChain a R (r + 1) ▷ _) ≫ ιTensorObj _ _ (r + 1 + 1) s (n + 1) (by omega)

/-- The cone on the tensor product `C(Δ[a]; R) ⊗ C(Δ[b]; S)`, as a map raising the degree by one:
`c ⊗ 1 + e ⊗ c`, where `c` is the cone from the vertex `0` on either factor
(`SSet.stdSimplex.coneChain`) and `e` collapses the `0`-chains of `Δ[a]` onto the vertex `0`
(`SSet.stdSimplex.constZeroChain`).  It is a contracting homotopy in positive degrees
(`SSet.stdSimplex.tensorConeChain_d`). -/
def tensorConeChain (n : ℕ) :
    ((Δ[a] : SSet.{w}).chainComplex R ⊗ (Δ[b] : SSet.{w}).chainComplex S).X n ⟶
      ((Δ[a] : SSet.{w}).chainComplex R ⊗ (Δ[b] : SSet.{w}).chainComplex S).X (n + 1) :=
  mapBifunctorDesc fun r s h ↦ tensorConeSummand a b R S r s n h

/-- On a summand of bidegree `(0, s)`, the cone on `C(Δ[a]; R) ⊗ C(Δ[b]; S)` is
`c ⊗ 1 + e ⊗ c`. -/
@[reassoc]
lemma ι_tensorConeChain_zero (s n : ℕ) (h : 0 + s = n) :
    ιTensorObj _ _ 0 s n h ≫ tensorConeChain a b R S n =
      (coneChain a R 0 ▷ _) ≫ ιTensorObj _ _ 1 s (n + 1) (by omega) +
        (constZeroChain a R ⊗ₘ coneChain b S s) ≫ ιTensorObj _ _ 0 (s + 1) (n + 1) (by omega) :=
  ι_mapBifunctorDesc _ _ _ _

/-- On a summand of bidegree `(r + 1, s)`, the cone on `C(Δ[a]; R) ⊗ C(Δ[b]; S)` is the cone on
the first factor. -/
@[reassoc]
lemma ι_tensorConeChain_succ (r s n : ℕ) (h : r + 1 + s = n) :
    ιTensorObj _ _ (r + 1) s n h ≫ tensorConeChain a b R S n =
      (coneChain a R (r + 1) ▷ _) ≫ ιTensorObj _ _ (r + 1 + 1) s (n + 1) (by omega) :=
  ι_mapBifunctorDesc _ _ _ _

/-- On the image of a boundary in the first factor, the cone on `C(Δ[a]; R) ⊗ C(Δ[b]; S)` is the
cone in the first factor: the second summand vanishes since collapsing onto the vertex `0` kills
boundaries. -/
@[reassoc]
private lemma d_whiskerRight_ι_tensorConeChain (r s n : ℕ) (h : r + s = n) :
    (((Δ[a] : SSet.{w}).chainComplex R).d (r + 1) r ▷ _) ≫ ιTensorObj _ _ r s n h ≫
        tensorConeChain a b R S n =
      (((Δ[a] : SSet.{w}).chainComplex R).d (r + 1) r ▷ _) ≫ (coneChain a R r ▷ _) ≫
        ιTensorObj _ _ (r + 1) s (n + 1) (by omega) := by
  rcases r with _ | r
  · rw [ι_tensorConeChain_zero, Preadditive.comp_add, whiskerRight_comp_tensorHom_assoc,
      d_constZeroChain, MonoidalPreadditive.zero_tensor, zero_comp, add_zero]
  · rw [ι_tensorConeChain_succ]

/-- The cone on the first factor, whiskered by the second, is a contracting homotopy in positive
degrees (`SSet.stdSimplex.coneChain_d`). -/
@[reassoc]
private lemma coneChain_whiskerRight_d (m : ℕ) (Z : C) :
    (coneChain a R (m + 1) ▷ Z) ≫ (((Δ[a] : SSet.{w}).chainComplex R).d (m + 1 + 1) (m + 1) ▷ Z) =
      𝟙 _ - (((Δ[a] : SSet.{w}).chainComplex R).d (m + 1) m ▷ Z) ≫ (coneChain a R m ▷ Z) := by
  rw [← comp_whiskerRight, coneChain_d, ← comp_whiskerRight, ← id_whiskerRight]
  exact (tensorRight Z).map_sub

/-- The cone on the vertices of the first factor, whiskered by the second, contracts onto the
vertex `0` (`SSet.stdSimplex.coneChain_zero_d`).  The degree `0 + 1` is the form in which the
boundary arises from `ChainComplex.ιTensorObj_D₁_succ`. -/
@[reassoc]
private lemma coneChain_zero_whiskerRight_d (Z : C) :
    (coneChain a R 0 ▷ Z) ≫ (((Δ[a] : SSet.{w}).chainComplex R).d (0 + 1) 0 ▷ Z) =
      𝟙 _ - (constZeroChain a R ▷ Z) := by
  rw [← comp_whiskerRight, coneChain_zero_d, ← id_whiskerRight]
  exact (tensorRight Z).map_sub

/-- The boundary in the second factor of the summand `e ⊗ c` of the cone on
`C(Δ[a]; R) ⊗ C(Δ[b]; S)` in positive degrees (`SSet.stdSimplex.coneChain_d`). -/
@[reassoc]
private lemma constZeroChain_tensorHom_coneChain_d (s : ℕ) :
    (constZeroChain a R ⊗ₘ coneChain b S (s + 1)) ≫
        (_ ◁ ((Δ[b] : SSet.{w}).chainComplex S).d (s + 1 + 1) (s + 1)) =
      (constZeroChain a R ▷ _) - (constZeroChain a R ⊗ₘ
        (((Δ[b] : SSet.{w}).chainComplex S).d (s + 1) s ≫ coneChain b S s)) := by
  have hL : ∀ (Z : C) {X Y : C} (f g : X ⟶ Y), Z ◁ (f - g) = Z ◁ f - Z ◁ g :=
    fun Z _ _ _ _ ↦ (tensorLeft Z).map_sub
  rw [tensorHom_comp_whiskerLeft, coneChain_d, tensorHom_def, tensorHom_def, hL, whiskerLeft_id,
    Preadditive.comp_sub, Category.comp_id]

/-- The cone on `C(Δ[a]; R) ⊗ C(Δ[b]; S)` is a contracting homotopy in positive degrees:
`∂ (c ∘ σ) = σ - c ∘ ∂ σ` for a chain `σ` of positive degree.  On a summand `u ⊗ v` this combines
the boundary formulas of the cones on the two factors with the Koszul sign rule. -/
lemma tensorConeChain_d (n : ℕ) :
    tensorConeChain a b R S (n + 1) ≫
        ((Δ[a] : SSet.{w}).chainComplex R ⊗ (Δ[b] : SSet.{w}).chainComplex S).d (n + 1 + 1)
          (n + 1) =
      𝟙 _ - ((Δ[a] : SSet.{w}).chainComplex R ⊗ (Δ[b] : SSet.{w}).chainComplex S).d (n + 1) n ≫
        tensorConeChain a b R S n := by
  have hd : ∀ m,
      ((Δ[a] : SSet.{w}).chainComplex R ⊗ (Δ[b] : SSet.{w}).chainComplex S).d (m + 1) m =
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (m + 1) m +
          mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (m + 1) m :=
    fun m ↦ mapBifunctor.d_eq _ _ _ _ _ _
  refine mapBifunctor.hom_ext fun r s h ↦ ?_
  rw [hd, hd, Preadditive.comp_sub]
  -- the identity of the tensor product is not syntactically the identity of the codomain of the
  -- inclusion of a summand
  refine Eq.trans ?_ (congrArg (· - _) (Category.comp_id _).symm)
  rcases r with _ | r
  · obtain rfl : s = n + 1 := by simp at h; omega
    simp only [ι_tensorConeChain_zero_assoc, ι_tensorConeChain_zero, Preadditive.add_comp,
      Preadditive.comp_add, Preadditive.sub_comp, Category.assoc, Category.id_comp,
      ChainComplex.ιTensorObj_D₁_succ, ChainComplex.ιTensorObj_D₁_zero,
      ChainComplex.ιTensorObj_D₂_succ, ChainComplex.ιTensorObj_D₂_succ_assoc,
      ChainComplex.ιTensorObj_D₁_zero_assoc, comp_zero, zero_comp, Preadditive.comp_zsmul,
      pow_zero, pow_one, one_smul, coneChain_zero_whiskerRight_d_assoc,
      constZeroChain_tensorHom_coneChain_d_assoc, whisker_exchange_assoc,
      whiskerLeft_comp_tensorHom_assoc]
    abel
  · rcases s with _ | s
    · obtain rfl : r = n := by simp at h; omega
      simp only [ι_tensorConeChain_succ_assoc, Preadditive.add_comp, Preadditive.comp_add,
        Preadditive.sub_comp, Category.assoc, Category.id_comp, ChainComplex.ιTensorObj_D₁_succ,
        ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_zero,
        ChainComplex.ιTensorObj_D₂_zero_assoc, d_whiskerRight_ι_tensorConeChain,
        coneChain_whiskerRight_d_assoc, comp_zero, zero_comp, add_zero]
    · simp only [ι_tensorConeChain_succ_assoc, ι_tensorConeChain_succ, Preadditive.add_comp,
        Preadditive.comp_add, Preadditive.sub_comp, Category.assoc, Category.id_comp,
        ChainComplex.ιTensorObj_D₁_succ, ChainComplex.ιTensorObj_D₁_succ_assoc,
        ChainComplex.ιTensorObj_D₂_succ, ChainComplex.ιTensorObj_D₂_succ_assoc,
        d_whiskerRight_ι_tensorConeChain, coneChain_whiskerRight_d_assoc, Preadditive.comp_zsmul,
        Preadditive.zsmul_comp, Preadditive.comp_neg, whisker_exchange_assoc, pow_succ _ (r + 1),
        mul_neg_one, neg_smul]
      abel

end TensorCone

end stdSimplex

section TensorAcyclicModels

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S R' S' : C}

/-- The tensor product of the chain maps of `f : K ⟶ K'` and `g : L ⟶ L'` sends the summand of a
pair of simplices `(x, y)` to the summand of `(f x, g y)`. -/
@[reassoc]
private lemma tensorHom_ιTensorObj_tensorHom_f {K K' L L' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L')
    {p q n : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n) :
    (K.ιChainComplex (R := R) x ⊗ₘ L.ιChainComplex (R := S) y) ≫ ιTensorObj _ _ p q n h ≫
        (chainComplexMap f R ⊗ₘ chainComplexMap g S).f n =
      (K'.ιChainComplex (f.app _ x) ⊗ₘ L'.ιChainComplex (g.app _ y)) ≫ ιTensorObj _ _ p q n h := by
  rw [tensorHom_eq_mapBifunctorMap, ι_tensorHom, tensorHom_comp_tensorHom_assoc,
    ι_chainComplexMap_f, ι_chainComplexMap_f]

/-- The tensor product of the chain maps classifying a pair of simplices `(x, y)`, followed by the
tensor product of the chain maps of `f` and `g`, is the tensor product of the chain maps
classifying `(f x, g y)`. -/
@[reassoc]
private lemma tensorHom_yonedaEquiv_symm_f_comp {K K' L L' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L')
    {p q : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (m : ℕ) :
    (chainComplexMap (yonedaEquiv.symm x) R ⊗ₘ chainComplexMap (yonedaEquiv.symm y) S).f m ≫
        (chainComplexMap f R ⊗ₘ chainComplexMap g S).f m =
      (chainComplexMap (yonedaEquiv.symm (f.app _ x)) R ⊗ₘ
        chainComplexMap (yonedaEquiv.symm (g.app _ y)) S).f m := by
  rw [← HomologicalComplex.comp_f, tensorHom_comp_tensorHom, ← Functor.map_comp,
    ← Functor.map_comp, yonedaEquiv_symm_comp, yonedaEquiv_symm_comp]

/-- The summand of a pair of simplices `(x, y)` of `K` and `L` in `C(K; R) ⊗ C(L; S)` is the image
of the summand of the pair of nondegenerate top simplices of the models `Δ[p]` and `Δ[q]` under
the maps classifying `x` and `y`. -/
private lemma tensorHom_ιTensorObj_eq_model {K L : SSet.{w}} {p q n : ℕ} (x : K _⦋p⦌)
    (y : L _⦋q⦌) (h : p + q = n) :
    (K.ιChainComplex (R := R) x ⊗ₘ L.ιChainComplex (R := S) y) ≫ ιTensorObj _ _ p q n h =
      ((Δ[p] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _)) ⊗ₘ
          (Δ[q] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _))) ≫ ιTensorObj _ _ p q n h ≫
        (chainComplexMap (yonedaEquiv.symm x) R ⊗ₘ chainComplexMap (yonedaEquiv.symm y) S).f n := by
  rw [tensorHom_eq_mapBifunctorMap, ι_tensorHom, tensorHom_comp_tensorHom_assoc,
    ιChainComplex_id_chainComplexMap_f, ιChainComplex_id_chainComplexMap_f]

/-- A natural family of maps out of the tensor products of simplicial chains is determined by its
values on the models: on the summand of a pair of simplices `(x, y)` it is the image of its value
on the pair of top simplices of `Δ[p]` and `Δ[q]` under the maps classifying `x` and `y`. -/
private lemma tensorHom_ιTensorObj_comp_eq_model {n m : ℕ}
    (u : ∀ K L : SSet.{w}, (K.chainComplex R ⊗ L.chainComplex S).X n ⟶
      (K.chainComplex R' ⊗ L.chainComplex S').X m)
    (hu : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
      (chainComplexMap f R ⊗ₘ chainComplexMap g S).f n ≫ u K' L' =
        u K L ≫ (chainComplexMap f R' ⊗ₘ chainComplexMap g S').f m)
    {K L : SSet.{w}} {p q : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫ ιTensorObj _ _ p q n h ≫ u K L =
      ((Δ[p] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _)) ⊗ₘ
          (Δ[q] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _))) ≫ ιTensorObj _ _ p q n h ≫
        u _ _ ≫ (chainComplexMap (yonedaEquiv.symm x) R' ⊗ₘ
          chainComplexMap (yonedaEquiv.symm y) S').f m := by
  rw [← Category.assoc, tensorHom_ιTensorObj_eq_model, Category.assoc, Category.assoc, hu]

variable [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- The natural extension of a family `c` of chains of `C(Δ[p]; R') ⊗ C(Δ[q]; S')` of degree
`n + 1`, indexed by `p + q = n`: the map raising the degree of `C(K; R) ⊗ C(L; S)` by one which
sends the summand of a pair of simplices `(x, y)` of bidegree `(p, q)` to the image of `c p q` under
the maps classifying `x` and `y`. -/
private def tensorExtend {n : ℕ}
    (c : ∀ p q : ℕ, p + q = n →
      (R ⊗ S ⟶ ((Δ[p] : SSet.{w}).chainComplex R' ⊗ (Δ[q] : SSet.{w}).chainComplex S').X (n + 1)))
    (K L : SSet.{w}) :
    (K.chainComplex R ⊗ L.chainComplex S).X n ⟶ (K.chainComplex R' ⊗ L.chainComplex S').X (n + 1) :=
  mapBifunctorDesc fun p q h ↦ tensorChainComplexXDesc fun x y ↦ c p q h ≫
    (chainComplexMap (yonedaEquiv.symm x) R' ⊗ₘ chainComplexMap (yonedaEquiv.symm y) S').f (n + 1)

@[reassoc]
private lemma ι_tensorExtend {n : ℕ}
    (c : ∀ p q : ℕ, p + q = n →
      (R ⊗ S ⟶ ((Δ[p] : SSet.{w}).chainComplex R' ⊗ (Δ[q] : SSet.{w}).chainComplex S').X (n + 1)))
    {K L : SSet.{w}} {p q : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫ ιTensorObj _ _ p q n h ≫ tensorExtend c K L =
      c p q h ≫
        (chainComplexMap (yonedaEquiv.symm x) R' ⊗ₘ chainComplexMap (yonedaEquiv.symm y) S').f
          (n + 1) := by
  simp [tensorExtend]

@[reassoc]
private lemma tensorHom_f_tensorExtend {n : ℕ}
    (c : ∀ p q : ℕ, p + q = n →
      (R ⊗ S ⟶ ((Δ[p] : SSet.{w}).chainComplex R' ⊗ (Δ[q] : SSet.{w}).chainComplex S').X (n + 1)))
    {K K' L L' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L') :
    (chainComplexMap f R ⊗ₘ chainComplexMap g S).f n ≫ tensorExtend c K' L' =
      tensorExtend c K L ≫ (chainComplexMap f R' ⊗ₘ chainComplexMap g S').f (n + 1) := by
  refine mapBifunctor.hom_ext fun p q h ↦ tensorChainComplexX_hom_ext fun x y ↦ ?_
  simp only [tensorHom_ιTensorObj_tensorHom_f_assoc, ι_tensorExtend, ι_tensorExtend_assoc,
    tensorHom_yonedaEquiv_symm_f_comp]

private lemma tensorExtend_zero {n : ℕ} (K L : SSet.{w}) :
    tensorExtend (fun p q (_ : p + q = n) ↦
      (0 : R ⊗ S ⟶ ((Δ[p] : SSet.{w}).chainComplex R' ⊗ (Δ[q] : SSet.{w}).chainComplex S').X
        (n + 1))) K L = 0 := by
  refine mapBifunctor.hom_ext fun p q h ↦ tensorChainComplexX_hom_ext fun x y ↦ ?_
  rw [ι_tensorExtend, zero_comp, comp_zero, comp_zero]

variable (θ : ∀ K L : SSet.{w},
  K.chainComplex R ⊗ L.chainComplex S ⟶ K.chainComplex R' ⊗ L.chainComplex S')

/-- The values of the homotopy on the models, defined by induction on `n`.  In degree zero they
vanish.  In degree `n + 1` and bidegree `(p, q)`, the value is the cone
`SSet.stdSimplex.tensorConeChain` on the chain `θ (ι) - h (∂ ι)` of `C(Δ[p]; R') ⊗ C(Δ[q]; S')`,
where `ι` is the summand of the pair of top simplices and `h` is the natural extension of the values
in degree `n`. -/
private def tensorModelHom : (n : ℕ) → ∀ p q : ℕ, p + q = n →
    (R ⊗ S ⟶ ((Δ[p] : SSet.{w}).chainComplex R' ⊗ (Δ[q] : SSet.{w}).chainComplex S').X (n + 1))
  | 0 => fun _ _ _ ↦ 0
  | n + 1 => fun p q h ↦
      ((Δ[p] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _)) ⊗ₘ
          (Δ[q] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _))) ≫ ιTensorObj _ _ p q (n + 1) h ≫
        ((θ (Δ[p]) (Δ[q])).f (n + 1) -
          ((Δ[p] : SSet.{w}).chainComplex R ⊗ (Δ[q] : SSet.{w}).chainComplex S).d (n + 1) n ≫
            tensorExtend (tensorModelHom n) (Δ[p]) (Δ[q])) ≫
        stdSimplex.tensorConeChain p q R' S' (n + 1)

variable {θ}

variable (hθ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
  (chainComplexMap f R ⊗ₘ chainComplexMap g S) ≫ θ K' L' =
    θ K L ≫ (chainComplexMap f R' ⊗ₘ chainComplexMap g S'))
include hθ

/-- The inductive step: if the extension `h` of the model values in degree `n` satisfies
`∂ h ∂ = ∂ θ` in degree `n`, then the extension of the model values in degree `n + 1` satisfies
`∂ h = θ - h ∂` in degree `n + 1`. -/
private lemma tensorExtend_tensorModelHom_succ_d (n : ℕ)
    (hcyc : ∀ K L : SSet.{w}, (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n ≫
        tensorExtend (tensorModelHom θ n) K L ≫
          (K.chainComplex R' ⊗ L.chainComplex S').d (n + 1) n =
      (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n ≫ (θ K L).f n)
    (K L : SSet.{w}) :
    tensorExtend (tensorModelHom θ (n + 1)) K L ≫
        (K.chainComplex R' ⊗ L.chainComplex S').d (n + 2) (n + 1) =
      (θ K L).f (n + 1) - (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n ≫
        tensorExtend (tensorModelHom θ n) K L := by
  -- the map `θ - h ∂` raising degrees by one is natural
  have hnat : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
      (chainComplexMap f R ⊗ₘ chainComplexMap g S).f (n + 1) ≫ ((θ K' L').f (n + 1) -
          (K'.chainComplex R ⊗ L'.chainComplex S).d (n + 1) n ≫
            tensorExtend (tensorModelHom θ n) K' L') =
        ((θ K L).f (n + 1) - (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n ≫
            tensorExtend (tensorModelHom θ n) K L) ≫
          (chainComplexMap f R' ⊗ₘ chainComplexMap g S').f (n + 1) := fun _ _ _ _ f g ↦ by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      ← tensorHom_f_tensorExtend, Hom.comm_assoc, ← HomologicalComplex.comp_f, hθ]
  -- on the models, the chain `(θ - h ∂) (ι)` is a cycle, so the cone on it bounds it
  have hmodel : ∀ p q (h : p + q = n + 1), tensorModelHom θ (n + 1) p q h ≫
      ((Δ[p] : SSet.{w}).chainComplex R' ⊗ (Δ[q] : SSet.{w}).chainComplex S').d (n + 2) (n + 1) =
        ((Δ[p] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _)) ⊗ₘ
          (Δ[q] : SSet.{w}).ιChainComplex (yonedaEquiv (𝟙 _))) ≫ ιTensorObj _ _ p q (n + 1) h ≫
          ((θ (Δ[p]) (Δ[q])).f (n + 1) -
            ((Δ[p] : SSet.{w}).chainComplex R ⊗ (Δ[q] : SSet.{w}).chainComplex S).d (n + 1) n ≫
              tensorExtend (tensorModelHom θ n) (Δ[p]) (Δ[q])) := fun p q h ↦ by
    have hcyc' : ((θ (Δ[p]) (Δ[q])).f (n + 1) -
        ((Δ[p] : SSet.{w}).chainComplex R ⊗ (Δ[q] : SSet.{w}).chainComplex S).d (n + 1) n ≫
          tensorExtend (tensorModelHom θ n) (Δ[p]) (Δ[q])) ≫
        ((Δ[p] : SSet.{w}).chainComplex R' ⊗ (Δ[q] : SSet.{w}).chainComplex S').d (n + 1) n =
          0 := by
      simp only [Preadditive.sub_comp, Category.assoc, Hom.comm, hcyc, sub_self]
    simp only [tensorModelHom, Category.assoc, stdSimplex.tensorConeChain_d, Preadditive.comp_sub,
      Category.comp_id, reassoc_of% hcyc', zero_comp, sub_zero]
  -- by naturality, the identity on a pair of simplices is the image of the identity on the models
  refine mapBifunctor.hom_ext fun p q h ↦ tensorChainComplexX_hom_ext fun x y ↦ ?_
  rw [ι_tensorExtend_assoc, Hom.comm, reassoc_of% hmodel,
    tensorHom_ιTensorObj_comp_eq_model (fun K L ↦ (θ K L).f (n + 1) -
      (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n ≫
        tensorExtend (tensorModelHom θ n) K L) hnat]

variable (h₀ : ∀ K L : SSet.{w}, (θ K L).f 0 = 0)
include h₀

/-- The extension `h` of the model values satisfies `∂ h = θ - h ∂` in every positive degree. -/
private lemma tensorExtend_tensorModelHom_succ_d' (n : ℕ) (K L : SSet.{w}) :
    tensorExtend (tensorModelHom θ (n + 1)) K L ≫
        (K.chainComplex R' ⊗ L.chainComplex S').d (n + 2) (n + 1) =
      (θ K L).f (n + 1) - (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n ≫
        tensorExtend (tensorModelHom θ n) K L := by
  induction n generalizing K L with
  | zero =>
    refine tensorExtend_tensorModelHom_succ_d hθ 0 (fun K L ↦ ?_) K L
    rw [tensorModelHom, tensorExtend_zero, zero_comp, comp_zero, h₀, comp_zero]
  | succ n ih =>
    refine tensorExtend_tensorModelHom_succ_d hθ (n + 1) (fun K L ↦ ?_) K L
    rw [ih, Preadditive.comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp, sub_zero]

end TensorAcyclicModels

section TensorHomotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R S R' S' : C}
  (φ ψ : ∀ K L : SSet.{w},
    K.chainComplex R ⊗ L.chainComplex S ⟶ K.chainComplex R' ⊗ L.chainComplex S')
  (hφ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
    (chainComplexMap f R ⊗ₘ chainComplexMap g S) ≫ φ K' L' =
      φ K L ≫ (chainComplexMap f R' ⊗ₘ chainComplexMap g S'))
  (hψ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
    (chainComplexMap f R ⊗ₘ chainComplexMap g S) ≫ ψ K' L' =
      ψ K L ≫ (chainComplexMap f R' ⊗ₘ chainComplexMap g S'))
  (h₀ : ∀ K L : SSet.{w}, (φ K L).f 0 = (ψ K L).f 0)

/-- **Acyclic models for tensor products of simplicial chains.**  Two families `φ` and `ψ` of chain
maps `C(K; R) ⊗ C(L; S) ⟶ C(K; R') ⊗ C(L; S')`, natural in both simplicial sets and equal in
degree zero, are chain homotopic.  The homotopy is natural in `K` and `L`
(`SSet.tensorChainComplexHomotopy_hom_naturality`). -/
def tensorChainComplexHomotopy (K L : SSet.{w}) : Homotopy (φ K L) (ψ K L) where
  hom i j :=
    if h : i + 1 = j then
      tensorExtend (tensorModelHom (fun K L ↦ φ K L - ψ K L) i) K L ≫ eqToHom (congrArg _ h)
    else 0
  zero _ _ h := dite_eq_right_iff.mpr fun h' ↦ absurd h' h
  comm i := by
    have hθ : ∀ ⦃K K' L L' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L'),
        (chainComplexMap f R ⊗ₘ chainComplexMap g S) ≫ (φ K' L' - ψ K' L') =
          (φ K L - ψ K L) ≫ (chainComplexMap f R' ⊗ₘ chainComplexMap g S') :=
      fun _ _ _ _ f g ↦ by rw [Preadditive.comp_sub, Preadditive.sub_comp, hφ, hψ]
    have h₀' : ∀ K L : SSet.{w}, (φ K L - ψ K L).f 0 = 0 := fun K L ↦ by
      rw [HomologicalComplex.sub_f_apply, h₀, sub_self]
    cases i with
    | zero =>
      simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, ↓reduceDIte,
        eqToHom_refl, Category.comp_id]
      rw [tensorModelHom, tensorExtend_zero, zero_comp, zero_add, zero_add, h₀]
    | succ n =>
      simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, ↓reduceDIte,
        eqToHom_refl, Category.comp_id]
      rw [tensorExtend_tensorModelHom_succ_d' hθ h₀' n K L, HomologicalComplex.sub_f_apply]
      abel

/-- The homotopy of `SSet.tensorChainComplexHomotopy` is natural in both simplicial sets. -/
@[reassoc]
lemma tensorChainComplexHomotopy_hom_naturality {K K' L L' : SSet.{w}} (f : K ⟶ K')
    (g : L ⟶ L') (i j : ℕ) :
    (chainComplexMap f R ⊗ₘ chainComplexMap g S).f i ≫
        (tensorChainComplexHomotopy φ ψ hφ hψ h₀ K' L').hom i j =
      (tensorChainComplexHomotopy φ ψ hφ hψ h₀ K L).hom i j ≫
        (chainComplexMap f R' ⊗ₘ chainComplexMap g S').f j := by
  simp only [tensorChainComplexHomotopy]
  split_ifs with h
  · subst h
    simp only [eqToHom_refl, Category.comp_id]
    exact tensorHom_f_tensorExtend _ f g
  · rw [comp_zero, zero_comp]

end TensorHomotopy

section EilenbergZilberTensor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L : SSet.{w}) (R S : C)

/-- In degree zero, the shuffle map followed by the Alexander–Whitney map is the identity: both
maps send the summand of a pair of vertices `(x, y)` to the summand of the vertex `(x, y)` and
back. -/
@[reassoc (attr := simp)]
lemma shuffle_alexanderWhitney_f_zero :
    (shuffle K L R S).f 0 ≫ (alexanderWhitney K L R S).f 0 = 𝟙 _ := by
  refine mapBifunctor.hom_ext fun p q h ↦ tensorChainComplexX_hom_ext fun x y ↦ ?_
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by simp at h; omega
  -- the identity of the tensor product is not syntactically the identity of the codomain of the
  -- inclusion of a summand
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.comp_id _).symm)
  rw [reassoc_of% (ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero K L R S x y)]
  refine (ιChainComplex_alexanderWhitney_f K L R S (n := 0) (x, y)).trans ?_
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.sub_zero, TauCeti.SimplexCategory.subinterval_zero_eq_id, op_id,
    Functor.map_id_apply]

/-- **The Eilenberg–Zilber homotopy** `AW ∘ shuffle ≃ id`: the shuffle map
`C(K; R) ⊗ C(L; S) ⟶ C(K × L; R ⊗ S)` followed by the Alexander–Whitney map is chain homotopic to
the identity of `C(K; R) ⊗ C(L; S)`.  The homotopy is the one given by acyclic models,
`SSet.tensorChainComplexHomotopy`, and so is natural in `K` and `L`. -/
def shuffleAlexanderWhitneyHomotopy :
    Homotopy (shuffle K L R S ≫ alexanderWhitney K L R S) (𝟙 _) :=
  tensorChainComplexHomotopy (fun K L ↦ shuffle K L R S ≫ alexanderWhitney K L R S)
    (fun _ _ ↦ 𝟙 _)
    (fun _ _ _ _ f g ↦ by
      rw [shuffle_naturality_assoc, alexanderWhitney_naturality, Category.assoc])
    (fun _ _ _ _ _ _ ↦ by rw [Category.comp_id, Category.id_comp])
    (fun _ _ ↦ by simp) K L

/-- **The Eilenberg–Zilber theorem**: the Alexander–Whitney map
`C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)` is a chain homotopy equivalence, with homotopy inverse the
shuffle map. -/
def eilenbergZilberHomotopyEquiv :
    HomotopyEquiv ((K ⊗ L).chainComplex (R ⊗ S)) (K.chainComplex R ⊗ L.chainComplex S) where
  hom := alexanderWhitney K L R S
  inv := shuffle K L R S
  homotopyHomInvId := alexanderWhitneyShuffleHomotopy K L R S
  homotopyInvHomId := shuffleAlexanderWhitneyHomotopy K L R S

@[simp]
lemma eilenbergZilberHomotopyEquiv_hom :
    (eilenbergZilberHomotopyEquiv K L R S).hom = alexanderWhitney K L R S :=
  (rfl)

@[simp]
lemma eilenbergZilberHomotopyEquiv_inv :
    (eilenbergZilberHomotopyEquiv K L R S).inv = shuffle K L R S :=
  (rfl)

end EilenbergZilberTensor

end SSet
