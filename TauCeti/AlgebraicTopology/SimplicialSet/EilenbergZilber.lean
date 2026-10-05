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
# The shuffle map after the Alexander–Whitney map is homotopic to the identity

For simplicial sets `K` and `L`, the composite of the Alexander–Whitney map
`C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)` with the shuffle map back to `C(K × L; R ⊗ S)` is chain
homotopic to the identity (`SSet.alexanderWhitneyShuffleHomotopy`).  This is one half of the
Eilenberg–Zilber theorem.  The composite is in general not the identity on unnormalized chains:
already for a `1`-simplex `x` of `K` and a vertex `y` of `L`, the summand of the `1`-simplex
`(x, s₀ y)` of `K × L` is sent to itself plus the summand of the degenerate `1`-simplex
`(s₀ x₀, s₀ y)`, where `x₀` is the initial vertex of `x`.

The homotopy comes from the method of acyclic models, in the following form
(`SSet.prodChainComplexHomotopy`).  Let `φ` and `ψ` be families of chain maps
`C(K × L; T) ⟶ C(K × L; T')`, natural in maps `K ⟶ K'` and `L ⟶ L'`, which agree in degree zero.
Then `φ` and `ψ` are chain homotopic, through a homotopy natural in `K` and `L`
(`SSet.prodChainComplexHomotopy_hom_naturality`).  An `n`-simplex `(x, y)` of `K × L` is the image
of the diagonal `n`-simplex of the model `Δ[n] × Δ[n]` under the map classifying `(x, y)`, so by
naturality the homotopy is determined by its values on these diagonal simplices.  These values are
built by induction on `n`: the chain that the homotopy must bound on the model is a cycle by the
inductive hypothesis, and the cone from the vertex `(0, 0)` of `Δ[n] × Δ[n]`
(`SSet.stdSimplex.prodConeChain`) bounds it, because this cone is a contracting homotopy in
positive degrees.

## Main definitions and results

* `SSet.prodChainComplexHomotopy`: two natural families of chain maps on the simplicial chains of
  products which agree in degree zero are chain homotopic.
* `SSet.prodChainComplexHomotopy_hom_naturality`: the homotopy is natural in both simplicial sets.
* `SSet.alexanderWhitney_shuffle_f_zero`: the Alexander–Whitney map followed by the shuffle map is
  the identity in degree zero.
* `SSet.alexanderWhitneyShuffleHomotopy`: the Alexander–Whitney map followed by the shuffle map is
  chain homotopic to the identity.

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

end SSet
