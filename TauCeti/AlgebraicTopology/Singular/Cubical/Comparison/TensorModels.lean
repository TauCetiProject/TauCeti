/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Models
public import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# The models of the tensor product of normalized cubical chains

The functor `N(X) ⊗ N(Y)` on pairs of spaces, with `N` the normalized cubical chains, is free on
the models `(Iᵖ, I^q)`, one for each pair of degrees `p + q = n`, in degree `n`
(`TauCeti.AcyclicModels.MultiModelPresentation`): a chain of the summand `Nₚ(X) ⊗ N_q(Y)` is
a combination of the images of the generator `[Iᵖ] ⊗ [I^q]` under the pairs of maps
`(Iᵖ, I^q) ⟶ (X, Y)`, with the coefficients of the two factors
(`TauCeti.cubicalModelPresentation`).  The simplicial singular chains of the product are acyclic
on these models, since a product of cubes is contractible.  This is the input to the method of
acyclic models for natural maps out of the tensor product.

## Main definitions

* `TauCeti.cubicalTensor k`: the functor `(X, Y) ↦ N(X; k) ⊗ N(Y; k)` on pairs of spaces.
* `TauCeti.cubicalTensorModelPresentation k`: its presentation on the models `(Iᵖ, I^q)`.
* `TauCeti.singularChainsProduct k`: the singular chains of the product, as a functor on pairs of
  spaces.
* `TauCeti.isAcyclicOnMulti_singularChainsProduct`: it is acyclic on any family of models with
  contractible products, in particular on these.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits Finsupp TensorProduct

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

/-- The functor `(X, Y) ↦ N(X; k) ⊗ N(Y; k)`, the tensor product of the normalized cubical chain
complexes, on pairs of spaces. -/
abbrev cubicalTensor : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  (normalizedCubicalChainComplex.{u} k).prod (normalizedCubicalChainComplex.{u} k) ⋙
    MonoidalCategory.tensor _

/-- The bidegrees `(p, q)` with `p + q = n`: the index of the models in degree `n`. -/
abbrev BidegreeIndex (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- The only bidegree of total degree `0` is `(0, 0)`. -/
theorem BidegreeIndex.eq_mk_zero_zero (i : BidegreeIndex 0) : i = ⟨(0, 0), rfl⟩ := by
  obtain ⟨⟨p, q⟩, h⟩ := i
  have h' : p + q = 0 := h
  exact Subtype.ext (Prod.ext (by simp only; omega) (by simp only; omega))

/-- The model of bidegree `(p, q)`: the pair of cubes `(Iᵖ, I^q)`. -/
abbrev cubicalBidegreeModel (n : ℕ) (i : BidegreeIndex n) : TopCat.{u} × TopCat.{u} :=
  (cubeModel.{u} i.1.1, cubeModel.{u} i.1.2)

variable {k}

/-- The coefficients of the tensor product of a normalized cubical chain of `X` of degree `p`
and of one of `Y` of degree `q` on the pairs of maps from the models: the product of the
coefficients of the factors. -/
def cubicalTensorSummandCoord (X Y : TopCat.{u}) (n p q : ℕ) (h : p + q = n) :
    NormalizedCubicalChain X k p ⊗[k] NormalizedCubicalChain Y k q →ₗ[k]
      ((Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ (X, Y))) →₀ k) :=
  lmapDomain k k (fun st : (cubeModel.{u} p ⟶ X) × (cubeModel.{u} q ⟶ Y) ↦
      (⟨⟨(p, q), h⟩, (st.1, st.2)⟩ :
        Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ (X, Y)))) ∘ₗ
    (finsuppTensorFinsupp' k _ _).toLinearMap ∘ₗ
    TensorProduct.map (cubicalCoord k X p) (cubicalCoord k Y q)

variable (k) in
/-- The coefficients of a chain of the tensor product in degree `n`, on the pairs of maps from the
models. -/
def cubicalTensorCoord (X : TopCat.{u} × TopCat.{u}) (n : ℕ) :
    ((cubicalTensor k).obj X).X n →ₗ[k]
      ((Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X)) →₀ k) :=
  (mapBifunctorDesc (A := ModuleCat.of k
      ((Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X)) →₀ k))
    (K₁ := (normalizedCubicalChainComplex.{u} k).obj X.1)
    (K₂ := (normalizedCubicalChainComplex.{u} k).obj X.2)
    (fun p q h ↦ ModuleCat.ofHom (cubicalTensorSummandCoord X.1 X.2 n p q h))).hom

variable (k) in
/-- The generator in bidegree `(p, q)`: the tensor product of the identity cubes of `Iᵖ` and
`I^q`, in the summand of bidegree `(p, q)`. -/
def cubicalTensorGen (n : ℕ) (i : BidegreeIndex n) :
    ((cubicalTensor k).obj (cubicalBidegreeModel.{u} n i)).X n :=
  (ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} i.1.1))
      ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} i.1.2)) i.1.1 i.1.2 n i.2).hom
    (NormalizedCubicalChain.ofCube (cubeModel.{u} i.1.1) k (upCube i.1.1) ⊗ₜ[k]
      NormalizedCubicalChain.ofCube (cubeModel.{u} i.1.2) k (upCube i.1.2))

/-- The generator is the image of the tensor product of the two identity cubes. -/
theorem cubicalTensorGen_def (n : ℕ) (i : BidegreeIndex n) :
    cubicalTensorGen k n i =
      (ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} i.1.1))
          ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} i.1.2)) i.1.1 i.1.2 n i.2).hom
        (NormalizedCubicalChain.ofCube (cubeModel.{u} i.1.1) k (upCube i.1.1) ⊗ₜ[k]
          NormalizedCubicalChain.ofCube (cubeModel.{u} i.1.2) k (upCube i.1.2)) :=
  (rfl)

/-- The coefficients of a chain of a summand of the tensor product are those of the summand. -/
-- Not a simp lemma: `simp` rewrites the types of both sides (the abbreviations `cubicalTensor` and
-- `cubicalBidegreeModel`), so the left-hand side is not in simp normal form.
theorem cubicalTensorCoord_ι (X : TopCat.{u} × TopCat.{u}) (n p q : ℕ) (h : p + q = n)
    (z : NormalizedCubicalChain X.1 k p ⊗[k] NormalizedCubicalChain X.2 k q) :
    cubicalTensorCoord k X n
        ((ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj X.1)
          ((normalizedCubicalChainComplex.{u} k).obj X.2) p q n h).hom z) =
      cubicalTensorSummandCoord X.1 X.2 n p q h z := by
  have e := ι_mapBifunctorDesc (K₁ := (normalizedCubicalChainComplex.{u} k).obj X.1)
    (K₂ := (normalizedCubicalChainComplex.{u} k).obj X.2) (F := curriedTensor (ModuleCat.{u} k))
    (c := ComplexShape.down ℕ)
    (f := fun p q h ↦ ModuleCat.ofHom (cubicalTensorSummandCoord X.1 X.2 n p q h)) p q h
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e) z

/-- The map induced on a pure tensor of a summand of the tensor product by a pair of maps is the
tensor product of the images of the factors. -/
theorem cubicalTensor_map_ι {X Y : TopCat.{u} × TopCat.{u}} (f : X ⟶ Y) (n p q : ℕ) (h : p + q = n)
    (a : NormalizedCubicalChain X.1 k p) (b : NormalizedCubicalChain X.2 k q) :
    ((cubicalTensor k).map f).f n
        ((ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj X.1)
          ((normalizedCubicalChainComplex.{u} k).obj X.2) p q n h).hom (a ⊗ₜ[k] b)) =
      (ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj Y.1)
          ((normalizedCubicalChainComplex.{u} k).obj Y.2) p q n h).hom
        ((((normalizedCubicalChainComplex.{u} k).map f.1).f p a) ⊗ₜ[k]
          (((normalizedCubicalChainComplex.{u} k).map f.2).f q b)) :=
  HomologicalComplex.ι_tensorHom_apply ((normalizedCubicalChainComplex.{u} k).map f.1)
    ((normalizedCubicalChainComplex.{u} k).map f.2) p q n h a b

/-- The coefficients of a tensor of two chains are the tensor product of their coefficients. -/
theorem cubicalTensorSummandCoord_tmul (X Y : TopCat.{u}) (n p q : ℕ) (h : p + q = n)
    (a : NormalizedCubicalChain X k p) (b : NormalizedCubicalChain Y k q) :
    cubicalTensorSummandCoord X Y n p q h (a ⊗ₜ[k] b) =
      mapDomain (fun st : (cubeModel.{u} p ⟶ X) × (cubeModel.{u} q ⟶ Y) ↦
        (⟨⟨(p, q), h⟩, (st.1, st.2)⟩ :
          Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ (X, Y))))
        (finsuppTensorFinsupp' k _ _ (cubicalCoord k X p a ⊗ₜ[k] cubicalCoord k Y q b)) :=
  (rfl)

/-- The coefficients of the tensor of the images of two chains under maps of spaces are those of
the chains, pushed forward by the composition with the maps. -/
theorem cubicalTensorSummandCoord_map {X X' Y Y' : TopCat.{u}} (f₁ : X ⟶ X') (f₂ : Y ⟶ Y')
    (n p q : ℕ)
    (h : p + q = n) (a : NormalizedCubicalChain X k p) (b : NormalizedCubicalChain Y k q) :
    cubicalTensorSummandCoord X' Y' n p q h
        (NormalizedCubicalChain.map k f₁.hom p a ⊗ₜ[k] NormalizedCubicalChain.map k f₂.hom q b) =
      mapDomain (fun s : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ (X, Y)) ↦
        (⟨s.1, s.2 ≫ ((f₁, f₂) : (X, Y) ⟶ (X', Y'))⟩ :
          Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ (X', Y'))))
        (cubicalTensorSummandCoord X Y n p q h (a ⊗ₜ[k] b)) := by
  rw [cubicalTensorSummandCoord_tmul, cubicalTensorSummandCoord_tmul, cubicalCoord_map,
    cubicalCoord_map,
    finsuppTensorFinsupp'_mapDomain, ← mapDomain_comp, ← mapDomain_comp]
  -- both sides push the coefficients forward along `(σ, τ) ↦ ⟨(p, q), (σ ≫ f₁, τ ≫ f₂)⟩`; the
  -- composition in the product category is componentwise by definition
  rfl

/-- The coefficients of the tensor product are natural. -/
theorem cubicalTensorCoord_map {X Y : TopCat.{u} × TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : ((cubicalTensor k).obj X).X n) :
    cubicalTensorCoord k Y n (((cubicalTensor k).map f).f n x) =
      mapDomain (fun s : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X) ↦
        (⟨s.1, s.2 ≫ f⟩ : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ Y)))
        (cubicalTensorCoord k X n x) := by
  have key : ((cubicalTensor k).map f).f n ≫ ModuleCat.ofHom (cubicalTensorCoord k Y n) =
      ModuleCat.ofHom (cubicalTensorCoord k X n) ≫ ModuleCat.ofHom (lmapDomain k k
        (fun s : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X) ↦
          (⟨s.1, s.2 ≫ f⟩ : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ Y)))) := by
    refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
    refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
    -- the goal is `coord (F f (ι (a ⊗ b))) = mapDomain _ (coord (ι (a ⊗ b)))`, a statement about
    -- the composite morphisms evaluated on `a ⊗ b`, which `exact` unfolds
    exact (congrArg (cubicalTensorCoord k Y n) (cubicalTensor_map_ι f n p q h a b)).trans
      ((cubicalTensorCoord_ι Y n p q h _).trans
        ((cubicalTensorSummandCoord_map f.1 f.2 n p q h a b).trans
        (congrArg (lmapDomain k k _) (cubicalTensorCoord_ι X n p q h (a ⊗ₜ[k] b))).symm))
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom key) x

/-- The image of the generator of bidegree `(p, q)` under a pair of maps is the tensor product of
the images of the identity cubes. -/
theorem map_cubicalTensorGen (X : TopCat.{u} × TopCat.{u}) (n p q : ℕ) (h : p + q = n)
    (σ : cubeModel.{u} p ⟶ X.1) (τ : cubeModel.{u} q ⟶ X.2) :
    ((cubicalTensor k).map ((σ, τ) : cubicalBidegreeModel.{u} n ⟨(p, q), h⟩ ⟶ X)).f n
        (cubicalTensorGen k n ⟨(p, q), h⟩) =
      (ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj X.1)
          ((normalizedCubicalChainComplex.{u} k).obj X.2) p q n h).hom
        (NormalizedCubicalChain.map k σ.hom p
            (NormalizedCubicalChain.ofCube (cubeModel.{u} p) k (upCube p)) ⊗ₜ[k]
          NormalizedCubicalChain.map k τ.hom q
            (NormalizedCubicalChain.ofCube (cubeModel.{u} q) k (upCube q))) :=
  cubicalTensor_map_ι ((σ, τ) : cubicalBidegreeModel.{u} n ⟨(p, q), h⟩ ⟶ X) n p q h _ _

variable (k) in
/-- The inclusion of the summand of bidegree `(p, q)` into the tensor product, as a linear map out
of the tensor product of the chains. -/
-- A proof-internal name for `(ιTensorObj …).hom`, which keeps the instances of the tensor product
-- of chains visible to `simp`.
private def summandInclusion (X : TopCat.{u} × TopCat.{u}) (n p q : ℕ) (h : p + q = n) :
    NormalizedCubicalChain X.1 k p ⊗[k] NormalizedCubicalChain X.2 k q →ₗ[k]
      ((cubicalTensor k).obj X).X n :=
  (ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj X.1)
    ((normalizedCubicalChainComplex.{u} k).obj X.2) p q n h).hom

/-- The combination of the images of the generators with the coefficients `c ⊗ d` is the tensor
product of the combinations of the images of the identity cubes. -/
private theorem linearCombination_cubicalTensorSummand (X : TopCat.{u} × TopCat.{u})
    (n p q : ℕ) (h : p + q = n)
    (c : (cubeModel.{u} p ⟶ X.1) →₀ k) (d : (cubeModel.{u} q ⟶ X.2) →₀ k) :
    linearCombination k (fun s : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X) ↦
        ((cubicalTensor k).map s.2).f n (cubicalTensorGen k n s.1))
      (mapDomain (fun st : (cubeModel.{u} p ⟶ X.1) × (cubeModel.{u} q ⟶ X.2) ↦
        (⟨⟨(p, q), h⟩, (st.1, st.2)⟩ : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X)))
        (finsuppTensorFinsupp' k _ _ (c ⊗ₜ[k] d))) =
      summandInclusion k X n p q h
        (linearCombination k (fun σ : cubeModel.{u} p ⟶ X.1 ↦ NormalizedCubicalChain.map k σ.hom p
            (NormalizedCubicalChain.ofCube (cubeModel.{u} p) k (upCube p))) c ⊗ₜ[k]
          linearCombination k (fun τ : cubeModel.{u} q ⟶ X.2 ↦ NormalizedCubicalChain.map k τ.hom q
            (NormalizedCubicalChain.ofCube (cubeModel.{u} q) k (upCube q))) d) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
    simp only [add_tmul, map_add, mapDomain_add, h₁, h₂]
  | single σ s =>
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d₁ d₂ h₁ h₂ => simp only [tmul_add, map_add, mapDomain_add, h₁, h₂]
    | single τ t =>
      rw [finsuppTensorFinsupp'_single_tmul_single, mapDomain_single, linearCombination_single,
        linearCombination_single, linearCombination_single, smul_tmul_smul, map_smul]
      exact congrArg ((s * t) • ·) (map_cubicalTensorGen X n p q h σ τ)

/-- A summand chain is the combination of the images of the generators with its coefficients. -/
private theorem linearCombination_cubicalTensorSummandCoord (X : TopCat.{u} × TopCat.{u})
    (n p q : ℕ) (h : p + q = n)
    (a : NormalizedCubicalChain X.1 k p) (b : NormalizedCubicalChain X.2 k q) :
    linearCombination k (fun s : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X) ↦
        ((cubicalTensor k).map s.2).f n (cubicalTensorGen k n s.1))
      (cubicalTensorSummandCoord X.1 X.2 n p q h (a ⊗ₜ[k] b)) =
      summandInclusion k X n p q h (a ⊗ₜ[k] b) := by
  -- a normalized cubical chain is the combination of the images of the identity cube with its
  -- coefficients
  have key : ∀ (Z : TopCat.{u}) (m : ℕ) (x : NormalizedCubicalChain Z k m),
      linearCombination k (fun σ : cubeModel.{u} m ⟶ Z ↦ NormalizedCubicalChain.map k σ.hom m
        (NormalizedCubicalChain.ofCube (cubeModel.{u} m) k (upCube m))) (cubicalCoord k Z m x) =
        x := fun Z m x ↦ by
    rw [linearCombination_apply]
    exact sum_cubicalCoord x
  rw [cubicalTensorSummandCoord_tmul, linearCombination_cubicalTensorSummand, key, key]

/-- Every chain of the tensor product is the combination of the images of the generators with its
coefficients. -/
theorem sum_cubicalTensorCoord (X : TopCat.{u} × TopCat.{u}) (n : ℕ)
    (x : ((cubicalTensor k).obj X).X n) :
    (cubicalTensorCoord k X n x).sum (fun s a ↦
      a • ((cubicalTensor k).map s.2).f n (cubicalTensorGen k n s.1)) = x := by
  have key : ModuleCat.ofHom (cubicalTensorCoord k X n) ≫ ModuleCat.ofHom
      (linearCombination k (fun s : Σ i : BidegreeIndex n, (cubicalBidegreeModel.{u} n i ⟶ X) ↦
        ((cubicalTensor k).map s.2).f n (cubicalTensorGen k n s.1))) = 𝟙 _ := by
    refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
    refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
    -- the goal is `lc (coord (ι (a ⊗ b))) = ι (a ⊗ b)`, with `ι = summandInclusion`
    have e : cubicalTensorCoord k X n (summandInclusion k X n p q h (a ⊗ₜ[k] b)) =
        cubicalTensorSummandCoord X.1 X.2 n p q h (a ⊗ₜ[k] b) := cubicalTensorCoord_ι X n p q h _
    exact (congrArg (linearCombination k _) e).trans
      (linearCombination_cubicalTensorSummandCoord X n p q h a b)
  exact (linearCombination_apply _ _).symm.trans
    (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom key) x)

variable (k) in
/-- **The tensor product of the normalized cubical chains is free on the pairs of cubes**: in
degree `n`, on the models `(Iᵖ, I^q)` with `p + q = n`. -/
-- The body is exposed so that `.model n i` reduces to `cubicalBidegreeModel n i` in the statements
-- of `cubicalTensorModelPresentation_gen` and `_coord`.
@[expose] def cubicalTensorModelPresentation :
    AcyclicModels.MultiModelPresentation (cubicalTensor.{u} k) BidegreeIndex where
  model := cubicalBidegreeModel
  gen := cubicalTensorGen k
  coord := cubicalTensorCoord k
  coord_map f n x := cubicalTensorCoord_map f n x
  sum_coord X n x := sum_cubicalTensorCoord X n x

/-- The models of `cubicalTensorModelPresentation` are the pairs of cubes. -/
@[simp]
theorem cubicalTensorModelPresentation_model (n : ℕ) (i : BidegreeIndex n) :
    (cubicalTensorModelPresentation.{u} k).model n i = cubicalBidegreeModel n i :=
  (rfl)

/-- The generators of `cubicalTensorModelPresentation` are the tensor products of the identity
cubes. -/
@[simp]
theorem cubicalTensorModelPresentation_gen (n : ℕ) (i : BidegreeIndex n) :
    (cubicalTensorModelPresentation.{u} k).gen n i = cubicalTensorGen k n i :=
  (rfl)

/-- The coefficients of `cubicalTensorModelPresentation` are `cubicalTensorCoord`. -/
@[simp]
theorem cubicalTensorModelPresentation_coord (X : TopCat.{u} × TopCat.{u}) (n : ℕ) :
    (cubicalTensorModelPresentation.{u} k).coord X n = cubicalTensorCoord k X n :=
  (rfl)

/-- The simplicial singular chains of the product of the two spaces, as a functor on pairs of
spaces. -/
abbrev singularChainsProduct (k : Type u) [Ring k] :
    TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  MonoidalCategory.tensor TopCat.{u} ⋙ singularChains k

/-- The product of two cubes is contractible. -/
instance (p q : ℕ) :
    ContractibleSpace
      ((MonoidalCategory.tensor TopCat.{u}).obj (cubeModel.{u} p, cubeModel.{u} q)) :=
  inferInstanceAs (ContractibleSpace (cubeModel.{u} p × cubeModel.{u} q))

/-- **The simplicial singular chains of the product are acyclic on any family of models whose
products are contractible.** -/
theorem isAcyclicOnMulti_singularChainsProduct (k : Type u) [Ring k] {ι : ℕ → Type*}
    (M : ∀ n, ι n → TopCat.{u} × TopCat.{u})
    [∀ n i, ContractibleSpace ((MonoidalCategory.tensor TopCat.{u}).obj (M n i))] :
    AcyclicModels.IsAcyclicOnMulti (singularChainsProduct k) M
      (fun X ↦ singularAugment k (X.1 ⊗ X.2)) where
  exists_d_eq_of_d_eq_zero n i q z hz :=
    singularChains_exists_d_eq_of_d_eq_zero
      ((MonoidalCategory.tensor TopCat.{u}).obj (M n i)) q z hz
  exists_d_eq_of_augment_eq_zero n i z hz :=
    singularChains_exists_d_eq_of_augment_eq_zero
      ((MonoidalCategory.tensor TopCat.{u}).obj (M n i)) z hz

variable (k) in
/-- **The simplicial singular chains of the product are acyclic on the models of the tensor
product of the normalized cubical chains**, since a product of cubes is contractible. -/
theorem isAcyclicOnMulti_singularChainsProduct_cubicalTensorModelPresentation :
    AcyclicModels.IsAcyclicOnMulti (singularChainsProduct k)
      (cubicalTensorModelPresentation.{u} k).model
      (fun X ↦ singularAugment k (X.1 ⊗ X.2)) :=
  isAcyclicOnMulti_singularChainsProduct k (fun n i ↦ cubicalBidegreeModel.{u} n i)

end TauCeti

end

end
