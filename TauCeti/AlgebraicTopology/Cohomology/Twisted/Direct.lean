/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Singular cochains with local coefficients

A cochain with coefficients in `L` assigns to every singular simplex an element of the fibre
at its initial vertex. Reindexing pulls back this family and transports its values back to the
original initial vertex. In particular the zeroth coface transports from vertex one to vertex
zero. The alternating coface differential therefore defines cohomology with values in `L`
itself, without a dualizability hypothesis on its fibres.

This differs from `LocalCoefficientSystem.twistedCochainComplex` in
`Cohomology/Twisted/Basic`, which applies a fixed-module Hom functor to `L`-twisted chains
and hence uses the corresponding dual coefficient system.

The construction follows Hatcher, *Algebraic Topology*, Section 3.H. Its transport identities
come from `Singular/Twisted/Basic`; the differential and its square-zero proof use Mathlib's
`AlgebraicTopology.alternatingCofaceMapComplex`.
-/

public section

noncomputable section

open CategoryTheory SimplexCategory
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
variable (L : LocalCoefficientSystem.{u, v, w} R X)

/-- All families of simplex coefficients, with no finite-support restriction. -/
abbrev cochainsAt (n : SimplexCategory) : ModuleCat.{max v w} R :=
  ModuleCat.of R (∀ σ : (TopCat.toSSet.obj X).obj (Opposite.op n), L.obj (initialVertex σ))

/-- Pullback of a cochain along a simplex reindexing, transporting back to the initial vertex. -/
def cochainsMap {m n : SimplexCategory} (α : m ⟶ n) : cochainsAt L m ⟶ cochainsAt L n :=
  ModuleCat.ofHom (LinearMap.pi fun σ ↦
    (L.map (inv (vertexTransport α.op σ))).hom.comp
      (LinearMap.proj ((TopCat.toSSet.obj X).map α.op σ)))

/-- Reindexing evaluates the original cochain on the reindexed simplex and transports back. -/
@[simp↓]
lemma cochainsMap_apply {m n : SimplexCategory} (α : m ⟶ n) (c : cochainsAt L m)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op n)) :
    cochainsMap L α c σ =
      L.map (inv (vertexTransport α.op σ)) (c ((TopCat.toSSet.obj X).map α.op σ)) := (rfl)

private lemma eqToHom_family_apply {n : SimplexCategory} (c : cochainsAt L n)
    {τ σ : (TopCat.toSSet.obj X).obj (Opposite.op n)} (h : τ = σ) :
    eqToHom (congrArg (fun ρ ↦ L.obj (initialVertex ρ)) h) (c τ) = c σ := by
  subst h
  rfl

private lemma cochainsMap_id (n : SimplexCategory) : cochainsMap L (𝟙 n) = 𝟙 _ := by
  ext c σ
  dsimp only [cochainsMap, ModuleCat.hom_ofHom, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  simp only [op_id, vertexTransport_id, inv_eqToHom, eqToHom_map]
  have h : (TopCat.toSSet.obj X).map (𝟙 (Opposite.op n)) σ = σ := by simp
  exact eqToHom_family_apply L c h

private lemma cochainsMap_comp {m n p : SimplexCategory} (α : m ⟶ n) (β : n ⟶ p) :
    cochainsMap L (α ≫ β) = cochainsMap L α ≫ cochainsMap L β := by
  ext c σ
  dsimp only [cochainsMap, ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  have hσ : (TopCat.toSSet.obj X).map (α ≫ β).op σ =
      (TopCat.toSSet.obj X).map α.op ((TopCat.toSSet.obj X).map β.op σ) := by simp
  have h := congrArg (fun f ↦ L.map (inv f)) (vertexTransport_comp β.op α.op σ)
  simp only [IsIso.inv_comp, inv_eqToHom, Functor.map_comp, eqToHom_map] at h
  rw [← ModuleCat.comp_apply, h, ModuleCat.comp_apply]
  rw [← eqToHom_family_apply L c hσ]
  simp only [← ModuleCat.comp_apply, eqToHom_trans, eqToHom_refl, ModuleCat.id_apply]
  -- Composition of the fibre maps evaluates as composition of their underlying linear maps.
  rfl

/-- The cosimplicial module of singular cochains valued in `L`. -/
def cochains : CosimplicialObject (ModuleCat.{max v w} R) where
  obj := cochainsAt L
  map := cochainsMap L
  map_id := cochainsMap_id L
  map_comp := cochainsMap_comp L

/-- The degree objects of local cochains are dependent products of the simplex fibres. -/
lemma cochains_obj (n : SimplexCategory) : (cochains L).obj n = cochainsAt L n := (rfl)

/-- A cosimplicial structure map is pullback followed by inverse vertex transport. -/
lemma cochains_map {m n : SimplexCategory} (α : m ⟶ n) :
    (cochains L).map α =
      eqToHom (cochains_obj L m) ≫ cochainsMap L α ≫
        eqToHom (cochains_obj L n).symm := (rfl)

/-- After identifying the degree objects with coefficient families, a cosimplicial map
pulls back simplex values and transports them back to the initial vertex. -/
-- Keep this as a named rewrite so `Functor.map_comp` can simplify the map first.
lemma cochains_map_apply {m n : SimplexCategory} (α : m ⟶ n) (c : cochainsAt L m)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op n)) :
    eqToHom (cochains_obj L n)
        ((cochains L).map α (eqToHom (cochains_obj L m).symm c)) σ =
      L.map (inv (vertexTransport α.op σ)) (c ((TopCat.toSSet.obj X).map α.op σ)) := (rfl)

/-- The singular cochain complex with values in the local coefficient system `L`. -/
def cochainComplex : CochainComplex (ModuleCat.{max v w} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (cochains L)

/-- Evaluation of a local cochain on one simplex. -/
def cochainComplexEval (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (cochainComplex L).X n →ₗ[R] L.obj (initialVertex σ) :=
  LinearMap.proj σ

/-- A degree of the cochain complex is the module of all families of simplex coefficients. -/
def cochainComplexXIso (n : ℕ) :
    (cochainComplex L).X n ≅ cochainsAt L ⦋n⦌ := Iso.refl _

/-- A family inserted into the complex has its prescribed simplex values. -/
@[simp↓]
lemma cochainComplexXIso_inv_eval (n : ℕ) (c : cochainsAt L ⦋n⦌)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    cochainComplexEval L n σ ((cochainComplexXIso L n).inv c) = c σ := (rfl)

/-- The family associated to a cochain consists of its simplex evaluations. -/
@[simp↓]
lemma cochainComplexXIso_hom_apply (n : ℕ) (c : (cochainComplex L).X n)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (cochainComplexXIso L n).hom c σ = cochainComplexEval L n σ c := (rfl)

/-- Cochains are determined by their values on every singular simplex. -/
@[ext]
lemma cochainComplex_ext {n : ℕ} {c d : (cochainComplex L).X n}
    (h : ∀ σ, cochainComplexEval L n σ c = cochainComplexEval L n σ d) : c = d :=
  funext h

/-- The differential is the alternating sum of the face values, transported back to the
initial vertex of the original simplex. -/
lemma cochainComplex_d_eval (n : ℕ) (c : (cochainComplex L).X n)
    (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    cochainComplexEval L (n + 1) σ ((cochainComplex L).d n (n + 1) c) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        L.map (inv (vertexTransport (δ i).op σ))
          (cochainComplexEval L n ((TopCat.toSSet.obj X).map (δ i).op σ) c) := by
  -- Expose the dependent-product carrier so evaluation uses its native module instances.
  dsimp only [cochainComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, cochains, cochainsAt] at c
  -- Reduce the adjacent differential to Mathlib's public coface sum using
  -- `CochainComplex.of_d`.
  simp only [cochainComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, cochains, CosimplicialObject.δ,
    cochainComplexEval, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cochainsMap L (δ i)).hom) c σ = _
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
    (cochainsMap_apply L (δ i) c σ)

/-- Every nonzeroth face preserves the initial vertex, so its cochain pullback only identifies
the two equal fibres. -/
lemma cochainsMap_δ_of_ne_zero {n : ℕ} {i : Fin (n + 2)} (hi : i ≠ 0)
    (c : cochainsAt L ⦋n⦌) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    cochainsMap L (δ i) c σ =
      eqToHom (congrArg L.obj
        (initialVertex_eq_initialVertex_map (δ i).op σ (δ_toOrderHom_zero hi)).symm)
        (c ((TopCat.toSSet.obj X).map (δ i).op σ)) := by
  dsimp only [cochainsMap, ModuleCat.hom_ofHom, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  simp only [vertexTransport_eq_eqToHom (δ i).op σ (δ_toOrderHom_zero hi),
    inv_eqToHom, eqToHom_map]

/-- The zeroth face transports its value from vertex one back to vertex zero. -/
lemma cochainsMap_δ_zero (n : ℕ) (c : cochainsAt L ⦋n⦌)
    (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    cochainsMap L (δ (0 : Fin (n + 2))) c σ =
      L.map (pathTransport σ (toTop.map (δ (0 : Fin (n + 2))) (toTopInitialVertex ⦋n⦌))
        (toTopInitialVertex ⦋n + 1⦌))
          (c ((TopCat.toSSet.obj X).map (δ (0 : Fin (n + 2))).op σ)) := by
  have h : inv (vertexTransport (δ (0 : Fin (n + 2))).op σ) =
      pathTransport σ (toTop.map (δ (0 : Fin (n + 2))) (toTopInitialVertex ⦋n⦌))
        (toTopInitialVertex ⦋n + 1⦌) := by
    apply IsIso.inv_eq_of_hom_inv_id
    simp only [vertexTransport_def, Quiver.Hom.unop_op]
    exact (pathTransport_comp σ _ _ _).trans (pathTransport_self σ _)
  exact congrArg (fun f ↦ L.map f
    (c ((TopCat.toSSet.obj X).map (δ (0 : Fin (n + 2))).op σ))) h

variable {L} {K N : LocalCoefficientSystem.{u, v, w} R X}

/-- A morphism of coefficient systems acts on every simplex value by its fibre map. -/
def cochainsCoefficientMap (η : L ⟶ K) : cochains L ⟶ cochains K where
  app n := ModuleCat.ofHom (LinearMap.pi fun σ ↦
    (η.app (initialVertex σ)).hom.comp (LinearMap.proj σ))
  naturality {m n} α := by
    dsimp only [cochains]
    ext c σ
    dsimp only [cochains, cochainsMap, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact congrArg (fun f ↦ f (c ((TopCat.toSSet.obj X).map α.op σ)))
      (η.naturality (inv (vertexTransport α.op σ)))

/-- The component of a coefficient-system morphism is the product of its fibre maps. -/
lemma cochainsCoefficientMap_app (η : L ⟶ K) (n : SimplexCategory) :
    (cochainsCoefficientMap η).app n = eqToHom (cochains_obj L n) ≫ ModuleCat.ofHom
      (LinearMap.pi fun σ : (TopCat.toSSet.obj X).obj (Opposite.op n) ↦
        (η.app (initialVertex σ)).hom.comp (LinearMap.proj σ)) ≫
      eqToHom (cochains_obj K n).symm := (rfl)

/-- After identifying the degree objects with coefficient families, the coefficient map
acts on each value by the corresponding fibre map. -/
@[simp↓]
lemma cochainsCoefficientMap_app_apply (η : L ⟶ K) (n : SimplexCategory)
    (c : cochainsAt L n) (σ : (TopCat.toSSet.obj X).obj (Opposite.op n)) :
    eqToHom (cochains_obj K n)
        ((cochainsCoefficientMap η).app n (eqToHom (cochains_obj L n).symm c)) σ =
      η.app (initialVertex σ) (c σ) := (rfl)

/-- Singular cochains as a functor of the coefficient system. -/
def cochainsFunctor : LocalCoefficientSystem.{u, v, w} R X ⥤
    CosimplicialObject (ModuleCat.{max v w} R) where
  obj := cochains
  map := cochainsCoefficientMap
  map_id L := by
    apply NatTrans.ext
    funext n
    dsimp only [cochains]
    ext c σ
    rfl
  map_comp η θ := by
    apply NatTrans.ext
    funext n
    dsimp only [cochains]
    ext c σ
    rfl

/-- The coefficient functor sends a system to its cosimplicial module of cochains. -/
lemma cochainsFunctor_obj (L : LocalCoefficientSystem.{u, v, w} R X) :
    (cochainsFunctor (R := R) (X := X)).obj L = cochains L := (rfl)

/-- The coefficient functor acts by the fibrewise coefficient map. -/
lemma cochainsFunctor_map (η : L ⟶ K) :
    (cochainsFunctor (R := R) (X := X)).map η =
      eqToHom (cochainsFunctor_obj L) ≫ cochainsCoefficientMap η ≫
        eqToHom (cochainsFunctor_obj K).symm := (rfl)

/-- The coefficient functor applies the fibre map to each simplex value. The explicit
identifications cross the opaque functor-object and degree-object presentations. -/
-- Keep this as a named rewrite so `Functor.map_comp` can simplify the map first.
lemma cochainsFunctor_map_app_apply (η : L ⟶ K) (n : SimplexCategory)
    (c : cochainsAt L n) (σ : (TopCat.toSSet.obj X).obj (Opposite.op n)) :
    eqToHom (cochains_obj K n)
        (((eqToHom (cochainsFunctor_obj L).symm ≫
          (cochainsFunctor (R := R) (X := X)).map η ≫
          eqToHom (cochainsFunctor_obj K)).app n)
            (eqToHom (cochains_obj L n).symm c)) σ =
      η.app (initialVertex σ) (c σ) := (rfl)

/-- The cochain map induced by a morphism of local coefficient systems. -/
def cochainComplexCoefficientMap (η : L ⟶ K) : cochainComplex L ⟶ cochainComplex K :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).map (cochainsCoefficientMap η)

/-- The induced cochain map applies the coefficient morphism to each simplex value. -/
@[simp]
lemma cochainComplexCoefficientMap_eval (η : L ⟶ K) (n : ℕ)
    (c : (cochainComplex L).X n) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    cochainComplexEval K n σ ((cochainComplexCoefficientMap η).f n c) =
      η.app (initialVertex σ) (cochainComplexEval L n σ c) := (rfl)

/-- The identity coefficient morphism induces the identity cochain map. -/
@[simp]
lemma cochainComplexCoefficientMap_id (L : LocalCoefficientSystem.{u, v, w} R X) :
    cochainComplexCoefficientMap (𝟙 L) = 𝟙 _ := by
  exact ((cochainsFunctor (R := R) (X := X)) ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _).map_id L

/-- Composition of coefficient morphisms induces composition of cochain maps. -/
@[reassoc]
lemma cochainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ N) :
    cochainComplexCoefficientMap (η ≫ θ) =
      cochainComplexCoefficientMap η ≫ cochainComplexCoefficientMap θ := by
  exact ((cochainsFunctor (R := R) (X := X)) ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _).map_comp η θ

variable (L)

/-- Singular cohomology with values in `L`. -/
abbrev cohomology (n : ℕ) : ModuleCat.{max v w} R := (cochainComplex L).homology n

variable {L}

/-- The map on local-coefficient cohomology induced by a morphism of local systems. -/
def cohomologyCoefficientMap (η : L ⟶ K) (n : ℕ) : cohomology L n ⟶ cohomology K n :=
  HomologicalComplex.homologyMap (cochainComplexCoefficientMap η) n

/-- The coefficient map on cohomology is induced by the coefficient map on cochains. -/
lemma cohomologyCoefficientMap_eq (η : L ⟶ K) (n : ℕ) :
    cohomologyCoefficientMap η n =
      HomologicalComplex.homologyMap (cochainComplexCoefficientMap η) n := (rfl)

/-- The identity coefficient morphism induces the identity on cohomology. -/
@[simp]
lemma cohomologyCoefficientMap_id (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) :
    cohomologyCoefficientMap (𝟙 L) n = 𝟙 _ := by
  simp [cohomologyCoefficientMap]

/-- Composition of coefficient morphisms induces composition on cohomology. -/
@[reassoc]
lemma cohomologyCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ N) (n : ℕ) :
    cohomologyCoefficientMap (η ≫ θ) n =
      cohomologyCoefficientMap η n ≫ cohomologyCoefficientMap θ n := by
  simp [cohomologyCoefficientMap, cochainComplexCoefficientMap_comp,
    HomologicalComplex.homologyMap_comp]

/-- For a constant system the differential is the ordinary alternating sum of face values. -/
lemma cochainComplex_d_eval_constant (M : ModuleCat.{w} R) (n : ℕ)
    (c : (cochainComplex ((constantFunctor X).obj M)).X n)
    (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    cochainComplexEval ((constantFunctor X).obj M) (n + 1) σ
        ((cochainComplex ((constantFunctor X).obj M)).d n (n + 1) c) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        cochainComplexEval ((constantFunctor X).obj M) n
          ((TopCat.toSSet.obj X).map (δ i).op σ) c := by
  rw [cochainComplex_d_eval]
  simp only [constantFunctor_obj_map]
  -- The identity of `ModuleCat` acts by the identity linear map on the constant fibre.
  rfl

end TauCeti.LocalCoefficientSystem
