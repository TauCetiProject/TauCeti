/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Sphere.Zero

/-!
# Cohomology of the Thom pair of a product line bundle

Let `B` be a topological space and `F` a real topological vector space of dimension one, given
with a continuous linear equivalence `e : F ≃L[ℝ] ℝ¹`. This file computes the singular
cohomology, with coefficients in any module `M` over a commutative ring `k`, of the complement
`B × (F ∖ {0})` of the zero section of the product bundle `B × F → B`, and of its Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) in every degree at least one.

* `B × (F ∖ {0})` has two sides, `e > 0` and `e < 0`, each homotopy equivalent to `B`. Let
  `σ ∈ H⁰(B × (F ∖ {0}); k)` be the class with value `1` on the positive side and `0` on the
  negative side (`TauCeti.prodThomPairPuncturedLineClass`), and `π : B × (F ∖ {0}) → B` the
  projection (`TauCeti.prodThomPairPuncturedProj`). Then every class of
  `Hᵐ(B × (F ∖ {0}); M)` is uniquely `π^* b + σ ⌣ π^* c` with `b, c ∈ Hᵐ(B; M)`
  (`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv`): `b` is its restriction to the
  negative side and `b + c` its restriction to the positive side
  (`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv_symm_apply`), along the sections
  `TauCeti.prodThomPairPuncturedLineSection`.
* In the long exact sequence of the pair, the restriction from `Hᵐ(B × F; M)` to
  `Hᵐ(B × (F ∖ {0}); M)` is injective with image the classes `π^* b`, so the connecting
  morphism `δ` identifies the classes `σ ⌣ π^* c` with the whole relative cohomology in degree
  `n + 1`: `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
  `Hⁿ(B; M) ≃ Hⁿ⁺¹(B × F, B × (F ∖ {0}); M)` for every `n`
  (`TauCeti.prodThomPairSingularCohomologyLineEquiv`), natural in `B`. It sends the unit of
  `H⁰(B; k)` to `δ σ`.

This is the rank-one case of the product case of the Thom isomorphism in cohomology, which is
then extended by Mayer–Vietoris over unions of trivializing open sets. The ranks `r ≥ 2`, where
`F ∖ {0}` is connected and `σ` is replaced by a class pulled back from the sphere `Sʳ⁻¹`, are
`TauCeti.prodThomPairSingularCohomologySphereEquiv`. Below degree one the relative cohomology
vanishes (`TauCeti.isZero_singularCohomology_prodThomPair`).

## Main definitions and results

* `TauCeti.prodThomPairPuncturedLineClass`: the class `σ` of the positive side, characterized
  by its values (`TauCeti.singularCohomologyZeroEval_prodThomPairPuncturedLineClass`).
* `TauCeti.prodThomPairPuncturedLineSection`: the sections `b ↦ (b, e⁻¹ (±1))` onto the two
  sides; a class of `Hᵐ(B × (F ∖ {0}); M)` is determined by its restrictions along them
  (`TauCeti.eq_zero_of_singularCohomologyMap_prodThomPairPuncturedLineSection_eq_zero`).
* `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv`:
  `Hᵐ(B; M) × Hᵐ(B; M) ≃ Hᵐ(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`, whose inverse is
  `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv_symm_apply`.
* `TauCeti.prodThomPairSingularCohomologyLineEquiv`:
  `Hⁿ(B; M) ≃ Hⁿ⁺¹(B × F, B × (F ∖ {0}); M)`, `c ↦ δ (σ ⌣ π^* c)`, with its naturality
  `TauCeti.prodThomPairSingularCohomologyLineEquiv_naturality`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first for a product bundle and then by Mayer–Vietoris).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w

namespace TauCeti

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]

/-! ### The class of the positive side -/

/-- Points of `B × (F ∖ {0})` joined by a path lie on the same side of the zero section. -/
private theorem pos_iff_of_joined (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    {p q : (prodThomPair B F).snd} (h : Joined p q) : 0 < e p.val.2 0 ↔ 0 < e q.val.2 0 := by
  -- Positivity is carried along any path; `Joined` is symmetric, so this gives both directions.
  suffices key : ∀ {p q : (prodThomPair B F).snd}, Joined p q → 0 < e p.val.2 0 → 0 < e q.val.2 0
      from
    ⟨key h, key h.symm⟩
  intro p q h hp
  obtain ⟨γ⟩ := h
  set g : unitInterval → ℝ := fun t ↦ e (γ t).val.2 0
  have hg : Continuous g := by fun_prop
  -- A vector of `ℝ¹` vanishes as soon as its coordinate does.
  have hne (t : unitInterval) : g t ≠ 0 := fun h0 ↦
    (γ t).property (e.map_eq_zero_iff.1 (by ext i; rw [Subsingleton.elim i 0]; exact h0))
  have h0 : g 0 = e p.val.2 0 := by simp [g]
  have h1 : g 1 = e q.val.2 0 := by simp [g]
  rw [← h0] at hp
  rw [← h1]
  by_contra hq
  obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hg ⟨not_lt.1 hq, hp.le⟩
  exact hne t ht

variable (k B) in
/-- Some class of `H⁰(B × (F ∖ {0}); k)` has the value `1` on the positive side and `0` on the
negative side, since these values are constant along paths. -/
private theorem exists_singularCohomologyZeroEval_eq_ite (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    ∃ u : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) 0,
      ∀ p : (prodThomPair B F).snd,
        singularCohomologyZeroEval p u = if 0 < e p.val.2 0 then 1 else 0 :=
  exists_singularCohomologyZeroEval_eq _ fun _ _ h ↦ by simp only [pos_iff_of_joined e h]

variable (k B) in
/-- The class of `H⁰(B × (F ∖ {0}); k)` which is `1` on the side of the zero section where the
coordinate `e` is positive and `0` on the other side
(`TauCeti.singularCohomologyZeroEval_prodThomPairPuncturedLineClass`). It is the rank-one
counterpart of the class `TauCeti.prodThomPairPuncturedClass` pulled back from a sphere. -/
def prodThomPairPuncturedLineClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      0 :=
  (exists_singularCohomologyZeroEval_eq_ite k B e).choose

/-- The class `TauCeti.prodThomPairPuncturedLineClass` has the value `1` on the positive side and
`0` on the negative side. -/
@[simp]
theorem singularCohomologyZeroEval_prodThomPairPuncturedLineClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (p : (prodThomPair B F).snd) :
    singularCohomologyZeroEval p (prodThomPairPuncturedLineClass k B e) =
      if 0 < e p.val.2 0 then 1 else 0 :=
  (exists_singularCohomologyZeroEval_eq_ite k B e).choose_spec p

/-! ### The two sides of the zero section -/

/-- The section `b ↦ (b, e⁻¹ t)` of the projection `B × (F ∖ {0}) → B` for `t ≠ 0`, landing on
the side of the zero section of the sign of `t`. It is the section
`TauCeti.prodThomPairPuncturedSection` at the point `e⁻¹ t`. -/
def prodThomPairPuncturedLineSection (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (t : ℝ)
    (ht : t ≠ 0) : TopCat.of B ⟶ (prodThomPair B F).snd :=
  prodThomPairPuncturedSection B (e.symm (EuclideanSpace.single 0 t)) (by simpa using ht)

/-- The section `TauCeti.prodThomPairPuncturedLineSection` sends `b` to `(b, e⁻¹ t)`. -/
@[simp]
theorem coe_prodThomPairPuncturedLineSection_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    (t : ℝ) (ht : t ≠ 0) (b : B) :
    (prodThomPairPuncturedLineSection e t ht b).val = (b, e.symm (EuclideanSpace.single 0 t)) :=
  prodThomPairPuncturedSection_apply _ _ b

/-- `TauCeti.prodThomPairPuncturedLineSection` is a section of the projection
`B × (F ∖ {0}) → B`. -/
@[simp]
theorem prodThomPairPuncturedLineSection_comp_prodThomPairPuncturedProj
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (t : ℝ) (ht : t ≠ 0) :
    prodThomPairPuncturedLineSection (B := B) e t ht ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
  prodThomPairPuncturedSection_comp_prodThomPairPuncturedProj _ _

/-- Restricting a class pulled back from the base to either side gives back the class. -/
private theorem singularCohomologyMap_prodThomPairPuncturedLineSection_prodThomPairPuncturedProj
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (t : ℝ) (ht : t ≠ 0) (m : ℕ)
    (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e t ht) m
        (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m b) = b := by
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    prodThomPairPuncturedLineSection_comp_prodThomPairPuncturedProj,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

/-- The class `σ` of the positive side restricts to the unit on the positive side. -/
private theorem singularCohomologyMap_prodThomPairPuncturedLineSection_one
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection (B := B) e 1 one_ne_zero) 0
        (prodThomPairPuncturedLineClass k B e) = (TopCat.of B).singularCohomologyZeroOne :=
  singularCohomologyZero_ext fun _ ↦ by
    rw [singularCohomologyZeroEval_naturality,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass,
      coe_prodThomPairPuncturedLineSection_apply]
    simp

/-- The class `σ` of the positive side restricts to zero on the negative side. -/
private theorem singularCohomologyMap_prodThomPairPuncturedLineSection_neg_one
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    TopCat.singularCohomologyMap
        (prodThomPairPuncturedLineSection (B := B) e (-1) (by norm_num)) 0
        (prodThomPairPuncturedLineClass k B e) = 0 :=
  singularCohomologyZero_ext fun _ ↦ by
    rw [singularCohomologyZeroEval_naturality,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass,
      coe_prodThomPairPuncturedLineSection_apply]
    simp

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv` from `B × (F ∖ {0})` to
`S⁰ × B`, as a morphism of `TopCat`. -/
private abbrev sphereZeroProdMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    (prodThomPair B F).snd ⟶ TopCat.sphere.{w} 0 ⊗ TopCat.of B :=
  TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun

/-- The homotopy equivalence with `S⁰ × B` carries the section at `t = ±1` to the slice through
the point `t` of `S⁰`. -/
private theorem prodThomPairPuncturedLineSection_comp_sphereZeroProdMap
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (s : TopCat.sphere.{w} 0) {t : ℝ} (ht : t ≠ 0)
    (hs : (s.down : EuclideanSpace ℝ (Fin 1)) = EuclideanSpace.single 0 t) :
    prodThomPairPuncturedLineSection (B := B) e t ht ≫ sphereZeroProdMap e =
      CartesianMonoidalCategory.lift (TopCat.ofHom (ContinuousMap.const B s)) (𝟙 _) := by
  have h1 : ‖t‖ = 1 := by simpa [hs] using s.down.property
  refine TopCat.ext fun b ↦ ?_
  have key : prodThomPairPuncturedHomotopyEquiv B e (prodThomPairPuncturedLineSection e t ht b) =
      (s, b) := by
    refine Prod.ext (ULift.ext (Subtype.ext ?_)) ((prodThomPairPuncturedHomotopyEquiv_apply_snd e
      _).trans (congrArg Prod.fst (coe_prodThomPairPuncturedLineSection_apply e t ht b)))
    rw [coe_prodThomPairPuncturedHomotopyEquiv_apply_fst,
      coe_prodThomPairPuncturedLineSection_apply]
    simp [hs, h1]
  -- Both sides evaluate at `b` to the two sides of `key`, by the definitions of composition in
  -- `TopCat` and of `CartesianMonoidalCategory.lift`.
  exact key

/-- **A class on `B × (F ∖ {0})` is determined on the two sides**: a class of
`Hᵐ(B × (F ∖ {0}); M)` whose restrictions along the sections `b ↦ (b, e⁻¹ (±1))` vanish is zero. -/
theorem eq_zero_of_singularCohomologyMap_prodThomPairPuncturedLineSection_eq_zero
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (y : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m)
    (hpos : TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e 1 one_ne_zero) m y = 0)
    (hneg : TopCat.singularCohomologyMap
      (prodThomPairPuncturedLineSection e (-1) (by norm_num)) m y = 0) :
    y = 0 := by
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
      (sphereZeroProdMap (B := B) e) m) :=
    (prodThomPairPuncturedHomotopyEquiv B e).isIso_singularCohomologyMap _ k M m
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (TopCat.singularCohomologyMap (sphereZeroProdMap e) m)).2 y
  suffices z = 0 by rw [this, map_zero]
  have : DiscreteTopology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    discreteTopology_sphere_of_finrank_eq_one finrank_euclideanSpace_fin 0 1
  have : DiscreteTopology (TopCat.sphere.{w} 0) := Homeomorph.ulift.isEmbedding.discreteTopology
  refine singularCohomology_prod_ext_of_discreteTopology m fun s ↦ ?_
  rw [map_zero]
  -- The `0`-sphere consists of the two points `±1`.
  have hs : (s.down : EuclideanSpace ℝ (Fin 1)) ∈
      ({EuclideanSpace.single 0 1, -EuclideanSpace.single 0 1} : Set _) :=
    sphere_eq_pair_of_finrank_eq_one finrank_euclideanSpace_fin (r := 1)
      (p := EuclideanSpace.single 0 1) (by simp) ▸ s.down.property
  rcases hs with hs | hs
  · rwa [← prodThomPairPuncturedLineSection_comp_sphereZeroProdMap e s one_ne_zero hs,
      TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
  · rwa [← prodThomPairPuncturedLineSection_comp_sphereZeroProdMap e s (t := -1) (by norm_num)
        (by rw [Set.mem_singleton_iff.1 hs]; ext i; by_cases hi : i = 0 <;> simp [hi]),
      TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]

/-! ### The cohomology of the punctured product line bundle -/

/-- The map `(b, c) ↦ π^* b + σ ⌣ π^* c` into the cohomology of the punctured product bundle. -/
private def lineMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) →ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearMap.coprod (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m).hom
    ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        0 m m (zero_add m) (prodThomPairPuncturedLineClass k B e) ∘ₗ
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m).hom)

private theorem lineMap_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    lineMap M e m bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 m m (zero_add m) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.2) :=
  -- `lineMap` is this sum by definition.
  (rfl)

/-- On the positive side, `π^* b + σ ⌣ π^* c` restricts to `b + c`. -/
private theorem singularCohomologyMap_prodThomPairPuncturedLineSection_one_lineMap
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e 1 one_ne_zero) m
      (lineMap M e m bc) = bc.1 + bc.2 := by
  rw [lineMap_apply, map_add, ← TopCat.singularCup_naturality,
    singularCohomologyMap_prodThomPairPuncturedLineSection_prodThomPairPuncturedProj,
    singularCohomologyMap_prodThomPairPuncturedLineSection_prodThomPairPuncturedProj,
    singularCohomologyMap_prodThomPairPuncturedLineSection_one,
    TopCat.singularCohomologyZeroOne_def,
    TopCat.singularCup_constSingularCocycle_left _ k (η := 𝟙 _) (by simp) (by simp)]

/-- On the negative side, `π^* b + σ ⌣ π^* c` restricts to `b`. -/
private theorem singularCohomologyMap_prodThomPairPuncturedLineSection_neg_one_lineMap
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e (-1) (by norm_num)) m
      (lineMap M e m bc) = bc.1 := by
  rw [lineMap_apply, map_add, ← TopCat.singularCup_naturality,
    singularCohomologyMap_prodThomPairPuncturedLineSection_prodThomPairPuncturedProj,
    singularCohomologyMap_prodThomPairPuncturedLineSection_neg_one, map_zero, LinearMap.zero_apply,
    add_zero]

/-- The candidate `(b, c)` reading `b` off the negative side and `b + c` off the positive side
is sent back to the class. -/
private theorem lineMap_restrict (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (y : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    lineMap M e m
        (TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e (-1) (by norm_num)) m y,
          TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e 1 one_ne_zero) m y -
            TopCat.singularCohomologyMap
              (prodThomPairPuncturedLineSection e (-1) (by norm_num)) m y) = y := by
  refine sub_eq_zero.1
    (eq_zero_of_singularCohomologyMap_prodThomPairPuncturedLineSection_eq_zero M e m _ ?_ ?_)
  · rw [map_sub, singularCohomologyMap_prodThomPairPuncturedLineSection_one_lineMap,
      add_sub_cancel, sub_self]
  · rw [map_sub, singularCohomologyMap_prodThomPairPuncturedLineSection_neg_one_lineMap, sub_self]

private theorem bijective_lineMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ) :
    Function.Bijective (lineMap (B := B) M e m) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun bc hbc ↦ ?_, fun y ↦ ⟨_, lineMap_restrict M e m y⟩⟩
  have h₁ := singularCohomologyMap_prodThomPairPuncturedLineSection_neg_one_lineMap M e m bc
  have h₂ := singularCohomologyMap_prodThomPairPuncturedLineSection_one_lineMap M e m bc
  rw [hbc, map_zero] at h₁ h₂
  have hc : bc.2 = 0 := by rw [← h₁, zero_add] at h₂; exact h₂.symm
  exact Prod.ext h₁.symm hc

variable (B) in
/-- **The cohomology of the punctured product line bundle.** For a continuous linear equivalence
`e : F ≃L[ℝ] ℝ¹`, every class of `Hᵐ(B × (F ∖ {0}); M)` is uniquely `π^* b + σ ⌣ π^* c` with
`b, c ∈ Hᵐ(B; M)`, where `π` is the projection to `B` and `σ` is the class
`TauCeti.prodThomPairPuncturedLineClass` of the positive side
(`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv_apply`). -/
def prodThomPairPuncturedLineSingularCohomologyEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    (m : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective (lineMap M e m) (bijective_lineMap M e m)

/-- The decomposition `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv` sends `(b, c)` to
`π^* b + σ ⌣ π^* c`. -/
@[simp]
theorem prodThomPairPuncturedLineSingularCohomologyEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    prodThomPairPuncturedLineSingularCohomologyEquiv M B e m bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 m m (zero_add m) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.2) :=
  lineMap_apply M e m bc

/-- On the positive side, the class `π^* b + σ ⌣ π^* c` of
`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv` restricts to `b + c`. -/
theorem singularCohomologyMap_prodThomPairPuncturedLineSection_one_lineSingularCohomologyEquiv
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e 1 one_ne_zero) m
        (prodThomPairPuncturedLineSingularCohomologyEquiv M B e m bc) = bc.1 + bc.2 :=
  singularCohomologyMap_prodThomPairPuncturedLineSection_one_lineMap M e m bc

/-- On the negative side, the class `π^* b + σ ⌣ π^* c` of
`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv` restricts to `b`. -/
theorem singularCohomologyMap_prodThomPairPuncturedLineSection_neg_one_lineSingularCohomologyEquiv
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e (-1) (by norm_num)) m
        (prodThomPairPuncturedLineSingularCohomologyEquiv M B e m bc) = bc.1 :=
  singularCohomologyMap_prodThomPairPuncturedLineSection_neg_one_lineMap M e m bc

/-- The inverse of the decomposition `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv`
reads `b` off the negative side and `c` as the difference of the restrictions to the two sides. -/
theorem prodThomPairPuncturedLineSingularCohomologyEquiv_symm_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (y : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    (prodThomPairPuncturedLineSingularCohomologyEquiv M B e m).symm y =
      (TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e (-1) (by norm_num)) m y,
        TopCat.singularCohomologyMap (prodThomPairPuncturedLineSection e 1 one_ne_zero) m y -
          TopCat.singularCohomologyMap
            (prodThomPairPuncturedLineSection e (-1) (by norm_num)) m y) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (lineMap_restrict M e m y).symm

/-- The classes `π^* b` of the decomposition
`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv` are the restrictions of the classes of
`B × F` pulled back from `B`. -/
private theorem prodThomPairPuncturedLineSingularCohomologyEquiv_apply_zero
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    prodThomPairPuncturedLineSingularCohomologyEquiv M B e m (b, 0) =
      TopCat.singularCohomologyMap (prodThomPair B F).map _
        (TopCat.singularCohomologyMap (prodThomPairProj B F) _ b) := by
  rw [prodThomPairPuncturedLineSingularCohomologyEquiv_apply, map_zero, map_zero, add_zero,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj]

/-! ### The cohomology of the Thom pair of a product line bundle -/

variable (B) in
/-- **The cohomology of the Thom pair of a product line bundle.** Let `e : F ≃L[ℝ] ℝ¹` be a
continuous linear equivalence, so that `F` has dimension `1`. Then, for every base degree `n` and
`m = n + 1`, `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
`Hⁿ(B; M) ≃ Hᵐ(B × F, B × (F ∖ {0}); M)`, where `π : B × (F ∖ {0}) → B` is the projection,
`σ ∈ H⁰(B × (F ∖ {0}); k)` is the class `TauCeti.prodThomPairPuncturedLineClass` of the positive
side, and `δ` is the connecting morphism of the pair
(`TauCeti.prodThomPairSingularCohomologyLineEquiv_apply`). -/
def prodThomPairSingularCohomologyLineEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective
    (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h).hom ∘ₗ
      (prodThomPairPuncturedLineSingularCohomologyEquiv M B e n).toLinearMap ∘ₗ
        LinearMap.inr k _ _) <| by
    have := e.toHomeomorph.contractibleSpace
    exact bijective_singularCohomologyδ_prodThomPair_comp_inr M
      (v := e.symm (EuclideanSpace.single 0 1)) (by simp) n m h
      (prodThomPairPuncturedLineSingularCohomologyEquiv M B e n)
      (prodThomPairPuncturedLineSingularCohomologyEquiv_apply_zero M e n)

/-- The equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv` is `c ↦ δ (D (0, c))` for
the decomposition `D` of the cohomology of the punctured product bundle. -/
private theorem prodThomPairSingularCohomologyLineEquiv_eq
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (n m : ℕ) (h : n + 1 = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologyLineEquiv M B e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h)
        ((prodThomPairPuncturedLineSingularCohomologyEquiv M B e n) (0, c)) :=
  -- The equivalence is this composite by definition.
  (rfl)

/-- The equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv` sends `c` to
`δ (σ ⌣ π^* c)`. -/
@[simp]
theorem prodThomPairSingularCohomologyLineEquiv_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    (n m : ℕ) (h : n + 1 = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologyLineEquiv M B e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h)
        ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 n n (zero_add n) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c)) := by
  rw [prodThomPairSingularCohomologyLineEquiv_eq,
    prodThomPairPuncturedLineSingularCohomologyEquiv_apply, map_zero, zero_add]

/-- The equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv` sends the unit
`1 ∈ H⁰(B; k)` to `δ σ`, where `σ` is `TauCeti.prodThomPairPuncturedLineClass`. -/
theorem prodThomPairSingularCohomologyLineEquiv_singularCohomologyZeroOne
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    (prodThomPairSingularCohomologyLineEquiv (𝟙_ (ModuleCat.{w} k)) B e 0 1)
        (TopCat.of B).singularCohomologyZeroOne =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        0 1) (prodThomPairPuncturedLineClass k B e) := by
  rw [prodThomPairSingularCohomologyLineEquiv_apply,
    singularCohomologyMap_singularCohomologyZeroOne,
    TopCat.singularCup_singularCohomologyZeroOne_right]

/-! ### Naturality in the base -/

section Naturality

variable {B' : Type w} [TopologicalSpace B'] (g : C(B, B'))

/-- The class `σ` of `TauCeti.prodThomPairPuncturedLineClass` is natural in the base. -/
@[simp]
theorem singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedLineClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) 0
        (prodThomPairPuncturedLineClass k B' e) = prodThomPairPuncturedLineClass k B e :=
  singularCohomologyZero_ext fun p ↦ by
    rw [singularCohomologyZeroEval_naturality,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass, prodThomPairMap_snd_apply]

/-- The decomposition `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv` is natural in the
base: restricting `π^* b + σ ⌣ π^* c` along the map induced by `g : B → B'` gives
`π^* (g^* b) + σ ⌣ π^* (g^* c)`. -/
theorem prodThomPairPuncturedLineSingularCohomologyEquiv_naturality
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (bc : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) m
        (prodThomPairPuncturedLineSingularCohomologyEquiv M B' e m bc) =
      prodThomPairPuncturedLineSingularCohomologyEquiv M B e m
        (TopCat.singularCohomologyMap (TopCat.ofHom g) m bc.1,
          TopCat.singularCohomologyMap (TopCat.ofHom g) m bc.2) := by
  rw [prodThomPairPuncturedLineSingularCohomologyEquiv_apply,
    prodThomPairPuncturedLineSingularCohomologyEquiv_apply, map_add,
    ← TopCat.singularCup_naturality,
    singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedLineClass]
  simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    snd_prodThomPairMap_comp_prodThomPairPuncturedProj]

/-- **Naturality of the cohomology of the Thom pair of a product line bundle.** The equivalence
`TauCeti.prodThomPairSingularCohomologyLineEquiv` commutes with the maps induced by a continuous
map `g : B → B'` of the bases. -/
theorem prodThomPairSingularCohomologyLineEquiv_naturality
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (n m : ℕ) (h : n + 1 = m := by lia)
    (c : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopPair.singularCohomologyMap (prodThomPairMap F g) m
        (prodThomPairSingularCohomologyLineEquiv M B' e n m h c) =
      prodThomPairSingularCohomologyLineEquiv M B e n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom g) n c) := by
  rw [prodThomPairSingularCohomologyLineEquiv_eq, prodThomPairSingularCohomologyLineEquiv_eq,
    ← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) n m h,
    ConcreteCategory.comp_apply,
    prodThomPairPuncturedLineSingularCohomologyEquiv_naturality M g e n, map_zero]

end Naturality

end TauCeti
