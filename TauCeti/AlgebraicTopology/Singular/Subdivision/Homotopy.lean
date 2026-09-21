/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.AffineChain

/-!
# Barycentric subdivision is chain homotopic to the identity

This file constructs the prism operator `P` of barycentric subdivision `S` and proves the chain
homotopy formula `∂ P + P ∂ = 1 - S`, first on affine chains and then on singular chains with
coefficients in an object `R` of a preadditive category with coproducts. On the standard simplex
`Δᵏ`, the operator is given by Hatcher's recursion `P Δᵏ = b · (Δᵏ - S Δᵏ - P ∂Δᵏ)`, where `b` is
the cone from the barycenter of `Δᵏ`; it is extended to all affine chains, and to singular chains,
by naturality. Consequently barycentric subdivision induces the identity on singular homology.
This is the step of the small-chains theorem that replaces a singular chain by its iterated
subdivision without changing its homology class.

## Main definitions and results

* `TauCeti.AffineChain.prism`: the prism operator on affine chains in a convex space, with
  `TauCeti.AffineChain.boundary_prism_add_prism_boundary`: `∂ (P c) + P (∂ c) = c - S c`.
* `TauCeti.singularPrismX`: the prism operator on singular chains, natural in the space
  (`TauCeti.singularPrismX_naturality`).
* `TauCeti.singularSubdivisionHomotopy`: the chain homotopy from the identity of the singular chain
  complex to its barycentric subdivision.
* `TauCeti.homologyMap_singularSubdivisionChainMap`: barycentric subdivision induces the identity
  on singular homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, step (2).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial Equiv AlgebraicTopology Finsupp

universe w v u

namespace TauCeti

namespace AffineChain

variable {E F : Type*}

section Prism

variable [ConvexSpace ℝ E] [ConvexSpace ℝ F]

/-- The prism operator on the standard simplex, defined by Hatcher's recursion
`P Δᵏ = b · (Δᵏ - S Δᵏ - P ∂Δᵏ)`, where `b` is the barycenter of `Δᵏ`, `S` is the barycentric
subdivision and `P ∂Δᵏ` is computed from `P Δᵏ⁻¹` through the facet inclusions. -/
def prismModel (k : ℕ) : (Fin (k + 2) → StdSimplex ℝ (Fin (k + 1))) →₀ ℤ :=
  match k with
  | 0 => 0
  | k + 1 => cone StdSimplex.barycenter (k + 1) (simplex (k + 1) -
      subdivision _ (k + 1) (simplex (k + 1)) -
      ∑ j : Fin (k + 2), ((-1 : ℤ) ^ (j : ℕ)) • map (StdSimplex.map j.succAbove) (k + 1)
        (prismModel k))

variable (E) in
/-- The prism operator on affine chains: a vertex tuple `v` is sent to the image of the prism
operator of the standard simplex under the affine map with vertices `v`. It is a chain homotopy
between the identity and the barycentric subdivision
(`TauCeti.AffineChain.boundary_prism_add_prism_boundary`). -/
def prism (k : ℕ) : ((Fin (k + 1) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 2) → E) →₀ ℤ) :=
  linearCombination ℤ fun v ↦ map (StdSimplex.affineMapMk (R := ℝ) v) (k + 1) (prismModel k)

@[simp]
lemma prism_single {k : ℕ} (v : Fin (k + 1) → E) (a : ℤ) :
    prism E k (single v a) =
      a • map (StdSimplex.affineMapMk (R := ℝ) v) (k + 1) (prismModel k) := by
  simp [prism]

lemma prism_simplex (k : ℕ) : prism _ k (simplex k) = prismModel k := by
  have : ⇑(StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single : Fin (k + 1) → _)) = id := by
    funext x
    simp [StdSimplex.affineMapMk_apply]
  rw [simplex_def, prism_single, this, map_id, one_smul, LinearMap.id_apply]

lemma prism_boundary_simplex (k : ℕ) :
    prism _ k (boundary _ k (simplex (k + 1))) = ∑ j : Fin (k + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • map (StdSimplex.map j.succAbove) (k + 1) (prismModel k) := by
  rw [simplex_def, boundary_single, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : ⇑(StdSimplex.affineMapMk (R := ℝ)
      ((StdSimplex.single : Fin (k + 2) → _) ∘ j.succAbove)) = StdSimplex.map j.succAbove := by
    funext x
    rw [StdSimplex.affineMapMk_apply, ← StdSimplex.iConvexComb_single (StdSimplex.map _ x),
      iConvexComb_map]
    rfl
  rw [one_mul, prism_single, this]

/-- The prism operator is natural under affine maps. -/
lemma map_prism (f : ConvexSpace.AffineMap ℝ E F) {k : ℕ} (c : (Fin (k + 1) → E) →₀ ℤ) :
    map f (k + 1) (prism E k c) = prism F k (map f k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    simp only [prism_single, map_single, map_zsmul, ← LinearMap.comp_apply, ← map_comp,
      ← StdSimplex.comp_affineMapMk]
    rfl

@[simp]
lemma prism_zero : prism E 0 = 0 := by
  refine lhom_ext' fun v ↦ LinearMap.ext_ring ?_
  simp [prismModel]

@[simp]
lemma prismModel_zero : prismModel 0 = 0 := by
  rw [prismModel]

lemma prismModel_succ (k : ℕ) : prismModel (k + 1) = cone StdSimplex.barycenter (k + 1)
    (simplex (k + 1) - subdivision _ (k + 1) (simplex (k + 1)) -
      prism _ k (boundary _ k (simplex (k + 1)))) := by
  rw [prism_boundary_simplex, prismModel]

/-- The chain homotopy formula on the standard simplex, assuming it in the degree below. -/
private lemma boundary_prism_add_prism_boundary_simplex_of (k : ℕ)
    (hk : boundary _ k (prism _ k (boundary _ k (simplex (k + 1)))) =
      boundary _ k (simplex (k + 1)) - subdivision _ k (boundary _ k (simplex (k + 1)))) :
    boundary _ (k + 1) (prism _ (k + 1) (simplex (k + 1))) +
        prism _ k (boundary _ k (simplex (k + 1))) =
      simplex (k + 1) - subdivision _ (k + 1) (simplex (k + 1)) := by
  have hc : boundary _ k (simplex (k + 1) - subdivision _ (k + 1) (simplex (k + 1)) -
      prism _ k (boundary _ k (simplex (k + 1)))) = 0 := by
    rw [map_sub, map_sub, hk, ← LinearMap.comp_apply (boundary _ k) (subdivision _ (k + 1)),
      boundary_subdivision, LinearMap.comp_apply, sub_self]
  rw [prism_simplex, prismModel_succ, boundary_cone, hc, map_zero, sub_zero, sub_add_cancel]

/-- The chain homotopy formula for all affine chains follows from the case of the standard
simplex by naturality under affine maps. -/
private lemma boundary_prism_add_prism_boundary_of (k : ℕ)
    (h : boundary _ (k + 1) (prism _ (k + 1) (simplex (k + 1))) +
        prism _ k (boundary _ k (simplex (k + 1))) =
      simplex (k + 1) - subdivision _ (k + 1) (simplex (k + 1)))
    (c : (Fin (k + 2) → E) →₀ ℤ) :
    boundary E (k + 1) (prism E (k + 1) c) + prism E k (boundary E k c) =
      c - subdivision E (k + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add]; rw [← sub_add_sub_comm, ← hc, ← hd]; abel
  | single v a =>
    rw [← smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← smul_add,
      ← smul_sub, ← map_affineMapMk_simplex, ← map_prism, ← map_boundary,
      ← map_boundary, ← map_prism, ← map_subdivision, ← map_add, ← map_sub, h]

/-- The chain homotopy formula on the standard simplex, by induction on the degree. -/
private lemma boundary_prism_add_prism_boundary_simplex (k : ℕ) :
    boundary _ (k + 1) (prism _ (k + 1) (simplex (k + 1))) +
        prism _ k (boundary _ k (simplex (k + 1))) =
      simplex (k + 1) - subdivision _ (k + 1) (simplex (k + 1)) := by
  induction k with
  | zero =>
    refine boundary_prism_add_prism_boundary_simplex_of 0 ?_
    simp [prism_zero]
  | succ k ih =>
    refine boundary_prism_add_prism_boundary_simplex_of (k + 1) ?_
    have := boundary_prism_add_prism_boundary_of k ih (boundary _ (k + 1) (simplex (k + 2)))
    rw [← LinearMap.comp_apply (boundary _ k) (boundary _ (k + 1)), boundary_boundary,
      LinearMap.zero_apply, map_zero, add_zero] at this
    exact this

/-- **The prism operator is a chain homotopy from the identity to the barycentric subdivision.**
For an affine chain `c` of positive degree, `∂ (P c) + P (∂ c) = c - S c`. -/
theorem boundary_prism_add_prism_boundary (k : ℕ) (c : (Fin (k + 2) → E) →₀ ℤ) :
    boundary E (k + 1) (prism E (k + 1) c) + prism E k (boundary E k c) =
      c - subdivision E (k + 1) c :=
  boundary_prism_add_prism_boundary_of k (boundary_prism_add_prism_boundary_simplex k) c

end Prism

end AffineChain


open AffineChain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  (X : TopCat.{w})

/-- The prism operator on singular `n`-chains of `X` with coefficients in `R`: the summand of a
singular simplex `σ` is sent to the push-forward along `σ` of the prism operator of the standard
simplex. -/
def singularPrismX (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X n ⟶ ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n) fun σ ↦
    singularChain R (X.toSSetObjEquiv _ σ) (n + 1) (prismModel n)

variable {R X} in
@[reassoc (attr := simp)]
lemma ιChainComplex_singularPrismX {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularPrismX R X n =
      singularChain R (X.toSSetObjEquiv _ σ) (n + 1) (prismModel n) :=
  Cofan.IsColimit.fac _ _ σ

/-- The singular prism operator vanishes on `0`-chains. -/
@[simp]
lemma singularPrismX_zero : singularPrismX R X 0 = 0 := by
  ext σ
  simp

/-- The prism operator is natural in the space. -/
@[reassoc]
lemma singularPrismX_naturality {Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫ singularPrismX R Y n =
      singularPrismX R X n ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f (n + 1) := by
  ext σ
  simp [SSet.ι_chainComplexMap_f_assoc, singularChain_comp_map]

/-- The chain homotopy formula for the singular prism operator in positive degrees:
`∂ P + P ∂ = 1 - S`. -/
lemma singularPrismX_boundary_add_boundary_singularPrismX (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ singularPrismX R X n +
        singularPrismX R X (n + 1) ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) =
      𝟙 _ - singularSubdivisionX R X (n + 1) := by
  ext σ
  have h := congrArg (singularChain R (X.toSSetObjEquiv _ σ) (n + 1))
    (boundary_prism_add_prism_boundary (E := StdSimplex ℝ (Fin (n + 2))) n (simplex (n + 1)))
  rw [map_add, map_sub, singularChain_boundary, prism_simplex, singularChain_simplex,
    singularChain_subdivision_simplex, prism_boundary_simplex] at h
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
    ιChainComplex_singularPrismX_assoc, SSet.ιChainComplex_d_assoc, Preadditive.sum_comp,
    Preadditive.zsmul_comp, ιChainComplex_singularPrismX, singularChain_δ]
  rw [← h, map_sum]
  simp only [map_zsmul]
  exact add_comm _ _

/-- **Barycentric subdivision is chain homotopic to the identity.** The singular prism operator
is a chain homotopy from the identity of the singular chain complex of `X` with coefficients in
`R` to its barycentric subdivision. -/
def singularSubdivisionHomotopy : Homotopy (𝟙 _) (singularSubdivisionChainMap R X) where
  hom i j := if h : i + 1 = j then singularPrismX R X i ≫ eqToHom (by rw [h]) else 0
  zero i j hij := by
    rw [ComplexShape.down_Rel] at hij
    simp [hij]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp [singularPrismX_boundary_add_boundary_singularPrismX]

@[simp]
lemma singularSubdivisionHomotopy_hom (n : ℕ) :
    (singularSubdivisionHomotopy R X).hom n (n + 1) = singularPrismX R X n := by
  simp [singularSubdivisionHomotopy]

/-- Barycentric subdivision induces the identity on singular homology. -/
@[simp]
lemma homologyMap_singularSubdivisionChainMap [CategoryWithHomology C] (n : ℕ) :
    HomologicalComplex.homologyMap (singularSubdivisionChainMap R X) n = 𝟙 _ := by
  rw [← (singularSubdivisionHomotopy R X).homologyMap_eq n, HomologicalComplex.homologyMap_id]

end TauCeti
