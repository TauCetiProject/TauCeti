/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
import TauCeti.Algebra.Homology.Homotopy

/-!
# Barycentric subdivision of singular chains with local coefficients

Barycentric subdivision of singular chains extends to the singular chains twisted by a local
coefficient system `L`. On the summand of a singular `k`-simplex `σ`, whose coefficients lie in the
fibre of `L` at the initial vertex of `σ`, it is the signed sum over the permutations `π` of the
summands of the singular simplices `σ ∘ StdSimplex.continuousAffineMapMk (vertex π)`, exactly as in
`TauCeti.singularSubdivisionX`. The coefficients are transported from the initial vertex of `σ` to
the initial vertex of each smaller simplex along the image under `σ` of the unique path class of the
standard simplex between the two points (`TauCeti.LocalCoefficientSystem.pathTransport`). The prism
operator of barycentric subdivision extends in the same way, and the chain homotopy formula
`∂ P + P ∂ = 1 - S` still holds, so twisted barycentric subdivision induces the identity on twisted
singular homology.

The operators are obtained by pushing the affine chains of the standard simplex
(`TauCeti.AffineChain`) forward along a singular simplex `σ`, with the coefficients transported from
a chosen point `σ z` (`TauCeti.LocalCoefficientSystem.twistedSingularChain`). The standard simplex
is simply connected, so transports inside `σ` compose and depend only on their endpoints. Hence this
push-forward commutes with the boundary and with faces, and the identities between affine chains
used for untwisted singular chains (`TauCeti.AffineChain.boundary_subdivision` and
`TauCeti.AffineChain.boundary_prism_add_prism_boundary`) transfer to twisted chains. Iterated
subdivisions are computed on affine chains as well
(`TauCeti.LocalCoefficientSystem.twistedSingularChain_subdivision_iterate`), which is what the
argument making twisted chains subordinate to an open cover consumes.

Both operators are natural in the space, and the subdivision is natural in the coefficient system.

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.twistedAffineSimplex`: the summand of an affine simplex of a
  singular simplex `σ`, with coefficients transported from a point of `σ`, and
  `TauCeti.LocalCoefficientSystem.twistedSingularChain`: its linear extension to affine chains,
  which commutes with the boundary (`twistedSingularChain_boundary`).
* `TauCeti.LocalCoefficientSystem.twistedSubdivisionChainMap`: the barycentric subdivision of
  twisted singular chains, computed on summands by `ιTwistedChainComplex_twistedSubdivisionX`.
* `TauCeti.LocalCoefficientSystem.twistedPrismX` and
  `TauCeti.LocalCoefficientSystem.twistedPrismX_boundary_add_boundary_twistedPrismX`: the prism
  operator and its chain homotopy formula.
* `TauCeti.LocalCoefficientSystem.twistedSubdivisionHomotopy`: **twisted barycentric subdivision is
  chain homotopic to the identity**, so it induces the identity on twisted homology
  (`homologyMap_twistedSubdivisionChainMap`).
* `twistedChainComplexMap_comp_twistedSubdivisionChainMap`,
  `twistedChainComplexMap_f_comp_twistedPrismX` and
  `twistedChainComplexCoefficientMap_comp_twistedSubdivisionChainMap`: naturality.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, steps (1)–(3), for
  barycentric subdivision and its prism operator, and Section 3.H for local coefficients.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial Equiv AlgebraicTopology Finsupp SimplexCategory

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

variable {n : SimplexCategoryᵒᵖ}

/-- The singular simplex `σ ∘ StdSimplex.continuousAffineMapMk v`. -/
private abbrev affineSimplex (σ : (TopCat.toSSet.obj X).obj n) {k : ℕ}
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) : (TopCat.toSSet.obj X) _⦋k⦌ :=
  (X.toSSetObjEquiv _).symm ((X.toSSetObjEquiv n σ).comp (StdSimplex.continuousAffineMapMk v))

/-- The affine map of topological simplices with vertices `v`. -/
private def affineToTop {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) :
    C(toTop.{v}.obj ⦋k⦌, toTop.{v}.obj n.unop) :=
  ⟨fun x ↦ ULift.up (StdSimplex.continuousAffineMapMk v x.down), by fun_prop⟩

private lemma affineToTop_apply_down {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1)))
    (x : toTop.{v}.obj ⦋k⦌) : (affineToTop v x).down = StdSimplex.continuousAffineMapMk v x.down :=
  rfl

/-- Transport inside an affine simplex of `σ` is transport inside `σ` between the images of the
two points. -/
private lemma pathTransport_affineSimplex (σ : (TopCat.toSSet.obj X).obj n) {k : ℕ}
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) (a b : toTop.{v}.obj ⦋k⦌) :
    pathTransport (affineSimplex σ v) a b =
      pathTransport σ (affineToTop v a) (affineToTop v b) := by
  let q : Path a b := PathConnectedSpace.somePath a b
  rw [pathTransport_eq_mk _ q, pathTransport_eq_mk _ (q.map (affineToTop v).continuous),
    Path.map_map]
  -- Both sides are the class of `q` pushed forward along the same function.
  rfl

/-- Vertex transport is transport inside the simplex between the two initial vertices. -/
private lemma vertexTransport_eq_pathTransport {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (σ : (TopCat.toSSet.obj X).obj m) :
    vertexTransport α σ = pathTransport σ (toTopInitialVertex m.unop)
      (toTop.map α.unop (toTopInitialVertex n.unop)) := by
  let q : Path (toTopInitialVertex.{v} m.unop) (toTop.map α.unop (toTopInitialVertex n.unop)) :=
    PathConnectedSpace.somePath _ _
  rw [vertexTransport_eq_mk α σ q, pathTransport_eq_mk σ q]

variable {L} in
private lemma map_comp_ιTwistedChainComplex_congr {k : ℕ} {a : FundamentalGroupoid X}
    {τ₁ τ₂ : (TopCat.toSSet.obj X) _⦋k⦌} (h : τ₁ = τ₂) {f₁ : a ⟶ initialVertex τ₁}
    {f₂ : a ⟶ initialVertex τ₂} (hf : f₁ ≫ eqToHom (congrArg initialVertex h) = f₂) :
    L.map f₁ ≫ ιTwistedChainComplex L k τ₁ = L.map f₂ ≫ ιTwistedChainComplex L k τ₂ := by
  subst h
  simp only [eqToHom_refl, Category.comp_id] at hf
  rw [hf]

/-- The summand of the singular simplex `σ ∘ StdSimplex.continuousAffineMapMk v` in the twisted
chains, with coefficients transported inside `σ` from the point `σ z` to its initial vertex. -/
-- The middle object of the composite is given as the initial vertex of the affine simplex, the
-- form in which `ιTwistedChainComplex_d` and the functoriality of `L` meet it in the proofs below;
-- the transport inside `σ` reaches the same object in another, definitionally equal, form.
def twistedAffineSimplex (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop) {k : ℕ}
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) :
    L.obj ⟨TopCat.simplexMap σ z⟩ ⟶ (twistedChainComplex L).X k :=
  @CategoryStruct.comp _ _ (L.obj ⟨TopCat.simplexMap σ z⟩)
    (L.obj (initialVertex (affineSimplex σ v))) _
    (L.map (X := ⟨TopCat.simplexMap σ z⟩) (Y := initialVertex (affineSimplex σ v))
      (pathTransport σ z (affineToTop v (toTopInitialVertex ⦋k⦌))))
    (ιTwistedChainComplex L k (affineSimplex σ v))

/-- The boundary of the summand of an affine simplex of `σ` is the alternating sum of the summands
of its facets, all with coefficients transported from the same point of `σ`. -/
@[simp]
lemma twistedAffineSimplex_d (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop)
    {k : ℕ} (v : Fin (k + 2) → StdSimplex ℝ (Fin (n.unop.len + 1))) :
    twistedAffineSimplex L σ z v ≫ (twistedChainComplex L).d (k + 1) k =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • twistedAffineSimplex L σ z (v ∘ i.succAbove) := by
  rw [twistedAffineSimplex, Category.assoc, ιTwistedChainComplex_d, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, twistedAffineSimplex]
  congr 1
  refine (L.map_comp_assoc _ _ _).symm.trans (map_comp_ιTwistedChainComplex_congr
    (TopCat.δ_toSSetObjEquiv_symm_comp_affineMapMk (X.toSSetObjEquiv _ σ) v i) ?_)
  have hp : affineToTop v (toTop.map (δ i) (toTopInitialVertex ⦋k⦌)) =
      affineToTop (v ∘ i.succAbove) (toTopInitialVertex.{v} ⦋k⦌) := by
    apply ULift.ext
    rw [affineToTop_apply_down, affineToTop_apply_down, toTop_map_toTopInitialVertex_down,
      toTopInitialVertex_down]
    simp [SimplexCategory.δ]
  rw [vertexTransport_eq_pathTransport, pathTransport_affineSimplex]
  exact (Category.assoc _ _ _).trans
    ((pathTransport_comp_assoc σ _ _ _ _).trans (pathTransport_eqToHom σ _ hp))

/-- Transporting the coefficients inside `σ` changes the point from which the summand of an affine
simplex in `σ` is transported. -/
@[reassoc (attr := simp)]
lemma map_pathTransport_comp_twistedAffineSimplex (σ : (TopCat.toSSet.obj X).obj n)
    (z z' : toTop.{v}.obj n.unop) {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) :
    L.map (pathTransport σ z z') ≫ twistedAffineSimplex L σ z' v =
      twistedAffineSimplex L σ z v := by
  rw [twistedAffineSimplex, twistedAffineSimplex]
  exact (L.map_comp_assoc _ _ _).symm.trans
    (congrArg (fun f ↦ L.map f ≫ ιTwistedChainComplex L k (affineSimplex σ v))
      (pathTransport_comp σ _ _ _))

/-- The summand of an affine simplex in an affine simplex of `σ` is the summand of the composite
affine simplex of `σ`. -/
lemma twistedAffineSimplex_comp_continuousAffineMapMk (σ : (TopCat.toSSet.obj X).obj n) {m : ℕ}
    (u : Fin (m + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) (z : toTop.{v}.obj ⦋m⦌) {k : ℕ}
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) :
    twistedAffineSimplex L
        ((X.toSSetObjEquiv _).symm ((X.toSSetObjEquiv n σ).comp
          (StdSimplex.continuousAffineMapMk u))) z v =
      twistedAffineSimplex L σ (ULift.up (StdSimplex.continuousAffineMapMk u z.down))
        (StdSimplex.affineMapMk u ∘ v) := by
  have hτ : affineSimplex (affineSimplex σ u) v =
      affineSimplex σ (StdSimplex.affineMapMk u ∘ v) := by
    apply (X.toSSetObjEquiv _).injective
    ext x
    simp [← StdSimplex.comp_affineMapMk]
  have hp : affineToTop u (affineToTop v (toTopInitialVertex.{v} ⦋k⦌)) =
      affineToTop (StdSimplex.affineMapMk u ∘ v) (toTopInitialVertex.{v} ⦋k⦌) := by
    apply ULift.ext
    rw [affineToTop_apply_down, affineToTop_apply_down, affineToTop_apply_down]
    simp
  unfold twistedAffineSimplex
  refine map_comp_ιTwistedChainComplex_congr hτ ?_
  rw [pathTransport_affineSimplex]
  exact pathTransport_eqToHom σ _ hp

/-- The summand of an affine simplex in a facet of `σ` is the summand of the affine simplex of `σ`
with the pushed-forward vertices. -/
lemma twistedAffineSimplex_δ {m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋m + 1⦌) (j : Fin (m + 2))
    (z : toTop.{v}.obj ⦋m⦌) {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) :
    twistedAffineSimplex L ((TopCat.toSSet.obj X).map (δ j).op σ) z v =
      twistedAffineSimplex L σ (toTop.map (δ j) z) (StdSimplex.map j.succAbove ∘ v) := by
  have hp : toTop.map (δ j) (affineToTop v (toTopInitialVertex.{v} ⦋k⦌)) =
      affineToTop (StdSimplex.map j.succAbove ∘ v) (toTopInitialVertex.{v} ⦋k⦌) := by
    apply ULift.ext
    have h := congr($(StdSimplex.comp_affineMapMk (R := ℝ)
      (StdSimplex.affineMap j.succAbove) v) (toTopInitialVertex.{v} ⦋k⦌).down)
    simp only [ConvexSpace.AffineMap.coe_comp, Function.comp_apply,
      StdSimplex.coe_affineMap] at h
    -- The coface map of topological simplices is `StdSimplex.map` of the coface, by definition.
    have hδ (x : toTop.{v}.obj ⦋m⦌) :
        (toTop.map (δ j) x).down = StdSimplex.map j.succAbove x.down := rfl
    rw [hδ, affineToTop_apply_down, affineToTop_apply_down, StdSimplex.continuousAffineMapMk_apply,
      StdSimplex.continuousAffineMapMk_apply, h]
  rw [twistedAffineSimplex, twistedAffineSimplex]
  refine map_comp_ιTwistedChainComplex_congr
    (TopCat.toSSetObjEquiv_symm_comp_affineMapMk_δ σ v j) ?_
  rw [pathTransport_map]
  exact pathTransport_eqToHom σ _ hp

/-- The twisted singular chain with coefficients transported from the point `σ z` obtained by
pushing forward along `σ` an affine chain `c` of the simplex of `σ`: a vertex tuple `v` is sent to
the summand `TauCeti.LocalCoefficientSystem.twistedAffineSimplex L σ z v` of the singular simplex
`σ ∘ StdSimplex.continuousAffineMapMk v`. -/
def twistedSingularChain (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop) (k : ℕ)
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    L.obj ⟨TopCat.simplexMap σ z⟩ ⟶ (twistedChainComplex L).X k :=
  linearCombination ℤ (fun v ↦ twistedAffineSimplex L σ z v) c

section TwistedSingularChain

variable (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop) {k : ℕ}

@[simp]
lemma twistedSingularChain_single (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1)))
    (a : ℤ) : twistedSingularChain L σ z k (single v a) = a • twistedAffineSimplex L σ z v := by
  rw [twistedSingularChain, linearCombination_single]

@[simp]
lemma twistedSingularChain_zero : twistedSingularChain L σ z k 0 = 0 :=
  map_zero (linearCombination ℤ fun v ↦ twistedAffineSimplex L σ z v)

@[simp]
lemma twistedSingularChain_add (c d : (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain L σ z k (c + d) =
      twistedSingularChain L σ z k c + twistedSingularChain L σ z k d :=
  map_add (linearCombination ℤ fun v ↦ twistedAffineSimplex L σ z v) c d

@[simp]
lemma twistedSingularChain_sub (c d : (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain L σ z k (c - d) =
      twistedSingularChain L σ z k c - twistedSingularChain L σ z k d :=
  map_sub (linearCombination ℤ fun v ↦ twistedAffineSimplex L σ z v) c d

@[simp]
lemma twistedSingularChain_zsmul (a : ℤ)
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain L σ z k (a • c) = a • twistedSingularChain L σ z k c := by
  rw [twistedSingularChain, map_zsmul]
  -- The two integer actions on morphisms of modules agree definitionally.
  rfl

@[simp]
lemma twistedSingularChain_sum {ι : Type*} (s : Finset ι)
    (c : ι → (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain L σ z k (∑ i ∈ s, c i) = ∑ i ∈ s, twistedSingularChain L σ z k (c i) :=
  map_sum (linearCombination ℤ fun v ↦ twistedAffineSimplex L σ z v) c s

end TwistedSingularChain

/-- Pushing affine chains forward into the twisted chains commutes with the boundary. -/
lemma twistedSingularChain_boundary (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop)
    {k : ℕ} (c : (Fin (k + 2) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain L σ z k (AffineChain.boundary _ k c) =
      twistedSingularChain L σ z (k + 1) c ≫ (twistedChainComplex L).d (k + 1) k := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, twistedSingularChain_add, hc, hd, Preadditive.add_comp]
  | single v a =>
    simp [twistedAffineSimplex_d, Finset.smul_sum, mul_smul]

/-- The summand of an affine simplex in a facet of `σ`, after transporting the coefficients to
the initial vertex of the facet, is the summand of the affine simplex of `σ` with the pushed-forward
vertices. -/
@[simp]
lemma map_vertexTransport_comp_twistedAffineSimplex {m : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋m + 1⦌) (j : Fin (m + 2)) {k : ℕ}
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) :
    L.map (vertexTransport (δ j).op σ) ≫ twistedAffineSimplex L ((TopCat.toSSet.obj X).map
        (δ j).op σ) (toTopInitialVertex ⦋m⦌) v =
      twistedAffineSimplex L σ (toTopInitialVertex ⦋m + 1⦌) (StdSimplex.map j.succAbove ∘ v) := by
  rw [twistedAffineSimplex_δ]
  exact (congrArg (fun f ↦ L.map f ≫ _) (vertexTransport_eq_pathTransport _ _)).trans
    (map_pathTransport_comp_twistedAffineSimplex L σ _ _ _)

/-- Pushing affine chains forward along a facet of a singular simplex, after transporting the
coefficients to the initial vertex of the facet, is pushing their images under the facet inclusion
forward along the singular simplex. -/
lemma map_vertexTransport_comp_twistedSingularChain {m : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋m + 1⦌) (j : Fin (m + 2)) {k : ℕ}
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) :
    L.map (vertexTransport (δ j).op σ) ≫ twistedSingularChain L ((TopCat.toSSet.obj X).map
        (δ j).op σ) (toTopInitialVertex ⦋m⦌) k c =
      twistedSingularChain L σ (toTopInitialVertex ⦋m + 1⦌) k
        (AffineChain.map (StdSimplex.map j.succAbove) k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [twistedSingularChain_add, Preadditive.comp_add, hc, hd, map_add]
  | single v a =>
    rw [twistedSingularChain_single, AffineChain.map_single, twistedSingularChain_single,
      Preadditive.comp_zsmul, map_vertexTransport_comp_twistedAffineSimplex]

open BarycentricSubdivision AffineChain

/-- The barycentric subdivision of twisted singular `k`-chains: the summand of a singular simplex
`σ` is sent to the signed sum over the permutations `π` of the summands of the singular simplices
`σ ∘ StdSimplex.continuousAffineMapMk (vertex π)`, the coefficients being transported inside `σ`
from its initial vertex to the initial vertex of each of them. -/
def twistedSubdivisionX (k : ℕ) : (twistedChainComplex L).X k ⟶ (twistedChainComplex L).X k :=
  eqToHom (twistedChainComplex_X L k) ≫ Sigma.desc fun σ ↦
    ∑ π : Perm (Fin (k + 1)), π.sign • twistedAffineSimplex L σ (toTopInitialVertex ⦋k⦌) (vertex π)

/-- The subdivision of the summand of a singular simplex `σ`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChainComplex_twistedSubdivisionX {k : ℕ} (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ιTwistedChainComplex L k σ ≫ twistedSubdivisionX L k =
      ∑ π : Perm (Fin (k + 1)), π.sign •
        twistedAffineSimplex L σ (toTopInitialVertex ⦋k⦌) (vertex π) := by
  simp [twistedSubdivisionX]

/-- On the summand of a singular simplex `σ`, the subdivision is the push-forward along `σ` of the
subdivision of the standard simplex. -/
lemma ιTwistedChainComplex_twistedSubdivisionX_eq {k : ℕ} (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ιTwistedChainComplex L k σ ≫ twistedSubdivisionX L k =
      twistedSingularChain L σ (toTopInitialVertex ⦋k⦌) k (subdivision _ k (simplex k)) := by
  have hv : ⇑(StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single : Fin (k + 1) → _)) = id := by
    funext x
    simp [StdSimplex.affineMapMk_apply]
  simp [simplex_def, hv, Units.smul_def]

/-- The barycentric subdivision of twisted singular chains is a chain map: `∂ S = S ∂`. -/
def twistedSubdivisionChainMap : twistedChainComplex L ⟶ twistedChainComplex L where
  f k := twistedSubdivisionX L k
  comm' := by
    rintro _ k rfl
    refine twistedChainComplex_hom_ext L fun σ ↦ ?_
    simp only [ιTwistedChainComplex_twistedSubdivisionX_assoc, Units.smul_def,
      Preadditive.sum_comp, Preadditive.zsmul_comp, twistedAffineSimplex_d,
      ιTwistedChainComplex_d_assoc, Category.assoc, ιTwistedChainComplex_twistedSubdivisionX,
      Preadditive.comp_sum, Preadditive.comp_zsmul, map_vertexTransport_comp_twistedAffineSimplex]
    simp only [← Units.smul_def]
    exact sum_sign_boundary fun w ↦ twistedAffineSimplex L σ (toTopInitialVertex ⦋k + 1⦌) w

@[simp]
lemma twistedSubdivisionChainMap_f (k : ℕ) :
    (twistedSubdivisionChainMap L).f k = twistedSubdivisionX L k := (rfl)

/-- Pushing the standard simplex forward along a singular simplex gives its summand. -/
lemma twistedSingularChain_simplex {k : ℕ} (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    twistedSingularChain L σ (toTopInitialVertex ⦋k⦌) k (simplex k) =
      ιTwistedChainComplex L k σ := by
  have hσ : affineSimplex σ (StdSimplex.single : Fin (k + 1) → _) = σ := by
    apply (X.toSSetObjEquiv _).injective
    ext z
    simp [StdSimplex.affineMapMk_apply]
  have hp : affineToTop (StdSimplex.single : Fin (k + 1) → _) (toTopInitialVertex.{v} ⦋k⦌) =
      toTopInitialVertex.{v} ⦋k⦌ := by
    apply ULift.ext
    rw [affineToTop_apply_down, StdSimplex.continuousAffineMapMk_apply, toTopInitialVertex_down,
      StdSimplex.affineMapMk_single]
  rw [simplex_def, twistedSingularChain_single, one_smul, twistedAffineSimplex]
  refine (map_comp_ιTwistedChainComplex_congr hσ ?_).trans
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp])
  exact (pathTransport_eqToHom σ _ hp).trans (pathTransport_self σ _)

/-- The barycentric subdivision is the identity on twisted singular `0`-chains. -/
@[simp]
lemma twistedSubdivisionX_zero : twistedSubdivisionX L 0 = 𝟙 _ := by
  refine twistedChainComplex_hom_ext L fun σ ↦ ?_
  rw [ιTwistedChainComplex_twistedSubdivisionX_eq, subdivision_zero, LinearMap.id_apply,
    twistedSingularChain_simplex, Category.comp_id]

/-- The prism operator on twisted singular `k`-chains: the summand of a singular simplex `σ` is
sent to the push-forward along `σ` of the prism operator of the standard simplex. -/
def twistedPrismX (k : ℕ) : (twistedChainComplex L).X k ⟶ (twistedChainComplex L).X (k + 1) :=
  eqToHom (twistedChainComplex_X L k) ≫ Sigma.desc fun σ ↦
    twistedSingularChain L σ (toTopInitialVertex ⦋k⦌) (k + 1) (prismModel k)

/-- The prism operator on the summand of a singular simplex `σ`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChainComplex_twistedPrismX {k : ℕ} (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ιTwistedChainComplex L k σ ≫ twistedPrismX L k =
      twistedSingularChain L σ (toTopInitialVertex ⦋k⦌) (k + 1) (prismModel k) := by
  simp [twistedPrismX]

/-- The twisted prism operator vanishes on `0`-chains. -/
@[simp]
lemma twistedPrismX_zero : twistedPrismX L 0 = 0 := by
  refine twistedChainComplex_hom_ext L fun σ ↦ ?_
  simp

/-- The chain homotopy formula for the twisted prism operator in positive degrees:
`∂ P + P ∂ = 1 - S`. -/
lemma twistedPrismX_boundary_add_boundary_twistedPrismX (k : ℕ) :
    (twistedChainComplex L).d (k + 1) k ≫ twistedPrismX L k +
        twistedPrismX L (k + 1) ≫ (twistedChainComplex L).d (k + 2) (k + 1) =
      𝟙 _ - twistedSubdivisionX L (k + 1) := by
  refine twistedChainComplex_hom_ext L fun σ ↦ ?_
  have h := congrArg (twistedSingularChain L σ (toTopInitialVertex ⦋k + 1⦌) (k + 1))
    (boundary_prism_add_prism_boundary (E := StdSimplex ℝ (Fin (k + 2))) k (simplex (k + 1)))
  rw [twistedSingularChain_add, twistedSingularChain_sub, twistedSingularChain_boundary,
    prism_simplex, twistedSingularChain_simplex, ← ιTwistedChainComplex_twistedSubdivisionX_eq,
    prism_boundary_simplex, twistedSingularChain_sum] at h
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
    ιTwistedChainComplex_twistedPrismX_assoc, ιTwistedChainComplex_d_assoc, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Category.assoc, ιTwistedChainComplex_twistedPrismX,
    map_vertexTransport_comp_twistedSingularChain]
  rw [← h]
  simp only [twistedSingularChain_zsmul]
  exact add_comm _ _

/-- **Barycentric subdivision of twisted chains is chain homotopic to the identity.** The twisted
prism operator is a chain homotopy from the identity of the twisted singular chain complex to its
barycentric subdivision. -/
def twistedSubdivisionHomotopy : Homotopy (𝟙 _) (twistedSubdivisionChainMap L) :=
  Homotopy.equivSubZero.symm <| Homotopy.mkChainComplex _ (twistedPrismX L) (by simp)
    fun k ↦ by simp [twistedPrismX_boundary_add_boundary_twistedPrismX]

@[simp]
lemma twistedSubdivisionHomotopy_hom (k : ℕ) :
    (twistedSubdivisionHomotopy L).hom k (k + 1) = twistedPrismX L k :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ k

/-- Barycentric subdivision induces the identity on twisted singular homology. -/
@[simp]
lemma homologyMap_twistedSubdivisionChainMap (k : ℕ) :
    HomologicalComplex.homologyMap (twistedSubdivisionChainMap L) k = 𝟙 _ := by
  rw [← (twistedSubdivisionHomotopy L).homologyMap_eq k, HomologicalComplex.homologyMap_id]

/-- The subdivision of the summand of an affine simplex of `σ` is the signed sum of the summands
of the affine simplices of its barycentric subdivision. -/
lemma twistedAffineSimplex_comp_twistedSubdivisionX (σ : (TopCat.toSSet.obj X).obj n)
    (z : toTop.{v}.obj n.unop) {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) :
    twistedAffineSimplex L σ z v ≫ twistedSubdivisionX L k =
      ∑ π : Perm (Fin (k + 1)), π.sign •
        twistedAffineSimplex L σ z (StdSimplex.affineMapMk v ∘ vertex π) := by
  rw [twistedAffineSimplex, Category.assoc, ιTwistedChainComplex_twistedSubdivisionX,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  rw [Units.smul_def, Units.smul_def, Preadditive.comp_zsmul,
    twistedAffineSimplex_comp_continuousAffineMapMk]
  congr 1
  exact map_pathTransport_comp_twistedAffineSimplex L σ z _ _

/-- Pushing the subdivision of an affine chain forward into the twisted chains gives the
barycentric subdivision of the pushed-forward chain. -/
lemma twistedSingularChain_subdivision (σ : (TopCat.toSSet.obj X).obj n)
    (z : toTop.{v}.obj n.unop) {k : ℕ}
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain L σ z k (subdivision _ k c) =
      twistedSingularChain L σ z k c ≫ twistedSubdivisionX L k := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, twistedSingularChain_add, hc, hd, Preadditive.add_comp]
  | single v a =>
    simp [twistedAffineSimplex_comp_twistedSubdivisionX, Finset.smul_sum, mul_smul,
      Units.smul_def]

/-- Pushing an iterated barycentric subdivision of an affine chain forward into the twisted chains
is the corresponding iterate of the twisted subdivision operator. -/
lemma twistedSingularChain_subdivision_iterate (σ : (TopCat.toSSet.obj X).obj n)
    (z : toTop.{v}.obj n.unop) {k r : ℕ}
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain L σ z k ((subdivision _ k)^[r] c) =
      twistedSingularChain L σ z k c ≫
        ((CategoryTheory.End.of (twistedSubdivisionChainMap L)) ^ r).f k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', twistedSingularChain_subdivision, ih, pow_succ']
    simp [Category.assoc]

section Naturality

variable {L} {K : LocalCoefficientSystem.{u, v, max v w} R X}

/-- The summands of affine simplices are natural in the coefficient system. -/
@[reassoc (attr := simp)]
lemma twistedAffineSimplex_comp_twistedChainComplexCoefficientMap_f (η : L ⟶ K)
    (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop) {k : ℕ}
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) :
    twistedAffineSimplex L σ z v ≫ (twistedChainComplexCoefficientMap η).f k =
      η.app _ ≫ twistedAffineSimplex K σ z v := by
  rw [twistedAffineSimplex, twistedAffineSimplex, Category.assoc,
    ιTwistedChainComplex_twistedChainComplexCoefficientMap_f, ← Category.assoc,
    ← Category.assoc]
  exact congrArg (· ≫ _) (η.naturality _)

/-- Barycentric subdivision of twisted chains is natural in the coefficient system. -/
@[reassoc]
lemma twistedChainComplexCoefficientMap_comp_twistedSubdivisionChainMap (η : L ⟶ K) :
    twistedChainComplexCoefficientMap η ≫ twistedSubdivisionChainMap K =
      twistedSubdivisionChainMap L ≫ twistedChainComplexCoefficientMap η := by
  ext k : 1
  refine twistedChainComplex_hom_ext L fun σ ↦ ?_
  simp [ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc, Preadditive.sum_comp,
    Preadditive.comp_sum, Units.smul_def]

variable (f : X ⟶ Y) (M : LocalCoefficientSystem.{u, v, max v w} R Y)

/-- A continuous map sends the summand of an affine simplex of `σ` to the summand of the same
affine simplex of the image of `σ`. -/
@[reassoc (attr := simp)]
lemma twistedAffineSimplex_comp_twistedChainComplexMap_f (σ : (TopCat.toSSet.obj X).obj n)
    (z : toTop.{v}.obj n.unop) {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) :
    twistedAffineSimplex ((pullback f.hom).obj M) σ z v ≫ (twistedChainComplexMap f M).f k =
      twistedAffineSimplex M ((TopCat.toSSet.map f).app n σ) z v := by
  rw [twistedAffineSimplex, twistedAffineSimplex, Category.assoc,
    ιTwistedChainComplex_twistedChainComplexMap_f]
  exact congrArg (fun g ↦ M.map g ≫ _) (map_pathTransport f σ z _)

/-- Pushing affine chains forward into the twisted chains is natural in the space. -/
@[reassoc (attr := simp)]
lemma twistedSingularChain_comp_twistedChainComplexMap_f (σ : (TopCat.toSSet.obj X).obj n)
    (z : toTop.{v}.obj n.unop) {k : ℕ}
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (n.unop.len + 1))) →₀ ℤ) :
    twistedSingularChain ((pullback f.hom).obj M) σ z k c ≫ (twistedChainComplexMap f M).f k =
      twistedSingularChain M ((TopCat.toSSet.map f).app n σ) z k c := by
  induction c using Finsupp.induction_linear with
  -- The two sides differ only in the form of the source object, which `rfl` sees through.
  | zero =>
    rw [twistedSingularChain_zero, twistedSingularChain_zero, Limits.zero_comp]
    rfl
  | add c d hc hd =>
    rw [twistedSingularChain_add, twistedSingularChain_add, Preadditive.add_comp, hc, hd]
    rfl
  | single v a =>
    rw [twistedSingularChain_single, twistedSingularChain_single, Preadditive.zsmul_comp,
      twistedAffineSimplex_comp_twistedChainComplexMap_f]
    rfl

/-- Barycentric subdivision of twisted chains is natural in the space. -/
@[reassoc]
lemma twistedChainComplexMap_comp_twistedSubdivisionChainMap :
    twistedChainComplexMap f M ≫ twistedSubdivisionChainMap M =
      twistedSubdivisionChainMap ((pullback f.hom).obj M) ≫ twistedChainComplexMap f M := by
  ext k : 1
  refine twistedChainComplex_hom_ext _ fun σ ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, twistedSubdivisionChainMap_f,
    twistedSubdivisionChainMap_f]
  calc _ = ιTwistedChainComplex M k ((TopCat.toSSet.map f).app _ σ) ≫ twistedSubdivisionX M k :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (ιTwistedChainComplex_twistedChainComplexMap_f f M k σ))
    _ = ∑ π : Perm (Fin (k + 1)), π.sign • twistedAffineSimplex M
          ((TopCat.toSSet.map f).app _ σ) (toTopInitialVertex ⦋k⦌) (vertex π) :=
        ιTwistedChainComplex_twistedSubdivisionX M _
    _ = _ := by
      rw [ιTwistedChainComplex_twistedSubdivisionX_assoc, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun π _ ↦ ?_
      rw [Units.smul_def, Units.smul_def, Preadditive.zsmul_comp,
        twistedAffineSimplex_comp_twistedChainComplexMap_f]
      -- The two sides differ only in the form of the source object, which `rfl` sees through.
      rfl

/-- The twisted prism operator is natural in the space. -/
@[reassoc]
lemma twistedChainComplexMap_f_comp_twistedPrismX (k : ℕ) :
    (twistedChainComplexMap f M).f k ≫ twistedPrismX M k =
      twistedPrismX ((pullback f.hom).obj M) k ≫ (twistedChainComplexMap f M).f (k + 1) := by
  refine twistedChainComplex_hom_ext _ fun σ ↦ ?_
  calc _ = ιTwistedChainComplex M k ((TopCat.toSSet.map f).app _ σ) ≫ twistedPrismX M k :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (ιTwistedChainComplex_twistedChainComplexMap_f f M k σ))
    _ = twistedSingularChain M ((TopCat.toSSet.map f).app _ σ) (toTopInitialVertex ⦋k⦌) (k + 1)
          (prismModel k) := ιTwistedChainComplex_twistedPrismX M _
    _ = _ := by
      rw [ιTwistedChainComplex_twistedPrismX_assoc,
        twistedSingularChain_comp_twistedChainComplexMap_f]

end Naturality

end LocalCoefficientSystem

end TauCeti
