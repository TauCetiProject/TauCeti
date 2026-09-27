/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution

/-!
# Graded commutativity of the cup product in bidegree `(1, 1)`

Let `P : TopPairing X Y Z` be a coefficient pairing of topological representations of a
topological group `G`, and let `P.flip : TopPairing Y X Z` be the opposite pairing
`TauCeti.TopPairing.flip`, `P.flip.bil y x = P.bil x y`. On continuous cohomology the cup
products in the two orders are related by graded commutativity,
`a ⌣_P b = (-1)^{mn} (b ⌣_{P.flip} a)`. This file proves the case of bidegree `(1, 1)`,

```text
cup P 1 1 a b = - cup P.flip 1 1 b a,
```

which is the case the cup square `H¹(G, M) × H¹(G, M) → H²(G, M)` of a commutative coefficient
ring is stated against.

The identity fails on cochains, and the proof is a homotopy. For homogeneous one-cochains `a` and
`b` the **cup-one product** `TauCeti.TopPairing.cupOneCochain a b` is the pointwise pairing
`(g₀, g₁) ↦ μ (a g₀ g₁) (b g₀ g₁)`, the bidegree-`(1, 1)` case of Steenrod's `∪₁`. When `a` and
`b` are cocycles, its differential is `-(a ⌣ b) - (b ⌣ᵒᵖ a)`
(`TauCeti.TopPairing.d_cupOneCochain`): expanding `μ (a g₀ g₂) (b g₀ g₂)` along the cocycle
identities `a g₀ g₂ = a g₀ g₁ + a g₁ g₂` and `b g₀ g₂ = b g₀ g₁ + b g₁ g₂` leaves exactly the two
cross terms `μ (a g₀ g₁) (b g₁ g₂)` and `μ (a g₁ g₂) (b g₀ g₁)`. The class-level statement follows
because the descended cup product is the class of the cup product of cocycles.

The same homotopy is already formalized on the explicit inhomogeneous model of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product`:
`TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1` is the cochain identity
`(a ⌣_μ b) + (b ⌣_{μᵒᵖ} a) = d¹ (g ↦ -μ (a g) (b g))` for inhomogeneous `1`-cocycles, and
`TauCeti.ContCohomology.explicitCup11_eq_neg_flip` is its descent to the explicit
`H¹ × H¹ → H²`. This file is the homogeneous-resolution counterpart of those two declarations,
stated on Mathlib's `continuousCohomology` so that it applies to `TauCeti.TopPairing.cup`. The
two primitives differ by a sign: the inhomogeneous one is the negated pointwise pairing
`g ↦ -μ (a g) (b g)`, whereas `cupOneCochain a b` is the unsigned pointwise pairing
`(g₀, g₁) ↦ μ (a g₀ g₁) (b g₀ g₁)` and the sign is carried by its differential,
`d (cupOneCochain a b) = -(a ⌣ b) - (b ⌣ᵒᵖ a)`. Equivalently
`(a ⌣ b) + (b ⌣ᵒᵖ a) = d (-cupOneCochain a b)`, the homogeneous form of the inhomogeneous
identity. The two differentials also follow different conventions (the inhomogeneous `d¹` of
`Cup.Product` against `TopRep.homogeneousCochains.d_one_apply`,
`(d a) g₀ g₁ g₂ = a g₁ g₂ - a g₀ g₂ + a g₀ g₁`), but the class-level statement only needs that
the sum `(a ⌣ b) + (b ⌣ᵒᵖ a)` is a coboundary, which neither the sign of the primitive nor the
convention affects; both descents therefore read `cup a b = - cup b a`.

## Main definitions

* `TauCeti.TopPairing.cupOne`, `TauCeti.TopPairing.cupOneCochain`: the cup-one product of two
  degree-one elements of the resolution, and of two homogeneous one-cochains.

## Main results

* `TauCeti.TopPairing.d_cupOneCochain`: the differential of the cup-one product of two cocycles
  is `-(a ⌣ b) - (b ⌣ᵒᵖ a)`.
* `TauCeti.TopPairing.cup_one_one_eq_neg_flip`: **graded commutativity in bidegree `(1, 1)`**,
  `cup P 1 1 a b = - cup P.flip 1 1 b a`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, (3.6).
* N. E. Steenrod, *Products of cocycles and extensions of mappings*, Ann. of Math. 48 (1947),
  290–320, for the `∪₁` product.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, (1.4.4).
-/

public section

namespace TauCeti

open CategoryTheory ContRepresentation TopRep _root_.ContinuousCohomology ContinuousMap

universe u v w

namespace TopPairing

section cupOne

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-! ### The cup-one product of one-cochains -/

/-- The cup-one product of two degree-one elements of the resolution, as a plain function:
`(a, b) ↦ ((g₀, g₁) ↦ μ (a g₀ g₁) (b g₀ g₁))`, built from the pointwise pairing so that the value
is continuous in `(g₀, g₁)`. Its bilinearity is recorded by `TauCeti.TopPairing.cupOne`. -/
private def cupOneAux (a : (TopRep.resolution'X X 1).V) (b : (TopRep.resolution'X Y 1).V) :
    (TopRep.resolution'X Z 1).V :=
  (⟨fun q : C(G, X.V) × C(G, Y.V) ↦ (P.pointwise 0 0 rfl).comp (q.1.prodMk q.2),
    (continuous_postcomp _).comp ContinuousMap.continuous_prodMk⟩ :
      C(C(G, X.V) × C(G, Y.V), C(G, Z.V))).comp
    ((a : C(G, C(G, X.V))).prodMk (b : C(G, C(G, Y.V))))

private theorem cupOneAux_apply (a : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y 1).V) (g₀ g₁ : G) :
    (P.cupOneAux a b : C(G, C(G, Z.V))) g₀ g₁ = P.bil (a g₀ g₁) (b g₀ g₁) := by
  rw [cupOneAux]
  exact P.pointwise_zero_apply rfl _ _

private theorem cupOneAux_add_left (a a' : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y 1).V) :
    P.cupOneAux (a + a') b = P.cupOneAux a b + P.cupOneAux a' b := by
  ext g₀ g₁
  simp only [P.cupOneAux_apply, ContinuousMap.add_apply, map_add, LinearMap.add_apply]

private theorem cupOneAux_smul_left (r : R) (a : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y 1).V) :
    P.cupOneAux (r • a) b = r • P.cupOneAux a b := by
  ext g₀ g₁
  simp only [P.cupOneAux_apply, ContinuousMap.smul_apply, map_smul, LinearMap.smul_apply]

private theorem cupOneAux_add_right (a : (TopRep.resolution'X X 1).V)
    (b b' : (TopRep.resolution'X Y 1).V) :
    P.cupOneAux a (b + b') = P.cupOneAux a b + P.cupOneAux a b' := by
  ext g₀ g₁
  simp only [P.cupOneAux_apply, ContinuousMap.add_apply, map_add]

private theorem cupOneAux_smul_right (r : R) (a : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y 1).V) :
    P.cupOneAux a (r • b) = r • P.cupOneAux a b := by
  ext g₀ g₁
  simp only [P.cupOneAux_apply, ContinuousMap.smul_apply, map_smul]

/-- **The cup-one product on degree-one elements of the resolution**, as an `R`-bilinear map: for
`a : C(G, C(G, X.V))` and `b : C(G, C(G, Y.V))`, the pointwise pairing
`(g₀, g₁) ↦ μ (a g₀ g₁) (b g₀ g₁)`. It is the bidegree-`(1, 1)` case of Steenrod's `∪₁`
product, and the homotopy behind graded commutativity of the cup product in that bidegree. -/
def cupOne : (TopRep.resolution'X X 1).V →ₗ[R] (TopRep.resolution'X Y 1).V →ₗ[R]
    (TopRep.resolution'X Z 1).V :=
  LinearMap.mk₂ R P.cupOneAux P.cupOneAux_add_left P.cupOneAux_smul_left P.cupOneAux_add_right
    P.cupOneAux_smul_right

@[simp]
theorem cupOne_apply (a : (TopRep.resolution'X X 1).V) (b : (TopRep.resolution'X Y 1).V)
    (g₀ g₁ : G) :
    (P.cupOne a b : C(G, C(G, Z.V))) g₀ g₁ = P.bil (a g₀ g₁) (b g₀ g₁) := by
  rw [cupOne, LinearMap.mk₂_apply, cupOneAux_apply]

/-- The cup-one product is equivariant. -/
theorem cupOne_ρ (g : G) (a : (TopRep.resolution'X X 1).V) (b : (TopRep.resolution'X Y 1).V) :
    P.cupOne ((TopRep.resolution'X X 1).ρ g a) ((TopRep.resolution'X Y 1).ρ g b) =
      (TopRep.resolution'X Z 1).ρ g (P.cupOne a b) := by
  ext g₀ g₁
  -- both sides evaluated at `(g₀, g₁)` are `μ (g • a (g⁻¹g₀) (g⁻¹g₁)) (g • b (g⁻¹g₀) (g⁻¹g₁))`
  simp only [coind₁_apply_apply, P.cupOne_apply, P.equivariant]

/-- **The cup-one product of homogeneous one-cochains**, as an `R`-bilinear map: the cup-one
product of the underlying elements of the resolution, which is invariant by equivariance. -/
def cupOneCochain : (TopRep.homogeneousCochains X).X 1 →ₗ[R]
    (TopRep.homogeneousCochains Y).X 1 →ₗ[R] (TopRep.homogeneousCochains Z).X 1 :=
  LinearMap.mk₂ R
    (fun a b ↦ ⟨P.cupOne a.1 b.1, fun g ↦ by rw [← P.cupOne_ρ, a.2 g, b.2 g]⟩)
    (fun a a' b ↦ Subtype.ext (LinearMap.map_add₂ _ a.1 a'.1 b.1))
    (fun r a b ↦ Subtype.ext (LinearMap.map_smul₂ _ r a.1 b.1))
    (fun a b b' ↦ Subtype.ext (map_add _ b.1 b'.1))
    (fun r a b ↦ Subtype.ext (LinearMap.map_smul _ r b.1))

/-- The underlying resolution element of the cup-one product of homogeneous cochains is the
cup-one product of the underlying elements. -/
-- Not a `simp` lemma: as for `coe_cupCochain`, `simp` rewrites the implicit carrier
-- `(TopRep.resolution' Z).X 1` on the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the statement is not in `simp`-normal
-- form; use it with `rw`.
theorem coe_cupOneCochain (a : (TopRep.homogeneousCochains X).X 1)
    (b : (TopRep.homogeneousCochains Y).X 1) :
    Subtype.val (P.cupOneCochain a b) = P.cupOne a.1 b.1 := by
  rw [cupOneCochain, LinearMap.mk₂_apply]

/-- The cup-one product of homogeneous one-cochains, evaluated:
`(a ∪₁ b) g₀ g₁ = μ (a g₀ g₁) (b g₀ g₁)`. -/
-- Not a `simp` lemma, for the same reason as `coe_cupOneCochain`: the implicit carrier
-- `(TopRep.resolution' Z).X 1` of the left-hand side is not in `simp`-normal form; use it with
-- `rw` or `simp only`.
theorem cupOneCochain_apply (a : (TopRep.homogeneousCochains X).X 1)
    (b : (TopRep.homogeneousCochains Y).X 1) (g₀ g₁ : G) :
    ((P.cupOneCochain a b).val : C(G, C(G, Z.V))) g₀ g₁ = P.bil (a.val g₀ g₁) (b.val g₀ g₁) := by
  rw [coe_cupOneCochain, cupOne_apply]

/-! ### The differential of the cup-one product -/

/-- **The differential of the cup-one product of two cocycles** is `-(a ⌣ b) - (b ⌣ᵒᵖ a)`: the
cup-one product is a homotopy between the cup product and the negative of the opposite cup
product. -/
theorem d_cupOneCochain {a : (TopRep.homogeneousCochains X).X 1}
    (ha : ((TopRep.homogeneousCochains X).d 1 (1 + 1)).hom a = 0)
    {b : (TopRep.homogeneousCochains Y).X 1}
    (hb : ((TopRep.homogeneousCochains Y).d 1 (1 + 1)).hom b = 0) :
    ((TopRep.homogeneousCochains Z).d 1 (1 + 1)).hom (P.cupOneCochain a b) =
      -P.cupCochain 1 1 a b - P.flip.cupCochain 1 1 b a := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  -- evaluate both sides at `(g₀, g₁, g₂)`
  rw [Submodule.coe_sub, Submodule.coe_neg]
  simp only [homogeneousCochains.d_one_apply (X := Z), P.cupOneCochain_apply,
    ContinuousMap.sub_apply, ContinuousMap.neg_apply, P.cupCochain_one_one_apply,
    P.flip.cupCochain_one_one_apply, flip_bil]
  -- expand `μ (a g₀ g₂) (b g₀ g₂)` along the two cocycle identities
  rw [homogeneousCochains.apply_eq_add_of_d_eq_zero ha g₀ g₁ g₂,
    homogeneousCochains.apply_eq_add_of_d_eq_zero hb g₀ g₁ g₂]
  simp only [map_add, LinearMap.add_apply]
  abel

/-! ### Graded commutativity on classes -/

/-- The classes of `a ⌣ b` and of `b ⌣ᵒᵖ a` add to zero, for one-cocycles `a` and `b`. -/
theorem π_cupCocycles_add_π_flip_cupCocycles_one_one (a : cocycles X 1) (b : cocycles Y 1) :
    π Z (1 + 1) (P.cupCocycles 1 1 a b) + π Z (1 + 1) (P.flip.cupCocycles 1 1 b a) = 0 := by
  set L := homogeneousCochains Z
  rw [← map_add,
    L.homologyπ_eq_zero_iff (1 + 1) (m := 1) (CochainComplex.prev_nat_succ 1)]
  refine ⟨-P.cupOneCochain ((homogeneousCochains X).iCycles 1 a)
    ((homogeneousCochains Y).iCycles 1 b), L.iCycles_injective (1 + 1) ?_⟩
  rw [L.iCycles_toCycles_apply, map_neg, P.d_cupOneCochain
    ((homogeneousCochains X).d_iCycles_apply (1 + 1) a)
    ((homogeneousCochains Y).d_iCycles_apply (1 + 1) b), map_add, iCycles_cupCocycles,
    iCycles_cupCocycles]
  abel

/-- **Graded commutativity of the cup product in bidegree `(1, 1)`**:
`cup P 1 1 a b = - cup P.flip 1 1 b a`. -/
theorem cup_one_one_eq_neg_flip (a : continuousCohomology 1 X) (b : continuousCohomology 1 Y) :
    P.cup 1 1 a b = -P.flip.cup 1 1 b a := by
  obtain ⟨a, rfl⟩ := (homogeneousCochains X).homologyπ_surjective 1 a
  obtain ⟨b, rfl⟩ := (homogeneousCochains Y).homologyπ_surjective 1 b
  rw [cup_π, cup_π, eq_neg_iff_add_eq_zero]
  exact P.π_cupCocycles_add_π_flip_cupCocycles_one_one a b

end cupOne

end TopPairing

end TauCeti
