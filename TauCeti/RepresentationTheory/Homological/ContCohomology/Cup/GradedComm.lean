/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution

/-!
# Graded commutativity of the cup product in bidegrees `(0, n)` and `(1, n)`

Let `P : TopPairing X Y Z` be a coefficient pairing of topological representations of a
topological group `G`, and let `P.flip : TopPairing Y X Z` be the opposite pairing
`TauCeti.TopPairing.flip`, `P.flip.bil y x = P.bil x y`. On continuous cohomology the cup
products in the two orders are related by graded commutativity,
`a ⌣_P b = (-1)^{mn} (b ⌣_{P.flip} a)`. This file proves the cases in which the first
degree is zero or one. In bidegree `(1, 1)` the result specializes to

```text
cup P 1 1 a b = - cup P.flip 1 1 b a,
```

which is the identity against which the cup square `H¹(G, M) × H¹(G, M) → H²(G, M)` of a
commutative coefficient ring is stated.

In bidegree `(0, n)` the identity already holds on cocycles. A homogeneous zero-cocycle is a
constant function, and the two Alexander–Whitney products therefore pair the same constant
coefficient with the same value of the `n`-cochain. The recursion on Mathlib's iterated-curried
coinduction resolution is recorded by
`TauCeti.TopPairing.resolutionCupPairing_zero_eq_flip`; its restrictions to homogeneous cochains
and cohomology are `TauCeti.TopPairing.cupCochain_zero_eq_flip` and
`TauCeti.TopPairing.cup_zero_eq_flip`.

In bidegree `(1, 1)` the identity fails on cochains, and the proof is a homotopy. For homogeneous
one-cochains `a` and `b` the **cup-one product** `TauCeti.TopPairing.cupOneCochain a b` is the
pointwise pairing
`(g₀, g₁) ↦ μ (a g₀ g₁) (b g₀ g₁)`, the bidegree-`(1, 1)` case of Steenrod's `∪₁`. When `a` and
`b` are cocycles, its differential is `-(a ⌣ b) - (b ⌣ᵒᵖ a)`
(`TauCeti.TopPairing.d_cupOneCochain`): expanding `μ (a g₀ g₂) (b g₀ g₂)` along the cocycle
identities `a g₀ g₂ = a g₀ g₁ + a g₁ g₂` and `b g₀ g₂ = b g₀ g₁ + b g₁ g₂` leaves exactly the two
cross terms `μ (a g₀ g₁) (b g₁ g₂)` and `μ (a g₁ g₂) (b g₀ g₁)`. The class-level statement follows
because the descended cup product is the class of the cup product of cocycles.

For every positive degree `n + 1`, `TauCeti.TopPairing.cupOneLeftCochain` extends this homotopy
to bidegree `(1, n + 1)`. Its homogeneous formula is
`(a ∪₁ b) (g₀, …, gₙ₊₁) = μ (a g₀ gₙ₊₁) (b g₀ … gₙ₊₁)`. Its differential is the negative
ordinary cup plus `(-1)^(n+1)` times the opposite cup, so it descends to graded commutativity in
all bidegrees whose first degree is one.

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
* `TauCeti.TopPairing.cupOneLeft`, `TauCeti.TopPairing.cupOneLeftCochain`: the cup-one product of
  a degree-one element and a positive-degree element, on the resolution and on homogeneous
  cochains.

## Main results

* `TauCeti.TopPairing.cup_zero_eq_flip`: **graded commutativity in bidegree `(0, n)`** for every
  `n`, with the degree transport between `n + 0` and `0 + n` explicit.
* `TauCeti.TopPairing.d_cupOneCochain`: the differential of the cup-one product of two cocycles
  is `-(a ⌣ b) - (b ⌣ᵒᵖ a)`.
* `TauCeti.TopPairing.cup_one_one_eq_neg_flip`: **graded commutativity in bidegree `(1, 1)`**,
  `cup P 1 1 a b = - cup P.flip 1 1 b a`.
* `TauCeti.TopPairing.cup_one_succ_eq_signed_flip`: **graded commutativity in every bidegree
  `(1, n + 1)`**, with the degree transport and sign explicit.

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

section degreeZero

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-! ### Graded commutativity with a degree-zero cocycle -/

/-- Pairing a fixed coefficient pointwise with an `(n + 1)`-fold iterated function is the
Alexander–Whitney pairing in the opposite order against the constant zero-degree resolution
element. This is the recursive identity behind graded commutativity in bidegree `(0, n)`. -/
private theorem pointwise_succ_eq_flip_resolutionCup : ∀ (n k : ℕ) (hk : k = n) (x : X.V)
    (b : (TopRep.resolutionX Y (n + 1)).V),
    P.pointwise (n + 1) (k + 1) (congrArg Nat.succ hk) (x, b) =
      P.flip.resolutionCup n 0 k (by omega) (b, (TopRep.d X 0).hom x)
  | 0, 0, _, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.pointwise_succ_apply, P.pointwise_zero_apply,
        P.flip.resolutionCup_zero_apply, P.flip.pointwise_zero_apply, flip_bil]
      rfl
  | n + 1, k + 1, hk, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.pointwise_succ_apply, P.flip.resolutionCup_succ_apply]
      exact pointwise_succ_eq_flip_resolutionCup n k (Nat.succ.inj hk) x (b g)

/-- The Alexander–Whitney pairing of the constant zero-degree resolution element with a degree
`n` element agrees with the opposite pairing in bidegree `(n, 0)`. -/
private theorem resolutionCup_zero_eq_flip : ∀ (n k : ℕ) (hk : k = n) (x : X.V)
    (b : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup 0 n k (by omega) ((TopRep.d X 0).hom x, b) =
      P.flip.resolutionCup n 0 k (by omega) (b, (TopRep.d X 0).hom x)
  | 0, 0, _, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.resolutionCup_zero_apply, P.flip.resolutionCup_zero_apply,
        P.pointwise_zero_apply, P.flip.pointwise_zero_apply, flip_bil]
  | n + 1, k + 1, hk, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.resolutionCup_zero_apply, P.flip.resolutionCup_succ_apply]
      exact P.pointwise_succ_eq_flip_resolutionCup n k (Nat.succ.inj hk) x (b g)

/-- **Graded commutativity on the resolution in bidegree `(0, n)`**, for a constant
zero-degree element. The opposite product is transported from degree `n + 0` to degree `0 + n`.
-/
theorem resolutionCupPairing_zero_eq_flip (n : ℕ) (x : X.V)
    (b : (TopRep.resolution'X Y n).V) :
    P.resolutionCupPairing 0 n ((TopRep.d X 0).hom x) b =
      ((TopRep.resolution Z).XIsoOfEq (by omega : n + 0 + 1 = 0 + n + 1)).hom.hom
        (P.flip.resolutionCupPairing n 0 b ((TopRep.d X 0).hom x)) := by
  rw [resolutionCupPairing_apply, resolutionCupPairing_apply]
  calc
    _ = P.flip.resolutionCup n 0 (0 + n) (by omega)
        (b, (TopRep.d X 0).hom x) :=
      P.resolutionCup_zero_eq_flip n (0 + n) (by omega) x b
    _ = ((TopRep.resolution Z).XIsoOfEq
          (by omega : n + 0 + 1 = 0 + n + 1)).hom.hom
        (P.flip.resolutionCup n 0 (n + 0) (Nat.add_comm n 0)
          (b, (TopRep.d X 0).hom x)) :=
      (P.flip.resolutionCup_cast (Nat.add_comm n 0) (by omega)
        (by omega : n + 0 + 1 = 0 + n + 1) (b, (TopRep.d X 0).hom x)).symm

/-- **Graded commutativity of homogeneous cochains in bidegree `(0, n)`**: if `a` is a
zero-cocycle, then `a ⌣_P b` is the degree transport of `b ⌣_{P.flip} a`. No cocycle condition
on `b` is needed. -/
theorem cupCochain_zero_eq_flip (n : ℕ) {a : (TopRep.homogeneousCochains X).X 0}
    (ha : ((TopRep.homogeneousCochains X).d 0 1).hom a = 0)
    (b : (TopRep.homogeneousCochains Y).X n) :
    P.cupCochain 0 n a b =
      ((TopRep.homogeneousCochains Z).XIsoOfEq (by omega : n + 0 = 0 + n)).hom
        (P.flip.cupCochain n 0 b a) := by
  apply Subtype.ext
  rw [coe_cupCochain, ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply,
    coe_cupCochain, TopRep.homogeneousCochains.eq_d_zero_apply_of_d_eq_zero ha]
  exact P.resolutionCupPairing_zero_eq_flip n (a.val 1) b.val

/-- **Graded commutativity of the cup product in bidegree `(0, n)`**:
`a ⌣_P b = b ⌣_{P.flip} a`, with the opposite product transported from degree `n + 0` to
degree `0 + n`. This is the zero-degree base case of the all-bidegree graded-commutativity
homotopy. -/
theorem cup_zero_eq_flip (n : ℕ) (a : continuousCohomology 0 X)
    (b : continuousCohomology n Y) :
    P.cup 0 n a b =
      (ContinuousCohomology.degreeCast Z (by omega : n + 0 = 0 + n)).hom
        (P.flip.cup n 0 b a) := by
  obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains X).homologyπ_surjective 0 a
  obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains Y).homologyπ_surjective n b
  rw [cup_π, cup_π]
  refine ContinuousCohomology.π_eq_degreeCast_π (by omega : n + 0 = 0 + n) _ _ ?_
  rw [iCycles_cupCocycles, iCycles_cupCocycles]
  exact P.cupCochain_zero_eq_flip n
    ((TopRep.homogeneousCochains X).d_iCycles_apply 1 a) _

end degreeZero

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

section cupOneLeft

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-! ### The cup-one product in bidegree `(1, n + 1)` -/

/-- The cup-one product of a degree-one resolution element and a degree-`n + 1` resolution
element. In homogeneous coordinates it is
`(a ∪₁ b) (g₀, …, gₙ₊₁) = μ (a g₀ gₙ₊₁) (b g₀ … gₙ₊₁)`.

The definition uses the opposite Alexander--Whitney product after fixing the first vertex: at
`g₀` it cups `b g₀`, of degree `n`, with `a g₀`, of degree zero. -/
private def cupOneLeftAux (n : ℕ) (a : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y (n + 1)).V) : (TopRep.resolution'X Z (n + 1)).V :=
  (P.flip.resolutionCup n 0 n (by omega)).comp (b.prodMk a)

private theorem cupOneLeftAux_apply (n : ℕ) (a : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y (n + 1)).V) (g : G) :
    P.cupOneLeftAux n a b g = P.flip.resolutionCup n 0 n (by omega) (b g, a g) := by
  rfl

private theorem cupOneLeftAux_add_left (n : ℕ) (a a' : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y (n + 1)).V) :
    P.cupOneLeftAux n (a + a') b = P.cupOneLeftAux n a b + P.cupOneLeftAux n a' b := by
  apply ContinuousMap.ext
  intro g
  rw [ContinuousMap.add_apply, cupOneLeftAux_apply, cupOneLeftAux_apply, cupOneLeftAux_apply,
    ContinuousMap.add_apply, P.flip.resolutionCup_add_right]

private theorem cupOneLeftAux_smul_left (n : ℕ) (r : R)
    (a : (TopRep.resolution'X X 1).V) (b : (TopRep.resolution'X Y (n + 1)).V) :
    P.cupOneLeftAux n (r • a) b = r • P.cupOneLeftAux n a b := by
  apply ContinuousMap.ext
  intro g
  rw [ContinuousMap.smul_apply, cupOneLeftAux_apply, cupOneLeftAux_apply,
    ContinuousMap.smul_apply, P.flip.resolutionCup_smul_right]

private theorem cupOneLeftAux_add_right (n : ℕ) (a : (TopRep.resolution'X X 1).V)
    (b b' : (TopRep.resolution'X Y (n + 1)).V) :
    P.cupOneLeftAux n a (b + b') = P.cupOneLeftAux n a b + P.cupOneLeftAux n a b' := by
  apply ContinuousMap.ext
  intro g
  rw [ContinuousMap.add_apply, cupOneLeftAux_apply, cupOneLeftAux_apply, cupOneLeftAux_apply,
    ContinuousMap.add_apply, P.flip.resolutionCup_add_left]

private theorem cupOneLeftAux_smul_right (n : ℕ) (r : R)
    (a : (TopRep.resolution'X X 1).V) (b : (TopRep.resolution'X Y (n + 1)).V) :
    P.cupOneLeftAux n a (r • b) = r • P.cupOneLeftAux n a b := by
  apply ContinuousMap.ext
  intro g
  rw [ContinuousMap.smul_apply, cupOneLeftAux_apply, cupOneLeftAux_apply,
    ContinuousMap.smul_apply, P.flip.resolutionCup_smul_left]

/-- **The cup-one product in bidegree `(1, n + 1)`**, as an `R`-bilinear map on the
coinduction resolution. -/
def cupOneLeft (n : ℕ) : (TopRep.resolution'X X 1).V →ₗ[R]
    (TopRep.resolution'X Y (n + 1)).V →ₗ[R] (TopRep.resolution'X Z (n + 1)).V :=
  LinearMap.mk₂ R (P.cupOneLeftAux n) (P.cupOneLeftAux_add_left n)
    (P.cupOneLeftAux_smul_left n) (P.cupOneLeftAux_add_right n)
    (P.cupOneLeftAux_smul_right n)

/-- Evaluating the cup-one product at its first vertex leaves the opposite Alexander--Whitney
product of the two restrictions. -/
theorem cupOneLeft_apply (n : ℕ) (a : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y (n + 1)).V) (g : G) :
    P.cupOneLeft n a b g = P.flip.resolutionCup n 0 n (by omega) (b g, a g) := by
  rw [cupOneLeft, LinearMap.mk₂_apply, cupOneLeftAux_apply]

/-- The cup-one product in bidegree `(1, n + 1)` is equivariant. -/
theorem cupOneLeft_ρ (n : ℕ) (g : G) (a : (TopRep.resolution'X X 1).V)
    (b : (TopRep.resolution'X Y (n + 1)).V) :
    P.cupOneLeft n ((TopRep.resolution'X X 1).ρ g a)
        ((TopRep.resolution'X Y (n + 1)).ρ g b) =
      (TopRep.resolution'X Z (n + 1)).ρ g (P.cupOneLeft n a b) := by
  apply ContinuousMap.ext
  intro h
  rw [TopRep.resolutionX_succ_ρ_apply_apply, P.cupOneLeft_apply, P.cupOneLeft_apply,
    TopRep.resolutionX_succ_ρ_apply_apply, TopRep.resolutionX_succ_ρ_apply_apply]
  exact P.flip.resolutionCup_ρ n 0 n (by omega) g (b (g⁻¹ * h)) (a (g⁻¹ * h))

/-- The cup-one product of a homogeneous one-cochain and a homogeneous `(n + 1)`-cochain. -/
def cupOneLeftCochain (n : ℕ) : (TopRep.homogeneousCochains X).X 1 →ₗ[R]
    (TopRep.homogeneousCochains Y).X (n + 1) →ₗ[R]
      (TopRep.homogeneousCochains Z).X (n + 1) :=
  LinearMap.mk₂ R
    (fun a b ↦ ⟨P.cupOneLeft n a.1 b.1, fun g ↦ by rw [← P.cupOneLeft_ρ, a.2 g, b.2 g]⟩)
    (fun a a' b ↦ Subtype.ext (LinearMap.map_add₂ _ a.1 a'.1 b.1))
    (fun r a b ↦ Subtype.ext (LinearMap.map_smul₂ _ r a.1 b.1))
    (fun a b b' ↦ Subtype.ext (map_add _ b.1 b'.1))
    (fun r a b ↦ Subtype.ext (LinearMap.map_smul _ r b.1))

/-- The underlying resolution element of `cupOneLeftCochain` is `cupOneLeft`. -/
-- Not a `simp` lemma, for the same reason as `coe_cupOneCochain`: `simp` rewrites the implicit
-- carrier `(TopRep.resolution' Z).X (n + 1)` on the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`; use it with `rw`.
theorem coe_cupOneLeftCochain (n : ℕ) (a : (TopRep.homogeneousCochains X).X 1)
    (b : (TopRep.homogeneousCochains Y).X (n + 1)) :
    Subtype.val (P.cupOneLeftCochain n a b) = P.cupOneLeft n a.1 b.1 := by
  rw [cupOneLeftCochain, LinearMap.mk₂_apply]

/-- The restrictions of a homogeneous one-cocycle at two first vertices differ by the constant
edge joining those vertices. The orientation is chosen for the cup-one calculation below. -/
private theorem apply_sub_apply_eq_neg_d_zero {a : (TopRep.homogeneousCochains X).X 1}
    (ha : ((TopRep.homogeneousCochains X).d 1 (1 + 1)).hom a = 0) (g h : G) :
    a.val h - a.val g = -(TopRep.d X 0).hom (a.val g h) := by
  apply ContinuousMap.ext
  intro x
  have hpath := TopRep.homogeneousCochains.apply_eq_add_of_d_eq_zero ha h g x
  have hloop := TopRep.homogeneousCochains.apply_eq_add_of_d_eq_zero ha g h g
  have hdiag := TopRep.homogeneousCochains.apply_eq_add_of_d_eq_zero ha g g g
  have hzero : a.val g g = 0 := by
    apply add_left_cancel (a := a.val g g)
    simpa using hdiag.symm
  have hsym : a.val h g = -a.val g h := by
    rw [hzero] at hloop
    apply eq_neg_iff_add_eq_zero.mpr
    rw [add_comm]
    exact hloop.symm
  rw [ContinuousMap.sub_apply, ContinuousMap.neg_apply, TopRep.d_zero, TopRep.hom_ofHom,
    ContRepresentation.coind₁ι_toFun, ContinuousMap.const_apply, hpath, hsym]
  abel

/-- Pairing a constant degree-zero resolution element with `b` is the pointwise pairing by its
constant value. -/
private theorem resolutionCup_zero_d_zero (n : ℕ) (x : X.V)
    (b : (TopRep.resolutionX Y (n + 1)).V) :
    P.resolutionCup 0 n n (by omega) ((TopRep.d X 0).hom x, b) =
      P.pointwise (n + 1) (n + 1) rfl (x, b) := by
  apply ContinuousMap.ext
  intro h
  rw [P.resolutionCup_zero_apply, P.pointwise_succ_apply]
  rfl

/-- Fixing the first vertex in the cup-one product produces the negative ordinary cup term. This
is the endpoint identity in the proof of the cup-one boundary formula. -/
private theorem cupOneLeft_sub_resolutionCup (n : ℕ)
    {a : (TopRep.homogeneousCochains X).X 1}
    (ha : ((TopRep.homogeneousCochains X).d 1 (1 + 1)).hom a = 0)
    (b : (TopRep.resolution'X Y (n + 1)).V) (g : G) :
    P.cupOneLeft n a.val b -
        P.flip.resolutionCup (n + 1) 0 (n + 1) (by omega) (b, a.val g) =
      -P.resolutionCup 0 (n + 1) (n + 1) (by omega) (a.val g, b) := by
  apply ContinuousMap.ext
  intro h
  rw [ContinuousMap.sub_apply, P.cupOneLeft_apply, P.flip.resolutionCup_succ_apply,
    ← P.flip.resolutionCup_sub_right, apply_sub_apply_eq_neg_d_zero ha]
  rw [← neg_one_smul R ((TopRep.d X 0).hom (a.val g h)),
    P.flip.resolutionCup_smul_right, neg_one_smul,
    ← P.resolutionCup_zero_eq_flip n n rfl (a.val g h) (b h),
    P.resolutionCup_zero_d_zero, ContinuousMap.neg_apply,
    P.resolutionCup_zero_apply]

/-- **The cup-one boundary formula in bidegree `(1, n + 1)`**. For cocycles `a` and `b`,
the differential of `a ∪₁ b` is the negative ordinary product plus the signed opposite product.
This is the cochain homotopy giving graded commutativity whenever the first degree is one. -/
theorem d_cupOneLeftCochain (n : ℕ) {a : (TopRep.homogeneousCochains X).X 1}
    (ha : ((TopRep.homogeneousCochains X).d 1 (1 + 1)).hom a = 0)
    {b : (TopRep.homogeneousCochains Y).X (n + 1)}
    (hb : ((TopRep.homogeneousCochains Y).d (n + 1) (n + 1 + 1)).hom b = 0) :
    ((TopRep.homogeneousCochains Z).d (n + 1) (n + 1 + 1)).hom
        (P.cupOneLeftCochain n a b) =
      -((TopRep.homogeneousCochains Z).XIsoOfEq
          (by omega : 1 + (n + 1) = n + 1 + 1)).hom (P.cupCochain 1 (n + 1) a b) +
        (-1 : R) ^ (n + 1) • P.flip.cupCochain (n + 1) 1 b a := by
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply, P.coe_cupOneLeftCochain, Submodule.coe_add,
    Submodule.coe_neg, Submodule.coe_smul,
    ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply,
    P.coe_cupCochain, P.flip.coe_cupCochain, P.resolutionCupPairing_apply,
    P.flip.resolutionCupPairing_apply, P.resolutionCup_cast (hk' := by omega)]
  apply ContinuousMap.ext
  intro g
  have hda0 : (TopRep.d X 2).hom a.val = 0 :=
    (TopRep.homogeneousCochains.d_apply X 1 a).symm.trans (congrArg Subtype.val ha)
  have hda_eval := congrArg (fun F : (TopRep.resolutionX X 3).V ↦ F g) hda0
  rw [TopRep.hom_d_succ_apply_apply, ContinuousMap.zero_apply] at hda_eval
  have hda : (TopRep.d X 1).hom (a.val g) = a.val := (sub_eq_zero.mp hda_eval).symm
  have hdb0 : (TopRep.d Y (n + 2)).hom b.val = 0 :=
    (TopRep.homogeneousCochains.d_apply Y (n + 1) b).symm.trans (congrArg Subtype.val hb)
  have hdb_eval := congrArg (fun F : (TopRep.resolutionX Y (n + 3)).V ↦ F g) hdb0
  rw [TopRep.hom_d_succ_apply_apply, ContinuousMap.zero_apply] at hdb_eval
  have hdb : (TopRep.d Y (n + 1)).hom (b.val g) = b.val :=
    (sub_eq_zero.mp hdb_eval).symm
  rw [TopRep.hom_d_succ_apply_apply, P.cupOneLeft_apply,
    P.flip.resolutionCup_leibniz n 0 n (by omega), hdb, hda,
    sub_add_eq_sub_sub, P.cupOneLeft_sub_resolutionCup n ha b.val g,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    P.resolutionCup_succ_apply, P.flip.resolutionCup_succ_apply, pow_succ, mul_neg_one,
    neg_smul]
  abel

/-- After transporting the ordinary cup to degree `n + 1 + 1`, its class is the signed class of
the opposite cup. This is the cocycle-level descent of `d_cupOneLeftCochain`. -/
private theorem degreeCast_π_cupCocycles_one_succ (n : ℕ) (a : cocycles X 1)
    (b : cocycles Y (n + 1)) :
    (ContinuousCohomology.degreeCast Z
        (by omega : 1 + (n + 1) = n + 1 + 1)).hom
        (π Z (1 + (n + 1)) (P.cupCocycles 1 (n + 1) a b)) =
      (-1 : R) ^ (n + 1) •
        π Z (n + 1 + 1) (P.flip.cupCocycles (n + 1) 1 b a) := by
  let h : 1 + (n + 1) = n + 1 + 1 := by omega
  let c : cocycles Z (n + 1 + 1) := ContinuousCohomology.cocyclesDegreeCast h
    (P.cupCocycles 1 (n + 1) a b)
  have hc := ContinuousCohomology.iCycles_cocyclesDegreeCast h
    (P.cupCocycles 1 (n + 1) a b)
  have hcπ := ContinuousCohomology.π_cocyclesDegreeCast h
    (P.cupCocycles 1 (n + 1) a b)
  rw [← hcπ, ← sub_eq_zero, ← map_smul, ← map_sub]
  set L := TopRep.homogeneousCochains Z
  refine (L.homologyπ_eq_zero_iff (n + 1 + 1) (CochainComplex.prev_nat_succ (n + 1))).2
    ⟨-P.cupOneLeftCochain n ((TopRep.homogeneousCochains X).iCycles 1 a)
      ((TopRep.homogeneousCochains Y).iCycles (n + 1) b),
      L.iCycles_injective (n + 1 + 1) ?_⟩
  rw [L.iCycles_toCycles_apply, map_neg, P.d_cupOneLeftCochain n
    ((TopRep.homogeneousCochains X).d_iCycles_apply 2 a)
    ((TopRep.homogeneousCochains Y).d_iCycles_apply (n + 2) b), neg_add_rev,
    neg_neg, map_sub, map_smul, hc,
    iCycles_cupCocycles, iCycles_cupCocycles]
  abel

/-- **Graded commutativity of the cup product in bidegree `(1, n + 1)`**:
`a ⌣_P b = (-1)^(n+1) (b ⌣_{P.flip} a)`, with the opposite product transported from degree
`n + 1 + 1` to degree `1 + (n + 1)`. -/
theorem cup_one_succ_eq_signed_flip (n : ℕ) (a : continuousCohomology 1 X)
    (b : continuousCohomology (n + 1) Y) :
    P.cup 1 (n + 1) a b =
      (ContinuousCohomology.degreeCast Z
          (by omega : n + 1 + 1 = 1 + (n + 1))).hom
        ((-1 : R) ^ (n + 1) • P.flip.cup (n + 1) 1 b a) := by
  obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains X).homologyπ_surjective 1 a
  obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains Y).homologyπ_surjective (n + 1) b
  rw [cup_π, cup_π]
  rw [← ContinuousCohomology.degreeCast_symm (by omega : 1 + (n + 1) = n + 1 + 1), Iso.symm_hom,
    ← P.degreeCast_π_cupCocycles_one_succ n a b, Iso.hom_inv_id_apply]

end cupOneLeft

end TopPairing

end TauCeti
