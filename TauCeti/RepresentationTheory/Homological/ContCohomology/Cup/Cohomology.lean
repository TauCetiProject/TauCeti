/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Basic

/-!
# The cup product on continuous cohomology

Let `P : TopPairing X Y Z` be an equivariant jointly continuous bilinear pairing of topological
representations of a topological group `G`. The Alexander–Whitney cup product of homogeneous
cochains `TauCeti.TopPairing.cupCochain` satisfies the Leibniz rule
`d (a ⌣ b) = d a ⌣ b + (-1)^m (a ⌣ d b)`, so a cocycle cupped with a cocycle is a cocycle, and a
coboundary cupped with a cocycle, or a cocycle with a coboundary, is a coboundary. This file
descends the cup product accordingly, first to the cocycles and then to Mathlib's continuous
cohomology, giving the bilinear map

```text
cup P m n : Hᵐ(G, X) →ₗ[R] Hⁿ(G, Y) →ₗ[R] Hᵐ⁺ⁿ(G, Z),
```

determined by `cup P m n [a] [b] = [a ⌣ b]` on classes of cocycles (`TauCeti.TopPairing.cup_π`).
Biadditivity, and more generally `R`-bilinearity, is carried by the type: additivity in either
argument is `LinearMap.map_add₂` and `map_add`.

The descent runs through `HomologicalComplex.descHomologyₗ`, the elementwise universal property of
homology in `TopModuleCat R`: a linear map out of the cycles that vanishes on the kernel of the
class map factors through the homology. It is applied twice, once in each variable, which is why
that universal property is stated for linear maps into an arbitrary module rather than for
morphisms of `TopModuleCat R`.

## Main definitions

* `TauCeti.TopPairing.cupCocycles`: the cup product of cocycles.
* `TauCeti.TopPairing.cup`: the cup product on continuous cohomology.

## Main results

* `TauCeti.TopPairing.iCycles_cupCocycles`: the cup product of cocycles is, on underlying
  cochains, the cup product of cochains.
* `TauCeti.TopPairing.homologyπ_cupCocycles_eq_zero_of_left_eq_zero` and
  `TauCeti.TopPairing.homologyπ_cupCocycles_eq_zero_of_right_eq_zero`: the cup product of a
  coboundary with a cocycle, in either order, is a coboundary.
* `TauCeti.TopPairing.cup_π`: the cup product of the classes of two cocycles is the class of their
  cup product.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, (1.4.1).
-/

public section

namespace TauCeti

open CategoryTheory ContRepresentation TopRep _root_.ContinuousCohomology

universe u v w

namespace TopPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-! ### The cup product of cocycles -/

/-- **The cup product of cocycles**: the cup product `TauCeti.TopPairing.cupCochain` of the
underlying homogeneous cochains, which is a cocycle by the Leibniz rule. -/
noncomputable def cupCocycles (m n : ℕ) :
    cocycles X m →ₗ[R] cocycles Y n →ₗ[R] cocycles Z (m + n) :=
  LinearMap.mk₂ R
    (fun a b ↦ (homogeneousCochains Z).cyclesMkOfEq
      (P.cupCochain m n ((homogeneousCochains X).iCycles m a) ((homogeneousCochains Y).iCycles n b))
      (m + n + 1) (CochainComplex.next ℕ (m + n)) (by
        rw [cupCochain_leibniz, (homogeneousCochains X).d_iCycles_apply (m + 1) a,
          (homogeneousCochains Y).d_iCycles_apply (n + 1) b, LinearMap.map_zero₂, map_zero,
          map_zero, smul_zero, add_zero]))
    (fun a a' b ↦ (homogeneousCochains Z).iCycles_injective (m + n) (by
      simp only [map_add, LinearMap.add_apply, HomologicalComplex.iCycles_cyclesMkOfEq]))
    (fun r a b ↦ (homogeneousCochains Z).iCycles_injective (m + n) (by
      simp only [map_smul, LinearMap.smul_apply, HomologicalComplex.iCycles_cyclesMkOfEq]))
    (fun a b b' ↦ (homogeneousCochains Z).iCycles_injective (m + n) (by
      simp only [map_add, HomologicalComplex.iCycles_cyclesMkOfEq]))
    (fun r a b ↦ (homogeneousCochains Z).iCycles_injective (m + n) (by
      simp only [map_smul, HomologicalComplex.iCycles_cyclesMkOfEq]))

/-- On underlying cochains, the cup product of cocycles is the cup product of cochains. -/
-- Not a `simp` lemma: `simp` rewrites the implicit carrier `(homogeneousCochains Z).X (m + n)` on
-- the left-hand side through `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the
-- statement is not in `simp`-normal form; use it with `rw`.
theorem iCycles_cupCocycles (m n : ℕ) (a : cocycles X m) (b : cocycles Y n) :
    (homogeneousCochains Z).iCycles (m + n) (P.cupCocycles m n a b) =
      P.cupCochain m n ((homogeneousCochains X).iCycles m a)
        ((homogeneousCochains Y).iCycles n b) := by
  rw [cupCocycles, LinearMap.mk₂_apply, HomologicalComplex.iCycles_cyclesMkOfEq]

/-! ### Coboundaries cup to coboundaries -/

/-- **A coboundary cupped with a cocycle is a coboundary**: the class of `a ⌣ b` vanishes when the
class of `a` does. -/
theorem homologyπ_cupCocycles_eq_zero_of_left_eq_zero (m n : ℕ) (a : cocycles X m)
    (ha : π X m a = 0) (b : cocycles Y n) : π Z (m + n) (P.cupCocycles m n a b) = 0 := by
  set K := homogeneousCochains X
  set L := homogeneousCochains Z
  cases m with
  | zero =>
    -- in degree zero there are no coboundaries, so `a = 0`
    have h0 : a = 0 := K.homologyπ_injective_of_d_eq_zero CochainComplex.prev_nat_zero
      (K.shape 0 0 (by simp)) (ha.trans (map_zero _).symm)
    rw [h0, LinearMap.map_zero₂, map_zero]
  | succ m =>
    obtain ⟨x, rfl⟩ := (K.homologyπ_eq_zero_iff (m + 1) (CochainComplex.prev_nat_succ m)).1 ha
    -- the witness is `x ⌣ b`, of degree `m + n`; by the Leibniz rule its differential is
    -- `d x ⌣ b`, up to the identification of the degrees `m + n + 1` and `m + 1 + n`
    refine (L.homologyπ_eq_zero_iff (m + 1 + n) (m := m + n)
      ((ComplexShape.up ℕ).prev_eq' (by simp only [ComplexShape.up_Rel]; omega))).2
      ⟨P.cupCochain m n x ((homogeneousCochains Y).iCycles n b), L.iCycles_injective (m + 1 + n) ?_⟩
    have hd := P.cupCochain_leibniz m n x ((homogeneousCochains Y).iCycles n b)
    rw [(homogeneousCochains Y).d_iCycles_apply (n + 1) b, map_zero, smul_zero, add_zero] at hd
    have hcast := ConcreteCategory.congr_hom
      (L.d_comp_XIsoOfEq_inv (by omega : m + 1 + n = m + n + 1) (m + n))
      (P.cupCochain m n x ((homogeneousCochains Y).iCycles n b))
    simp only [ConcreteCategory.comp_apply] at hcast
    rw [L.iCycles_toCycles_apply, iCycles_cupCocycles, K.iCycles_toCycles_apply, ← hcast, hd]
    exact Iso.hom_inv_id_apply _ _

/-- **A cocycle cupped with a coboundary is a coboundary**: the class of `a ⌣ b` vanishes when the
class of `b` does. -/
theorem homologyπ_cupCocycles_eq_zero_of_right_eq_zero (m n : ℕ) (a : cocycles X m)
    (b : cocycles Y n) (hb : π Y n b = 0) : π Z (m + n) (P.cupCocycles m n a b) = 0 := by
  set K := homogeneousCochains Y
  set L := homogeneousCochains Z
  cases n with
  | zero =>
    have h0 : b = 0 := K.homologyπ_injective_of_d_eq_zero CochainComplex.prev_nat_zero
      (K.shape 0 0 (by simp)) (hb.trans (map_zero _).symm)
    rw [h0, map_zero, map_zero]
  | succ n =>
    obtain ⟨y, rfl⟩ := (K.homologyπ_eq_zero_iff (n + 1) (CochainComplex.prev_nat_succ n)).1 hb
    -- the witness is `(-1)^m • (a ⌣ y)`, of degree `m + n`; by the Leibniz rule its differential
    -- is `(-1)^m • (-1)^m • (a ⌣ d y) = a ⌣ d y`
    refine (L.homologyπ_eq_zero_iff (m + (n + 1)) (m := m + n)
      (CochainComplex.prev_nat_succ (m + n))).2
      ⟨(-1 : R) ^ m • P.cupCochain m n ((homogeneousCochains X).iCycles m a) y,
        L.iCycles_injective (m + (n + 1)) ?_⟩
    have hd := P.cupCochain_leibniz m n ((homogeneousCochains X).iCycles m a) y
    rw [(homogeneousCochains X).d_iCycles_apply (m + 1) a, LinearMap.map_zero₂, map_zero,
      zero_add] at hd
    rw [L.iCycles_toCycles_apply, iCycles_cupCocycles, K.iCycles_toCycles_apply]
    -- `m + (n + 1)` and `m + n + 1` are the same natural number by definition, so the differential
    -- `L.d (m + n) (m + (n + 1))` of the goal is the `L.d (m + n) (m + n + 1)` of the Leibniz rule
    change (L.d (m + n) (m + n + 1)).hom _ = _
    rw [map_smul, hd, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-! ### The cup product on continuous cohomology -/

/-- **The cup product on continuous cohomology**, `Hᵐ(G, X) →ₗ[R] Hⁿ(G, Y) →ₗ[R] Hᵐ⁺ⁿ(G, Z)`, for
a coefficient pairing `P : TopPairing X Y Z`: the class of `a ⌣ b` on the classes of the cocycles
`a` and `b` (`cup_π`). -/
noncomputable def cup (m n : ℕ) :
    continuousCohomology m X →ₗ[R] continuousCohomology n Y →ₗ[R] continuousCohomology (m + n) Z :=
  (homogeneousCochains X).descHomologyₗ
    ((homogeneousCochains Y).descHomologyₗ
      ((P.cupCocycles m n).compr₂ (π Z (m + n)).hom.toLinearMap).flip
      (fun b hb ↦ LinearMap.ext fun a ↦
        P.homologyπ_cupCocycles_eq_zero_of_right_eq_zero m n a b hb)).flip
    (fun a ha ↦ LinearMap.ext fun β ↦ by
      obtain ⟨b, rfl⟩ := (homogeneousCochains Y).homologyπ_surjective n β
      rw [LinearMap.flip_apply, HomologicalComplex.descHomologyₗ_π, LinearMap.flip_apply,
        LinearMap.compr₂_apply, LinearMap.zero_apply]
      exact P.homologyπ_cupCocycles_eq_zero_of_left_eq_zero m n a ha b)

/-- **The cup product on classes**: the cup product of the classes of two cocycles is the class of
their cup product. -/
@[simp]
theorem cup_π (m n : ℕ) (a : cocycles X m) (b : cocycles Y n) :
    P.cup m n (π X m a) (π Y n b) = π Z (m + n) (P.cupCocycles m n a b) := by
  rw [cup, HomologicalComplex.descHomologyₗ_π, LinearMap.flip_apply,
    HomologicalComplex.descHomologyₗ_π, LinearMap.flip_apply, LinearMap.compr₂_apply]
  rfl

end TopPairing

end TauCeti
