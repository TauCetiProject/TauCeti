/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GradedMonoid
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.GradedAlgebra

/-!
# Cup products of finite families of mod-two classes

For a topological group `G`, a finite type `ι`, degrees `d : ι → ℕ` and classes
`x i ∈ H^{d i}(G, 𝔽₂)`, the cup product of the whole family is a class

```text
⌣_{i : ι} x i  ∈  H^{∑ i, d i}(G, 𝔽₂).
```

In characteristic two the cup product is commutative without a Koszul sign
(`TauCeti.trivialF2TopPairing_cup_comm`), so this product needs no ordering of `ι`. This is the
form in which multiplicative formulas indexed by an unordered finite set are stated, such as the
restriction and double-coset formula for the Evens norm, where the factors are indexed by the
double cosets `V \ G / U`.

The product is `Finset.dProd` in the graded commutative ring `TauCeti.cohomF2 G`, taken over all
of `ι`. It is characterized by `TauCeti.cohomF2.mk_cupFamily`: as an element of the total graded
monoid it is the product of the homogeneous classes `x i`. Equivalently, in the total cohomology
algebra `TauCeti.gradedCohomF2 G` it is the product of the components
(`TauCeti.cohomF2.of_cupFamily`). For two classes it is their cup product
(`TauCeti.cohomF2.cupFamily_fin_two`), and pullback along a continuous homomorphism commutes with
it (`TauCeti.trivialF2Map_cupFamily`), because pullback preserves the unit
(`TauCeti.trivialF2Map_one`) and the cup product (`TauCeti.trivialF2Map_cup`).

## Main definitions

* `TauCeti.cohomF2.cupFamily`: the cup product of a finite family of mod-two classes.

## Main results

* `TauCeti.cohomF2.mk_cupFamily`, `TauCeti.cohomF2.eq_cupFamily_iff`: the characteristic equation
  in the total graded monoid.
* `TauCeti.cohomF2.of_cupFamily`: the same product in the total cohomology algebra.
* `TauCeti.cohomF2.cupFamily_fin_two`: the cup product of a pair of classes.
* `TauCeti.trivialF2Map_cupFamily`: naturality under pullback along continuous homomorphisms.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), §6, Proposition 3: the double-coset formula, a product over the
  double cosets.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace cohomF2

variable {ι : Type*} [Fintype ι]

/-- **The cup product of a finite family of mod-two classes** `x i ∈ H^{d i}(G, 𝔽₂)`, a class of
degree `∑ i, d i`. The cup product with trivial `𝔽₂` coefficients is commutative, so the family is
indexed by an unordered finite type. It is characterized by `TauCeti.cohomF2.mk_cupFamily`. -/
noncomputable def cupFamily (d : ι → ℕ) (x : ∀ i, cohomF2 G (d i)) : cohomF2 G (∑ i, d i) :=
  Finset.univ.dProd d x

/-- **The characteristic equation of `cupFamily`**: in the total graded monoid, the cup product of
a family is the product of its classes. -/
@[simp]
theorem mk_cupFamily (d : ι → ℕ) (x : ∀ i, cohomF2 G (d i)) :
    GradedMonoid.mk _ (cupFamily d x) = ∏ i, GradedMonoid.mk (d i) (x i) :=
  GradedMonoid.mk_finset_dProd _ _ _

/-- A class of degree `∑ i, d i` is the cup product of the family `x` exactly when, in the total
graded monoid, it is the product of the classes `x i`. -/
theorem eq_cupFamily_iff {d : ι → ℕ} {x : ∀ i, cohomF2 G (d i)} {y : cohomF2 G (∑ i, d i)} :
    y = cupFamily d x ↔ GradedMonoid.mk _ y = ∏ i, GradedMonoid.mk (d i) (x i) :=
  Finset.eq_dProd_iff

/-- In the total cohomology algebra `gradedCohomF2 G`, the cup product of a family is the product
of the homogeneous components. -/
@[simp]
theorem of_cupFamily (d : ι → ℕ) (x : ∀ i, cohomF2 G (d i)) :
    DirectSum.of (cohomF2 G) _ (cupFamily d x) = ∏ i, DirectSum.of (cohomF2 G) (d i) (x i) :=
  DirectSum.of_finset_dProd _ _ _

/-- The cup product of a family of two classes is their cup product, transported to the degree
`∑ i, d i`. -/
theorem cupFamily_fin_two (d : Fin 2 → ℕ) (x : ∀ i, cohomF2 G (d i)) :
    cupFamily d x = (ContinuousCohomology.degreeCast (trivialF2 G) (Fin.sum_univ_two d).symm).hom
      ((trivialF2TopPairing G).cup (d 0) (d 1) (x 0) (x 1)) := by
  refine (eq_cupFamily_iff.2 ?_).symm
  rw [Fin.prod_univ_two, GradedMonoid.mk_mul_mk, gMul_eq_cup]
  exact Sigma.ext (Fin.sum_univ_two d) (ContinuousCohomology.degreeCast_hom_apply_heq _ _)

end cohomF2

/-- Pullback with trivial `𝔽₂` coefficients along a continuous homomorphism commutes with the cup
product of a finite family of classes. -/
@[simp]
theorem trivialF2Map_cupFamily {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →ₜ* G) {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (x : ∀ i, cohomF2 G (d i)) :
    trivialF2Map φ _ (cohomF2.cupFamily d x) =
      cohomF2.cupFamily d fun i ↦ trivialF2Map φ (d i) (x i) :=
  Finset.map_dProd (fun {n} ↦ trivialF2Map φ n) (by simp) (fun _ _ ↦ by simp) _ _ _

end TauCeti
