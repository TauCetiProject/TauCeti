/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Filtered.Basic
public import TauCeti.LowDimTopology.Heegaard.Grid.HatDifferential
public import TauCeti.LowDimTopology.Heegaard.Knot.Full

/-!
# The filtered and unblocked grid differentials are Heegaard Floer domain counts

Let `G` be an `n × n` grid diagram, viewed as a multi-pointed genus-one Heegaard diagram
(`TauCeti.GridDiagram.heegaardRegionSystem`) whose basepoints are the `O`-markings, the `w`'s,
and the `X`-markings, the `z`'s, with every square a region of Euler characteristic `1`. The
index-one nonnegative domains of this diagram are exactly the domains of the empty rectangles,
with any multiplicities at the markings
(`TauCeti.GridDiagram.minusDomains_eq_image_emptyRectangles`): one direction is Lipshitz's index
of a rectangle, the other is the corner count of
`TauCeti.GridDiagram.exists_gridRectangleBetween_isEmpty_domain_eq`. In particular every count is
finite (`TauCeti.GridDiagram.finite_minusDomains`).

The full multi-pointed differential of the diagram (`TauCeti.HeegaardRegionSystem.fullDifferential`)
records the multiplicity of a domain at each marking by its own variable. Its coefficient from `x`
to `y` is therefore the sum, over the empty rectangles `r` from `x` to `y`, of the monomial of the
markings that `r` covers, each with exponent one. Keeping the variable `V_c` of the `O`-marking of
each column `c`:

* **Setting the variables of the `X`-markings to `1`** forgets the `X`-markings and counts all
  empty rectangles: this is the filtered grid differential
  (`TauCeti.GridDiagram.aeval_sumElim_X_one_fullCoefficient`,
  `TauCeti.GridDiagram.mapRange_aeval_sumElim_X_one_fullDifferential`), the differential of the
  filtered complex whose Alexander filtration is recorded by the `X`-markings.
* **Setting the variables of the `X`-markings to `0`** keeps exactly the domains with `n_X = 0`, the
  empty rectangles covering no `X`-marking: this is the unblocked grid differential `∂⁻` of `GC⁻`
  (`TauCeti.GridDiagram.aeval_sumElim_X_zero_fullCoefficient`,
  `TauCeti.GridDiagram.mapRange_aeval_sumElim_X_zero_fullDifferential`), the associated graded
  differential.

So the filtered grid complex and its associated graded complex `GC⁻` are, under the identification
of grid states with generators (`TauCeti.GridDiagram.gridStateEquivGenerator`), the complexes of
domain counts of the Heegaard diagram, and the filtered complex is not its associated graded: the
empty rectangles covering an `X`-marking are counted with the multiplicities the filtration
prescribes. This is the combinatorial half of the comparison of Manolescu, Ozsváth and Sarkar: it
excludes every index-one domain other than the empty rectangles. That each empty rectangle carries
exactly one holomorphic disk modulo translation is analytic and is not formalized here.

## Main results

* `TauCeti.GridDiagram.mem_minusDomains_iff_exists_mem_emptyRectangles` and
  `TauCeti.GridDiagram.minusDomains_eq_image_emptyRectangles`: the index-one nonnegative domains are
  the domains of the empty rectangles.
* `TauCeti.GridDiagram.finite_minusDomains`: there are finitely many.
* `TauCeti.GridDiagram.fullCoefficient_gridStateEquivGenerator` and
  `TauCeti.GridDiagram.aeval_fullCoefficient_gridStateEquivGenerator`: the full coefficients, and
  their evaluations, are sums over the empty rectangles.
* `TauCeti.GridDiagram.aeval_sumElim_X_one_fullCoefficient` and
  `TauCeti.GridDiagram.aeval_sumElim_X_zero_fullCoefficient`: the specializations of the full
  coefficients are the filtered and unblocked grid coefficients.
* `TauCeti.GridDiagram.mapRange_aeval_sumElim_X_one_fullDifferential` and
  `TauCeti.GridDiagram.mapRange_aeval_sumElim_X_zero_fullDifferential`: the same for the
  differentials.

## References

* C. Manolescu, P. Ozsváth and S. Sarkar, *A combinatorial description of knot Floer homology*,
  Ann. of Math. **169** (2009), [arXiv:math/0607691](https://arxiv.org/abs/math/0607691), §2,
  where the positive domains of Maslov index one in a grid diagram are shown to be the empty
  rectangles, and the filtered complex `C⁻(G)` with one variable for each `O`-marking is
  identified with the knot Floer complex of the multi-pointed diagram.
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Grid Homology for Knots and Links*, Mathematical
  Surveys and Monographs **208**, AMS, 2015, Chapters 4 and 13, for the unblocked and filtered
  grid complexes.
-/

public section

namespace TauCeti

open Finset MvPolynomial

variable {n : ℕ}

namespace GridDiagram

variable [NeZero n] (G : GridDiagram n)

section Domains

variable {x y : GridState n} {D : Fin n × Fin n → ℤ}

/-- The domain of an empty rectangle is counted by the minus differential of the multi-pointed
Heegaard diagram of a grid diagram: it is a nonnegative domain of Maslov index one. -/
theorem domain_mem_minusDomains (R : GridRectangleBetween x y) (hR : R.IsEmpty) :
    R.toGridRectangle.domain ∈ G.heegaardRegionSystem.minusDomains 1
      (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) :=
  HeegaardRegionSystem.mem_minusDomains_iff.2 ⟨G.isDomainBetween_domain R,
    R.toGridRectangle.domain_nonneg, (G.maslovIndex_domain_eq_one_iff R).2 hR⟩

/-- **The index-one domains of a grid diagram are its empty rectangles.** A domain from `x` to `y`
is a nonnegative domain of Maslov index one of the Heegaard diagram of a grid diagram exactly when
it is the domain of an empty rectangle from `x` to `y`, whatever markings the rectangle covers. -/
theorem mem_minusDomains_iff_exists_mem_emptyRectangles :
    D ∈ G.heegaardRegionSystem.minusDomains 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) ↔
      ∃ R ∈ GridRectangleBetween.emptyRectangles x y, R.toGridRectangle.domain = D := by
  constructor
  · intro hD'
    obtain ⟨hD, hD₀, hμ⟩ := HeegaardRegionSystem.mem_minusDomains_iff.1 hD'
    obtain ⟨R, hR, rfl⟩ := G.exists_gridRectangleBetween_isEmpty_domain_eq hD hD₀ hμ
    exact ⟨R, (GridRectangleBetween.mem_emptyRectangles R).2 hR, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    exact G.domain_mem_minusDomains R ((GridRectangleBetween.mem_emptyRectangles R).1 hR)

/-- The domains counted by the minus differential of the Heegaard diagram of a grid diagram are the
domains of the empty rectangles. -/
theorem minusDomains_eq_image_emptyRectangles :
    G.heegaardRegionSystem.minusDomains 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) =
      (fun R : GridRectangleBetween x y => R.toGridRectangle.domain) ''
        (GridRectangleBetween.emptyRectangles x y : Set (GridRectangleBetween x y)) := by
  ext D
  rw [mem_minusDomains_iff_exists_mem_emptyRectangles]
  simp

/-- The Heegaard diagram of a grid diagram has finitely many nonnegative domains of Maslov index
one between any two generators. -/
theorem finite_minusDomains (g h : G.heegaardRegionSystem.Generator) :
    (G.heegaardRegionSystem.minusDomains 1 g h).Finite := by
  obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective g
  obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective h
  rw [minusDomains_eq_image_emptyRectangles]
  exact (Finset.finite_toSet _).image _

/-- A sum over the counted domains of the Heegaard diagram of a grid diagram is the sum over the
empty rectangles of the values at their domains. -/
private theorem finsum_mem_minusDomains {M : Type*} [AddCommMonoid M]
    (f : (Fin n × Fin n → ℤ) → M) (x y : GridState n) :
    ∑ᶠ D ∈ G.heegaardRegionSystem.minusDomains 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y), f D =
      ∑ R ∈ GridRectangleBetween.emptyRectangles x y, f R.toGridRectangle.domain := by
  rw [minusDomains_eq_image_emptyRectangles,
    finsum_mem_image GridRectangleBetween.toGridRectangle_domain_injective.injOn,
    finsum_mem_coe_finset]

end Domains

section Weights

variable {S : Type*} [CommSemiring S]

/-- The weight in the full differential of the domain of a rectangle, with the variables of the
markings evaluated at `g`: the product of the values at the markings the rectangle covers. -/
private theorem prod_pow_domain_basepoint (g : Fin n ⊕ Fin n → S) (R : GridRectangle n) :
    ∏ b, g b ^ (R.domain (G.heegaardRegionSystem.basepoint b)).toNat =
      (∏ c, if (c, G.O c) ∈ R.coveredSquares then g (Sum.inl c) else 1) *
        ∏ c, if (c, G.X c) ∈ R.coveredSquares then g (Sum.inr c) else 1 := by
  rw [Fintype.prod_sum_type]
  congr 1 <;> refine Finset.prod_congr rfl fun c _ => ?_ <;>
    simp only [heegaardRegionSystem_basepoint_inl, heegaardRegionSystem_basepoint_inr,
      GridRectangle.domain_apply] <;> split_ifs <;> simp

/-- With the variables of the `X`-markings set to `1`, the weight of the domain of a rectangle is
its `O`-monomial. -/
private theorem prod_pow_domain_basepoint_sumElim_X_one (R : GridRectangle n) :
    ∏ b, (Sum.elim MvPolynomial.X 1 b : MvPolynomial (Fin n) (ZMod 2)) ^
        (R.domain (G.heegaardRegionSystem.basepoint b)).toNat =
      G.OMonomial (ZMod 2) R := by
  rw [prod_pow_domain_basepoint, OMonomial_eq_prod_OColumns, ← Finset.prod_filter]
  simp only [Sum.elim_inr, Pi.one_apply, ite_self, Finset.prod_const_one, mul_one, Sum.elim_inl]
  congr 1
  ext c
  simp

/-- With the variables of the `X`-markings set to `0`, the weight of the domain of a rectangle is
its `O`-monomial if it covers no `X`-marking, and `0` otherwise. -/
private theorem prod_pow_domain_basepoint_sumElim_X_zero (R : GridRectangle n) :
    ∏ b, (Sum.elim MvPolynomial.X 0 b : MvPolynomial (Fin n) (ZMod 2)) ^
        (R.domain (G.heegaardRegionSystem.basepoint b)).toNat =
      if Disjoint R.coveredSquares G.XSet then G.OMonomial (ZMod 2) R else 0 := by
  have hO := G.prod_pow_domain_basepoint_sumElim_X_one R
  rw [prod_pow_domain_basepoint] at hO ⊢
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, ite_self, Finset.prod_const_one,
    mul_one, Pi.zero_apply] at hO ⊢
  rw [hO]
  split_ifs with hX
  · rw [Finset.prod_eq_one fun c _ =>
      ite_eq_right fun hc => Finset.disjoint_left.mp hX hc ((G.mem_XSet _).2 rfl), mul_one]
  · obtain ⟨p, hp, hpX⟩ := Finset.not_disjoint_iff.mp hX
    rw [Finset.prod_eq_zero (Finset.mem_univ p.1), mul_zero]
    rw [(G.mem_XSet p).1 hpX]
    exact ite_eq_left hp

end Weights

section Coefficients

/-- **The full coefficient of a grid diagram counts the empty rectangles.** Evaluating the variable
of each marking at an element `g` of an algebra, the full coefficient of the Heegaard diagram of a
grid diagram from `x` to `y` is the sum, over the empty rectangles from `x` to `y`, of the product
of the values of `g` at the `O`- and `X`-markings that the rectangle covers. -/
theorem aeval_fullCoefficient_gridStateEquivGenerator {S : Type*} [CommSemiring S]
    [Algebra (ZMod 2) S] (g : Fin n ⊕ Fin n → S) (x y : GridState n) :
    aeval g (G.heegaardRegionSystem.fullCoefficient 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y)) =
      ∑ R ∈ GridRectangleBetween.emptyRectangles x y,
        (∏ c, if (c, G.O c) ∈ R.toGridRectangle.coveredSquares then g (Sum.inl c) else 1) *
          ∏ c, if (c, G.X c) ∈ R.toGridRectangle.coveredSquares then g (Sum.inr c) else 1 := by
  rw [HeegaardRegionSystem.aeval_fullCoefficient_of_finite _ (G.finite_minusDomains _ _),
    finsum_mem_minusDomains]
  exact Finset.sum_congr rfl fun R _ => G.prod_pow_domain_basepoint g _

/-- **The full coefficient of a grid diagram counts the empty rectangles.** The full coefficient of
the Heegaard diagram of a grid diagram from `x` to `y` is the sum, over the empty rectangles from
`x` to `y`, of the monomial of the `O`- and `X`-markings that the rectangle covers, each with
exponent one. -/
theorem fullCoefficient_gridStateEquivGenerator (x y : GridState n) :
    G.heegaardRegionSystem.fullCoefficient 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) =
      ∑ R ∈ GridRectangleBetween.emptyRectangles x y,
        (∏ c, if (c, G.O c) ∈ R.toGridRectangle.coveredSquares then
          MvPolynomial.X (Sum.inl c) else 1) *
          ∏ c, if (c, G.X c) ∈ R.toGridRectangle.coveredSquares then
            MvPolynomial.X (Sum.inr c) else 1 := by
  rw [← G.aeval_fullCoefficient_gridStateEquivGenerator, aeval_X_left_apply]

/-- **The filtered grid differential counts the index-one domains.** In the full coefficient of
the Heegaard diagram of a grid diagram from `x` to `y`, keep the variable `V_c` of the `O`-marking
of each column and set the variables of the `X`-markings to `1`. The result is the coefficient of
the filtered grid differential, the sum of the weights of all empty rectangles from `x` to `y`. -/
@[simp]
theorem aeval_sumElim_X_one_fullCoefficient (x y : GridState n) :
    aeval (Sum.elim MvPolynomial.X 1)
        (G.heegaardRegionSystem.fullCoefficient 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y)) =
      G.filteredCoefficient (ZMod 2) x y := by
  rw [aeval_fullCoefficient_gridStateEquivGenerator, filteredCoefficient_def]
  exact Finset.sum_congr rfl fun R _ =>
    (G.prod_pow_domain_basepoint _ _).symm.trans (G.prod_pow_domain_basepoint_sumElim_X_one _)

/-- **The unblocked grid differential counts the index-one domains avoiding the `X`-markings.** In
the full coefficient of the Heegaard diagram of a grid diagram from `x` to `y`, keep the variable
`V_c` of the `O`-marking of each column and set the variables of the `X`-markings to `0`. The
result is the coefficient of the unblocked grid differential `∂⁻`, the sum of the weights of the
empty rectangles from `x` to `y` covering no `X`-marking. -/
@[simp]
theorem aeval_sumElim_X_zero_fullCoefficient (x y : GridState n) :
    aeval (Sum.elim MvPolynomial.X 0)
        (G.heegaardRegionSystem.fullCoefficient 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y)) =
      G.unblockedCoefficient (ZMod 2) x y := by
  classical
  have h : G.unblockedRectangles x y = (GridRectangleBetween.emptyRectangles x y).filter
      (fun R => Disjoint R.toGridRectangle.coveredSquares G.XSet) := by
    ext R
    rw [mem_unblockedRectangles, Finset.mem_filter, GridRectangleBetween.mem_emptyRectangles]
  rw [aeval_fullCoefficient_gridStateEquivGenerator, unblockedCoefficient_def, h,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun R _ =>
    (G.prod_pow_domain_basepoint _ _).symm.trans (G.prod_pow_domain_basepoint_sumElim_X_zero _)

end Coefficients

section Differentials

/-- Specializing the variables of the full differential of the Heegaard diagram of a grid diagram
by a ring homomorphism `f` gives a differential `d` on grid chains, if the coefficients of `d` are
the images under `f` of the full coefficients. -/
private theorem mapRange_fullDifferential_equivMapDomain {F : Type*}
    [FunLike F (MvPolynomial (Fin n ⊕ Fin n) (ZMod 2)) (MvPolynomial (Fin n) (ZMod 2))]
    [RingHomClass F (MvPolynomial (Fin n ⊕ Fin n) (ZMod 2)) (MvPolynomial (Fin n) (ZMod 2))]
    (f : F) {d : GridChainMinus (ZMod 2) n → GridChainMinus (ZMod 2) n}
    {e : GridState n → GridState n → MvPolynomial (Fin n) (ZMod 2)}
    (hd : ∀ c y, d c y = c.sum fun x a => a * e x y)
    (he : ∀ x y, f (G.heegaardRegionSystem.fullCoefficient 1 (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y)) = e x y)
    (c : GridState n →₀ MvPolynomial (Fin n ⊕ Fin n) (ZMod 2)) :
    Finsupp.mapRange f (map_zero f) (G.heegaardRegionSystem.fullDifferential 1
        (Finsupp.equivMapDomain G.gridStateEquivGenerator c)) =
      Finsupp.equivMapDomain G.gridStateEquivGenerator (d (Finsupp.mapRange f (map_zero f) c)) := by
  refine Finsupp.ext fun g => ?_
  obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective g
  have hc : Finsupp.mapRange f (map_zero f) (Finsupp.equivMapDomain G.gridStateEquivGenerator c) =
      Finsupp.equivMapDomain G.gridStateEquivGenerator (Finsupp.mapRange f (map_zero f) c) :=
    Finsupp.ext fun _ => by simp [Finsupp.equivMapDomain_apply]
  rw [HeegaardRegionSystem.mapRange_fullDifferential_apply, hc, Finsupp.sum_equivMapDomain,
    Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, hd]
  simp only [he]

/-- **The filtered grid differential is the Heegaard Floer differential with `X = 1`.** Under the
identification of grid states with the generators of the Heegaard diagram of a grid diagram,
keeping the variables of the `O`-markings and setting those of the `X`-markings to `1` in the
coefficients of a chain intertwines the full differential of the diagram with the filtered grid
differential. -/
theorem mapRange_aeval_sumElim_X_one_fullDifferential
    (c : GridState n →₀ MvPolynomial (Fin n ⊕ Fin n) (ZMod 2)) :
    Finsupp.mapRange (aeval (Sum.elim MvPolynomial.X 1)) (map_zero _)
        (G.heegaardRegionSystem.fullDifferential 1
          (Finsupp.equivMapDomain G.gridStateEquivGenerator c)) =
      Finsupp.equivMapDomain G.gridStateEquivGenerator
        (G.filteredDifferential (ZMod 2)
          (Finsupp.mapRange (aeval (Sum.elim MvPolynomial.X 1)) (map_zero _) c)) :=
  G.mapRange_fullDifferential_equivMapDomain _ (G.filteredDifferential_apply_apply (ZMod 2))
    G.aeval_sumElim_X_one_fullCoefficient c

/-- **The unblocked grid differential is the Heegaard Floer differential with `X = 0`.** Under the
identification of grid states with the generators of the Heegaard diagram of a grid diagram,
keeping the variables of the `O`-markings and setting those of the `X`-markings to `0` in the
coefficients of a chain intertwines the full differential of the diagram with the unblocked grid
differential `∂⁻`. -/
theorem mapRange_aeval_sumElim_X_zero_fullDifferential
    (c : GridState n →₀ MvPolynomial (Fin n ⊕ Fin n) (ZMod 2)) :
    Finsupp.mapRange (aeval (Sum.elim MvPolynomial.X 0)) (map_zero _)
        (G.heegaardRegionSystem.fullDifferential 1
          (Finsupp.equivMapDomain G.gridStateEquivGenerator c)) =
      Finsupp.equivMapDomain G.gridStateEquivGenerator
        (G.unblockedDifferential (ZMod 2)
          (Finsupp.mapRange (aeval (Sum.elim MvPolynomial.X 0)) (map_zero _) c)) :=
  G.mapRange_fullDifferential_equivMapDomain _ (G.unblockedDifferential_apply_apply (ZMod 2))
    G.aeval_sumElim_X_zero_fullCoefficient c

end Differentials

end GridDiagram

end TauCeti
