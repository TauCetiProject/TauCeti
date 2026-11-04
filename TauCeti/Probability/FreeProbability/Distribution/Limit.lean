/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Distribution.Convergence
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Order.OrderClosed

/-!
# Limits of star distributions

If every word moment of a family converges, the limits define a unique linear functional on
noncommutative star polynomials. The ambient algebras may vary with the approximation parameter.
Normalization, positivity on squares and traciality pass to this functional. In particular,
expected star-moment limits of random matrices have an algebraic positive tracial realization,
even when no bounded C*-realization is available.

No topology or boundedness on the ambient algebras is required.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 1 and 4.
-/

public section

open Filter Topology

namespace TauCeti

variable {R T ι : Type*} {A : T → Type*} {B : Type*}
  [CommSemiring R] [StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [T2Space R]
  [∀ t, Semiring (A t)] [∀ t, Algebra R (A t)] [∀ t, StarRing (A t)]
  [∀ t, StarModule R (A t)] [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
  {φ : (t : T) → A t →ₗ[R] R} {a : (t : T) → ι → A t}
  {l : Filter T} [l.NeBot] {ψ : B →ₗ[R] R} {b : ι → B}

omit [IsTopologicalSemiring R] [∀ t, StarModule R (A t)] in
/-- Normalization passes to a star-moment limit. It suffices that the approximating
functionals are eventually normalized. -/
theorem TendstoInStarMoments.starDistribution_one (h : TendstoInStarMoments φ a l ψ b)
    (hφ : ∀ᶠ t in l, φ t 1 = 1) : starDistribution ψ b 1 = 1 := by
  have hlim : Tendsto (fun t => φ t 1) l (𝓝 (ψ 1)) := by
    simpa only [List.map_nil, List.prod_nil] using
      (tendstoInMoments_iff.1 (tendstoInStarMoments_iff.1 h)) []
  simp only [starDistribution_apply, map_one]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hφ.mono fun t ht => ht.symm))

/-- Traciality passes to the limiting polynomial functional. It is enough to have traces
eventually; no topology on the approximating algebras is used. -/
theorem TendstoInStarMoments.starDistribution_mul_comm
    (h : TendstoInStarMoments φ a l ψ b)
    (hφ : ∀ᶠ t in l, ∀ x y, φ t (x * y) = φ t (y * x))
    (p q : StarPolynomial R ι) :
    starDistribution ψ b (p * q) = starDistribution ψ b (q * p) := by
  apply tendsto_nhds_unique (h.tendsto_starDistribution (p * q))
  exact (h.tendsto_starDistribution (q * p)).congr'
    (hφ.mono fun t ht => (TauCeti.starDistribution_mul_comm ht (a t) p q).symm)

/-- Compatibility with the involution passes to the limiting polynomial functional when
the scalar involution is continuous. -/
theorem TendstoInStarMoments.starDistribution_star [ContinuousStar R]
    (h : TendstoInStarMoments φ a l ψ b)
    (hφ : ∀ᶠ t in l, ∀ x, φ t (star x) = star (φ t x)) (p : StarPolynomial R ι) :
    starDistribution ψ b (star p) = star (starDistribution ψ b p) := by
  apply tendsto_nhds_unique (h.tendsto_starDistribution (star p))
  exact (h.tendsto_starDistribution p).star.congr'
    (hφ.mono fun t ht => (TauCeti.starDistribution_star ht (a t) p).symm)

omit [T2Space R] in
/-- Positivity on squares passes to a star-moment limit over an ordered scalar semiring with
closed order. This applies in particular to the usual partial order on the complex numbers. -/
theorem TendstoInStarMoments.starDistribution_star_mul_self_nonneg
    [PartialOrder R] [OrderClosedTopology R] (h : TendstoInStarMoments φ a l ψ b)
    (hφ : ∀ᶠ t in l, ∀ x, 0 ≤ φ t (star x * x)) (p : StarPolynomial R ι) :
    0 ≤ starDistribution ψ b (star p * p) := by
  exact ge_of_tendsto (h.tendsto_starDistribution (star p * p))
    (hφ.mono fun t ht => TauCeti.starDistribution_star_mul_self_nonneg ht (a t) p)

omit [IsTopologicalSemiring R] [∀ t, StarModule R (A t)] in
/-- Convergence of every word moment constructs a unique limiting functional on star
polynomials. The empty word is included, and no positivity or normalization is needed. -/
theorem existsUnique_tendstoInStarMoments
    (hm : ∀ w : List (ι × Bool), ∃ z : R,
      Tendsto (fun t => φ t (w.map (StarPolynomial.withStar (a t))).prod) l (𝓝 z)) :
    ∃! χ : StarPolynomial R ι →ₗ[R] R,
      TendstoInStarMoments φ a l χ (StarPolynomial.X (R := R)) := by
  -- Use Mathlib's Module.Basis.constr on the word basis of the free algebra.
  -- Polynomial convergence then follows from the polynomial test criterion for
  -- TendstoInStarMoments.
  classical
  choose m hm using hm
  let F := (FreeAlgebra.basisFreeMonoid R (ι × Bool)).constr R
    (fun w => m w.toList)
  let χ := F.comp (StarPolynomial.toFreeAlgebra R ι).toLinearMap
  have hletters (x : ι × Bool) :
      StarPolynomial.toFreeAlgebra R ι (StarPolynomial.withStar (StarPolynomial.X (R := R)) x) =
        FreeAlgebra.ι R x := by
    obtain ⟨i, _ | _⟩ := x <;> simp
  have hword (w : List (ι × Bool)) :
      χ (w.map (StarPolynomial.withStar (StarPolynomial.X (R := R)))).prod = m w := by
    have hmap : StarPolynomial.toFreeAlgebra R ι
        (w.map (StarPolynomial.withStar (StarPolynomial.X (R := R)))).prod =
          FreeAlgebra.basisFreeMonoid R (ι × Bool) (FreeMonoid.ofList w) := by
      simp only [map_list_prod, List.map_map, Function.comp_def, hletters,
        basisFreeMonoid_apply]
    simp only [χ, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, hmap,
      F, Module.Basis.constr_basis]
  have hχ : TendstoInStarMoments φ a l χ (StarPolynomial.X (R := R)) := by
    rw [tendstoInStarMoments_iff, tendstoInMoments_iff]
    intro w
    rw [hword]
    exact hm w
  refine ⟨χ, hχ, fun χ' hχ' => ?_⟩
  simpa only [starDistribution_X] using hχ'.starDistribution_eq hχ

omit [T2Space R] in
/-- Convergent word moments of normalized positive tracial functionals determine a unique
normalized positive tracial functional on star polynomials. This is an algebraic realization:
no boundedness of the variables, faithfulness, or common ambient algebra is asserted. -/
theorem existsUnique_positive_tracial_starDistribution_of_tendsto
    [PartialOrder R] [OrderClosedTopology R]
    (hm : ∀ w : List (ι × Bool), ∃ z : R,
      Tendsto (fun t => φ t (w.map (StarPolynomial.withStar (a t))).prod) l (𝓝 z))
    (hone : ∀ᶠ t in l, φ t 1 = 1)
    (hpos : ∀ᶠ t in l, ∀ x, 0 ≤ φ t (star x * x))
    (htrace : ∀ᶠ t in l, ∀ x y, φ t (x * y) = φ t (y * x)) :
    ∃! χ : StarPolynomial R ι →ₗ[R] R,
      TendstoInStarMoments φ a l χ (StarPolynomial.X (R := R)) ∧
      χ 1 = 1 ∧ (∀ p, 0 ≤ χ (star p * p)) ∧ (∀ p q, χ (p * q) = χ (q * p)) := by
  obtain ⟨χ, hχ, hunique⟩ := existsUnique_tendstoInStarMoments hm
  refine ⟨χ, ⟨hχ, ?_, ?_, ?_⟩, fun χ' hχ' => hunique χ' hχ'.1⟩
  · simpa only [starDistribution_X] using hχ.starDistribution_one hone
  · intro p
    simpa only [starDistribution_X] using hχ.starDistribution_star_mul_self_nonneg hpos p
  · intro p q
    simpa only [starDistribution_X] using hχ.starDistribution_mul_comm htrace p q

end TauCeti
