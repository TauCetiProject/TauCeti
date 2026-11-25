/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Summand
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Decomposition
import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement

/-!
# Nikulin's generators decompose every nondegenerate finite quadratic module and pairing

Every nondegenerate finite quadratic module is isometric to an orthogonal sum of Nikulin's
generators:

* the odd cyclic modules `q_θ^{(p)}(p^k)` on `ℤ/p^k`, for an odd prime `p`, `k ≥ 1` and `θ` prime
  to `p`, with `b(x, y) = θxy / p^k`;
* the dyadic cyclic modules `q_θ^{(2)}(2^k)` on `ℤ/2^k`, for `k ≥ 1` and `θ` odd, with
  `q(x) = θx² / 2^{k+1}`;
* the rank-two modules `u^{(2)}(2^k)` and `v^{(2)}(2^k)` on `(ℤ/2^k)²`, for `k ≥ 1`, with
  `q(x) = x₁x₂ / 2^k` and `q(x) = (x₁² + x₁x₂ + x₂²) / 2^k`.

This is the generator half of Nikulin's Proposition 1.8.1. The orthogonal sum is written as a
product of four orthogonal sums, one for each family, each indexed by `Fin n`.

The proof splits off one generator at a time. A nontrivial nondegenerate module `A` has a prime
`p` dividing its order. For odd `p` some cyclic subgroup of `p`-power order is nondegenerate
(`TauCeti.FiniteBilinearModule.exists_isNondegenerate_restrict_zmultiples`), and it is an odd
cyclic generator; for `p = 2` some nonzero subgroup is a dyadic generator
(`TauCeti.FiniteQuadraticModule.exists_dyadic_summand`). Such a summand `H` is nondegenerate, so
`A ≅ H ⊥ H⊥` with `H⊥` nondegenerate of smaller order, and induction on the order applies to
`H⊥`.

In order `2^N` no odd cyclic generator occurs, since its order is odd and greater than `1`.

Every symmetric pairing on a finite abelian group is the polar form of a quadratic map
(`TauCeti.FiniteQuadraticModule.toFiniteBilinearModule_surjective`), so the same decompositions
hold for nondegenerate finite bilinear modules, with the generators replaced by their pairings. On a
finite `2`-group these are the cyclic pairings `ηxy / 2^k` on `ℤ/2^k` with `η` odd and the pairings
of `u^{(2)}(2^k)` and `v^{(2)}(2^k)` on `(ℤ/2^k)²`, with matrices `2^{-k} [[0, 1], [1, 0]]` and
`2^{-k} [[2, 1], [1, 2]]`: the pairings `A^k(η)`, `E_0^k` and `E_1^k` of Kawauchi and Kojima. This
is the decomposition half of their classification of linking pairings on finite `2`-groups.

The decomposition is not unique: Nikulin's Proposition 1.8.2 lists the relations among the
generators, and they are not treated here.

## Main declarations

* `TauCeti.FiniteQuadraticModule.exists_isometry_prod_pi_generators`: a nondegenerate finite
  quadratic module is isometric to an orthogonal sum of odd cyclic, dyadic cyclic, `u` and `v`
  generators.
* `TauCeti.FiniteQuadraticModule.exists_isometry_prod_pi_dyadic_of_natCard_eq_two_pow`: in order
  `2^N`, only the dyadic generators occur.
* `TauCeti.FiniteBilinearModule.exists_isometry_prod_pi_generators` and
  `TauCeti.FiniteBilinearModule.exists_isometry_prod_pi_dyadic_of_natCard_eq_two_pow`: the same
  decompositions for nondegenerate symmetric pairings.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.1.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
* A. Kawauchi and S. Kojima, *Algebraic classification of linking pairings on 3-manifolds*,
  Math. Ann. 253 (1980), 29–42.
-/

public section

open AddSubgroup QuadraticMap.IsometryEquiv

universe u

namespace TauCeti

namespace FiniteQuadraticModule

/-- A nontrivial nondegenerate finite quadratic module has a nonzero nondegenerate subgroup whose
restricted form is isometric to one of Nikulin's generators. -/
private theorem exists_generator_summand {A : FiniteQuadraticModule.{u}} (hA : A.IsNondegenerate)
    (hA1 : Nat.card A ≠ 1) :
    ∃ H : AddSubgroup A, H ≠ ⊥ ∧ (A.restrict H).IsNondegenerate ∧
      ((∃ (m : ℕ) (hm : Odd m) (θ : ℤ), (IsPrimePow m ∧ IsCoprime (m : ℤ) θ) ∧
          Nonempty (Isometry (oddCyclic m hm θ) (A.restrict H))) ∨
        (∃ (k : ℕ) (θ : ℤ), Odd θ ∧ Nonempty (Isometry (dyadicCyclic (k + 1) θ) (A.restrict H))) ∨
        (∃ k : ℕ, Nonempty (Isometry (dyadicU (k + 1)) (A.restrict H))) ∨
        (∃ k : ℕ, Nonempty (Isometry (dyadicV (k + 1)) (A.restrict H)))) := by
  obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd hA1
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · -- At `2`, a dyadic generator splits off.
    obtain ⟨H, k, hH, h⟩ := exists_dyadic_summand hA hpA
    rcases h with ⟨θ, hθ, ⟨g⟩⟩ | ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
    · exact ⟨H, hH, g.isNondegenerate ((isNondegenerate_dyadicCyclic_iff _ θ).2 hθ),
        Or.inr (Or.inl ⟨k, θ, hθ, ⟨g⟩⟩)⟩
    · exact ⟨H, hH, g.isNondegenerate (isNondegenerate_dyadicU _),
        Or.inr (Or.inr (Or.inl ⟨k, ⟨g⟩⟩))⟩
    · exact ⟨H, hH, g.isNondegenerate (isNondegenerate_dyadicV _),
        Or.inr (Or.inr (Or.inr ⟨k, ⟨g⟩⟩))⟩
  · -- At an odd prime, a nondegenerate cyclic subgroup is an odd cyclic generator.
    obtain ⟨z, k, hk, hz, hzA⟩ :=
      A.toFiniteBilinearModule.exists_isNondegenerate_restrict_zmultiples hp2 hA hpA
    have hzA' : (A.restrict (zmultiples z)).IsNondegenerate := by
      rwa [IsNondegenerate, restrict_toFiniteBilinearModule]
    have : IsAddCyclic (A.restrict (zmultiples z)) := inferInstanceAs (IsAddCyclic (zmultiples z))
    have hcard : Nat.card (A.restrict (zmultiples z)) = p ^ k := (Nat.card_zmultiples z).trans hz
    have hodd : Odd (Nat.card (A.restrict (zmultiples z))) :=
      hcard ▸ (hp.odd_of_ne_two hp2).pow
    obtain ⟨θ, hθ, hg⟩ := exists_oddCyclic_isometry (A.restrict (zmultiples z)) hodd hzA'
    refine ⟨zmultiples z, ?_, hzA', Or.inl ⟨_, hodd, θ,
      ⟨hcard ▸ hp.isPrimePow.pow hk.ne', hθ⟩, hg⟩⟩
    rw [Ne, zmultiples_eq_bot]
    rintro rfl
    rw [addOrderOf_zero] at hz
    exact (Nat.one_lt_pow hk.ne' hp.one_lt).ne hz

/-- **Nikulin's generator decomposition.** A nondegenerate finite quadratic module is isometric to
an orthogonal sum of Nikulin's generators: odd cyclic modules `q_θ^{(p)}(p^k)` of odd prime-power
order `m = p^k` with `θ` prime to `m`, dyadic cyclic modules `q_η^{(2)}(2^{k+1})` with `η` odd, and
rank-two modules `u^{(2)}(2^{k+1})` and `v^{(2)}(2^{k+1})`. -/
theorem exists_isometry_prod_pi_generators (A : FiniteQuadraticModule.{u})
    (hA : A.IsNondegenerate) :
    ∃ (a : ℕ) (m : Fin a → ℕ) (hm : ∀ i, Odd (m i)) (θ : Fin a → ℤ)
      (b : ℕ) (k : Fin b → ℕ) (η : Fin b → ℤ) (c : ℕ) (ku : Fin c → ℕ) (d : ℕ) (kv : Fin d → ℕ),
      (∀ i, IsPrimePow (m i) ∧ IsCoprime (m i : ℤ) (θ i)) ∧ (∀ i, Odd (η i)) ∧
        Nonempty (Isometry ((pi fun i ↦ oddCyclic (m i) (hm i) (θ i)).prod
          ((pi fun i ↦ dyadicCyclic (k i + 1) (η i)).prod
            ((pi fun i ↦ dyadicU (ku i + 1)).prod (pi fun i ↦ dyadicV (kv i + 1))))) A) := by
  induction hN : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ N ih =>
  rcases eq_or_ne N 1 with rfl | hN1
  · -- The trivial module is the empty orthogonal sum.
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 hN).1
    refine ⟨0, Fin.elim0, fun i ↦ i.elim0, Fin.elim0, 0, Fin.elim0, Fin.elim0, 0, Fin.elim0, 0,
      Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, ⟨?_⟩⟩
    exact Isometry.ofSubsingleton
  -- Split off a generator `C = A|_H`; its complement `D = A|_{H⊥}` is nondegenerate and smaller.
  obtain ⟨H, hH, hHnd, hgen⟩ := exists_generator_summand hA (hN ▸ hN1)
  let e := A.restrictProdOrthogonalComplementIsometry hHnd
  set D := A.restrict (A.toFiniteBilinearModule.orthogonalComplement H) with hD
  have hDnd : D.IsNondegenerate := by
    rw [hD, IsNondegenerate, restrict_toFiniteBilinearModule]
    exact hA.isNondegenerate_restrict_orthogonalComplement
      ((A.restrict_toFiniteBilinearModule H) ▸ hHnd)
  have hDlt : Nat.card D < N := by
    rw [← hN, ← Nat.card_congr e.toLinearEquiv.toEquiv, Nat.card_prod]
    exact lt_mul_left Nat.card_pos ((one_lt_card_iff_ne_bot H).2 hH)
  obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f⟩⟩ := ih _ hDlt D hDnd rfl
  -- Insert the generator into its family, then move it to the front.
  rcases hgen with ⟨m₀, hm₀, θ₀, hmθ₀, ⟨g⟩⟩ | ⟨k₀, η₀, hη₀, ⟨g⟩⟩ | ⟨k₀, ⟨g⟩⟩ | ⟨k₀, ⟨g⟩⟩
  · refine ⟨a + 1, Fin.cons m₀ m, Fin.cases hm₀ hm, Fin.cons θ₀ θ, b, k, η, c, ku, d, kv,
      Fin.cases hmθ₀ hmθ, hη, ⟨?_⟩⟩
    exact ((consPi _).symm.prod (.refl _)).trans
      ((prodAssoc _ _ _).trans ((g.prod f).trans e))
  · refine ⟨a, m, hm, θ, b + 1, Fin.cons k₀ k, Fin.cons η₀ η, c, ku, d, kv, hmθ,
      Fin.cases hη₀ hη, ⟨?_⟩⟩
    exact ((QuadraticMap.IsometryEquiv.refl _).prod
      (((consPi _).symm.prod (.refl _)).trans (prodAssoc _ _ _))).trans
      ((prodLeftComm _ _ _).trans ((g.prod f).trans e))
  · refine ⟨a, m, hm, θ, b, k, η, c + 1, Fin.cons k₀ ku, d, kv, hmθ, hη, ⟨?_⟩⟩
    exact ((QuadraticMap.IsometryEquiv.refl _).prod ((QuadraticMap.IsometryEquiv.refl _).prod
      (((consPi _).symm.prod (.refl _)).trans (prodAssoc _ _ _)))).trans
      (((QuadraticMap.IsometryEquiv.refl _).prod (prodLeftComm _ _ _)).trans
        ((prodLeftComm _ _ _).trans ((g.prod f).trans e)))
  · refine ⟨a, m, hm, θ, b, k, η, c, ku, d + 1, Fin.cons k₀ kv, hmθ, hη, ⟨?_⟩⟩
    exact ((QuadraticMap.IsometryEquiv.refl _).prod ((QuadraticMap.IsometryEquiv.refl _).prod
      ((QuadraticMap.IsometryEquiv.refl _).prod (consPi _).symm))).trans
      (((QuadraticMap.IsometryEquiv.refl _).prod ((QuadraticMap.IsometryEquiv.refl _).prod
        (prodLeftComm _ _ _))).trans
        (((QuadraticMap.IsometryEquiv.refl _).prod (prodLeftComm _ _ _)).trans
          ((prodLeftComm _ _ _).trans ((g.prod f).trans e))))

/-- **Nikulin's decomposition at the prime `2`.** A nondegenerate finite quadratic module of order
`2^N` is isometric to an orthogonal sum of dyadic generators: cyclic modules
`q_η^{(2)}(2^{k+1})` with `η` odd, and rank-two modules `u^{(2)}(2^{k+1})` and
`v^{(2)}(2^{k+1})`. -/
theorem exists_isometry_prod_pi_dyadic_of_natCard_eq_two_pow (A : FiniteQuadraticModule.{u})
    (hA : A.IsNondegenerate) {N : ℕ} (hN : Nat.card A = 2 ^ N) :
    ∃ (b : ℕ) (k : Fin b → ℕ) (η : Fin b → ℤ) (c : ℕ) (ku : Fin c → ℕ) (d : ℕ) (kv : Fin d → ℕ),
      (∀ i, Odd (η i)) ∧
        Nonempty (Isometry ((pi fun i ↦ dyadicCyclic (k i + 1) (η i)).prod
          ((pi fun i ↦ dyadicU (ku i + 1)).prod (pi fun i ↦ dyadicV (kv i + 1)))) A) := by
  obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f⟩⟩ :=
    exists_isometry_prod_pi_generators A hA
  -- An odd cyclic summand has odd order `m > 1` dividing `#A = 2^N`, which is impossible.
  have ha : a = 0 := by
    by_contra ha
    let i : Fin a := ⟨0, Nat.pos_of_ne_zero ha⟩
    have hdvd : m i ∣ 2 ^ N := by
      rw [← hN, ← Nat.card_congr f.toLinearEquiv.toEquiv, Nat.card_prod, Nat.card_pi]
      refine Dvd.dvd.mul_right ?_ _
      simpa using Finset.dvd_prod_of_mem (fun j ↦ Nat.card (oddCyclic (m j) (hm j) (θ j)))
        (Finset.mem_univ i)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      exact Nat.not_odd_iff_even.2 even_two ((Nat.odd_pow_iff hj0).1 (hj ▸ hm i))
    exact not_isPrimePow_one (by simpa [hj, hj0] using (hmθ i).1)
  subst ha
  -- The empty orthogonal sum of odd cyclic summands is trivial and can be dropped.
  exact ⟨b, k, η, c, ku, d, kv, hη, ⟨(uniqueProd _ _).symm.trans f⟩⟩

end FiniteQuadraticModule

namespace FiniteBilinearModule

open FiniteQuadraticModule (oddCyclic dyadicCyclic dyadicU dyadicV pi)

/-- **Nikulin's generator decomposition for symmetric pairings.** A nondegenerate finite bilinear
module is isometric to an orthogonal sum of the pairings of Nikulin's generators: the pairings
`θxy / p^k` of the odd cyclic modules `q_θ^{(p)}(p^k)` with `θ` prime to `p`, the pairings
`ηxy / 2^{k+1}` of the dyadic cyclic modules `q_η^{(2)}(2^{k+1})` with `η` odd, and the pairings
of `u^{(2)}(2^{k+1})` and `v^{(2)}(2^{k+1})`, with matrices `2^{-(k+1)} [[0, 1], [1, 0]]` and
`2^{-(k+1)} [[2, 1], [1, 2]]`. -/
theorem exists_isometry_prod_pi_generators (A : FiniteBilinearModule.{u})
    (hA : A.IsNondegenerate) :
    ∃ (a : ℕ) (m : Fin a → ℕ) (hm : ∀ i, Odd (m i)) (θ : Fin a → ℤ)
      (b : ℕ) (k : Fin b → ℕ) (η : Fin b → ℤ) (c : ℕ) (ku : Fin c → ℕ) (d : ℕ) (kv : Fin d → ℕ),
      (∀ i, IsPrimePow (m i) ∧ IsCoprime (m i : ℤ) (θ i)) ∧ (∀ i, Odd (η i)) ∧
        Nonempty (Isometry ((pi fun i ↦ oddCyclic (m i) (hm i) (θ i)).prod
          ((pi fun i ↦ dyadicCyclic (k i + 1) (η i)).prod
            ((pi fun i ↦ dyadicU (ku i + 1)).prod
              (pi fun i ↦ dyadicV (kv i + 1))))).toFiniteBilinearModule A) := by
  -- Decompose a quadratic refinement of `A`; its bilinear module is `A` itself.
  obtain ⟨Q, rfl⟩ := FiniteQuadraticModule.toFiniteBilinearModule_surjective A
  obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f⟩⟩ :=
    Q.exists_isometry_prod_pi_generators hA
  exact ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f.toFiniteBilinearModule⟩⟩

/-- **Decomposition of symmetric pairings on finite `2`-groups.** A nondegenerate finite bilinear
module of order `2^N` is isometric to an orthogonal sum of the pairings of the dyadic generators:
the cyclic pairings `ηxy / 2^{k+1}` on `ℤ/2^{k+1}` with `η` odd, and the pairings of
`u^{(2)}(2^{k+1})` and `v^{(2)}(2^{k+1})` on `(ℤ/2^{k+1})²`, with matrices
`2^{-(k+1)} [[0, 1], [1, 0]]` and `2^{-(k+1)} [[2, 1], [1, 2]]`. These are the pairings
`A^{k+1}(η)`, `E_0^{k+1}` and `E_1^{k+1}` of Kawauchi and Kojima. -/
theorem exists_isometry_prod_pi_dyadic_of_natCard_eq_two_pow (A : FiniteBilinearModule.{u})
    (hA : A.IsNondegenerate) {N : ℕ} (hN : Nat.card A = 2 ^ N) :
    ∃ (b : ℕ) (k : Fin b → ℕ) (η : Fin b → ℤ) (c : ℕ) (ku : Fin c → ℕ) (d : ℕ) (kv : Fin d → ℕ),
      (∀ i, Odd (η i)) ∧
        Nonempty (Isometry ((pi fun i ↦ dyadicCyclic (k i + 1) (η i)).prod
          ((pi fun i ↦ dyadicU (ku i + 1)).prod
            (pi fun i ↦ dyadicV (kv i + 1)))).toFiniteBilinearModule A) := by
  obtain ⟨Q, rfl⟩ := FiniteQuadraticModule.toFiniteBilinearModule_surjective A
  obtain ⟨b, k, η, c, ku, d, kv, hη, ⟨f⟩⟩ :=
    Q.exists_isometry_prod_pi_dyadic_of_natCard_eq_two_pow hA hN
  exact ⟨b, k, η, c, ku, d, kv, hη, ⟨f.toFiniteBilinearModule⟩⟩

end FiniteBilinearModule

end TauCeti
