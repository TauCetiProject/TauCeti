/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Decomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification

/-!
# Symmetric pairings on finite abelian groups of odd order

On a finite abelian group `A` of odd order `n`, a symmetric pairing `b : A × A → ℚ/ℤ` has exactly
one quadratic refinement, the map

```text
q(x) = ((n + 1) / 2) · b(x, x).
```

Indeed every quadratic map `q` with polar form `b` satisfies `2q(x) = b(x, x)` and `n q(x) = 0`,
so `q(x) = (n + 1) q(x) = ((n + 1) / 2) · b(x, x)`. Consequently a bilinear isometry between finite
quadratic modules of odd order preserves the quadratic maps, and finite quadratic modules of odd
order are classified by their bilinear modules alone.

Through this refinement, Nikulin's decomposition and the classification of orthogonal sums of odd
cyclic generators pass from quadratic modules to symmetric pairings. For an odd prime `p`, every
nondegenerate symmetric pairing on a finite abelian `p`-group is an orthogonal sum of the pairings
`b_θ^{(p)}(p^k)` of the generators `q_θ^{(p)}(p^k)`, on `ℤ/p^k` with `b(x, y) = θxy / p^k`, for
`k ≥ 1` and `θ` prime to `p`. Two such orthogonal sums are isometric exactly when, for every
`m ≥ 1`, they have the same number of summands of order `p^m`, and the Legendre symbols of the
coefficients of these summands have the same product; that product is the Legendre symbol of the
determinant `∏ θᵢ` of the homogeneous summand of order `p^m`.

## Main declarations

* `TauCeti.FiniteBilinearModule.quadraticRefinement`: the quadratic refinement
  `x ↦ ((n + 1) / 2) · b(x, x)` of a finite bilinear module of odd order `n`.
* `TauCeti.FiniteQuadraticModule.quadratic_eq_nsmul_pairing_self_of_odd` and
  `TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`: every finite quadratic module of odd
  order is the quadratic refinement of its bilinear module.
* `TauCeti.FiniteQuadraticModule.map_quadratic_of_odd` and
  `TauCeti.FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd`: a bilinear isometry between
  finite quadratic modules of odd order is a quadratic isometry.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`: finite quadratic
  modules of odd order are isometric exactly when their bilinear modules are.
* `TauCeti.FiniteBilinearModule.exists_isometry_pi_oddCyclic_of_natCard_eq_pow`: at an odd prime
  `p`, a nondegenerate finite bilinear module of order `p^N` is an orthogonal sum of the pairings
  `b_θ^{(p)}(p^k)`, `k ≥ 1`, with `θ` prime to `p`.
* `TauCeti.FiniteBilinearModule.nonempty_isometry_pi_oddCyclic_iff`: the classification of
  orthogonal sums of the pairings `b_θ^{(p)}(p^k)` by the numbers of summands of each order and
  the products of the Legendre symbols of their coefficients.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti

universe u v

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule.{u})

/-- **The quadratic refinement of a symmetric pairing of odd order.** On a finite abelian group
of odd order `n`, the quadratic map `x ↦ ((n + 1) / 2) • b(x, x)` has polar form `b`, since
`(n + 1) • b(x, y) = b(x, y)`. It is the only finite quadratic module structure with pairing `b`
(`TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`).

Exposed so that its bilinear module is `A` by definition, and bilinear isometries into or out of
`A` are bilinear isometries of the refinement. -/
@[expose] noncomputable def quadraticRefinement (hA : Odd (Nat.card A)) :
    FiniteQuadraticModule where
  toFiniteBilinearModule := A
  quadratic := LinearMap.BilinMap.toQuadraticMap (((Nat.card A + 1) / 2) • A.toBilin)
  polar_eq_pairing' x y := by
    obtain ⟨t, ht⟩ := hA
    have hn : Nat.card A • A.pairing x y = 0 := by
      rw [← pairing_nsmul_left, card_nsmul_eq_zero', pairing_zero_left]
    have h2 : (Nat.card A + 1) / 2 * 2 = Nat.card A + 1 := by omega
    rw [LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, toBilin_apply, toBilin_apply, A.pairing_comm y x,
      ← smul_add, ← two_nsmul, smul_smul, h2, succ_nsmul, hn, zero_add]

/-- The bilinear module of the quadratic refinement of `A` is `A`. -/
@[simp]
theorem quadraticRefinement_toFiniteBilinearModule (hA : Odd (Nat.card A)) :
    (A.quadraticRefinement hA).toFiniteBilinearModule = A :=
  (rfl)

/-- The quadratic refinement of a pairing `b` on a group of odd order `n` is
`x ↦ ((n + 1) / 2) • b(x, x)`. -/
@[simp]
theorem quadraticRefinement_quadratic (hA : Odd (Nat.card A)) (x : A) :
    (A.quadraticRefinement hA).quadratic x = ((Nat.card A + 1) / 2) • A.pairing x x :=
  (LinearMap.BilinMap.toQuadraticMap_apply _ x).trans <| by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, toBilin_apply]

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- On a finite quadratic module of odd order `n`, the quadratic map is determined by the pairing:
`q(x) = ((n + 1) / 2) • b(x, x)`. -/
theorem quadratic_eq_nsmul_pairing_self_of_odd (hA : Odd (Nat.card A)) (x : A) :
    A.quadratic x = ((Nat.card A + 1) / 2) • A.toFiniteBilinearModule.pairing x x := by
  have h2 : (Nat.card A + 1) / 2 * 2 = Nat.card A + 1 := by
    obtain ⟨t, ht⟩ := hA
    omega
  rw [← polar_eq_pairing, QuadraticMap.polar_self, smul_smul, h2, succ_nsmul,
    A.natCard_nsmul_quadratic_of_odd hA, zero_add]

/-- **Uniqueness of the quadratic refinement in odd order.** A finite quadratic module of odd
order is the quadratic refinement of its bilinear module. -/
theorem eq_quadraticRefinement (A : FiniteQuadraticModule.{u}) (hA : Odd (Nat.card A)) :
    A = A.toFiniteBilinearModule.quadraticRefinement hA := by
  obtain ⟨B, q, hq⟩ := A
  congr 1
  ext x
  exact (quadratic_eq_nsmul_pairing_self_of_odd (A := ⟨B, q, hq⟩) hA x).trans
    (B.quadraticRefinement_quadratic hA x).symm

/-- A bilinear isometry between finite quadratic modules of odd order preserves the quadratic
maps. -/
theorem map_quadratic_of_odd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : B.quadratic (f x) = A.quadratic x := by
  have hB : Nat.card B = Nat.card A := (Nat.card_congr f.toAddEquiv.toEquiv).symm
  rw [quadratic_eq_nsmul_pairing_self_of_odd (hB ▸ hA), quadratic_eq_nsmul_pairing_self_of_odd hA,
    hB, f.map_pairing]

/-- A bilinear isometry between finite quadratic modules of odd order, as a quadratic isometry. -/
def isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    Isometry A B where
  toLinearEquiv := f.toAddEquiv.toIntLinearEquiv
  map_app' := map_quadratic_of_odd hA f

/-- The quadratic isometry `isometryOfBilinearIsometryOfOdd hA f` acts as `f`. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : isometryOfBilinearIsometryOfOdd hA f x = f x :=
  (rfl)

/-- Forgetting the quadratic maps of `isometryOfBilinearIsometryOfOdd hA f` recovers `f`. -/
@[simp]
theorem toFiniteBilinearModule_isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toFiniteBilinearModule = f :=
  -- Both sides have the additive equivalence `f.toAddEquiv`, repackaged as a `ℤ`-linear one.
  FiniteBilinearModule.Isometry.toAddEquiv_injective
    (Isometry.toFiniteBilinearModule_toAddEquiv _)

/-- Finite quadratic modules of odd order are isometric exactly when their bilinear modules are.
In odd order no Gauss-sum condition is needed, unlike Nikulin's comparison theorem
`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_and_gaussSign_eq`. -/
theorem nonempty_isometry_iff_bilinear_isometry_of_odd (hA : Odd (Nat.card A)) :
    Nonempty (Isometry A B) ↔
      Nonempty (FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toFiniteBilinearModule⟩, fun ⟨f⟩ ↦ ⟨isometryOfBilinearIsometryOfOdd hA f⟩⟩

end FiniteQuadraticModule

namespace FiniteBilinearModule

open Finset
open FiniteQuadraticModule (oddCyclic pi)

variable {p : ℕ} [Fact p.Prime]

/-- **Decomposition of symmetric pairings on `p`-groups at an odd prime.** A nondegenerate finite
bilinear module of order `p^N`, for an odd prime `p`, is isometric to an orthogonal sum of the
pairings `b_θ^{(p)}(p^k)` of the odd cyclic generators, with `k ≥ 1` and `θ` prime to `p`. -/
theorem exists_isometry_pi_oddCyclic_of_natCard_eq_pow (hp : Odd p) (A : FiniteBilinearModule.{u})
    (hA : A.IsNondegenerate) {N : ℕ} (hN : Nat.card A = p ^ N) :
    ∃ (n : ℕ) (k : Fin n → ℕ) (θ : Fin n → ℤ), (∀ i, 0 < k i ∧ IsCoprime (p : ℤ) (θ i)) ∧
      Nonempty (Isometry
        (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i)).toFiniteBilinearModule A) := by
  -- The bilinear module of the refinement is `A` by definition
  -- (`quadraticRefinement_toFiniteBilinearModule`), so `hA` and `f.toFiniteBilinearModule` apply.
  obtain ⟨n, k, θ, hkθ, ⟨f⟩⟩ :=
    (A.quadraticRefinement (hN ▸ hp.pow)).exists_isometry_pi_oddCyclic_of_natCard_eq_pow hp hA hN
  exact ⟨n, k, θ, hkθ, ⟨f.toFiniteBilinearModule⟩⟩

/-- **Classification of symmetric pairings on `p`-groups at an odd prime.** For an odd prime `p`,
exponents `k_i`, `l_j` and coefficients `θ_i`, `η_j` prime to `p`, the orthogonal sums of the
pairings `b_{θ_i}^{(p)}(p^{k_i})` and `b_{η_j}^{(p)}(p^{l_j})` are isometric exactly when, for
every `m ≥ 1`, they have the same number of summands of order `p^m`, and the Legendre symbols of
the coefficients of these summands have the same product. -/
theorem nonempty_isometry_pi_oddCyclic_iff (hp : Odd p) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) (l : κ → ℕ) {θ : ι → ℤ} {η : κ → ℤ} (hθ : ∀ i, IsCoprime (p : ℤ) (θ i))
    (hη : ∀ j, IsCoprime (p : ℤ) (η j)) :
    Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i)).toFiniteBilinearModule
      (pi fun j ↦ oddCyclic (p ^ l j) hp.pow (η j)).toFiniteBilinearModule) ↔
      ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m} ∧
        ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j) := by
  have hodd : Odd (Nat.card (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))) := by
    rw [Nat.card_pi]
    simpa [Finset.prod_pow_eq_pow_sum] using hp.pow
  rw [← FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd]
  exact FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff hp k l hθ hη

end FiniteBilinearModule

end TauCeti
