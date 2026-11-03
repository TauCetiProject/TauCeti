/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Splitting
public import TauCeti.LinearAlgebra.Charpoly.Nilpotent
public import TauCeti.NumberTheory.NewtonPolygon.InitialSegment
public import TauCeti.NumberTheory.NewtonPolygon.Slopes

/-!
# Finite factors and initial segments of the Fredholm polygon

Let `w` be a row-compact endomorphism of a module `P` with property (Pr), and suppose `P` splits
boundedly as `M ⊕ N` with `M` finite, such that `w` maps `M` into itself (the lower-left block
vanishes). By `TauCeti.charPowerSeries_eq_projectiveCharpolyRev_mul_of_split`, the Fredholm
series factors as

`det (1 - T w) = Q · S`,

where `Q = det (1 - T w|_M)` is a polynomial and `S` is the Fredholm series of the complementary
block. For a free `M` the degree of `Q` is at most the rank, with equality exactly when `w|_M`
has nonzero determinant, in particular when it is invertible
(`LinearMap.natDegree_projectiveCharpolyRev_eq_finrank_iff`).

This file reads the Newton polygon of `det (1 - T w)` off such a splitting. Over a reduced
coefficient ring a nilpotent block has `Q = 1`
(`LinearMap.projectiveCharpolyRev_eq_one_of_isNilpotent`), so it contributes nothing to the
Fredholm series (`TauCeti.charPowerSeries_eq_of_split_of_isNilpotent`), in accordance with zero
eigenvalues being invisible to it.

Over a complete nontrivially normed field `K` whose norm is `‖x‖ = B ^ (-v x)` for a real
valuation `v` and a base `B > 1`, if every finite slope of the Newton polygon of `Q` is at most
every finite slope of the Newton polygon of `S`, then the Newton polygon of `det (1 - T w)` agrees
with that of `Q` on `[0, deg Q]`
(`TauCeti.newtonPolygon_charPowerSeries_eq_of_split`). Thus the finite summand supplies the
initial segment of the Fredholm polygon, and its slopes are the first `deg Q` slopes of `w`.

## Main results

* `TauCeti.charPowerSeries_eq_of_split_of_isNilpotent`: a nilpotent finite summand does not
  change the Fredholm series over a reduced ring.
* `TauCeti.newtonPolygon_charPowerSeries_eq_of_split`: a finite invariant summand whose slopes
  precede those of its complement supplies the initial segment of the Fredholm polygon.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5–7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open ContinuousLinearMap PowerSeries

namespace TauCeti

section Nilpotent

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [NormedRing.IsTate R] [IsReduced R]
  {M N P : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [Module.Finite R M] [SeminormedAddCommGroup N] [Module R N]
  [SeminormedAddCommGroup P] [Module R P]

/-- **A nilpotent finite summand is invisible to the Fredholm series.** Over a reduced
coefficient ring, if `w` is upper triangular for a bounded splitting `i r + j s = id` through a
finite `M` and a complement `N`, and its block `r w i` on `M` is nilpotent, then
`det (1 - T w)` is the Fredholm series of the complementary block `s w j`. Reducedness is needed:
over `K[ε]/(ε²)` the nilpotent scalar `ε` on a line has `det (1 - T ε) = 1 - ε T`. -/
theorem charPowerSeries_eq_of_split_of_isNilpotent {w : P →L[R] P} (hw : w.IsPrCompact)
    (hM : HasPr R M) (hN : HasPr R N)
    (i : M →L[R] P) (r : P →L[R] M) (j : N →L[R] P) (s : P →L[R] N)
    (hsplit : i.comp r + j.comp s = .id R P) (htri : s.comp (w.comp i) = 0)
    (hnil : IsNilpotent (r.comp (w.comp i))) :
    w.charPowerSeries = (s.comp (w.comp j)).charPowerSeries := by
  have := hM.projective
  have hnil' : IsNilpotent (r.comp (w.comp i) : M →ₗ[R] M) := hnil.map toLinearMapRingHom
  rw [charPowerSeries_eq_projectiveCharpolyRev_mul_of_split hw hM hN i r j s hsplit htri,
    LinearMap.projectiveCharpolyRev_eq_one_of_isNilpotent hnil',
    Polynomial.coe_one, one_mul]

end Nilpotent

section Field

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {B : ℝ} (hB : 1 < B)
  (hv : ∀ x ≠ 0, ‖x‖ = B ^ (-(v x).untop₀))
  {M N P : Type*} [NormedAddCommGroup M] [Module K M] [IsBoundedSMul K M]
  [FiniteDimensional K M] [SeminormedAddCommGroup N] [Module K N]
  [SeminormedAddCommGroup P] [Module K P]

include hB hv in
/-- **Initial segment of the Fredholm polygon.** Let `w` be a row-compact endomorphism of a
module with property (Pr), upper triangular for a bounded splitting `i r + j s = id` through a
finite-dimensional `M` and a complement `N`. If every finite slope of the Newton polygon of the
finite factor `Q = det (1 - T (r w i))` is at most every finite slope of the Newton polygon of the
complementary Fredholm series `det (1 - T (s w j))`, then the Newton polygon of `det (1 - T w)`
agrees with that of `Q` at every index up to the degree of `Q`. -/
theorem newtonPolygon_charPowerSeries_eq_of_split {w : P →L[K] P} (hw : w.IsPrCompact)
    (hM : HasPr K M) (hN : HasPr K N)
    (i : M →L[K] P) (r : P →L[K] M) (j : N →L[K] P) (s : P →L[K] N)
    (hsplit : i.comp r + j.comp s = .id K P) (htri : s.comp (w.comp i) = 0)
    (hslopes : ∀ σ ∈ ((r.comp (w.comp i) : M →ₗ[K] M).projectiveCharpolyRev).newtonSlopes v,
      ∀ l ∈ finiteEdges ((s.comp (w.comp j)).charPowerSeries.newtonPolygon v),
        σ ≤ unitSlope ((s.comp (w.comp j)).charPowerSeries.newtonPolygon v) l)
    {n : ℕ} (hn : n ≤ ((r.comp (w.comp i) : M →ₗ[K] M).projectiveCharpolyRev).natDegree) :
    w.charPowerSeries.newtonPolygon v n =
      ((r.comp (w.comp i) : M →ₗ[K] M).projectiveCharpolyRev).newtonPolygon v n := by
  set Q := (r.comp (w.comp i) : M →ₗ[K] M).projectiveCharpolyRev
  set S := (s.comp (w.comp j)).charPowerSeries
  have hS : S.IsEntire := ((hw.comp_clm j hN).clm_comp s hN).isEntire_charPowerSeries
  have hQ0 : Q.coeff 0 = 1 := LinearMap.coeff_projectiveCharpolyRev_zero _
  have hQ : Q ≠ 0 := fun h ↦ by simp [h] at hQ0
  have hord : S.order = (0 : ℕ) := order_eq_nat.2 ⟨by simp [S], fun _ h ↦ absurd h (by omega)⟩
  have hp : (Q : K⟦X⟧).newtonPolygon v Q.natDegree ≠ ⊤ := by
    rw [Polynomial.newtonPolygon_coe, Polynomial.newtonPolygon_natDegree, v.ne_top_iff]
    exact Polynomial.leadingCoeff_ne_zero.2 hQ
  have key := (isEntire_coe Q).newtonPolygon_mul_eqOn_initialSegment v hB hv hS hp hord
    (fun k hk _ l hl ↦ by
      rw [Polynomial.newtonPolygon_coe] at hk ⊢
      exact hslopes _ ((Q.mem_newtonSlopes v).2 ⟨k, hk, rfl⟩) l hl) n hn
  rw [add_zero, Polynomial.newtonPolygon_coe, coeff_zero_eq_constantCoeff,
    constantCoeff_charPowerSeries, v.map_one, add_zero] at key
  rw [charPowerSeries_eq_projectiveCharpolyRev_mul_of_split hw hM hN i r j s hsplit htri]
  exact key

end Field

end TauCeti
