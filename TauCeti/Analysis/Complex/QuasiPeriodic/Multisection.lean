/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.QuasiPeriodic.Basic
public import TauCeti.Analysis.Contour.Argument.PowerSum
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Holomorphic curves in a flat line bundle of infinite-order holonomy lie on the zero section

Let `V ⧸ L` be a compact complex torus and let `N` be the flat unitary line bundle of a character
`ψ : L → S¹`, the quotient of `V × ℂ` by `ω • (z, w) = (z + ω, ψ ω w)`. A curve in the total space
of `N` which is finite over the torus is described on `V × ℂ` by its fibres: for each `z ∈ V` the
multiset `R z` of the points `w` with `(z, w)` on the curve, counted with multiplicity. The curve
is invariant under the deck group exactly when

`R (z + ω) = ψ ω • R z`,

and it is holomorphic when the power sums `p_k (z) = ∑_{w ∈ R z} wᵏ` are holomorphic functions of
`z`; by Newton's identities, so are then the elementary symmetric functions `b_k (z)` of `R z`, the
coefficients of the polynomial `∏_{w ∈ R z} (X - w)` cutting the curve out.

The power sum `p_k` is a holomorphic section of `N ^ k`: `p_k (z + ω) = ψ ω ^ k p_k (z)`. If some
holonomy of `ψ` has infinite order, every positive power of `N` is a nontrivial flat line on every
finite covering torus, so it has no nonzero holomorphic section
(`Differentiable.eq_zero_of_add_eq_pow_smul`). Hence all the power sums vanish, and every fibre
consists of zeros: the curve lies on the zero section, with some multiplicity
(`TauCeti.eq_replicate_card_zero_of_add_eq_map_mul`). Deck invariance is only required for a
subgroup `L' ≤ L` of finite index, so the statement applies to curves in the pull-back of `N` to
every finite covering torus `V ⧸ L'`.

An analytic curve is locally cut out by one holomorphic equation. If near each base point `z₀`
the fibres are the zeros, in a disc `|w - c| < K`, of the slices `w ↦ f (z, w)` of a function `f`
analytic near `{z₀} × closedBall c K` and without zeros on `{z₀} × sphere c K`, the argument
principle makes the power sums of the fibres holomorphic
(`TauCeti.Contour.differentiableAt_sum_map_pow_zeroMultiset`), so such a curve lies on the zero
section (`TauCeti.eq_replicate_card_zero_of_eventuallyEq_zeroMultiset`).

For a square-zero torus `C` in a symplectic four-manifold whose normal line `N` carries a flat
structure of irrational holonomy, this is the rigidity of `C` in its integrable normal model:
a holomorphic curve in the total space of `N`, finite over `C` and described by its fibres as
above, is supported on the zero section `C`. Infinite order cannot be dropped: if `ψ` is
nontrivial with values `±1`, the constant fibres `R z = {a, -a}`, `a ≠ 0`, are deck invariant and
have constant power sums, but do not lie on the zero section.

## Main results

* `TauCeti.eq_replicate_card_zero_of_add_eq_map_mul`: a deck-invariant family of multisets with
  holomorphic power sums, over a flat line of infinite-order holonomy, consists of zeros.
* `TauCeti.eq_replicate_card_zero_of_eventuallyEq_zeroMultiset`: the same for a deck-invariant
  family of multisets which are locally the zeros of the slices of a holomorphic function.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open Filter Metric Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {R : V → Multiset ℂ} {L L' : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]
  {ψ : AddChar L Circle} {ω₀ : L}

/-- **Holomorphic curves in a flat line of infinite-order holonomy lie on the zero section.**
Let `ψ` be a unitary character of a full lattice `L` taking a value of infinite order, and let
`L' ≤ L` be a subgroup of finite index. Let `R` be a family of multisets of complex numbers,
invariant under the deck group of the pull-back of the flat line of `ψ` to `V ⧸ L'`, that is
`R (z + ω) = ψ ω • R z` for `ω ∈ L'`, whose power sums `z ↦ ∑_{w ∈ R z} wᵏ`, `k > 0`, are
holomorphic. Then every `R z` consists of zeros. -/
theorem eq_replicate_card_zero_of_add_eq_map_mul (hω₀ : ¬IsOfFinOrder (ψ ω₀)) (hL' : L' ≤ L)
    (hidx : L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0)
    (hR : ∀ k, 0 < k → Differentiable ℂ fun z ↦ ((R z).map (· ^ k)).sum)
    (h : ∀ z, ∀ (ω) (hω : ω ∈ L'), R (z + ω) = (R z).map ((ψ ⟨ω, hL' hω⟩ : ℂ) * ·)) (z : V) :
    R z = Multiset.replicate (Multiset.card (R z)) 0 := by
  refine Multiset.eq_replicate_card_zero_of_sum_map_pow_eq_zero fun k hk _ ↦ ?_
  -- The `k`-th power sum is a holomorphic section of the `k`-th power of the flat line.
  refine congrFun ((hR k hk).eq_zero_of_add_eq_pow_smul hω₀ hL' hidx hk.ne' fun z ω hω ↦ ?_) z
  simp [h z ω hω, mul_pow, Multiset.sum_map_mul_left]

/-- **Curves cut out locally by holomorphic equations.** Let `ψ`, `L'` and the deck invariance of
`R` be as in `TauCeti.eq_replicate_card_zero_of_add_eq_map_mul`. Suppose that near every base
point `z₀` the multisets `R z` are the zeros, in a disc `ball c K`, of the slices `w ↦ f (z, w)` of
a function `f` analytic at every point of `{z₀} × closedBall c K` and without zeros on
`{z₀} × sphere c K`. Then every `R z` consists of zeros. -/
theorem eq_replicate_card_zero_of_eventuallyEq_zeroMultiset (hω₀ : ¬IsOfFinOrder (ψ ω₀))
    (hL' : L' ≤ L) (hidx : L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0)
    (hR : ∀ z₀, ∃ (f : V × ℂ → ℂ) (c : ℂ) (K : ℝ),
      (∀ ζ ∈ closedBall c K, AnalyticAt ℂ f (z₀, ζ)) ∧ (∀ ζ ∈ sphere c K, f (z₀, ζ) ≠ 0) ∧
        R =ᶠ[𝓝 z₀] fun z ↦ AnalyticOnNhd.zeroMultiset (fun w ↦ f (z, w)) (ball c K))
    (h : ∀ z, ∀ (ω) (hω : ω ∈ L'), R (z + ω) = (R z).map ((ψ ⟨ω, hL' hω⟩ : ℂ) * ·)) (z : V) :
    R z = Multiset.replicate (Multiset.card (R z)) 0 := by
  refine eq_replicate_card_zero_of_add_eq_map_mul hω₀ hL' hidx (fun k _ z₀ ↦ ?_) h z
  -- By the argument principle the power sums of the local zeros are holomorphic.
  obtain ⟨f, c, K, hf, hsphere, hRf⟩ := hR z₀
  exact (Contour.differentiableAt_sum_map_pow_zeroMultiset hf hsphere k).congr_of_eventuallyEq
    (hRf.mono fun z hz ↦ by simp only [hz])

end TauCeti
