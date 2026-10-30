/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Zero
public import TauCeti.KnotTheory.Grid.SignAssignment.Basic

/-!
# The signed unblocked grid complex

Given a sign assignment `S` for grid states of size `n`, the *signed* unblocked differential of a
grid diagram counts each empty `X`-avoiding rectangle `r` from `x` to `y` with the sign `S(r)`:

`∂⁻_S x = ∑_y ∑_r S(r) V^{O(r)} · y`.

It is defined over the polynomial ring `R[V₀, …, V_{n-1}]` for an arbitrary commutative ring `R`,
and it squares to zero there: the juxtaposition argument pairs the two-step terms of `∂⁻_S ∘ ∂⁻_S`
off two by two, the two terms of a pair cover the same domain, so they have equal weights and, by
the square rule, opposite signs. The annular two-step terms cover an `X`-marking and are not
counted at all, so the annulus rules are not needed here.

In characteristic two every sign is `1`, and the signed differential is the unblocked differential
`TauCeti.GridDiagram.unblockedDifferential`. Changing the sign assignment by a gauge `f`
conjugates the signed differential by the diagonal automorphism `x ↦ f(x) x` of `GC⁻`, so the
signed complexes of gauge-equivalent sign assignments are isomorphic.

## Main definitions

* `TauCeti.GridDiagram.signedUnblockedCoefficient`: the matrix coefficient of `∂⁻_S`.
* `TauCeti.GridDiagram.signedUnblockedDifferential`: the signed unblocked differential `∂⁻_S`.

## Main results

* `TauCeti.GridDiagram.signedUnblockedDifferential_comp_self_eq_zero`: `∂⁻_S ∘ ∂⁻_S = 0` over
  every commutative ring.
* `TauCeti.GridDiagram.signedUnblockedDifferential_eq_unblockedDifferential`: in characteristic
  two the signed differential is the unblocked differential.
* `TauCeti.GridDiagram.signedUnblockedDifferential_gauge`: a gauge transform of the sign
  assignment conjugates the signed differential by `TauCeti.GridChain.gaugeEquiv`.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4: the complex with signs.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 15: grid homology with integer coefficients.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (S : GridSignAssignment n) (R : Type*) [CommRing R]

/-! ### The signed differential -/

/-- The matrix coefficient of the signed unblocked differential from `x` to `y`: the signed sum of
the weights of the empty rectangles from `x` to `y` that carry no `X`-marking. -/
noncomputable def signedUnblockedCoefficient (x y : GridState n) : MvPolynomial (Fin n) R :=
  ∑ r ∈ G.unblockedRectangles x y, (S.signOf r : ℤ) • G.OMonomial R r.toGridRectangle

/-- The signed matrix coefficient is the signed sum of the weights of its rectangles. -/
theorem signedUnblockedCoefficient_def (x y : GridState n) :
    G.signedUnblockedCoefficient S R x y =
      ∑ r ∈ G.unblockedRectangles x y, (S.signOf r : ℤ) • G.OMonomial R r.toGridRectangle := by
  rw [signedUnblockedCoefficient]

/-- The signed unblocked differential has no diagonal matrix coefficient. -/
@[simp]
theorem signedUnblockedCoefficient_self (x : GridState n) :
    G.signedUnblockedCoefficient S R x x = 0 := by
  rw [signedUnblockedCoefficient_def, unblockedRectangles_self, Finset.sum_empty]

/-- The signed unblocked differential `∂⁻_S` of a grid diagram, for the sign assignment `S`, as a
linear map on `GC⁻` over the polynomial ring. -/
noncomputable def signedUnblockedDifferential :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.linearCombination (MvPolynomial (Fin n) R) fun x =>
    Finsupp.equivFunOnFinite.symm (G.signedUnblockedCoefficient S R x)

/-- The `y`-coefficient of the signed differential of the generator `x` is the signed matrix
coefficient. -/
theorem signedUnblockedDifferential_single_apply (x y : GridState n) :
    G.signedUnblockedDifferential S R (Finsupp.single x 1) y =
      G.signedUnblockedCoefficient S R x y := by
  simp [signedUnblockedDifferential]

/-- The coefficient formula for the signed differential on an arbitrary chain. -/
@[simp]
theorem signedUnblockedDifferential_apply_apply (c : GridChainMinus R n) (y : GridState n) :
    G.signedUnblockedDifferential S R c y =
      c.sum fun x a => a * G.signedUnblockedCoefficient S R x y := by
  simp [signedUnblockedDifferential, Finsupp.linearCombination_apply, Finsupp.sum_apply]

/-- The matrix of the square of the signed differential: its `(x, z)` entry is the sum over
intermediate grid states of the products of the two matrix coefficients. -/
theorem signedUnblockedDifferential_sq_single_apply (x z : GridState n) :
    G.signedUnblockedDifferential S R (G.signedUnblockedDifferential S R (Finsupp.single x 1)) z =
      ∑ y : GridState n,
        G.signedUnblockedCoefficient S R x y * G.signedUnblockedCoefficient S R y z := by
  rw [signedUnblockedDifferential_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp

/-! ### The square of the signed differential -/

/-- The two-step matrix entry of the square of the signed differential is the sum, over the
two-step decompositions it counts, of the decomposition weights times the products of the two
signs. -/
theorem sum_signedUnblockedCoefficient_mul_signedUnblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.signedUnblockedCoefficient S R x y * G.signedUnblockedCoefficient S R y z =
      ∑ D ∈ G.unblockedDecompositions x z,
        ((S.signOf D.first * S.signOf D.second : ℤˣ) : ℤ) • G.unblockedDecompositionWeight R D := by
  have hstep : ∀ y : GridState n,
      G.signedUnblockedCoefficient S R x y * G.signedUnblockedCoefficient S R y z =
        ∑ r₁ ∈ G.unblockedRectangles x y, ∑ r₂ ∈ G.unblockedRectangles y z,
          ((S.signOf r₁ * S.signOf r₂ : ℤˣ) : ℤ) •
            (G.OMonomial R r₁.toGridRectangle * G.OMonomial R r₂.toGridRectangle) := fun y => by
    rw [G.signedUnblockedCoefficient_def S R x y, G.signedUnblockedCoefficient_def S R y z,
      Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm, Units.val_mul]
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hstep y]
  simp only [unblockedDecompositionWeight_def]
  exact (G.sum_unblockedDecompositions x z fun _ r₁ r₂ => ((S.signOf r₁ * S.signOf r₂ : ℤˣ) : ℤ) •
    (G.OMonomial R r₁.toGridRectangle * G.OMonomial R r₂.toGridRectangle)).symm

/-- Every matrix entry of the square of the signed differential vanishes. -/
theorem sum_signedUnblockedCoefficient_mul_signedUnblockedCoefficient_eq_zero
    (x z : GridState n) :
    ∑ y : GridState n,
      G.signedUnblockedCoefficient S R x y * G.signedUnblockedCoefficient S R y z = 0 := by
  rw [G.sum_signedUnblockedCoefficient_mul_signedUnblockedCoefficient S R x z]
  have hmem : ∀ D ∈ G.unblockedDecompositions x z, D.first.IsEmpty ∧ D.second.IsEmpty :=
    fun D hD => by
      obtain ⟨h₁, h₂⟩ := (G.mem_unblockedDecompositions x z D).mp hD
      exact ⟨G.isEmpty_of_mem_unblockedRectangles h₁, G.isEmpty_of_mem_unblockedRectangles h₂⟩
  -- Two decompositions with opposite sign products and equal weights cancel.
  have hcancel : ∀ (D E : GridRectangleDecomposition x z),
      S.signOf E.first * S.signOf E.second = -(S.signOf D.first * S.signOf D.second) →
      G.unblockedDecompositionWeight R E = G.unblockedDecompositionWeight R D →
      ((S.signOf D.first * S.signOf D.second : ℤˣ) : ℤ) • G.unblockedDecompositionWeight R D +
        ((S.signOf E.first * S.signOf E.second : ℤˣ) : ℤ) •
          G.unblockedDecompositionWeight R E = 0 := fun D E hsign hweight => by
    rw [hsign, hweight, Units.val_neg, neg_smul, add_neg_cancel]
  rcases eq_or_ne z x with rfl | hzx
  · -- A rectangle and a counted rectangle back would cover an annulus, hence an `X`-marking.
    refine Finset.sum_eq_zero fun D hD => ?_
    obtain ⟨h₁, h₂⟩ := (G.mem_unblockedDecompositions z z D).mp hD
    rcases G.unblockedRectangles_eq_empty_or_unblockedRectangles_eq_empty z D.middle with he | he
    · rw [he] at h₁
      exact absurd h₁ (Finset.notMem_empty _)
    · rw [he] at h₂
      exact absurd h₂ (Finset.notMem_empty _)
  refine G.sum_unblockedDecompositions_eq_zero hzx _ (fun D hD h => ?_)
    (fun D hD hone hfirst hsecond => ?_)
  · obtain ⟨h₁, h₂⟩ := hmem D hD
    refine hcancel D _ (S.signOf_mul_signOf_eq_neg h₁ h₂ (D.isEmpty_commute_first h h₁ h₂)
      (D.isEmpty_commute_second h h₁ h₂) (D.commute_ne h) ?_)
      (G.unblockedDecompositionWeight_commute R D h)
    rw [D.commute_first_toGridRectangle h, D.commute_second_toGridRectangle h, add_comm]
  · have hrecut := (D.isRecut_recut hone hfirst hsecond)
    exact hcancel D _ (S.signOf_mul_signOf_eq_neg hfirst hsecond hrecut.isEmpty_first
      hrecut.isEmpty_second (D.recut_ne hone hfirst hsecond) hrecut.isRepartition.val_add_val_eq)
      (G.unblockedDecompositionWeight_recut R D hone hfirst hsecond)

/-- The signed unblocked differential squares to zero, over every commutative ring. -/
theorem signedUnblockedDifferential_comp_self_eq_zero :
    G.signedUnblockedDifferential S R ∘ₗ G.signedUnblockedDifferential S R =
      (0 : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun z => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  rw [G.signedUnblockedDifferential_sq_single_apply S R x z]
  exact G.sum_signedUnblockedCoefficient_mul_signedUnblockedCoefficient_eq_zero S R x z

/-! ### Characteristic two -/

/-- In characteristic two every sign is `1`, so the signed matrix coefficient is the unblocked
one. -/
theorem signedUnblockedCoefficient_eq_unblockedCoefficient [CharP R 2] (x y : GridState n) :
    G.signedUnblockedCoefficient S R x y = G.unblockedCoefficient R x y := by
  rw [signedUnblockedCoefficient_def, unblockedCoefficient_def]
  refine Finset.sum_congr rfl fun r _ => ?_
  rcases Int.units_eq_one_or (S.signOf r) with h | h
  · rw [h, Units.val_one, one_zsmul]
  · rw [h, Units.val_neg, Units.val_one, neg_smul, one_zsmul, CharTwo.neg_eq]

/-- In characteristic two the signed unblocked differential is the unblocked differential, for
every sign assignment. -/
theorem signedUnblockedDifferential_eq_unblockedDifferential [CharP R 2] :
    G.signedUnblockedDifferential S R = G.unblockedDifferential R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [signedUnblockedDifferential_single_apply, unblockedDifferential_single_apply,
    signedUnblockedCoefficient_eq_unblockedCoefficient]

/-! ### Gauge transforms -/

/-- A gauge transform multiplies the signed matrix coefficient from `x` to `y` by `f x * f y`. -/
theorem signedUnblockedCoefficient_gauge (f : GridState n → ℤˣ) (x y : GridState n) :
    G.signedUnblockedCoefficient (S.gauge f) R x y =
      ((f x * f y : ℤˣ) : ℤ) • G.signedUnblockedCoefficient S R x y := by
  rw [signedUnblockedCoefficient_def, signedUnblockedCoefficient_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [S.signOf_gauge f (G.isEmpty_of_mem_unblockedRectangles hr), Units.val_mul, mul_smul]

/-- A gauge transform of the sign assignment conjugates the signed differential by the gauge
automorphism of `GC⁻`. In particular the signed complexes of gauge-equivalent sign assignments are
isomorphic. -/
theorem signedUnblockedDifferential_gauge (f : GridState n → ℤˣ) :
    G.signedUnblockedDifferential (S.gauge f) R =
      (GridChain.gaugeEquiv R f).toLinearMap ∘ₗ G.signedUnblockedDifferential S R ∘ₗ
        (GridChain.gaugeEquiv R f).toLinearMap := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearEquiv.coe_coe,
    GridChain.gaugeEquiv_single]
  rw [signedUnblockedDifferential_single_apply, signedUnblockedCoefficient_gauge,
    GridChain.gaugeEquiv_apply_apply]
  simp only [signedUnblockedDifferential_apply_apply, Finsupp.sum_single_index, zero_mul,
    zsmul_eq_mul, Units.val_mul, Int.cast_mul]
  ring

end GridDiagram

end TauCeti
