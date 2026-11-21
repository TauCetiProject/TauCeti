/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Diagonal.Basic

/-!
# Range and invertibility of diagonal operators on `c₀`

A bounded diagonal over a normed division ring is injective, or has dense range, exactly when
none of its entries vanish. Invertibility is stronger: the reciprocal entries must be bounded.
`diagonalEquiv` constructs the continuous inverse from this bound. Conversely, testing an
inverse on coordinate vectors bounds the reciprocals.

The index type is arbitrary and discrete, including the empty type. No ultrametric hypothesis
is needed. These criteria distinguish dense diagonal inclusions of coefficient spaces from
isomorphisms.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, §10.
-/

public noncomputable section

open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction

namespace ZeroAtInftyContinuousMap

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I]

section NormedDivisionRing

variable [NormedDivisionRing K] (d : I →ᵇ K)

/-- A diagonal operator is injective exactly when every entry is nonzero. -/
theorem injective_diagonalCLM_iff : Function.Injective (diagonalCLM d) ↔ ∀ i, d i ≠ 0 := by
  classical
  constructor
  · intro h i hi
    have hz : diagonalCLM d (single i 1) = 0 := by simp [hi]
    have := congrArg (fun x : C₀(I, K) ↦ x i) (h (hz.trans (map_zero _).symm))
    simp at this
  · intro hd x y h
    ext i
    exact mul_right_cancel₀ (hd i) (by simpa using congrArg (fun x : C₀(I, K) ↦ x i) h)

/-- A diagonal operator has dense range exactly when every entry is nonzero. -/
theorem denseRange_diagonalCLM_iff : DenseRange (diagonalCLM d) ↔ ∀ i, d i ≠ 0 := by
  classical
  constructor
  · intro h i hi
    have hc : Continuous (fun x : C₀(I, K) ↦ x i) :=
      (evalCLM (β := K) K i).continuous.congr (fun x ↦ evalCLM_apply K i x)
    have hz : (single i 1 : C₀(I, K)) i = 0 :=
      h.induction_on (single i 1) (isClosed_eq hc continuous_const) (by simp [hi])
    simp at hz
  · intro hd
    have hs : Submodule.span K (Set.range fun i : I ↦ (single i 1 : C₀(I, K))) ≤
        (diagonalCLM d).range := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨single i (d i)⁻¹, by simp [hd i]⟩
    exact dense_span_single_one.mono hs

/-- Membership in the range of a nonvanishing diagonal means that dividing the coordinates
by its entries still gives a null family. -/
theorem mem_range_diagonalCLM_iff (hd : ∀ i, d i ≠ 0) (y : C₀(I, K)) :
    y ∈ (diagonalCLM d).range ↔
      Tendsto (fun i ↦ y i / d i) cofinite (𝓝 0) := by
  constructor
  · rintro ⟨x, rfl⟩
    simpa [hd] using x.tendsto_cofinite
  · intro hy
    exact ⟨mkOfDiscrete _ hy, by ext i; simp [hd]⟩

/-- A nonvanishing bounded diagonal with bounded reciprocal defines a continuous linear
automorphism of `c₀`. -/
def diagonalEquiv (hd : ∀ i, d i ≠ 0) (hb : BddAbove (Set.range fun i ↦ ‖(d i)⁻¹‖)) :
    C₀(I, K) ≃L[K] C₀(I, K) := by
  let e : I →ᵇ K := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i ↦ (d i)⁻¹) (Classical.choose hb) (fun i ↦ Classical.choose_spec hb ⟨i, rfl⟩)
  exact
    { diagonalCLM d with
      invFun := diagonalCLM e
      left_inv x := by ext i; simp [e, hd]
      right_inv x := by ext i; simp [e, hd]
      continuous_toFun := (diagonalCLM d).continuous
      continuous_invFun := (diagonalCLM e).continuous }

/-- The diagonal equivalence has the original diagonal as its forward operator. -/
@[simp]
theorem diagonalEquiv_toContinuousLinearMap (hd : ∀ i, d i ≠ 0)
    (hb : BddAbove (Set.range fun i ↦ ‖(d i)⁻¹‖)) :
    (diagonalEquiv d hd hb : C₀(I, K) →L[K] C₀(I, K)) = diagonalCLM d := (rfl)

/-- The diagonal equivalence multiplies each coordinate by the diagonal entry. -/
@[simp]
theorem diagonalEquiv_apply (hd : ∀ i, d i ≠ 0)
    (hb : BddAbove (Set.range fun i ↦ ‖(d i)⁻¹‖)) (x : C₀(I, K)) (i : I) :
    diagonalEquiv d hd hb x i = x i * d i := by
  rw [← ContinuousLinearEquiv.coe_coe, diagonalEquiv_toContinuousLinearMap, diagonalCLM_apply]

/-- The inverse diagonal equivalence divides each coordinate by the diagonal entry. -/
@[simp]
theorem diagonalEquiv_symm_apply (hd : ∀ i, d i ≠ 0)
    (hb : BddAbove (Set.range fun i ↦ ‖(d i)⁻¹‖)) (y : C₀(I, K)) (i : I) :
    (diagonalEquiv d hd hb).symm y i = y i / d i := by
  have h := congrArg (fun x : C₀(I, K) ↦ x i)
    ((diagonalEquiv d hd hb).apply_symm_apply y)
  rw [← ContinuousLinearEquiv.coe_coe, diagonalEquiv_toContinuousLinearMap,
    diagonalCLM_apply] at h
  exact (eq_div_iff (hd i)).2 h

/-- A diagonal is invertible as a continuous endomorphism exactly when its entries are nonzero
and their reciprocals are bounded. No completeness hypothesis is required. -/
theorem isUnit_diagonalCLM_iff :
    IsUnit (diagonalCLM d) ↔
      (∀ i, d i ≠ 0) ∧ BddAbove (Set.range fun i ↦ ‖(d i)⁻¹‖) := by
  classical
  constructor
  · rintro ⟨u, hu⟩
    let e := ContinuousLinearEquiv.ofUnit u
    have he : (e : C₀(I, K) →L[K] C₀(I, K)) = diagonalCLM d := hu
    have hd := (injective_diagonalCLM_iff d).1 (he ▸ e.injective)
    obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp
      (e.symm.continuous.continuousAt (x := 0)) 1 zero_lt_one
    have hlower (i : I) : δ ≤ ‖d i‖ := by
      by_contra! hi
      have hsingle : e (single i 1) = single i (d i) := by
        rw [← ContinuousLinearEquiv.coe_coe, he, diagonalCLM_single, one_mul]
      have h := hsmall (x := single i (d i)) (by simpa using hi)
      rw [← hsingle, e.symm_apply_apply] at h
      simp at h
    refine ⟨hd, ⟨δ⁻¹, ?_⟩⟩
    rintro _ ⟨i, rfl⟩
    simpa [norm_inv, one_div] using one_div_le_one_div_of_le hδ (hlower i)
  · rintro ⟨hd, hb⟩
    exact ⟨(diagonalEquiv d hd hb).toUnit, rfl⟩

end NormedDivisionRing

end ZeroAtInftyContinuousMap
