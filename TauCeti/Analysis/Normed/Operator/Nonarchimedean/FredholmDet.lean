/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.CharPowerSeries
public import TauCeti.RingTheory.PowerSeries.Entire.Eval

/-!
# The Fredholm determinant of a row-compact operator

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1`, and `I` a discrete
index type. For an endomorphism `u` of the model space `C₀(I, R)`, the Fredholm series
`H_u(T) = det (1 - T u)` is the principal-minor series `u.matrixCoeff.charPowerSeries` of its
matrix, and the **Fredholm determinant** `det (1 - u)` is its value `H_u(1)` at `T = 1`
(`ContinuousLinearMap.fredholmDet`). For row-compact `u` the series is entire, so this value is
a genuine convergent sum, and the value of `H_u` at any scalar `a` is the Fredholm determinant
of `a • u` (`ContinuousLinearMap.IsRowCompact.fredholmDet_smul`).

The main result is the multiplicativity of the Fredholm determinant over ultrametric Tate
scalars: for row-compact `u` and `v`, which need not commute,

`det (1 - (u + v - u v)) = det (1 - u) det (1 - v)`
(`ContinuousLinearMap.IsRowCompact.fredholmDet_add_sub_mul`),

since `1 - (u + v - u v) = (1 - u) (1 - v)`. The proof truncates `u` and `v` to a finite set `S`
of output coordinates. The truncated identity is the finite determinant identity
`det ((1 - A) (1 - B)) = det (1 - A) det (1 - B)` for the blocks of `u` and `v` on `S`
(`ContinuousLinearMap.fredholmDet_indicatorCLM_comp`). The truncations converge in operator norm
and share a null row majorant, so their Fredholm determinants converge
(`ContinuousLinearMap.tendsto_fredholmDet_of_tendsto`).

Consequently, if `1 - a • u` is invertible in the algebra of continuous endomorphisms then
`H_u(a)` is a unit of `R`
(`ContinuousLinearMap.IsRowCompact.isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul`): the
inverse is `1 - w` for a row-compact `w`, and `det (1 - a u) det (1 - w) = det 1 = 1`. Over
coefficient rings with nilpotents this is a statement about units, not only about nonvanishing.

## Main definitions

* `ContinuousLinearMap.fredholmDet`: the Fredholm determinant `det (1 - u) = H_u(1)`.

## Main results

* `ContinuousLinearMap.fredholmDet_eq_det`: on a finite index type, `det (1 - u)` is the
  determinant of `1` minus the matrix of `u`.
* `ContinuousLinearMap.tendsto_fredholmDet_of_tendsto`: continuity of the Fredholm determinant
  in operator norm along families with a common null row majorant.
* `ContinuousLinearMap.IsRowCompact.fredholmDet_add_sub_mul`: multiplicativity.
* `ContinuousLinearMap.IsRowCompact.isUnit_fredholmDet_of_isUnit_one_sub` and
  `ContinuousLinearMap.IsRowCompact.isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul`: an
  invertible `1 - a • u` has a unit Fredholm determinant.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5–6.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

section Defs

variable [NormedCommRing R]

/-- The **Fredholm determinant** `det (1 - u)` of an endomorphism `u` of the model space
`C₀(I, R)`: the value at `T = 1` of its Fredholm series `det (1 - T u)`, the principal-minor
series of its matrix. When `u` is row compact over a complete ultrametric ring with `‖1‖ = 1`
the series is entire (`Matrix.isRestricted_charPowerSeries`), so this value is a convergent
sum. -/
noncomputable def fredholmDet (u : C₀(I, R) →L[R] C₀(I, R)) : R :=
  u.matrixCoeff.charPowerSeries.evalAt (1 : R)

theorem fredholmDet_def (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.fredholmDet = u.matrixCoeff.charPowerSeries.evalAt (1 : R) :=
  (rfl)

/-- The Fredholm determinant of the zero operator is `det 1 = 1`. -/
@[simp]
theorem fredholmDet_zero : (0 : C₀(I, R) →L[R] C₀(I, R)).fredholmDet = 1 := by
  simp [fredholmDet_def]

/-- **Finite matrix comparison.** On a finite index type, the Fredholm determinant is the
determinant of `1` minus the matrix. -/
theorem fredholmDet_eq_det [Fintype I] (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.fredholmDet = (1 - u.matrixCoeff).det := by
  rw [fredholmDet_def, Matrix.charPowerSeries_eq_charpolyRev, PowerSeries.evalAt_coe,
    Polynomial.coe_aeval_eq_eval, Matrix.eval_one_charpolyRev]

/-- The Fredholm determinant of the output truncation `π_S ∘ u` to a finite set `S` is
`det (1 - A)` for the finite block `A` of the matrix of `u` on `S`. -/
theorem fredholmDet_indicatorCLM_comp (S : Finset I) (u : C₀(I, R) →L[R] C₀(I, R)) :
    ((indicatorCLM R (S : Set I)).comp u).fredholmDet =
      (1 - u.matrixCoeff.submatrix (Subtype.val : S → I) Subtype.val).det := by
  rw [fredholmDet_def, charPowerSeries_matrixCoeff_indicatorCLM_comp, PowerSeries.evalAt_coe,
    Polynomial.coe_aeval_eq_eval, Matrix.eval_one_charpolyRev]

end Defs

variable [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

/-- **The Fredholm series at a scalar.** For row-compact `u` and any `a : R`, the value
`H_u(a)` of the Fredholm series of `u` is the Fredholm determinant of `a • u`. -/
theorem IsRowCompact.fredholmDet_smul {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (a : R) : (a • u).fredholmDet = u.matrixCoeff.charPowerSeries.evalAt a := by
  rw [fredholmDet_def, matrixCoeff_smul, Matrix.charPowerSeries_smul a fun n ↦
    Matrix.summable_principalMinor hu.norm_matrixCoeff_le_rowNorm hu.tendsto_rowNorm n,
    PowerSeries.evalAt_rescale, smul_eq_mul, mul_one]

variable [TauCeti.NormedRing.IsTate R]

/-- **Continuity of the Fredholm determinant.** If endomorphisms `w a` of `C₀(I, R)` converge
in operator norm to `w₀`, and all of them have entries bounded by a common null row majorant
`r`, then their Fredholm determinants converge to that of `w₀`. -/
theorem tendsto_fredholmDet_of_tendsto {α : Type*} {l : Filter α}
    {w : α → C₀(I, R) →L[R] C₀(I, R)} {w₀ : C₀(I, R) →L[R] C₀(I, R)} {r : I → ℝ}
    (hr : Tendsto r cofinite (𝓝 0)) (hw : ∀ a i j, ‖(w a).matrixCoeff i j‖ ≤ r i)
    (hw₀ : ∀ i j, ‖w₀.matrixCoeff i j‖ ≤ r i) (h : Tendsto (fun a ↦ ‖w a - w₀‖) l (𝓝 0)) :
    Tendsto (fun a ↦ (w a).fredholmDet) l (𝓝 w₀.fredholmDet) := by
  have hG :=
    TauCeti.tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendsto_ringOpNorm_of_le
      hr hw hw₀ h one_pos
  have hent₀ : w₀.matrixCoeff.charPowerSeries.IsEntire :=
    PowerSeries.isEntire_iff.2 (Matrix.isRestricted_charPowerSeries hw₀ hr)
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ ↦ norm_nonneg _) (fun a ↦ ?_) hG)
  have hent : (w a).matrixCoeff.charPowerSeries.IsEntire :=
    PowerSeries.isEntire_iff.2 (Matrix.isRestricted_charPowerSeries (hw a) hr)
  rw [fredholmDet_def, fredholmDet_def, ← hent.evalAt_sub hent₀]
  exact PowerSeries.norm_evalAt_le_gaussNorm
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted ((hent.sub hent₀).isRestricted 1)) (by simp)

omit [NormOneClass R] [CompleteSpace R] in
/-- The entries of `u + v - u x` in row `i` are bounded by
`max (max (rᵢ(u)) (rᵢ(v))) (rᵢ(u) ‖v‖)` whenever the entries of `x` are bounded by `‖v‖`. -/
private theorem norm_matrixCoeff_add_sub_mul_le (u v x : C₀(I, R) →L[R] C₀(I, R))
    (hx : ∀ k j, ‖x.matrixCoeff k j‖ ≤ ‖v‖) (i j : I) :
    ‖(u + v - u * x).matrixCoeff i j‖ ≤
      max (max (u.rowNorm i) (v.rowNorm i)) (u.rowNorm i * ‖v‖) := by
  rw [matrixCoeff_sub, matrixCoeff_add, Matrix.sub_apply, Matrix.add_apply, matrixCoeff_mul,
    sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
      (u.norm_matrixCoeff_le_rowNorm i j) (v.norm_matrixCoeff_le_rowNorm i j))) ?_)
  rw [norm_neg]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (u.rowNorm_nonneg i) (ringOpNorm_nonneg v)) fun k ↦ ?_
  exact (norm_mul_le _ _).trans (mul_le_mul (u.norm_matrixCoeff_le_rowNorm i k) (hx k j)
    (norm_nonneg _) (u.rowNorm_nonneg i))

omit [DecidableEq I] [NormOneClass R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R] in
/-- The output truncation of `u + v - u v` built from the truncations `u_S = π_S ∘ u` and
`v_S = π_S ∘ v` is `π_S ∘ (u + v - u v_S)`. -/
private theorem indicatorCLM_comp_add_sub_mul (S : Set I) (u v : C₀(I, R) →L[R] C₀(I, R)) :
    (indicatorCLM R S).comp u + (indicatorCLM R S).comp v -
        (indicatorCLM R S).comp u * (indicatorCLM R S).comp v =
      (indicatorCLM R S).comp (u + v - u * (indicatorCLM R S).comp v) := by
  simp [mul_def, comp_add, comp_sub, comp_assoc]

omit [NormOneClass R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R] in
/-- **Multiplicativity for output truncations.** For a finite set `S`, the identity
`det (1 - (u_S + v_S - u_S v_S)) = det (1 - u_S) det (1 - v_S)` for `u_S = π_S ∘ u` and
`v_S = π_S ∘ v` is the finite identity `det ((1 - A) (1 - B)) = det (1 - A) det (1 - B)` for the
blocks `A`, `B` of `u`, `v` on `S`. -/
private theorem fredholmDet_indicatorCLM_comp_add_sub_mul (S : Finset I)
    (u v : C₀(I, R) →L[R] C₀(I, R)) :
    ((indicatorCLM R (S : Set I)).comp u + (indicatorCLM R (S : Set I)).comp v -
        (indicatorCLM R (S : Set I)).comp u * (indicatorCLM R (S : Set I)).comp v).fredholmDet =
      ((indicatorCLM R (S : Set I)).comp u).fredholmDet *
        ((indicatorCLM R (S : Set I)).comp v).fredholmDet := by
  let A := u.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I)
  let B := v.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I)
  -- The block of `u (π_S ∘ v)` on `S` is `A B`, since the rows of `π_S ∘ v` outside `S` vanish.
  have hsub : (u + v - u * (indicatorCLM R (S : Set I)).comp v).matrixCoeff.submatrix
      (Subtype.val : S → I) Subtype.val = A + B - A * B := by
    ext i j
    rw [Matrix.submatrix_apply, matrixCoeff_sub, Matrix.sub_apply, matrixCoeff_mul,
      tsum_eq_sum (s := S) fun k hk ↦ by simp [hk], ← Finset.sum_coe_sort S]
    simp [A, B, Matrix.mul_apply]
  rw [indicatorCLM_comp_add_sub_mul, fredholmDet_indicatorCLM_comp, fredholmDet_indicatorCLM_comp,
    fredholmDet_indicatorCLM_comp, ← Matrix.det_mul, hsub]
  congr 1
  noncomm_ring

/-- **Multiplicativity of the Fredholm determinant.** For row-compact endomorphisms `u` and `v`
of `C₀(I, R)`, which need not commute,
`det (1 - (u + v - u v)) = det (1 - u) det (1 - v)`, reflecting
`1 - (u + v - u v) = (1 - u) (1 - v)`. -/
theorem IsRowCompact.fredholmDet_add_sub_mul {u v : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (hv : v.IsRowCompact) :
    (u + v - u * v).fredholmDet = u.fredholmDet * v.fredholmDet := by
  let P : Finset I → C₀(I, R) →L[R] C₀(I, R) := fun S ↦ indicatorCLM R (S : Set I)
  have hP (S : Finset I) (x : C₀(I, R) →L[R] C₀(I, R)) (i j : I) :
      ‖((P S).comp x).matrixCoeff i j‖ ≤ ‖x.matrixCoeff i j‖ := by
    by_cases hi : i ∈ S <;> simp [P, hi]
  have htrunc {x : C₀(I, R) →L[R] C₀(I, R)} (hx : x.IsRowCompact) :
      Tendsto (fun S ↦ ‖(P S).comp x - x‖) atTop (𝓝 0) :=
    hx.tendsto_ringOpNorm_indicatorCLM_comp_sub
  have htend {x : C₀(I, R) →L[R] C₀(I, R)} (hx : x.IsRowCompact) :
      Tendsto (fun S ↦ ((P S).comp x).fredholmDet) atTop (𝓝 x.fredholmDet) :=
    tendsto_fredholmDet_of_tendsto hx.tendsto_rowNorm (fun S i j ↦ (hP S x i j).trans
      (x.norm_matrixCoeff_le_rowNorm i j)) x.norm_matrixCoeff_le_rowNorm (htrunc hx)
  -- The truncations of `u + v - u v` share the null row majorant `r`, by the ultrametric
  -- inequality and `‖(u x)ᵢⱼ‖ ≤ rᵢ(u) ‖v‖` whenever the entries of `x` are bounded by `‖v‖`.
  let r : I → ℝ := fun i ↦ max (max (u.rowNorm i) (v.rowNorm i)) (u.rowNorm i * ‖v‖)
  have hr : Tendsto r cofinite (𝓝 0) := by
    simpa [r] using (hu.tendsto_rowNorm.max hv.tendsto_rowNorm).max
      (hu.tendsto_rowNorm.mul_const ‖v‖)
  have hdet := tendsto_fredholmDet_of_tendsto hr (fun (S : Finset I) i j ↦ ?_)
    (norm_matrixCoeff_add_sub_mul_le u v v v.norm_matrixCoeff_le)
    (by
      -- The scoped operator ring is named explicitly: its continuity instances are not found on
      -- `C₀(I, R) →L[R] C₀(I, R)` without it.
      let := (TauCeti.RingOpNorm.seminormedRing : SeminormedRing (C₀(I, R) →L[R] C₀(I, R)))
      have hu' := tendsto_iff_norm_sub_tendsto_zero.2 (htrunc hu)
      have hv' := tendsto_iff_norm_sub_tendsto_zero.2 (htrunc hv)
      exact tendsto_iff_norm_sub_tendsto_zero.1 ((hu'.add hv').sub (hu'.mul hv')))
  · exact tendsto_nhds_unique (hdet.congr (fredholmDet_indicatorCLM_comp_add_sub_mul · u v))
      ((htend hu).mul (htend hv))
  · rw [indicatorCLM_comp_add_sub_mul]
    exact (hP S _ i j).trans (norm_matrixCoeff_add_sub_mul_le u v _
      (fun k j ↦ (hP S v k j).trans (v.norm_matrixCoeff_le k j)) i j)

/-- If `1 - u` is invertible in the algebra of continuous endomorphisms of `C₀(I, R)` for a
row-compact `u`, the Fredholm determinant `det (1 - u)` is a unit of `R`. -/
theorem IsRowCompact.isUnit_fredholmDet_of_isUnit_one_sub {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (h : IsUnit (1 - u)) : IsUnit u.fredholmDet := by
  obtain ⟨g, hg⟩ := h
  let w : C₀(I, R) →L[R] C₀(I, R) := -(↑g⁻¹ * u)
  have hw : w.IsRowCompact := (hu.clm_comp (↑g⁻¹ : C₀(I, R) →L[R] C₀(I, R))).neg
  -- `u + w - u w = u - (1 - u) g⁻¹ u = 0`. The identity is stated in an arbitrary ring because on
  -- `C₀(I, R)` the operator subtraction only unfolds to the ring subtraction at default
  -- transparency, which `noncomm_ring` and `rw` do not use.
  have key {A : Type _} [Ring A] (a x : A) (h : (1 - a) * x = a) : a + -x - a * -x = 0 := calc
    a + -x - a * -x = a - (1 - a) * x := by noncomm_ring
    _ = 0 := by rw [h, sub_self]
  have hzero : u + w - u * w = 0 :=
    key u _ (by rw [← mul_assoc, ← hg, Units.mul_inv, one_mul])
  have := hu.fredholmDet_add_sub_mul hw
  rw [hzero, fredholmDet_zero] at this
  exact IsUnit.of_mul_eq_one _ this.symm

/-- **Invertibility forces a unit determinant.** If `u` is row compact and `1 - a • u` is
invertible in the algebra of continuous endomorphisms of `C₀(I, R)`, then the value `H_u(a)` of
the Fredholm series of `u` is a unit of `R`. -/
theorem IsRowCompact.isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {a : R} (h : IsUnit (1 - a • u)) :
    IsUnit (u.matrixCoeff.charPowerSeries.evalAt a) :=
  hu.fredholmDet_smul a ▸ (hu.smul a).isUnit_fredholmDet_of_isUnit_one_sub h

end ContinuousLinearMap
