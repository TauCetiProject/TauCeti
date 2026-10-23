/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.RingTheory.Norm.Quadratic

/-!
# Trace transfer in a quadratic algebra

If `x` generates a degree-two algebra over a field and `x² = d`, the basis `(1, x)`
identifies the trace transfer of the unit line with `⟨2, 2d⟩`. This supplies the
general degree-two version of the trace-form calculation, with an explicit isometry
whose coordinates can be used to compute invariants of transferred forms.

The trace of `x` vanishes by `Algebra.IsQuadraticExtension.trace_eq_zero_of_sq_eq`, which
also covers split and nonreduced algebras.

For a quadratic field extension the file also diagonalizes the twisted trace forms
`Tr_*⟨a⟩ : y ↦ Tr (a y²)`, the transfers of the rank-one forms `⟨a⟩` that Kahn's formula for the
Stiefel–Whitney classes of a transferred form evaluates. There are two cases.

* If `Tr a ≠ 0`, **Kahn's basis** `(1, x / a)` is orthogonal, and
  `Tr_*⟨a⟩ ≅ ⟨Tr a, d · Tr a / N a⟩`
  (`equivalent_traceTransfer_smul_sq_weightedSumSquares_of_sq`).
* If `Tr a = 0` and `a ≠ 0`, then `1` and `a⁻¹` are isotropic and `Tr_*⟨a⟩` is the hyperbolic
  plane (`equivalent_traceTransfer_smul_sq_hyperbolicPlane`).

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. 78 (1984), 223–256.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

/-- In square-root coordinates, the trace transfer of the unit line is `⟨2, 2d⟩`. -/
theorem traceTransfer_sq_basisRepr {x : L} {d : K}
    (hfin : Module.finrank K L = 2) (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L d) :
    ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).basisRepr
      (quadraticExtensionBasis K L hx hfin) =
      weightedSumSquares K ![(2 : K), 2 * d] := by
  have : Algebra.IsQuadraticExtension K L := ⟨hfin⟩
  have htrace := Algebra.IsQuadraticExtension.trace_eq_zero_of_sq_eq hx hx2
  ext v
  rw [QuadraticMap.basisRepr, QuadraticMap.comp_apply,
    QuadraticMap.traceTransfer_sq, LinearMap.BilinMap.toQuadraticMap_apply,
    Algebra.traceForm_apply]
  simp only [LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    Fin.sum_univ_two, quadraticExtensionBasis_zero, quadraticExtensionBasis_one,
    Algebra.smul_def]
  have hpoly :
      ((algebraMap K L) (v 0) * 1 + (algebraMap K L) (v 1) * x) *
          ((algebraMap K L) (v 0) * 1 + (algebraMap K L) (v 1) * x) =
        (algebraMap K L) ((v 0) ^ 2 + d * (v 1) ^ 2) +
          (algebraMap K L) (2 * (v 0) * (v 1)) * x := by
    simp only [map_add, map_pow, map_mul]
    calc
      _ = (algebraMap K L) (v 0) ^ 2 +
            (algebraMap K L) (v 1) ^ 2 * x ^ 2 +
            (algebraMap K L) (2 * v 0 * v 1) * x := by
          simp only [map_mul, map_ofNat]
          ring
      _ = _ := by rw [hx2]; simp only [map_mul]; ring
  have hcross :
      (Algebra.trace K L) ((algebraMap K L) (2 * v 0 * v 1) * x) = 0 := by
    rw [← Algebra.smul_def, map_smul, htrace, smul_zero]
  rw [hpoly, map_add, Algebra.trace_algebraMap, hfin]
  rw [hcross]
  simp [weightedSumSquares_apply, Fin.sum_univ_two, nsmul_eq_mul]
  ring

/-- The square-root coordinate map is an isometry from the transferred unit line
to the diagonal form `⟨2, 2d⟩`. -/
noncomputable def traceTransferSqIsometryEquivWeightedSumSquaresOfSq
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) :
    ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).IsometryEquiv
      (weightedSumSquares K ![(2 : K), 2 * d]) := by
  let b := quadraticExtensionBasis K L hx hfin
  let e := ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).isometryEquivBasisRepr b
  refine { e with map_app' := fun z => ?_ }
  rw [← traceTransfer_sq_basisRepr hfin hx hx2]
  exact e.map_app z

/-- The isometry's underlying linear equivalence is the coordinate equivalence
for the square-root basis. -/
private theorem traceTransferSqIsometryEquivWeightedSumSquaresOfSq_toLinearEquiv
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) :
    (traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2).toLinearEquiv =
      (quadraticExtensionBasis K L hx hfin).equivFun := by
  rfl

/-- The isometry uses coordinates in the square-root basis. -/
@[simp]
theorem traceTransferSqIsometryEquivWeightedSumSquaresOfSq_apply
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d)
    (z : L) :
    traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2 z =
      (quadraticExtensionBasis K L hx hfin).equivFun z := by
  simpa only [IsometryEquiv.coe_toLinearEquiv] using
    LinearEquiv.congr_fun
      (traceTransferSqIsometryEquivWeightedSumSquaresOfSq_toLinearEquiv hfin hx hx2) z

/-- The inverse isometry reconstructs an element from its square-root coordinates. -/
@[simp]
theorem traceTransferSqIsometryEquivWeightedSumSquaresOfSq_symm_apply
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d)
    (v : Fin 2 → K) :
    (traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2).symm v =
      (quadraticExtensionBasis K L hx hfin).equivFun.symm v := by
  simpa only [IsometryEquiv.coe_symm_toLinearEquiv, IsometryEquiv.coe_toLinearEquiv] using
    LinearEquiv.congr_fun
      (congrArg LinearEquiv.symm
        (traceTransferSqIsometryEquivWeightedSumSquaresOfSq_toLinearEquiv hfin hx hx2)) v

/-- The trace transfer of the unit line in a degree-two algebra generated by
`x² = d` is equivalent to `⟨2, 2d⟩`. -/
theorem equivalent_traceTransfer_sq_weightedSumSquares_of_sq
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) :
    ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Equivalent
      (weightedSumSquares K ![(2 : K), 2 * d]) :=
  ⟨traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2⟩

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Kahn's basis.** Let `x ∉ K` generate a quadratic extension `L/K` with `x² = d`, and let
`a : L` have nonzero trace. Then `1` and `x / a` are orthogonal for the twisted trace form
`Tr_*⟨a⟩ : y ↦ Tr (a y²)`, with values `Tr a` and `Tr (d / a) = d · Tr a / N a`, so
`Tr_*⟨a⟩ ≅ ⟨Tr a, d · Tr a / N a⟩`.

The hypothesis `Tr a ≠ 0` cannot be dropped: at `Tr a = 0` both entries vanish, while for
`a ≠ 0` the form is the hyperbolic plane (`equivalent_traceTransfer_smul_sq_hyperbolicPlane`). -/
theorem equivalent_traceTransfer_smul_sq_weightedSumSquares_of_sq [Invertible (2 : K)]
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) {a : L}
    (htr : Algebra.trace K L a ≠ 0) :
    ((a • QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Equivalent
      (weightedSumSquares K
        ![Algebra.trace K L a, d * Algebra.trace K L a / Algebra.norm K a]) := by
  have : Algebra.IsQuadraticExtension K L := ⟨hfin⟩
  have hx0 := Algebra.IsQuadraticExtension.trace_eq_zero_of_sq_eq hx hx2
  have ha : a ≠ 0 := by
    rintro rfl
    simp at htr
  set Q := (a • QuadraticMap.sq (R := L) (A := L)).traceTransfer K
  have hQ (z : L) : Q z = Algebra.trace K L (a * (z * z)) := by
    simp [Q]
  -- `x / a ∉ K`: otherwise `x ∈ K a`, and `Tr x = 0` would force `Tr a = 0`.
  have hy : x / a ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    have hxc : x = algebraMap K L c * a := by
      rw [hc]
      field_simp
    have hc0 : c * Algebra.trace K L a = 0 := by
      rw [← hx0, hxc, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rcases mul_eq_zero.mp hc0 with rfl | h
    · exact hx ⟨0, by simp [hxc]⟩
    · exact htr h
  let b := quadraticExtensionBasis K L hy hfin
  have hpolar : QuadraticMap.polar Q 1 (x / a) = 0 := by
    have h2x : a * ((1 + x / a) * (1 + x / a)) - a * (1 * 1) - a * (x / a * (x / a)) =
        (2 : K) • x := by
      rw [Algebra.smul_def, map_ofNat]
      field_simp
      ring
    rw [QuadraticMap.polar, hQ, hQ, hQ, ← map_sub, ← map_sub, h2x, map_smul, hx0, smul_zero]
  have horth : (associated Q).IsOrthoᵢ b := by
    intro i j hij
    rw [Function.onFun, QuadraticMap.associated_isOrtho,
      ← QuadraticMap.isOrtho_polarBilin]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [b] using hpolar
    · simpa [b, QuadraticMap.polar_comm] using hpolar
    · exact absurd rfl hij
  have hval : (fun i => Q (b i)) =
      ![Algebra.trace K L a, d * Algebra.trace K L a / Algebra.norm K a] := by
    have hinv : a * (x / a * (x / a)) = d • a⁻¹ := by
      rw [Algebra.smul_def, ← hx2]
      field_simp
    ext i
    fin_cases i
    · simp [b, hQ]
    · simp only [b, Fin.mk_one, quadraticExtensionBasis_one, hQ, hinv, map_smul,
        Algebra.IsQuadraticExtension.trace_inv, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      ring
  rw [← hval, ← QuadraticMap.basisRepr_eq_of_iIsOrtho Q b horth]
  exact ⟨Q.isometryEquivBasisRepr b⟩

/-- **The twisted trace form at trace zero.** If `L/K` is a quadratic extension and `a ≠ 0` has
trace zero, then `Tr_*⟨a⟩ : y ↦ Tr (a y²)` is the hyperbolic plane. Indeed `1` and `a⁻¹` are
isotropic, as `Tr (a⁻¹) = Tr a / N a = 0`, and their polar pairing is `2 Tr 1 = 4`. -/
theorem equivalent_traceTransfer_smul_sq_hyperbolicPlane [Invertible (2 : K)]
    (hfin : Module.finrank K L = 2) {a : L} (ha : a ≠ 0) (htr : Algebra.trace K L a = 0) :
    ((a • QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Equivalent
      (hyperbolicPlane K) := by
  have : Algebra.IsQuadraticExtension K L := ⟨hfin⟩
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ hfin
  have h4 : (4 : K) ≠ 0 := by
    convert mul_self_ne_zero.mpr (two_ne_zero' K) using 1
    norm_num
  set Q := (a • QuadraticMap.sq (R := L) (A := L)).traceTransfer K
  have hQ (z : L) : Q z = Algebra.trace K L (a * (z * z)) := by
    simp [Q]
  set c : K := (4 : K)⁻¹ with hc
  set y : L := algebraMap K L c * a⁻¹
  have h1 : Q 1 = 0 := by simp [hQ, htr]
  have hyQ : Q y = 0 := by
    have : a * (y * y) = algebraMap K L (c * c) * a⁻¹ := by
      rw [map_mul]
      simp only [y]
      field_simp
    rw [hQ, this, ← Algebra.smul_def, map_smul, Algebra.IsQuadraticExtension.trace_inv, htr,
      zero_div, smul_zero]
  have hpolar : QuadraticMap.polar Q 1 y = 1 := by
    have : a * ((1 + y) * (1 + y)) - a * (1 * 1) - a * (y * y) = algebraMap K L (2 * c) := by
      rw [map_mul, map_ofNat]
      simp only [y]
      field_simp
      ring
    rw [QuadraticMap.polar, hQ, hQ, hQ, ← map_sub, ← map_sub, this, Algebra.trace_algebraMap,
      hfin, nsmul_eq_mul, hc]
    field_simp
    norm_num
  -- `1` and `y` span `L`, since `y ∉ K`: otherwise `a = c / y ∈ K`, and `Tr a = 2 a ≠ 0`.
  have hy : y ∉ Set.range (algebraMap K L) := by
    rintro ⟨e, he⟩
    have hac : a = algebraMap K L (c / e) := by
      have hy0 : y ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero h4)) (inv_ne_zero ha)
      rw [map_div₀, he]
      field_simp
      simp only [y]
      field_simp
    have hce : c / e ≠ 0 := by
      rintro h
      exact ha (by rw [hac, h, map_zero])
    rw [hac, Algebra.trace_algebraMap, hfin, two_nsmul, ← two_mul] at htr
    exact hce ((mul_eq_zero.mp htr).resolve_left (two_ne_zero' K))
  have hspan : Submodule.span K {1, y} = ⊤ := by
    have hli := TauCeti.linearIndependent_one_of_notMem_range_algebraMap K L hy
    rw [← Matrix.range_cons_cons_empty,
      hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hfin])]
  exact QuadraticMap.Equivalent.trans
    ⟨{ toLinearEquiv := (LinearEquiv.ofTop _ hspan).symm, map_app' := fun _ => by simp }⟩
    (Q.equivalent_restrict_span_pair_hyperbolicPlane h1 hyQ hpolar)

end Field

end TauCeti
