/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import TauCeti.LinearAlgebra.Matrix.Determinant.ZeroRowSum
public import TauCeti.Logic.Equiv.Sum
public import TauCeti.NumberTheory.NumberField.SUnits.Lattice

/-!
# The S-regulator

Let `S` be a finite set of finite places of a number field `K`. A family `ε : ι → S.unit K` is a
fundamental system of `S`-units if, together with the torsion, it generates the `S`-units and it
has `NumberField.Units.rank K + #S` members. The imported lattice API identifies fundamental
systems with the families whose `S`-logarithmic images form a `ℤ`-basis of the `S`-unit lattice
`TauCeti.NumberField.SUnit.unitLattice S`.

The `S`-regulator is the covolume of the `S`-unit lattice. It is positive, and for any fundamental
system `ε` and any infinite place `w'` it is the absolute value of the determinant of the square
matrix of weighted logarithms of the `ε i` at the places of `S` and the infinite places other
than `w'`. The choice of `w'` does not matter because the product formula makes the rows of the
full matrix of weighted logarithms, over all places in `S` and at infinity, sum to zero. For
`S = ∅` the `S`-regulator is the regulator of `K`.

## Main definitions and results

* `TauCeti.NumberField.SUnit.regulator`: the `S`-regulator, with
  `TauCeti.NumberField.SUnit.regulator_pos` and `TauCeti.NumberField.SUnit.regulator_ne_zero`.
* `TauCeti.NumberField.SUnit.regulator_eq_abs_det`: the determinant formula for the
  `S`-regulator, the `S`-analogue of Mathlib's `NumberField.Units.regulator_eq_det`.
* `TauCeti.NumberField.SUnit.regulator_empty`: the `∅`-regulator is the regulator of `K`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.5 (the `S`-unit theorem 1.5.13).

The definitions and the determinant formula are modelled on Mathlib's regulator of a number field,
`NumberField.Units.regulator` and `NumberField.Units.regulator_eq_det` in
`Mathlib.NumberTheory.NumberField.Units.Regulator`, by Xavier Roblot.
-/

public section

open Finset IsDedekindDomain Module NumberField NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem TauCeti.SUnit

namespace TauCeti.NumberField.SUnit

noncomputable section

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-! ### The S-regulator -/

open Classical in
/-- The `S`-regulator is the covolume of the `S`-unit lattice. -/
def regulator : ℝ := ZLattice.covolume (unitLattice S)

open Classical in
/-- The defining covolume formula for the `S`-regulator. -/
theorem regulator_def : regulator S = ZLattice.covolume (unitLattice S) :=
  (rfl)

/-- The `S`-regulator is positive. -/
theorem regulator_pos : 0 < regulator S := by
  classical
  exact ZLattice.covolume_pos _ _

/-- The `S`-regulator is nonzero. -/
theorem regulator_ne_zero : regulator S ≠ 0 :=
  (regulator_pos S).ne'

/-! ### The determinant formula -/

variable {S}

/-- The full matrix of weighted logarithms of a family of `S`-units: the row of `ε i` lists
`mult w * log (w (ε i))` at the infinite places `w` and `log ‖ε i‖_v` at the places `v ∈ S`. -/
private def fullLogMatrix {ι : Type*} (ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    Matrix ι (InfinitePlace K ⊕ S) ℝ :=
  Matrix.of fun i ↦ Sum.elim (fun w ↦ (w.mult : ℝ) * Real.log (w ((ε i : Kˣ) : K)))
    (fun v ↦ Real.log (FinitePlace.mk v.1 ((ε i : Kˣ) : K)))

/-- The rows of the full matrix of weighted logarithms sum to zero: this is the product formula. -/
private theorem sum_fullLogMatrix {ι : Type*}
    (ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (i : ι) :
    ∑ j, fullLogMatrix ε i j = 0 := by
  rw [Fintype.sum_sum_type]
  exact sum_mult_mul_log_add_sum_log_finitePlace S (ε i)

/-- The square matrix of weighted logarithms of a family of `S`-units, without the column of the
infinite place `w'`: the row of `ε i` lists `mult w * log (w (ε i))` at the infinite places
`w ≠ w'` and `log ‖ε i‖_v` at the places `v ∈ S`, in the order given by `e`. -/
private def logMatrix {ι : Type*} (ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (w' : InfinitePlace K) (e : ι ≃ ({w // w ≠ w'} ⊕ S)) : Matrix ι ι ℝ :=
  Matrix.of fun i k ↦ Sum.elim (fun w : {w // w ≠ w'} ↦
    (w.1.mult : ℝ) * Real.log (w.1 ((ε i : Kˣ) : K)))
    (fun v : S ↦ Real.log (FinitePlace.mk v.1 ((ε i : Kˣ) : K))) (e k)

private theorem logMatrix_apply {ι : Type*} (ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (w' : InfinitePlace K) (e : ι ≃ ({w // w ≠ w'} ⊕ S)) (i k : ι) :
    logMatrix ε w' e i k = Sum.elim (fun w : {w // w ≠ w'} ↦
      (w.1.mult : ℝ) * Real.log (w.1 ((ε i : Kˣ) : K)))
      (fun v : S ↦ Real.log (FinitePlace.mk v.1 ((ε i : Kˣ) : K))) (e k) :=
  rfl

private theorem logMatrix_eq {ι : Type*} (ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (w' : InfinitePlace K) (e : ι ≃ ({w // w ≠ w'} ⊕ S)) :
    logMatrix ε w' e = Matrix.of fun i k ↦ Sum.elim (fun w : {w // w ≠ w'} ↦
      (w.1.mult : ℝ) * Real.log (w.1 ((ε i : Kˣ) : K)))
      (fun v : S ↦ Real.log (FinitePlace.mk v.1 ((ε i : Kˣ) : K))) (e k) :=
  rfl

/-- Deleting the column of the infinite place `w'` from the full matrix of weighted logarithms
gives the matrix of the determinant formula. -/
private theorem fullLogMatrix_submatrix {ι : Type*}
    (ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (w' : InfinitePlace K)
    (e : ι ≃ ({w // w ≠ w'} ⊕ S)) :
    (fullLogMatrix ε).submatrix id (fun k ↦ ((e.trans (Equiv.sumSubtypeNe w')) k :
      InfinitePlace K ⊕ S)) = logMatrix ε w' e := by
  ext i k
  rcases hk : e k with w | v <;> simp [fullLogMatrix, logMatrix_apply, hk]

/-- **The determinant formula for the `S`-regulator.** For a family `ε` of `S`-units that, together
with the torsion subgroup, generates the `S`-units, an infinite place `w'` and any identification
`e` of `ι` with the places of `S` and the infinite places other than `w'`, the `S`-regulator is the
absolute value of the determinant of the matrix whose `i`-th row lists `mult w * log (w (ε i))` at
the infinite places `w ≠ w'` and `log ‖ε i‖_v` at the places `v ∈ S`, in the order given by `e`.
The family `ε` is then a fundamental system, its cardinality being forced by `e`. This is the
`S`-analogue of Mathlib's `NumberField.Units.regulator_eq_det`. -/
theorem regulator_eq_abs_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K}
    (hε : Subgroup.closure (Set.range ε) ⊔
      CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) = ⊤)
    (w' : InfinitePlace K) (e : ι ≃ ({w // w ≠ w'} ⊕ S)) :
    regulator S = |(Matrix.of fun i k ↦ Sum.elim (fun w : {w // w ≠ w'} ↦
      (w.1.mult : ℝ) * Real.log (w.1 ((ε i : Kˣ) : K)))
      (fun v : S ↦ Real.log (FinitePlace.mk v.1 ((ε i : Kˣ) : K))) (e k)).det| := by
  classical
  -- The cardinality of `ι` is forced by `e`, so `ε` is a fundamental system.
  have hcard : Fintype.card ι = Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ S) := by
    simp [Fintype.card_congr e, Fintype.card_subtype_compl]
  have hε' : IsFundSystem (S : Set (HeightOneSpectrum (𝓞 K))) ε := by
    refine ⟨inferInstance, ?_, hε⟩
    have hc : Fintype.card ι = NumberField.Units.rank K + #S := by
      rw [hcard, ← Module.finrank_fintype_fun_eq_card ℝ, finrank_logSpace]
    simpa using hc
  -- First the case of the distinguished place `w₀`, from the basis `basisOfIsFundSystem hε'`.
  set e₀ := Fintype.equivOfCardEq hcard
  have h₀ : regulator S = |(logMatrix ε w₀ e₀).det| := by
    rw [regulator_def, ZLattice.covolume_eq_det _ ((basisOfIsFundSystem hε').reindex e₀),
      ← Matrix.det_submatrix_equiv_self e₀]
    congr 2
    ext i k
    rcases hk : e₀ k with w | v <;> simp [logMatrix_apply, hk]
  -- Then move the omitted place from `w₀` to `w'`.
  rw [← logMatrix_eq]
  rw [h₀, ← fullLogMatrix_submatrix, ← fullLogMatrix_submatrix]
  exact Matrix.abs_det_submatrix_eq_of_sum_eq_zero _ (sum_fullLogMatrix ε) _ _

/-- The `S`-regulator of the empty set of places is the regulator of `K`. -/
theorem regulator_empty : regulator (∅ : Finset (HeightOneSpectrum (𝓞 K))) =
    NumberField.Units.regulator K := by
  classical
  set T : Set (HeightOneSpectrum (𝓞 K)) :=
    ((∅ : Finset (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 K)))
  set ε : Fin (NumberField.Units.rank K) → T.unit K := fun i ↦
    unitOfUnits T K (NumberField.Units.fundSystem K i)
  -- The ordinary fundamental system generates the `∅`-units modulo torsion.
  have hε : Subgroup.closure (Set.range ε) ⊔ CommGroup.torsion (T.unit K) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨u, hu⟩ := Set.mem_unit_empty_iff (R := 𝓞 K) K |>.mp (by simpa [T] using x.2)
    have hx : unitOfUnits T K u = x := Subtype.ext (Units.ext (by rw [val_unitOfUnits, hu]))
    have hu' : u ∈ Subgroup.closure (Set.range (NumberField.Units.fundSystem K)) ⊔
        NumberField.Units.torsion K := by
      rw [NumberField.Units.closure_fundSystem_sup_torsion_eq_top]
      exact Subgroup.mem_top u
    rw [← hx]
    -- `NumberField.Units.torsion K` is by definition `CommGroup.torsion (𝓞 K)ˣ`.
    refine sup_le_sup (le_of_eq ?_) (CommGroup.map_torsion_le _)
      (Subgroup.map_sup _ _ (unitOfUnits T K) ▸ Subgroup.mem_map_of_mem _ hu')
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [regulator_eq_abs_det hε w₀
      ((NumberField.Units.equivFinRank K).trans (Equiv.sumEmpty _ _).symm),
    NumberField.Units.regulator_eq_det K w₀ (NumberField.Units.equivFinRank K).symm,
    ← Matrix.det_submatrix_equiv_self (NumberField.Units.equivFinRank K)]
  congr 2
  ext i k
  simp [ε]

end

end TauCeti.NumberField.SUnit
