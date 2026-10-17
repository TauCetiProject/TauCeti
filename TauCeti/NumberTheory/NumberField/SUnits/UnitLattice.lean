/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.NumberTheory.NumberField.SUnits.Height
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.NumberTheory.NumberField.Units.SUnit.Basic

/-!
# The S-unit lattice and the S-regulator

Let `S` be a finite set of finite places of a number field `K`. The image of the `S`-logarithmic
embedding `TauCeti.NumberField.SUnit.logEmbedding S` is the `S`-unit lattice
`TauCeti.NumberField.SUnit.unitLattice S`, a full `ℤ`-lattice in the `S`-logarithmic space
`({w : InfinitePlace K // w ≠ w₀} ⊕ S) → ℝ`, of rank `NumberField.Units.rank K + #S`. Its
covolume is the `S`-regulator `TauCeti.NumberField.SUnit.regulator S`. These are the
`S`-analogues of Mathlib's `NumberField.Units.unitLattice` and `NumberField.Units.regulator`.

The proof follows the shape of Mathlib's proof that `NumberField.Units.unitLattice` is a full
lattice in `Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`, with two changes.

* **Discreteness** comes from Northcott's property: an `S`-unit whose image has supremum norm at
  most `r` has logarithmic height at most `(rank K + #S) * r`
  (`TauCeti.NumberField.SUnit.logHeight₁_le_mul_norm_logEmbedding`), and a number field has only
  finitely many elements of bounded height.
* **Spanning** comes from the rank. The kernel of the embedding is the torsion subgroup
  (`TauCeti.NumberField.SUnit.logEmbedding_ker`), so the lattice is isomorphic to the `S`-units
  modulo torsion, whose rank `rank K + #S` is the `S`-unit theorem
  (`TauCeti.finrank_sUnits_numberField`). A discrete subgroup spans a real subspace of dimension
  equal to its rank (`Real.finrank_eq_int_finrank_of_discrete`), which here is the dimension of
  the whole space.

## Main definitions

* `TauCeti.NumberField.SUnit.unitLattice`: the image of the `S`-logarithmic embedding.
* `TauCeti.NumberField.SUnit.logEmbeddingEquiv`: the `ℤ`-linear equivalence between the
  `S`-units modulo torsion and the `S`-unit lattice.
* `TauCeti.NumberField.SUnit.regulator`: the covolume of the `S`-unit lattice.

## Main results

* `TauCeti.NumberField.SUnit.unitLattice_inter_ball_finite`: the lattice meets every ball in a
  finite set.
* `TauCeti.NumberField.SUnit.unitLattice_rank`: the lattice has rank `rank K + #S`.
* `TauCeti.NumberField.SUnit.unitLattice_span_eq_top`: the lattice spans the `S`-logarithmic
  space.
* `TauCeti.NumberField.SUnit.instIsZLatticeUnitLattice`: the lattice is a full `ℤ`-lattice.
* `TauCeti.NumberField.SUnit.regulator_def`: the `S`-regulator is the covolume of the lattice.
* `TauCeti.NumberField.SUnit.regulator_pos`: the `S`-regulator is positive.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.5 (the `S`-unit theorem 1.5.13).
-/

public noncomputable section

open Finset IsDedekindDomain Module NumberField NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The `S`-unit lattice: the image of the `S`-logarithmic embedding. -/
def unitLattice : Submodule ℤ (logSpace S) :=
  Submodule.map (logEmbedding S).toIntLinearMap ⊤

/-- The `S`-unit lattice is the range of the `S`-logarithmic embedding, viewed as a `ℤ`-linear
map. -/
theorem range_toIntLinearMap_logEmbedding :
    LinearMap.range (logEmbedding S).toIntLinearMap = unitLattice S :=
  LinearMap.range_eq_map _

variable {S} in
/-- A vector lies in the `S`-unit lattice exactly when it is the `S`-logarithmic embedding of an
`S`-unit. -/
theorem mem_unitLattice_iff {y : logSpace S} :
    y ∈ unitLattice S ↔
      ∃ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K, logEmbedding S (Additive.ofMul x) = y := by
  rw [← range_toIntLinearMap_logEmbedding, LinearMap.mem_range]
  exact Additive.ofMul.surjective.exists

/-- The `S`-logarithmic embedding of an `S`-unit lies in the `S`-unit lattice. -/
theorem logEmbedding_mem_unitLattice (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    logEmbedding S x ∈ unitLattice S :=
  Submodule.mem_map_of_mem trivial

/-! ### Discreteness -/

open Classical in
/-- The `S`-unit lattice meets every closed ball in a finite set. -/
theorem unitLattice_inter_ball_finite (r : ℝ) :
    ((unitLattice S : Set (logSpace S)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_ge r 0
  · simp [Metric.closedBall_eq_empty.mpr hr]
  set B : ℝ := (NumberField.Units.rank K + #S) * r
  have hfin : {x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K |
      Height.logHeight₁ ((x : Kˣ) : K) ≤ B}.Finite :=
    (NumberField.finite_setOfPred_logHeight₁_le K B).preimage
      (Units.val_injective.comp Subtype.val_injective).injOn
  refine (hfin.image fun x ↦ logEmbedding S (Additive.ofMul x)).subset ?_
  rintro _ ⟨hy, hyr⟩
  obtain ⟨x, rfl⟩ := mem_unitLattice_iff.mp hy
  exact ⟨x, (logHeight₁_le_mul_norm_logEmbedding S x).trans <|
    mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hyr) (by positivity), rfl⟩

/-- The `S`-unit lattice is discrete. -/
instance instDiscreteTopologyUnitLattice : DiscreteTopology (unitLattice S) := by
  classical
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by simp)
  · refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
    convert unitLattice_inter_ball_finite S 1
    ext x
    refine ⟨?_, fun ⟨hx1, hx2⟩ ↦ ⟨⟨x, hx1⟩, hx2, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨Subtype.mem x, hx⟩

/-! ### The `S`-units modulo torsion -/

/-- The kernel of the `S`-logarithmic embedding, as a `ℤ`-linear map, is the torsion submodule. -/
private theorem ker_toIntLinearMap_logEmbedding :
    LinearMap.ker (logEmbedding S).toIntLinearMap =
      Submodule.torsion ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) := by
  ext x
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, ofMul_mem_torsion_int_iff,
    logEmbedding_eq_zero_iff]

/-- The `S`-logarithmic embedding induces a `ℤ`-linear equivalence from the `S`-units modulo
torsion onto the `S`-unit lattice, sending the class of `x` to `logEmbedding S x`
(`TauCeti.NumberField.SUnit.logEmbeddingEquiv_apply`). -/
def logEmbeddingEquiv :
    (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ⧸
        Submodule.torsion ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) ≃ₗ[ℤ]
      unitLattice S :=
  (Submodule.quotEquivOfEq _ _ (ker_toIntLinearMap_logEmbedding S).symm).trans <|
    (logEmbedding S).toIntLinearMap.quotKerEquivRange.trans <|
      LinearEquiv.ofEq _ _ (range_toIntLinearMap_logEmbedding S)

@[simp]
theorem logEmbeddingEquiv_apply (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (logEmbeddingEquiv S (Submodule.Quotient.mk (Additive.ofMul x)) : logSpace S) =
      logEmbedding S (Additive.ofMul x) := by
  rfl

/-! ### Rank and spanning -/

/-- The `S`-logarithmic space has dimension `rank K + #S`. -/
theorem finrank_logSpace : finrank ℝ (logSpace S) = NumberField.Units.rank K + #S := by
  classical
  simp [finrank_fintype_fun_eq_card, NumberField.Units.rank]

/-- The `S`-unit lattice has rank `rank K + #S`. -/
@[simp]
theorem unitLattice_rank : finrank ℤ (unitLattice S) = NumberField.Units.rank K + #S := by
  rw [← (logEmbeddingEquiv S).finrank_eq, finrank_quotient_eq_of_le_torsion le_rfl,
    finrank_sUnits_numberField]
  simp

/-- The `S`-unit lattice spans the `S`-logarithmic space over `ℝ`. -/
theorem unitLattice_span_eq_top :
    Submodule.span ℝ (unitLattice S : Set (logSpace S)) = ⊤ := by
  classical
  have h := Real.finrank_eq_int_finrank_of_discrete
    (s := (unitLattice S : Set (logSpace S))) (by rw [Submodule.span_eq]; infer_instance)
  rw [Set.finrank, Set.finrank, Submodule.span_eq, unitLattice_rank,
    ← finrank_logSpace S] at h
  exact Submodule.eq_top_of_finrank_eq h

open Classical in
/-- The `S`-unit lattice is a full `ℤ`-lattice in the `S`-logarithmic space. -/
instance instIsZLatticeUnitLattice : IsZLattice ℝ (unitLattice S) where
  span_top := unitLattice_span_eq_top S

/-! ### The `S`-regulator -/

open Classical in
/-- The `S`-regulator of a number field: the covolume of the `S`-unit lattice. -/
def regulator : ℝ := ZLattice.covolume (unitLattice S)

open Classical in
/-- The `S`-regulator is the covolume of the `S`-unit lattice. -/
theorem regulator_def : regulator S = ZLattice.covolume (unitLattice S) := by
  rfl

/-- The `S`-regulator is positive. -/
theorem regulator_pos : 0 < regulator S := by
  classical
  exact ZLattice.covolume_pos _ _

/-- The `S`-regulator is nonzero. -/
theorem regulator_ne_zero : regulator S ≠ 0 :=
  (regulator_pos S).ne'

end TauCeti.NumberField.SUnit
