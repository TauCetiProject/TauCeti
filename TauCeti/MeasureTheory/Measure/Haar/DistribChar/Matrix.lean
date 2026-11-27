/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Transvection
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# The Haar character of the general linear group

Let `A` be a commutative locally compact second countable topological ring. The group `GL ι A`
acts on the column vectors `ι → A` by `Matrix.mulVec`, so it has a distributive Haar character
`distribHaarChar (ι → A) : GL ι A →* ℝ≥0`, the factor by which `g` scales additive Haar measure
on `ι → A`. This file computes it on transvections and diagonal matrices, and over a field `K`
in general:

`distribHaarChar (ι → K) g = distribHaarChar K (det g)`,

that is, `g` scales Haar measure on `Kⁿ` by the factor by which multiplication by `det g` scales
Haar measure on `K`. Over a nonarchimedean local field this factor is the normalized absolute
value `|det g|_K` (`MeasureTheory.distribHaarChar_eq_normalizedAbsoluteValue_det`). This is the
local computation behind the scaling of Haar measure on `𝔸ⁿ` by `GL_n` over the adeles of a
number field, through the module of the determinant.

The proof follows Mathlib's computation for Lebesgue measure on `ι → ℝ`
(`Real.volume_preserving_transvectionStruct`, `Real.map_matrix_volume_pi_eq_smul_volume_pi`): a
transvection preserves every product of copies of an additively invariant measure, by Fubini's
theorem along the sheared coordinate; a diagonal matrix scales a box coordinatewise; and over a
field every invertible matrix is a product of these
(`Matrix.diagonal_transvection_induction_of_det_ne_zero`).

## Main results

* `MeasureTheory.measurePreserving_transvection_mulVec`: a transvection preserves the product
  `Measure.pi fun _ ↦ μ` of copies of an additively invariant σ-finite measure `μ`.
* `MeasureTheory.distribHaarChar_transvection`: a transvection has Haar character one.
* `MeasureTheory.distribHaarChar_diagGL`: the diagonal matrix with unit entries `d i` scales Haar
  measure by `∏ i, distribHaarChar A (d i)`.
* `MeasureTheory.distribHaarChar_eq_distribHaarChar_det`: over a locally compact second countable
  field, the Haar character of `g ∈ GL ι K` on `ι → K` is the Haar character of `det g` on `K`.

## References

* A. Weil, *Basic Number Theory*, Chapter I, §2 (the module of an automorphism of a
  finite-dimensional vector space over a locally compact field is the module of its
  determinant).
* The same reduction to the determinant is the step `New.map_mulVec_haar_finAdele`
  (`src/Lib/Adelic/Adeles/IdeleModulus.lean`) of grh-lean takes over the finite adeles
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); no code of
  that file is used here.
-/

public section

open Matrix Set
open scoped NNReal ENNReal Pointwise

namespace MeasureTheory

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-! ### Transvections preserve product measures -/

section Transvection

variable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableMul A]

/-- **Transvections preserve product measures.** For an additively invariant σ-finite measure
`μ` on a commutative ring `A`, the transvection adding `c` times the `j`-th coordinate to the
`i`-th one preserves the product measure `Measure.pi fun _ ↦ μ` on `ι → A`. This generalizes
Mathlib's `Real.volume_preserving_transvectionStruct`, whose proof it follows. -/
theorem measurePreserving_transvection_mulVec (μ : Measure A) [μ.IsAddLeftInvariant]
    [SigmaFinite μ] {i j : ι} (hij : i ≠ j) (c : A) :
    MeasurePreserving (transvection i j c *ᵥ ·) (Measure.pi fun _ : ι ↦ μ)
      (Measure.pi fun _ : ι ↦ μ) := by
  -- The transvection adds `c` times the `j`-th coordinate to the `i`-th one.
  have hT : (transvection i j c *ᵥ · : (ι → A) → ι → A) =
      fun v ↦ Function.update v i (v i + c * v j) :=
    funext fun v ↦ by rw [← TauCeti.coe_transvectionUnit hij, TauCeti.transvectionUnit_mulVec]
  have ht : Measurable (transvection i j c *ᵥ · : (ι → A) → ι → A) := by
    rw [hT]
    fun_prop
  refine ⟨ht, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  -- By Fubini's theorem it suffices to integrate along the `i`-th coordinate, where the
  -- transvection is a translation.
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  simp_rw [hT, Function.update_self, Function.update_of_ne hij.symm, Function.update_idem]
  exact lintegral_add_right_eq_self (fun xᵢ ↦ indicator (univ.pi s) 1 (Function.update x i xᵢ))
    (c * x j)

end Transvection

/-! ### The Haar character on transvections and diagonal matrices -/

section Generators

variable [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [SecondCountableTopology A]

/-- **Transvections have Haar character one.** The transvection adding `c` times the `j`-th
coordinate to the `i`-th one preserves additive Haar measure on `ι → A`. -/
@[simp]
theorem distribHaarChar_transvection {i j : ι} (hij : i ≠ j) (c : A) :
    distribHaarChar (ι → A) (GeneralLinearGroup.transvection i j hij c) = 1 := by
  borelize A
  let ν : Measure (ι → A) := Measure.pi fun _ ↦ Measure.addHaar
  obtain ⟨L⟩ : Nonempty (TopologicalSpace.PositiveCompacts (ι → A)) := inferInstance
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν)
    (Measure.measure_pos_of_nonempty_interior ν L.interior_nonempty).ne'
    L.isCompact.measure_lt_top.ne ?_
  -- The inverse transvection is a measure preserving homeomorphism.
  let e := (Homeomorph.smul (TauCeti.transvectionUnit hij (-c) : GL ι A) :
    (ι → A) ≃ₜ (ι → A)).toMeasurableEquiv
  have he : MeasurePreserving e ν ν := by
    convert measurePreserving_transvection_mulVec Measure.addHaar hij (-c) using 1
    ext x : 1
    simp [e, Units.smul_def]
  rw [← TauCeti.transvectionUnit_eq_transvection, ← Set.preimage_smul_inv,
    TauCeti.transvectionUnit_inv, ENNReal.coe_one, one_mul]
  exact he.measure_preimage_equiv _

/-- **The Haar character of a diagonal matrix.** The diagonal matrix with unit entries `d i`
scales additive Haar measure on `ι → A` by the product of the factors by which the `d i` scale
additive Haar measure on `A`. -/
@[simp]
theorem distribHaarChar_diagGL (d : ι → Aˣ) :
    distribHaarChar (ι → A) (TauCeti.diagGL d) = ∏ i, distribHaarChar A (d i) := by
  borelize A
  let μ : Measure A := Measure.addHaar
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts A) := inferInstance
  -- Compute with the box whose sides are a compact set `K` with nonempty interior.
  have hK₀ : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hK : μ K ≠ ∞ := K.isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi fun _ : ι ↦ μ)
    (s := univ.pi fun _ ↦ (K : Set A)) (by simp [Measure.pi_pi, hK₀])
    (by simp [Measure.pi_pi, hK]) ?_
  have hbox : TauCeti.diagGL d • univ.pi (fun _ ↦ (K : Set A)) =
      univ.pi fun i ↦ d i • (K : Set A) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, Units.smul_def, TauCeti.diagGL_coe,
      smul_eq_mulVec, mem_univ_pi, mem_univ_pi]
    refine forall_congr' fun i ↦ ?_
    rw [mulVec_diagonal, Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul,
      Pi.inv_apply]
  rw [hbox, Measure.pi_pi, Measure.pi_pi]
  push_cast
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ (distribHaarChar_mul μ (d i) K).symm

end Generators

/-! ### The Haar character over a field -/

section Field

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [SecondCountableTopology K]

/-- **The Haar character of `GL_n` is that of the determinant.** Over a locally compact field
`K`, an invertible matrix `g` scales additive Haar measure on `ι → K` by the factor by which
multiplication by `det g` scales additive Haar measure on `K`. -/
theorem distribHaarChar_eq_distribHaarChar_det (g : GL ι K) :
    distribHaarChar (ι → K) g = distribHaarChar K (GeneralLinearGroup.det g) := by
  -- Every invertible matrix is a product of diagonal matrices and transvections.
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun M ↦ ∀ g : GL ι K, (g : Matrix ι ι K) = M →
      distribHaarChar (ι → K) g = distribHaarChar K (GeneralLinearGroup.det g))
    g ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero (fun D hD g hg ↦ ?_) (fun t g hg ↦ ?_)
    (fun M N hM hN hPM hPN g hg ↦ ?_) g rfl
  · have hD' : ∀ i, D i ≠ 0 := by
      simpa [det_diagonal, Finset.prod_ne_zero_iff] using hD
    have hg' : g = TauCeti.diagGL fun i ↦ Units.mk0 (D i) (hD' i) := Units.ext (by simp [hg])
    have hdet : GeneralLinearGroup.det g = ∏ i, Units.mk0 (D i) (hD' i) :=
      Units.ext (by simp [hg, det_diagonal])
    rw [hdet, map_prod, hg', distribHaarChar_diagGL]
  · obtain ⟨i, j, hij, c⟩ := t
    have hg' : g = GeneralLinearGroup.transvection i j hij c :=
      Units.ext (by rw [hg, TransvectionStruct.toMatrix_mk, GeneralLinearGroup.val_transvection])
    rw [hg', distribHaarChar_transvection, ← TauCeti.transvectionUnit_eq_transvection,
      TauCeti.det_transvectionUnit, map_one]
  · have hg' : g = GeneralLinearGroup.mkOfDetNeZero M hM * GeneralLinearGroup.mkOfDetNeZero N hN :=
      Units.ext (by rw [hg, Units.val_mul, GeneralLinearGroup.val_mkOfDetNeZero,
        GeneralLinearGroup.val_mkOfDetNeZero])
    rw [hg', map_mul, map_mul, map_mul, hPM _ (GeneralLinearGroup.val_mkOfDetNeZero M hM),
      hPN _ (GeneralLinearGroup.val_mkOfDetNeZero N hN)]

end Field

end MeasureTheory
