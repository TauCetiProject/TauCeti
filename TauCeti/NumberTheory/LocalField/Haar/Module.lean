/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.NumberTheory.LocalField.Haar.Basic
public import TauCeti.NumberTheory.LocalField.Lattice
public import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.MeasureTheory.Group.BoundedLineSections
import TauCeti.MeasureTheory.Measure.AEMeasurable

/-!
# Linear Haar change of variables and lattice normalizations over local fields

Let `E` be a nonarchimedean local field with valuation ring `𝒪[E]`, residue field `𝓀[E]` of
cardinality `q = Nat.card 𝓀[E]`, and normalized absolute value `|·|_E`
(`TauCeti.normalizedAbsoluteValue E`), and let `V` be a finite-dimensional `E`-vector space
carrying its `E`-module topology (`IsModuleTopology E V`).

Every `E`-linear automorphism `T : V ≃ₗ[E] V` is a topological group automorphism of `V`, and this
file establishes the nonarchimedean counterpart of `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`
from the Smith-normal-form integral-matrix scaling of
`TauCeti.MeasureTheory.Group.LocalFieldScaling`:
* proper `E`-subspaces `W < ⊤` have `μ`-measure zero
  (`MeasureTheory.Measure.addHaar_submodule_of_isNonarchimedeanLocalField`);
* for **every** `E`-linear endomorphism `f : V →ₗ[E] V` (invertible or singular) and every subset
  `s : Set V`, `μ (f '' s) = |det f|_E * μ s`
  (`MeasureTheory.Measure.addHaar_image_linearMap_of_isNonarchimedeanLocalField`);
* for `T : V ≃ₗ[E] V`, `Measure.map T μ = |det T|_E⁻¹ • μ`
  (`MeasureTheory.Measure.map_linearEquiv_addHaar_of_isNonarchimedeanLocalField`), and for any
  group `G` acting continuously and `E`-linearly on `V`, `distribHaarChar V g = |det (g • ·)|_E`
  (`MeasureTheory.distribHaarChar_eq_normalizedAbsoluteValue_det_of_isModuleTopology`);
* scalar multiplication by `c : E` scales `μ` by `|c|_E ^ finrank E V`
  (`MeasureTheory.Measure.addHaar_smul_module_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.addHaar_preimage_smul_module_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.map_smul_module_addHaar_of_isNonarchimedeanLocalField`).

Notice that this Jacobian is completely independent of any choice of basis or lattice and of the
overall normalization of `μ`. When `V` is additionally equipped with a lattice
`L : Submodule 𝒪[E] V` (`[L.IsFullLattice E]`) or a finite basis `b : Module.Basis ι E V`,
compact-openness of `L` yields a canonical regular additive Haar measure
`Submodule.IsFullLattice.localAddHaar L` (respectively `b.localAddHaar`) giving `L`
(respectively the `𝒪[E]`-span of `b`) mass one. Changing basis from `b` to `b'` rescales the
measure by `|b.det b'|_E⁻¹` (`Module.Basis.localAddHaar_eq_smul`), so
`b'.localAddHaar = b.localAddHaar` whenever `b.det b'` has valuation one
(`valuation E (b.det b') = 1`, equivalently `b.det b' ∈ 𝒪[E]ˣ`; in particular, for any integral
change of basis in `GL_n(𝒪[E])`, and likewise for any `T ∈ GL(L)`).

## Main definitions

* `Submodule.IsFullLattice.positiveCompacts`: a full `𝒪[E]`-lattice `L` in `V` packaged as a
  `TopologicalSpace.PositiveCompacts V`.
* `Submodule.IsFullLattice.localAddHaar`: the regular additive Haar measure on `V` normalized by
  `μ L = 1`.
* `Module.Basis.localAddHaar`: the regular additive Haar measure on `V` normalized by giving
  `Submodule.span 𝒪[E] (Set.range b)` measure one.

## Main results

* `MeasureTheory.Measure.addHaar_submodule_of_isNonarchimedeanLocalField`: proper subspaces of `V`
  are Haar-null.
* `MeasureTheory.Measure.addHaar_image_linearMap_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.addHaar_image_continuousLinearMap_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.addHaar_image_mulVec_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.addHaar_preimage_mulVec_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.map_mulVec_addHaar_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.map_linearEquiv_addHaar_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.map_continuousLinearEquiv_addHaar_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.map_linearMap_addHaar_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.map_continuousLinearMap_addHaar_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.map_smul_module_addHaar_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.lintegral_comp_linearEquiv_addHaar_of_isNonarchimedeanLocalField`,
  `MeasureTheory.Measure.integral_comp_linearEquiv_addHaar_of_isNonarchimedeanLocalField`: linear,
  matrix, and scalar-dilation change of variables on `V` and `ι → E`.
* `MeasureTheory.distribHaarChar_eq_normalizedAbsoluteValue_det_of_isModuleTopology`:
  `distribHaarChar V g = |det (g • ·)|_E`.
* `Submodule.IsFullLattice.map_localAddHaar`, `Submodule.IsFullLattice.localAddHaar_congr`,
  `Submodule.IsFullLattice.map_linearEquiv_addHaar_of_mem_stabilizer`,
  `Module.Basis.map_localAddHaar`, `Module.Basis.localAddHaar_eq_smul`,
  `Module.Basis.localAddHaar_eq_of_valuation_det_eq_one`: transport along linear equivalences,
  congruence of equal lattices, invariance under `GL(L)`, and change-of-basis scaling.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Vol. I, Cambridge University Press, 2023, §3.5, pp. 186–188.
* A. Weil, *Basic Number Theory*, 3rd ed., Springer, 1974, Chapter I, §2, Proposition 3.
-/

public section

open MeasureTheory MeasureTheory.Measure Module Set TopologicalSpace ValuativeRel
open scoped ENNReal NNReal NNRat Pointwise

namespace MeasureTheory.Measure

open TauCeti

section ModuleSpace

variable {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [AddCommGroup V] [Module E V] [Module.Finite E V]
  [TopologicalSpace V] [IsModuleTopology E V] [MeasurableSpace V] [BorelSpace V]

/-- **Proper subspaces are Haar-null.** Any proper `E`-linear subspace `W ≠ ⊤` of a
finite-dimensional `E`-vector space `V` carrying the module topology has additive Haar measure
zero. -/
theorem addHaar_submodule_of_isNonarchimedeanLocalField (μ : Measure V) [μ.IsAddHaarMeasure]
    (W : Submodule E V) (hW : W ≠ ⊤) : μ (W : Set V) = 0 := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  obtain ⟨f, hf0, hWker⟩ := W.exists_le_ker_of_lt_top hW.lt_top
  obtain ⟨v, hfv⟩ : ∃ v, f v ≠ 0 := by
    by_contra! h
    exact hf0 (LinearMap.ext h)
  obtain ⟨ι, b, i, -, hf_eq⟩ := exists_basis_of_pairing_ne_zero hfv
  have : Finite ι := Module.Finite.finite_basis b
  borelize (ι → E)
  let e : V ≃L[E] (ι → E) := b.equivFun.toContinuousLinearEquivOfIsModuleTopology
  let ν : Measure (ι → E) := μ.map e
  have _ : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hsub : e '' (W : Set V) ⊆ {a : ι → E | a i = 0} := by
    rintro _ ⟨w, hw, rfl⟩
    have hfw : f w = 0 := hWker hw
    rw [hf_eq, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero] at hfw
    simpa [e, Basis.equivFun_apply] using hfw.resolve_left hfv
  rw [← e.toHomeomorph.measurableEmbedding.map_apply_image μ (W : Set V),
    ContinuousLinearEquiv.coe_toHomeomorph]
  exact measure_mono_null hsub (measure_setOf_apply_eq_zero ν i)

/-- Algebraic identity relating `|det A|_E` to the valuation exponent `k` of a cleared matrix
`B = ϖ ^ m • A` over `𝒪[E]`. -/
private theorem normalizedAbsoluteValue_det_mul_inv_pow {E : Type*} [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] {ϖ : 𝒪[E]} (hϖ : Irreducible ϖ)
    {d : E} {b : 𝒪[E]} {m n k : ℕ} (hbd : (b : E) = ((ϖ : E) ^ m) ^ n * d)
    (hk : Associated b (ϖ ^ k)) :
    ((normalizedAbsoluteValue E d : ℝ≥0) : ℝ≥0∞) *
      (1 / (Nat.card 𝓀[E] : ℝ≥0∞) ^ (m * n)) = 1 / (Nat.card 𝓀[E] : ℝ≥0∞) ^ k := by
  obtain ⟨u, hu⟩ := hk.symm
  have hval := congrArg (fun x : 𝒪[E] ↦ normalizedAbsoluteValue E (x : E)) hu
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hbd,
    ← pow_mul, normalizedAbsoluteValue_irreducible hϖ, normalizedAbsoluteValue_coe_unit,
    mul_one] at hval
  have hnnr := congrArg (fun q : ℚ≥0 ↦ ((q : ℝ≥0) : ℝ≥0∞)) hval.symm
  have hq0 : (Nat.card 𝓀[E] : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simpa [one_div, mul_comm, inv_pow, ENNReal.coe_inv (pow_ne_zero _ hq0)] using hnnr

/-- Invertible-matrix step for `addHaar_image_linearMap_of_isNonarchimedeanLocalField`:
if `IsUnit A.det`, then `A.mulVec` scales any additive Haar measure on `ι → E` by `|det A|_E`. -/
private theorem addHaar_image_mulVec_of_isUnit_det {E ι : Type*} [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (ι → E)] [BorelSpace (ι → E)] (μ : Measure (ι → E)) [μ.IsAddHaarMeasure]
    {A : Matrix ι ι E} (hA : IsUnit A.det) (s : Set (ι → E)) :
    μ (A.mulVec '' s) = ((normalizedAbsoluteValue E A.det : ℝ≥0) : ℝ≥0∞) * μ s := by
  -- Clear denominators via `B = ϖ ^ m • A ∈ Matrix ι ι 𝒪[E]` and cancel `ϖ ^ m • 1`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hϖ0 : (ϖ : E) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  obtain ⟨m, hm⟩ := exists_mem_scaledIntegerBox hϖ (fun p : ι × ι ↦ A p.1 p.2)
  rw [mem_scaledIntegerBox] at hm
  let B : Matrix ι ι 𝒪[E] := Matrix.of fun i j ↦ ⟨(ϖ : E) ^ m * A i j, hm (i, j)⟩
  have hBmap : B.map (algebraMap 𝒪[E] E) = ((ϖ : E) ^ m) • A := by
    ext i j
    simp [B, Algebra.algebraMap_ofSubsemiring_apply]
  have hBdet_coe : (B.det : E) = ((ϖ : E) ^ m) ^ Fintype.card ι * A.det := by
    have h := congrArg Matrix.det hBmap
    rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det, Algebra.algebraMap_ofSubsemiring_apply,
      Matrix.det_smul] at h
  have hBdet0 : B.det ≠ 0 := by
    intro h0
    have h0' : (B.det : E) = 0 := by simp [h0]
    rw [hBdet_coe] at h0'
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero m hϖ0)) hA.ne_zero h0'
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hBdet0 hϖ
  let C : Matrix ι ι 𝒪[E] := (ϖ ^ m) • 1
  have hCdet : Associated C.det (ϖ ^ (m * Fintype.card ι)) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, ← pow_mul]
  have hB_haar := addHaar_image_mulVec μ hϖ hk s
  have hC_haar := addHaar_image_mulVec μ hϖ hCdet (A.mulVec '' s)
  have hBC_img : (C.map (algebraMap 𝒪[E] E)).mulVec '' (A.mulVec '' s) =
      (B.map (algebraMap 𝒪[E] E)).mulVec '' s := by
    have hCmap : C.map (algebraMap 𝒪[E] E) = ((ϖ : E) ^ m) • (1 : Matrix ι ι E) := by
      ext i j
      simp [C, Matrix.one_apply, apply_ite (algebraMap 𝒪[E] E),
        Algebra.algebraMap_ofSubsemiring_apply]
    rw [← image_comp, hCmap, hBmap]
    congr 1
    ext x
    rw [Function.comp_apply, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rw [hBC_img, hB_haar, ← normalizedAbsoluteValue_det_mul_inv_pow hϖ hBdet_coe hk,
    mul_comm ((normalizedAbsoluteValue E A.det : ℝ≥0) : ℝ≥0∞), mul_assoc] at hC_haar
  have hq_ne0 : 1 / (Nat.card 𝓀[E] : ℝ≥0∞) ^ (m * Fintype.card ι) ≠ 0 := by
    simp [ENNReal.pow_eq_top_iff]
  have hq_lt : 1 / (Nat.card 𝓀[E] : ℝ≥0∞) ^ (m * Fintype.card ι) ≠ ∞ := by
    have h1 : (Nat.card 𝓀[E] : ℝ≥0∞) ^ (m * Fintype.card ι) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
    simp [one_div, h1]
  exact ((ENNReal.mul_right_inj hq_ne0 hq_lt).1 hC_haar).symm

/-- **Linear Haar change of variables for arbitrary endomorphisms.** For any `E`-linear map
`f : V →ₗ[E] V` (invertible or singular) on a finite-dimensional `E`-vector space `V` with its
module topology, every additive Haar measure `μ` satisfies `μ (f '' s) = |det f|_E * μ s`. -/
@[simp, grind =]
theorem addHaar_image_linearMap_of_isNonarchimedeanLocalField (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : V →ₗ[E] V) (s : Set V) :
    μ (f '' s) = ((normalizedAbsoluteValue E f.det : ℝ≥0) : ℝ≥0∞) * μ s := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  by_cases hf : f.det = 0
  · have h0 : μ (f '' s) = 0 := measure_mono_null (image_subset_range f s)
      (addHaar_submodule_of_isNonarchimedeanLocalField μ (LinearMap.range f)
        (LinearMap.range_lt_top_of_det_eq_zero hf).ne)
    simp [h0, hf]
  · let b := Module.finBasis E V
    let ι := Fin (Module.finrank E V)
    borelize (ι → E)
    let e : V ≃L[E] (ι → E) := b.equivFun.toContinuousLinearEquivOfIsModuleTopology
    let ν : Measure (ι → E) := μ.map e
    have _ : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
    let A : Matrix ι ι E := LinearMap.toMatrix b b f
    have hAdet : A.det = f.det := LinearMap.det_toMatrix b f
    have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (hAdet.symm ▸ hf)
    have hcomm : e '' (f '' s) = A.mulVec '' (e '' s) := by
      rw [← image_comp, ← image_comp]
      congr 1
      ext x
      simp only [Function.comp_apply, e,
        LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology, Basis.equivFun_apply]
      exact congrFun (LinearMap.toMatrix_mulVec_repr b b f x).symm _
    rw [← e.toHomeomorph.measurableEmbedding.map_apply_image μ (f '' s),
      ContinuousLinearEquiv.coe_toHomeomorph, hcomm, addHaar_image_mulVec_of_isUnit_det ν hA,
      hAdet]
    simp only [ν, ← ContinuousLinearEquiv.coe_toHomeomorph (e := e),
      e.toHomeomorph.measurableEmbedding.map_apply_image]

/-- Image of a set under a continuous linear map `f : V →L[E] V` (invertible or singular) scales
any additive Haar measure on `V` by `|det f|_E`. -/
@[simp, grind =]
theorem addHaar_image_continuousLinearMap_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] (f : V →L[E] V) (s : Set V) :
    μ (f '' s) =
      ((normalizedAbsoluteValue E (LinearMap.det (f : V →ₗ[E] V)) : ℝ≥0) : ℝ≥0∞) * μ s :=
  addHaar_image_linearMap_of_isNonarchimedeanLocalField μ (f : V →ₗ[E] V) s

/-- Image of a set under a linear equivalence `T : V ≃ₗ[E] V` scales any additive Haar measure on
`V` by `|det T|_E`. -/
@[simp, grind =]
theorem addHaar_image_linearEquiv_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[E] V) (s : Set V) :
    μ (T '' s) =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ≥0) : ℝ≥0∞) * μ s :=
  addHaar_image_linearMap_of_isNonarchimedeanLocalField μ (T : V →ₗ[E] V) s

/-- Image of a set under a continuous linear equivalence `T : V ≃L[E] V` scales any additive Haar
measure on `V` by `|det T|_E`. -/
@[simp, grind =]
theorem addHaar_image_continuousLinearEquiv_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃L[E] V) (s : Set V) :
    μ (T '' s) =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ≥0) : ℝ≥0∞) * μ s :=
  addHaar_image_linearEquiv_of_isNonarchimedeanLocalField μ T.toLinearEquiv s

/-- Preimage of a set under a linear equivalence `T : V ≃ₗ[E] V` scales any additive Haar measure
on `V` by `|det T|_E⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_linearEquiv_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[E] V) (s : Set V) :
    μ (T ⁻¹' s) =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ≥0) : ℝ≥0∞)⁻¹ * μ s := by
  rw [← T.image_symm_eq_preimage, addHaar_image_linearEquiv_of_isNonarchimedeanLocalField,
    LinearEquiv.det_coe_symm, map_inv₀, NNRat.cast_inv,
    ENNReal.coe_inv (coe_normalizedAbsoluteValue_ne_zero T.isUnit_det'.ne_zero)]

/-- Preimage of a set under a continuous linear equivalence `T : V ≃L[E] V` scales any additive
Haar measure on `V` by `|det T|_E⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_continuousLinearEquiv_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃L[E] V) (s : Set V) :
    μ (T ⁻¹' s) =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ≥0) : ℝ≥0∞)⁻¹ * μ s :=
  addHaar_preimage_linearEquiv_of_isNonarchimedeanLocalField μ T.toLinearEquiv s

/-- Preimage of a set under an invertible linear map `f : V →ₗ[E] V` (`f.det ≠ 0`) scales any
additive Haar measure on `V` by `|det f|_E⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_linearMap_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] {f : V →ₗ[E] V} (hf : f.det ≠ 0) (s : Set V) :
    μ (f ⁻¹' s) = ((normalizedAbsoluteValue E f.det : ℝ≥0) : ℝ≥0∞)⁻¹ * μ s := by
  let T : V ≃ₗ[E] V := LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.2 hf)
  have hcoe : (T : V →ₗ[E] V) = f := LinearMap.coe_equivOfIsUnitDet _
  have hfun : (T : V → V) = f := DFunLike.coe_fn_eq.2 hcoe
  simpa only [← hfun, hcoe] using addHaar_preimage_linearEquiv_of_isNonarchimedeanLocalField μ T s

/-- Preimage of a set under an invertible continuous linear map `f : V →L[E] V` (`det f ≠ 0`)
scales any additive Haar measure on `V` by `|det f|_E⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_continuousLinearMap_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] {f : V →L[E] V} (hf : LinearMap.det (f : V →ₗ[E] V) ≠ 0) (s : Set V) :
    μ (f ⁻¹' s) =
      ((normalizedAbsoluteValue E (LinearMap.det (f : V →ₗ[E] V)) : ℝ≥0) : ℝ≥0∞)⁻¹ * μ s :=
  addHaar_preimage_linearMap_of_isNonarchimedeanLocalField μ hf s

/-- **Pushforward of additive Haar measure under a linear equivalence.** For any `T : V ≃ₗ[E] V`
and any additive Haar measure `μ` on `V`, `Measure.map T μ = |det T|_E⁻¹ • μ`, independently of
basis and Haar normalization. -/
theorem map_linearEquiv_addHaar_of_isNonarchimedeanLocalField (μ : Measure V) [μ.IsAddHaarMeasure]
    (T : V ≃ₗ[E] V) :
    map T μ =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ≥0)⁻¹ : ℝ≥0) • μ := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  have hT : Measurable T := (IsModuleTopology.continuous_of_linearMap (T : V →ₗ[E] V)).measurable
  ext s hs
  rw [map_apply hT hs, addHaar_preimage_linearEquiv_of_isNonarchimedeanLocalField μ T s,
    smul_apply, nnreal_smul_coe_apply,
    ENNReal.coe_inv (coe_normalizedAbsoluteValue_ne_zero T.isUnit_det'.ne_zero)]

/-- Pushforward of additive Haar measure under a continuous linear equivalence `T : V ≃L[E] V`. -/
theorem map_continuousLinearEquiv_addHaar_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃L[E] V) :
    map T μ =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ≥0)⁻¹ : ℝ≥0) • μ :=
  map_linearEquiv_addHaar_of_isNonarchimedeanLocalField μ T.toLinearEquiv

/-- Pushforward of additive Haar measure under a linear endomorphism `f : V →ₗ[E] V` of nonzero
determinant. -/
theorem map_linearMap_addHaar_of_isNonarchimedeanLocalField (μ : Measure V) [μ.IsAddHaarMeasure]
    {f : V →ₗ[E] V} (hf : f.det ≠ 0) :
    map f μ = ((normalizedAbsoluteValue E f.det : ℝ≥0)⁻¹ : ℝ≥0) • μ := by
  let T : V ≃ₗ[E] V := LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.2 hf)
  have hcoe : (T : V →ₗ[E] V) = f := LinearMap.coe_equivOfIsUnitDet _
  have hfun : (T : V → V) = f := DFunLike.coe_fn_eq.2 hcoe
  simpa only [← hfun, hcoe] using map_linearEquiv_addHaar_of_isNonarchimedeanLocalField μ T

/-- Pushforward of additive Haar measure under a continuous linear endomorphism `f : V →L[E] V` of
nonzero determinant. -/
theorem map_continuousLinearMap_addHaar_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] {f : V →L[E] V} (hf : LinearMap.det (f : V →ₗ[E] V) ≠ 0) :
    map f μ =
      ((normalizedAbsoluteValue E (LinearMap.det (f : V →ₗ[E] V)) : ℝ≥0)⁻¹ : ℝ≥0) • μ :=
  map_linearMap_addHaar_of_isNonarchimedeanLocalField μ hf

/-- Scalar multiplication by `c : E` on `V` multiplies additive Haar measure by
`|c|_E ^ finrank E V`. -/
@[simp, grind =]
theorem addHaar_smul_module_of_isNonarchimedeanLocalField (μ : Measure V) [μ.IsAddHaarMeasure]
    (c : E) (s : Set V) :
    μ (c • s) = ((normalizedAbsoluteValue E c : ℝ≥0) : ℝ≥0∞) ^ Module.finrank E V * μ s := by
  have hsmul : c • s = (c • (LinearMap.id : V →ₗ[E] V)) '' s := by
    ext x
    simp
  rw [hsmul, addHaar_image_linearMap_of_isNonarchimedeanLocalField, LinearMap.det_smul,
    LinearMap.det_id, mul_one, map_pow, NNRat.cast_pow, ENNReal.coe_pow]

/-- Preimage of a set under scalar multiplication by `c ≠ 0` on `V` multiplies any additive Haar
measure by `(|c|_E ^ finrank E V)⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_smul_module_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] {c : E} (hc : c ≠ 0) (s : Set V) :
    μ ((c • ·) ⁻¹' s) =
      (((normalizedAbsoluteValue E c : ℝ≥0) : ℝ≥0∞) ^ Module.finrank E V)⁻¹ * μ s := by
  have hpre : (c • ·) ⁻¹' s = (c • (LinearMap.id : V →ₗ[E] V)) ⁻¹' s := by
    ext x
    simp
  have hdet : (c • (LinearMap.id : V →ₗ[E] V)).det ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hc
  rw [hpre, addHaar_preimage_linearMap_of_isNonarchimedeanLocalField μ hdet,
    LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow, NNRat.cast_pow, ENNReal.coe_pow]

/-- Pushforward of additive Haar measure on `V` under scalar multiplication by `c ≠ 0`. -/
@[simp, grind =]
theorem map_smul_module_addHaar_of_isNonarchimedeanLocalField (μ : Measure V) [μ.IsAddHaarMeasure]
    {c : E} (hc : c ≠ 0) :
    map (c • ·) μ =
      (((normalizedAbsoluteValue E c : ℝ≥0) ^ Module.finrank E V)⁻¹ : ℝ≥0) • μ := by
  have hfun : (c • · : V → V) = ⇑(c • (LinearMap.id : V →ₗ[E] V)) :=
    funext fun x ↦ by simp
  have hdet : (c • (LinearMap.id : V →ₗ[E] V)).det ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hc
  rw [hfun, map_linearMap_addHaar_of_isNonarchimedeanLocalField μ hdet, LinearMap.det_smul,
    LinearMap.det_id, mul_one, map_pow, NNRat.cast_pow]

/-- Lower Lebesgue integral change of variables on `V` under `T : V ≃ₗ[E] V`. -/
theorem lintegral_comp_linearEquiv_addHaar_of_isNonarchimedeanLocalField (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[E] V) (f : V → ℝ≥0∞) :
    ∫⁻ x, f (T x) ∂μ =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ∫⁻ x, f x ∂μ := by
  let e : V ≃ᵐ V := T.toContinuousLinearEquivOfIsModuleTopology.toHomeomorph.toMeasurableEquiv
  have h := lintegral_map_equiv f e (μ := μ)
  have he : ⇑e = ⇑T := by simp [e]
  rw [he, map_linearEquiv_addHaar_of_isNonarchimedeanLocalField μ T, lintegral_smul_measure,
    ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_inv (coe_normalizedAbsoluteValue_ne_zero T.isUnit_det'.ne_zero)] at h
  exact h.symm

/-- Bochner integral change of variables on `V` under `T : V ≃ₗ[E] V`. -/
theorem integral_comp_linearEquiv_addHaar_of_isNonarchimedeanLocalField {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure V) [μ.IsAddHaarMeasure]
    (T : V ≃ₗ[E] V) (f : V → F) :
    ∫ x, f (T x) ∂μ =
      ((normalizedAbsoluteValue E (LinearMap.det (T : V →ₗ[E] V)) : ℝ)⁻¹) • ∫ x, f x ∂μ := by
  let e : V ≃ᵐ V := T.toContinuousLinearEquivOfIsModuleTopology.toHomeomorph.toMeasurableEquiv
  have h := integral_map_equiv e f (μ := μ)
  have he : ⇑e = ⇑T := by simp [e]
  rw [he, map_linearEquiv_addHaar_of_isNonarchimedeanLocalField μ T, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.coe_inv] at h
  exact h.symm

omit [Module.Finite E V] in
/-- **Zero-dimensional check (`dim_E V = 0`).** On a zero-dimensional `E`-vector space, every
`E`-linear automorphism has determinant `1` and preserves every additive Haar measure. -/
example [Subsingleton V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : V ≃ₗ[E] V) :
    map T μ = μ := by
  have : Module.Finite E V := Module.Finite.of_finite
  rw [map_linearEquiv_addHaar_of_isNonarchimedeanLocalField μ T,
    LinearMap.det_eq_one_of_subsingleton, map_one]
  simp

end ModuleSpace

section MatrixSpace

variable {E ι : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → E)] [BorelSpace (ι → E)]

/-- **Matrix Haar change of variables** for arbitrary (possibly singular) matrices
`A : Matrix ι ι E` on `ι → E`: `μ (A.mulVec '' s) = |det A|_E * μ s`. -/
@[simp, grind =]
theorem addHaar_image_mulVec_of_isNonarchimedeanLocalField (μ : Measure (ι → E))
    [μ.IsAddHaarMeasure] (A : Matrix ι ι E) (s : Set (ι → E)) :
    μ (A.mulVec '' s) = ((normalizedAbsoluteValue E A.det : ℝ≥0) : ℝ≥0∞) * μ s := by
  rw [← Matrix.coe_mulVecLin A, ← Matrix.toLin'_apply' A,
    addHaar_image_linearMap_of_isNonarchimedeanLocalField, LinearMap.det_toLin']

/-- Preimage of a set under `A.mulVec` (`A.det ≠ 0`) on `ι → E` scales any additive Haar measure
by `|det A|_E⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_mulVec_of_isNonarchimedeanLocalField (μ : Measure (ι → E))
    [μ.IsAddHaarMeasure] {A : Matrix ι ι E} (hA : A.det ≠ 0) (s : Set (ι → E)) :
    μ (A.mulVec ⁻¹' s) = ((normalizedAbsoluteValue E A.det : ℝ≥0) : ℝ≥0∞)⁻¹ * μ s := by
  rw [← Matrix.coe_mulVecLin A, ← Matrix.toLin'_apply' A,
    addHaar_preimage_linearMap_of_isNonarchimedeanLocalField μ (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin']

/-- Pushforward of additive Haar measure on `ι → E` under `A.mulVec` (`A.det ≠ 0`). -/
theorem map_mulVec_addHaar_of_isNonarchimedeanLocalField (μ : Measure (ι → E)) [μ.IsAddHaarMeasure]
    {A : Matrix ι ι E} (hA : A.det ≠ 0) :
    map A.mulVec μ = ((normalizedAbsoluteValue E A.det : ℝ≥0)⁻¹ : ℝ≥0) • μ := by
  rw [← Matrix.coe_mulVecLin A, ← Matrix.toLin'_apply' A,
    map_linearMap_addHaar_of_isNonarchimedeanLocalField μ (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin']

end MatrixSpace

section ProdChecks

section Helpers

variable {E : Type*} [Field E]

private noncomputable def firstCoordScale (a : E) : (E × E) →ₗ[E] (E × E) :=
  LinearMap.prodMap (a • (LinearMap.id : E →ₗ[E] E)) (LinearMap.id : E →ₗ[E] E)

private theorem coe_firstCoordScale (a : E) :
    ⇑(firstCoordScale a) = fun p : E × E ↦ (a * p.1, p.2) := by
  ext p <;> simp [firstCoordScale]

private theorem det_firstCoordScale (a : E) : LinearMap.det (firstCoordScale a) = a := by
  rw [firstCoordScale, LinearMap.det_prodMap, LinearMap.det_smul, Module.finrank_self, pow_one,
    LinearMap.det_id, mul_one, mul_one]

end Helpers

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E]

/-- Sanity check on `E × E`: scaling the first coordinate by `a` multiplies Haar measure by
`|a|_E`. -/
example (μ : Measure (E × E)) [μ.IsAddHaarMeasure] (a : E) (s : Set (E × E)) :
    μ ((fun p : E × E ↦ (a * p.1, p.2)) '' s) =
      ((normalizedAbsoluteValue E a : ℝ≥0) : ℝ≥0∞) * μ s := by
  rw [← coe_firstCoordScale a, addHaar_image_linearMap_of_isNonarchimedeanLocalField,
    det_firstCoordScale]

/-- Sanity check on `E × E`: pushing an additive Haar measure forward along `(x, y) ↦ (a * x, y)`
(`a ≠ 0`) rescales it by `|a|_E⁻¹`. -/
example (μ : Measure (E × E)) [μ.IsAddHaarMeasure] {a : E} (ha : a ≠ 0) :
    map (fun p : E × E ↦ (a * p.1, p.2)) μ =
      ((normalizedAbsoluteValue E a : ℝ≥0)⁻¹ : ℝ≥0) • μ := by
  rw [← coe_firstCoordScale a,
    map_linearMap_addHaar_of_isNonarchimedeanLocalField μ (by rwa [det_firstCoordScale]),
    det_firstCoordScale]

/-- Sanity check on `E × E`: diagonal scaling `(x, y) ↦ (ϖ * x, y)` by a uniformizer `ϖ ∈ Eˣ`
pushes any additive Haar measure forward to `q • μ`. -/
example (μ : Measure (E × E)) [μ.IsAddHaarMeasure] {ϖ : Eˣ} (hϖ : IsUniformizer E ϖ) :
    map (fun p : E × E ↦ ((ϖ : E) * p.1, p.2)) μ = (Nat.card 𝓀[E] : ℝ≥0) • μ := by
  rw [← coe_firstCoordScale (ϖ : E),
    map_linearMap_addHaar_of_isNonarchimedeanLocalField μ
      (by rw [det_firstCoordScale]; exact ϖ.ne_zero),
    det_firstCoordScale, normalizedAbsoluteValue_coe, (isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd,
    zpow_neg_one]
  congr 1
  push_cast
  exact inv_inv _

end ProdChecks

end MeasureTheory.Measure

namespace MeasureTheory

section DistribHaarCharModule

open TauCeti

variable (E : Type*) {V G : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [AddCommGroup V] [Module E V] [Module.Finite E V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [IsModuleTopology E V]
  [Group G] [DistribMulAction G V] [SMulCommClass G E V] [ContinuousConstSMul G V]

/-- **Distributive Haar character of a linear group action.** On a finite-dimensional `E`-vector
space `V` carrying its module topology, any group `G` acting continuously and `E`-linearly on `V`
satisfies `distribHaarChar V g = |det (g • ·)|_E`. Specializes directly to `V ≃ₗ[E] V`,
`LinearMap.GeneralLinearGroup E V`, and `(V →L[E] V)ˣ`. -/
theorem distribHaarChar_eq_normalizedAbsoluteValue_det_of_isModuleTopology (g : G) :
    distribHaarChar V g =
      (normalizedAbsoluteValue E (LinearMap.det (DistribSMul.toLinearMap E V g)) : ℝ≥0) := by
  borelize V
  let K : PositiveCompacts V := Classical.arbitrary (PositiveCompacts V)
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := addHaarMeasure K) (s := (K : Set V))
    (by simp [addHaarMeasure_self]) (by simp [addHaarMeasure_self]) ?_
  rw [← Set.image_smul]
  exact Measure.addHaar_image_linearMap_of_isNonarchimedeanLocalField (addHaarMeasure K)
    (DistribSMul.toLinearMap E V g) _

end DistribHaarCharModule

end MeasureTheory

/-! ### Lattice-normalized and basis-normalized Haar measures -/

namespace Submodule.IsFullLattice

open TauCeti

variable {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [AddCommGroup V] [Module E V] [Module 𝒪[E] V]
  [IsScalarTower 𝒪[E] E V] [TopologicalSpace V] [IsModuleTopology E V]

section Lattice

variable (L : Submodule 𝒪[E] V) [L.IsFullLattice E]

/-- A full `𝒪[E]`-lattice `L` in `V` packaged as a `PositiveCompacts V`: `L` is compact and open,
and contains `0`. -/
noncomputable def positiveCompacts : PositiveCompacts V where
  carrier := (L : Set V)
  isCompact' := IsFullLattice.isCompact L
  interior_nonempty' := by
    rw [(IsFullLattice.isOpen L).interior_eq]
    exact ⟨0, L.zero_mem⟩

/-- The underlying set of `Submodule.IsFullLattice.positiveCompacts L` is `(L : Set V)`. -/
@[simp, grind =]
theorem coe_positiveCompacts : (positiveCompacts L : Set V) = (L : Set V) :=
  (rfl)

/-- Membership in `Submodule.IsFullLattice.positiveCompacts L` is membership in `L`. -/
@[simp, grind =]
theorem mem_positiveCompacts (x : V) : x ∈ positiveCompacts L ↔ x ∈ L := by
  rw [← SetLike.mem_coe, coe_positiveCompacts, SetLike.mem_coe]

section Borel

variable [MeasurableSpace V] [BorelSpace V]

/-- The canonical regular additive Haar measure on `V` normalized so that the lattice `L` has
measure one. -/
noncomputable def localAddHaar : Measure V :=
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  addHaarMeasure (positiveCompacts L)

/-- `Submodule.IsFullLattice.localAddHaar L` is `addHaarMeasure` at
`Submodule.IsFullLattice.positiveCompacts L`. -/
theorem localAddHaar_def :
    let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
    localAddHaar L = addHaarMeasure (positiveCompacts L) :=
  (rfl)

instance isAddHaarMeasure_localAddHaar : (localAddHaar L).IsAddHaarMeasure := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  rw [localAddHaar_def]
  infer_instance

instance regular_localAddHaar : (localAddHaar L).Regular := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  rw [localAddHaar_def]
  infer_instance

instance sigmaFinite_localAddHaar : SigmaFinite (localAddHaar L) := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  have : Module.Finite E V := Module.Finite.of_isFullLattice (A := E) L
  have : SecondCountableTopology V :=
    TauCeti.ModuleTopology.secondCountableTopology (Module.finBasis E V)
  rw [localAddHaar_def]
  infer_instance

/-- The lattice-normalized Haar measure gives `L` mass one. -/
@[simp, grind =]
theorem localAddHaar_self : localAddHaar L (L : Set V) = 1 := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  rw [localAddHaar_def, ← coe_positiveCompacts L]
  exact addHaarMeasure_self

/-- Every σ-finite translation-invariant measure on `V` is its mass on `L` times
`Submodule.IsFullLattice.localAddHaar L`. -/
theorem eq_smul_localAddHaar (μ : Measure V) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    μ = μ (L : Set V) • localAddHaar L := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  have : Module.Finite E V := Module.Finite.of_isFullLattice (A := E) L
  have : SecondCountableTopology V :=
    TauCeti.ModuleTopology.secondCountableTopology (Module.finBasis E V)
  rw [localAddHaar_def, ← coe_positiveCompacts L]
  exact addHaarMeasure_unique μ (positiveCompacts L)

/-- A σ-finite translation-invariant measure on `V` equals
`Submodule.IsFullLattice.localAddHaar L` if and only if it gives `L` mass one. -/
theorem eq_localAddHaar_iff (μ : Measure V) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    μ = localAddHaar L ↔ μ (L : Set V) = 1 := by
  refine ⟨fun h ↦ h ▸ localAddHaar_self L, fun h ↦ ?_⟩
  rw [eq_smul_localAddHaar L μ, h, one_smul]

/-- Pushing a lattice-normalized Haar measure forward along a linear equivalence `e : V ≃ₗ[E] W`
yields the Haar measure attached to the transported lattice
`L.map ((e : V →ₗ[E] W).restrictScalars 𝒪[E])`. -/
@[simp]
theorem map_localAddHaar {W : Type*} [AddCommGroup W] [Module E W] [Module 𝒪[E] W]
    [IsScalarTower 𝒪[E] E W] [TopologicalSpace W] [IsModuleTopology E W]
    [MeasurableSpace W] [BorelSpace W] (e : V ≃ₗ[E] W) :
    Measure.map e (localAddHaar L) =
      localAddHaar (L.map ((e : V →ₗ[E] W).restrictScalars 𝒪[E])) := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  let _ : IsTopologicalAddGroup W := IsModuleTopology.isTopologicalAddGroup E W
  let ee : V ≃L[E] W := e.toContinuousLinearEquivOfIsModuleTopology
  have _ : ((localAddHaar L).map ee).IsAddHaarMeasure :=
    ee.isAddHaarMeasure_map (localAddHaar L)
  have _ : SigmaFinite ((localAddHaar L).map ee) :=
    ee.toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have hee : ⇑ee = ⇑e := LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology e
  let L' : Submodule 𝒪[E] W := L.map ((e : V →ₗ[E] W).restrictScalars 𝒪[E])
  rw [← hee, eq_localAddHaar_iff L']
  have hpre : ee ⁻¹' (L' : Set W) = (L : Set V) := by
    ext x
    simp [L', hee]
  rw [Measure.map_apply ee.continuous.measurable (isClosed L').measurableSet, hpre,
    localAddHaar_self L]

end Borel

/-- **`GL(L)` preserves every additive Haar measure on `V`.** -/
theorem map_linearEquiv_addHaar_of_mem_stabilizer [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {T : V ≃ₗ[E] V}
    (hT : T ∈ MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V)) :
    Measure.map T μ = μ := by
  have : Module.Finite E V := Module.Finite.of_isFullLattice (A := E) L
  rw [Measure.map_linearEquiv_addHaar_of_isNonarchimedeanLocalField μ T,
    normalizedAbsoluteValue_det_eq_one_of_mem_stabilizer L hT]
  simp

end Lattice

/-- Equal lattices with separately inferred `IsFullLattice` instances define the same
`Submodule.IsFullLattice.localAddHaar`. -/
theorem localAddHaar_congr [MeasurableSpace V] [BorelSpace V]
    {L₁ L₂ : Submodule 𝒪[E] V} [L₁.IsFullLattice E] [L₂.IsFullLattice E] (h : L₁ = L₂) :
    localAddHaar L₁ = localAddHaar L₂ := by
  subst h
  rfl

end Submodule.IsFullLattice

namespace Module.Basis

open TauCeti

variable {E V ι : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [AddCommGroup V] [Module E V] [Module 𝒪[E] V]
  [IsScalarTower 𝒪[E] E V] [TopologicalSpace V] [IsModuleTopology E V]
  [Finite ι]

section BorelV

variable [MeasurableSpace V] [BorelSpace V]

/-- The regular additive Haar measure on `V` attached to a finite `E`-basis `b`, normalized so that
the `𝒪[E]`-lattice `Submodule.span 𝒪[E] (Set.range b)` has measure one. -/
noncomputable def localAddHaar (b : Basis ι E V) : Measure V :=
  Submodule.IsFullLattice.localAddHaar (Submodule.span 𝒪[E] (Set.range b))

/-- `b.localAddHaar` is `Submodule.IsFullLattice.localAddHaar` of
`Submodule.span 𝒪[E] (Set.range b)`. -/
theorem localAddHaar_def (b : Basis ι E V) :
    b.localAddHaar = Submodule.IsFullLattice.localAddHaar (Submodule.span 𝒪[E] (Set.range b)) :=
  (rfl)

instance isAddHaarMeasure_localAddHaar (b : Basis ι E V) : b.localAddHaar.IsAddHaarMeasure := by
  rw [localAddHaar_def]
  infer_instance

instance regular_localAddHaar (b : Basis ι E V) : b.localAddHaar.Regular := by
  rw [localAddHaar_def]
  infer_instance

instance sigmaFinite_localAddHaar (b : Basis ι E V) : SigmaFinite b.localAddHaar := by
  rw [localAddHaar_def]
  infer_instance

/-- Under `b.localAddHaar`, the `𝒪[E]`-span of `b` has measure one. -/
@[simp, grind =]
theorem localAddHaar_span_range (b : Basis ι E V) :
    b.localAddHaar (Submodule.span 𝒪[E] (Set.range b) : Set V) = 1 :=
  Submodule.IsFullLattice.localAddHaar_self (Submodule.span 𝒪[E] (Set.range b))

/-- Every σ-finite translation-invariant measure on `V` is its mass on the `𝒪[E]`-span of `b`
times `b.localAddHaar`. -/
theorem eq_smul_localAddHaar (b : Basis ι E V) (μ : Measure V) [SigmaFinite μ]
    [μ.IsAddLeftInvariant] :
    μ = μ (Submodule.span 𝒪[E] (Set.range b) : Set V) • b.localAddHaar :=
  Submodule.IsFullLattice.eq_smul_localAddHaar (Submodule.span 𝒪[E] (Set.range b)) μ

/-- A σ-finite translation-invariant measure on `V` equals `b.localAddHaar` if and only if it
gives the `𝒪[E]`-span of `b` mass one. -/
theorem eq_localAddHaar_iff (b : Basis ι E V) (μ : Measure V) [SigmaFinite μ]
    [μ.IsAddLeftInvariant] :
    μ = b.localAddHaar ↔ μ (Submodule.span 𝒪[E] (Set.range b) : Set V) = 1 :=
  Submodule.IsFullLattice.eq_localAddHaar_iff (Submodule.span 𝒪[E] (Set.range b)) μ

/-- Reindexing a finite basis does not change its normalized additive Haar measure. -/
@[simp, grind =]
theorem localAddHaar_reindex {ι' : Type*} [Finite ι'] (b : Basis ι E V) (e : ι ≃ ι') :
    (b.reindex e).localAddHaar = b.localAddHaar := by
  simp only [localAddHaar_def, Basis.coe_reindex, e.symm.surjective.range_comp]

/-- Pushing a basis-normalized Haar measure forward along a linear equivalence `e : V ≃ₗ[E] W`
yields the Haar measure attached to the transported basis `b.map e`. -/
@[simp]
theorem map_localAddHaar {W : Type*} [AddCommGroup W] [Module E W] [Module 𝒪[E] W]
    [IsScalarTower 𝒪[E] E W] [TopologicalSpace W] [IsModuleTopology E W]
    [MeasurableSpace W] [BorelSpace W] (b : Basis ι E V) (e : V ≃ₗ[E] W) :
    Measure.map e b.localAddHaar = (b.map e).localAddHaar := by
  have hspan :
      (Submodule.span 𝒪[E] (Set.range b)).map ((e : V →ₗ[E] W).restrictScalars 𝒪[E]) =
        Submodule.span 𝒪[E] (Set.range (b.map e)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    simp [Basis.map_apply]
  rw [localAddHaar_def, Submodule.IsFullLattice.map_localAddHaar, localAddHaar_def]
  exact Submodule.IsFullLattice.localAddHaar_congr hspan

/-- **Change-of-basis formula for normalized Haar measures.** For two finite `E`-bases `b` and `b'`
of `V` indexed by a `Fintype ι`, `b'.localAddHaar = |b.det b'|_E⁻¹ • b.localAddHaar`. -/
theorem localAddHaar_eq_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Basis ι E V) :
    b'.localAddHaar =
      ((normalizedAbsoluteValue E (b.det b') : ℝ≥0)⁻¹ : ℝ≥0) • b.localAddHaar := by
  have : Module.Finite E V := Module.Finite.of_basis b
  let T : V ≃ₗ[E] V := b.equiv b' (Equiv.refl ι)
  have hb' : b.map T = b' := by
    ext i
    simp [T]
  have hdet : LinearMap.det (T : V →ₗ[E] V) = b.det b' := b'.det_basis b
  conv_lhs => rw [← hb']
  rw [← b.map_localAddHaar T, Measure.map_linearEquiv_addHaar_of_isNonarchimedeanLocalField, hdet]

/-- **Change-of-basis invariance for valuation-one determinant.** Whenever the transition
determinant `b.det b'` has valuation one (equivalently `b.det b' ∈ 𝒪[E]ˣ` — in particular whenever
`b'` is obtained from `b` by an integral change of basis in `GL_n(𝒪[E])`),
`b'.localAddHaar = b.localAddHaar`. -/
theorem localAddHaar_eq_of_valuation_det_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Basis ι E V) (hdet : valuation E (b.det b') = 1) :
    b'.localAddHaar = b.localAddHaar := by
  have habs : normalizedAbsoluteValue E (b.det b') = 1 :=
    (normalizedAbsoluteValue_eq_one_iff _).2 hdet
  rw [localAddHaar_eq_smul b b', habs]
  simp

end BorelV

/-- On the field `E` itself, the singleton basis `Module.Basis.singleton ι E` induces
`TauCeti.localAddHaar E`. -/
@[simp]
theorem localAddHaar_singleton {E ι : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Unique ι] :
    (Basis.singleton ι E).localAddHaar = TauCeti.localAddHaar E := by
  symm
  refine (Basis.singleton ι E).eq_localAddHaar_iff _ |>.2 ?_
  have hspan :
      (Submodule.span 𝒪[E] (Set.range (Basis.singleton ι E)) : Set E) = (𝒪[E] : Set E) := by
    rw [Basis.coe_span_range]
    ext x
    simp
  rw [hspan, localAddHaar_integer]

/-- On the coordinate space `ι → E`, the standard basis `Pi.basisFun E ι` induces the product of
copies of `TauCeti.localAddHaar E`. -/
theorem localAddHaar_basisFun {E ι : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] :
    (Pi.basisFun E ι).localAddHaar = Measure.pi (fun _ : ι ↦ TauCeti.localAddHaar E) := by
  symm
  refine (Pi.basisFun E ι).eq_localAddHaar_iff _ |>.2 ?_
  have hbox : (Submodule.span 𝒪[E] (Set.range (Pi.basisFun E ι)) : Set (ι → E)) =
      integerBox E ι := by
    rw [Basis.coe_span_range, integerBox_def]
    ext x
    simp
  rw [hbox, integerBox_def, Measure.pi_pi]
  simp

end Module.Basis
