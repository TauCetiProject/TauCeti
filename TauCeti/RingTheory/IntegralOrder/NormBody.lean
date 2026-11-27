/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.RingTheory.Discriminant.Regular
public import TauCeti.RingTheory.IntegralOrder.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import TauCeti.LinearAlgebra.TensorProduct.Basis
import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# The regular norm body of a rational algebra

In real coordinates for a rational basis, consider the open sublevel set of the absolute
regular norm. Its bounded symmetric convex subsets can be used in Minkowski's theorem,
even when the norm region itself is unbounded or nonconvex. The supremum of their volumes
becomes independent of the rational basis after multiplication by the square root of the
absolute regular discriminant. This normalization is used in estimates for the class
index of orders in division algebras.

## References

* D. Masser and G. Wüstholz, *Factorization estimates for abelian varieties*, §2, pp. 8–10.
-/

public section

open MeasureTheory Module Set
open scoped ENNReal TensorProduct

namespace Module.Basis

variable {ι D : Type*} [Fintype ι] [Ring D] [Algebra ℚ D]

/-- The open region where the absolute regular norm is less than one, in the real
coordinates induced by a rational basis. -/
noncomputable def regularNormRegion (b : Basis ι ℚ D) : Set (ι → ℝ) :=
  {x | |Algebra.norm ℝ ((b.baseChange ℝ).equivFun.symm x)| < 1}

/-- Membership in the norm region is the strict absolute regular-norm inequality. -/
@[simp]
theorem mem_regularNormRegion (b : Basis ι ℚ D) (x : ι → ℝ) :
    x ∈ b.regularNormRegion ↔ |Algebra.norm ℝ ((b.baseChange ℝ).equivFun.symm x)| < 1 :=
  Iff.rfl

/-- The supremum of the volumes of bounded, symmetric convex bodies with nonempty interior
in the regular norm region, measured in the given coordinates. -/
noncomputable def regularNormBodyVolume (b : Basis ι ℚ D) : ℝ≥0∞ :=
  ⨆ s : {s : Set (ι → ℝ) // Bornology.IsBounded s ∧ Convex ℝ s ∧
    (interior s).Nonempty ∧ (∀ x ∈ s, -x ∈ s) ∧ s ⊆ b.regularNormRegion}, volume s.val

/-- Every admissible body gives a lower bound on the norm-body volume. -/
theorem volume_le_regularNormBodyVolume (b : Basis ι ℚ D) {s : Set (ι → ℝ)}
    (hb : Bornology.IsBounded s) (hc : Convex ℝ s) (hi : (interior s).Nonempty)
    (hs : ∀ x ∈ s, -x ∈ s) (hn : s ⊆ b.regularNormRegion) :
    volume s ≤ b.regularNormBodyVolume :=
  le_iSup_of_le ⟨s, hb, hc, hi, hs, hn⟩ le_rfl

/-- A bound on the volumes of all admissible bodies bounds their supremum. -/
theorem regularNormBodyVolume_le_iff (b : Basis ι ℚ D) {v : ℝ≥0∞} :
    b.regularNormBodyVolume ≤ v ↔
      ∀ s : Set (ι → ℝ), Bornology.IsBounded s → Convex ℝ s →
        (interior s).Nonempty → (∀ x ∈ s, -x ∈ s) →
        s ⊆ b.regularNormRegion → volume s ≤ v := by
  simp only [regularNormBodyVolume, iSup_le_iff, Subtype.forall, and_imp]

/-- The regular norm region is open in the real coordinate space. -/
theorem isOpen_regularNormRegion (b : Basis ι ℚ D) : IsOpen b.regularNormRegion := by
  classical
  let c := b.baseChange ℝ
  let f := (LinearMap.toMatrix c c).comp
    ((Algebra.lmul ℝ (ℝ ⊗[ℚ] D)).toLinearMap.comp c.equivFun.symm.toLinearMap)
  have hf := f.continuous_of_finiteDimensional.matrix_det.abs
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
    regularNormRegion, Algebra.norm_apply, LinearMap.det_toMatrix] using
      (isOpen_lt hf (continuous_const (y := (1 : ℝ))))

/-- The norm-body volume is positive for every rational basis of a nontrivial algebra. -/
theorem regularNormBodyVolume_pos [Nontrivial D] (b : Basis ι ℚ D) :
    0 < b.regularNormBodyVolume := by
  classical
  have := Module.Finite.of_basis b
  have hzero : (0 : ι → ℝ) ∈ b.regularNormRegion := by
    have : Nontrivial (ℝ ⊗[ℚ] D) :=
      (Algebra.TensorProduct.includeRight_injective (B := D) (algebraMap ℚ ℝ).injective).nontrivial
    simp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp b.isOpen_regularNormRegion (0 : ι → ℝ) hzero
  have hpos : 0 < volume (Metric.ball (0 : ι → ℝ) r) :=
    Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.2 hr)
  refine hpos.trans_le (b.volume_le_regularNormBodyVolume Metric.isBounded_ball
    (convex_ball 0 r) ?_ ?_ hball)
  · rw [Metric.isOpen_ball.interior_eq]
    exact Metric.nonempty_ball.2 hr
  · intro x hx
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hx

private theorem mul_regularNormBodyVolume_le_of_image {κ : Type*} [Fintype κ]
    (b : Basis ι ℚ D) (c : Basis κ ℚ D) (e : (ι → ℝ) ≃L[ℝ] (κ → ℝ)) (d : ℝ≥0∞)
    (hr : ∀ x ∈ b.regularNormRegion, e x ∈ c.regularNormRegion)
    (hv : ∀ s : Set (ι → ℝ), volume (e '' s) = d * volume s) :
    d * b.regularNormBodyVolume ≤ c.regularNormBodyVolume := by
  rw [regularNormBodyVolume, ENNReal.mul_iSup, iSup_le_iff]
  rintro ⟨s, hb, hc, hi, hs, hn⟩
  rw [← hv]
  refine c.volume_le_regularNormBodyVolume
    (e.toContinuousLinearMap.lipschitzWith.isBounded_image hb)
    (hc.linear_image e.toLinearEquiv.toLinearMap) ?_ ?_ ?_
  · exact (e.toHomeomorph.image_interior s) ▸ hi.image e
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hs x hx, map_neg e x⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hr x (hn hx)

private theorem det_mul_regularNormBodyVolume_le [DecidableEq ι] (b c : Basis ι ℚ D) :
    ENNReal.ofReal |((b.toMatrix c).det : ℝ)| * c.regularNormBodyVolume ≤
      b.regularNormBodyVolume := by
  let e := ((c.baseChange ℝ).equivFun.symm.trans (b.baseChange ℝ).equivFun).toContinuousLinearEquiv
  have he : LinearMap.det e.toLinearEquiv.toLinearMap = ((b.toMatrix c).det : ℝ) := by
    have hmat : LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι) e.toLinearEquiv.toLinearMap =
        (b.toMatrix c).map (fun q => (q : ℝ)) := by
      ext i j
      simp [e, Basis.toMatrix_apply]
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ ι), hmat, Rat.cast_det]
  refine c.mul_regularNormBodyVolume_le_of_image b e _ ?_ ?_
  · intro x hx
    simpa only [mem_regularNormRegion, e, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hx
  · intro s
    rw [Measure.addHaar_image_continuousLinearEquiv, he]

/-- The volume in coordinates `b` equals the volume in coordinates `c` multiplied by the absolute
determinant of `b.toMatrix c`, whose columns are the vectors of `c` in coordinates `b`. -/
theorem regularNormBodyVolume_eq_det_mul [DecidableEq ι] (b c : Basis ι ℚ D) :
    b.regularNormBodyVolume = ENNReal.ofReal |((b.toMatrix c).det : ℝ)| *
      c.regularNormBodyVolume := by
  refine le_antisymm ?_ (det_mul_regularNormBodyVolume_le b c)
  have hd : ((b.toMatrix c).det : ℝ) * ((c.toMatrix b).det : ℝ) = 1 := by
    exact_mod_cast (by rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self,
      Matrix.det_one] : (b.toMatrix c).det * (c.toMatrix b).det = 1)
  have h : ENNReal.ofReal |((b.toMatrix c).det : ℝ)| *
      (ENNReal.ofReal |((c.toMatrix b).det : ℝ)| * b.regularNormBodyVolume) ≤
      ENNReal.ofReal |((b.toMatrix c).det : ℝ)| * c.regularNormBodyVolume := by
    gcongr
    exact det_mul_regularNormBodyVolume_le c b
  rwa [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, hd, abs_one,
    ENNReal.ofReal_one, one_mul] at h

private theorem regularNormBodyVolume_le_reindex {κ : Type*} [Fintype κ]
    (b : Basis ι ℚ D) (σ : ι ≃ κ) :
    b.regularNormBodyVolume ≤ (b.reindex σ).regularNormBodyVolume := by
  let e := ContinuousLinearEquiv.piCongrLeft (R := ℝ) (fun _ : κ => ℝ) σ
  have he (x : ι → ℝ) (i : ι) : e x (σ i) = x i := by
    simp [e, ContinuousLinearEquiv.piCongrLeft]
  have hvol := volume_measurePreserving_piCongrLeft (fun _ : κ => ℝ) σ
  rw [← one_mul b.regularNormBodyVolume]
  refine b.mul_regularNormBodyVolume_le_of_image (b.reindex σ) e 1 ?_ ?_
  · intro x hx
    have hcoord : ((b.reindex σ).baseChange ℝ).equivFun.symm (e x) =
        (b.baseChange ℝ).equivFun.symm x := by
      rw [Basis.baseChange_reindex]
      apply ((b.baseChange ℝ).reindex σ).equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      funext j
      obtain ⟨i, rfl⟩ := σ.surjective j
      rw [he, Basis.equivFun_apply, Basis.repr_reindex_apply,
        Equiv.symm_apply_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simpa only [mem_regularNormRegion, hcoord] using hx
  · intro s
    rw [one_mul]
    let eₘ := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ
    rw [← hvol.map_eq, eₘ.map_apply]
    congr 1
    exact eₘ.toEquiv.preimage_image s

/-- Permuting or renaming the basis indices preserves the coordinate volume. -/
@[simp]
theorem regularNormBodyVolume_reindex {κ : Type*} [Fintype κ]
    (b : Basis ι ℚ D) (σ : ι ≃ κ) :
    (b.reindex σ).regularNormBodyVolume = b.regularNormBodyVolume := by
  refine le_antisymm ?_ (regularNormBodyVolume_le_reindex b σ)
  have he : (b.reindex σ).reindex σ.symm = b := by
    ext i
    simp
  simpa only [he] using regularNormBodyVolume_le_reindex (b.reindex σ) σ.symm

/-- Multiplying by the square root of the absolute regular discriminant cancels the
change in coordinate volume. -/
theorem sqrt_regularDiscr_mul_regularNormBodyVolume_eq [DecidableEq ι] (b c : Basis ι ℚ D) :
    ENNReal.ofReal (Real.sqrt |(Algebra.regularDiscr ℚ b : ℝ)|) * b.regularNormBodyVolume =
      ENNReal.ofReal (Real.sqrt |(Algebra.regularDiscr ℚ c : ℝ)|) * c.regularNormBodyVolume := by
  classical
  have hd : (Algebra.regularDiscr ℚ c : ℝ) =
      ((b.toMatrix c).det : ℝ) ^ 2 * (Algebra.regularDiscr ℚ b : ℝ) := by
    exact_mod_cast Algebra.regularDiscr_eq_det_toMatrix_sq_mul b c
  rw [regularNormBodyVolume_eq_det_mul b c, hd, abs_mul, abs_pow,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _), ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    mul_comm (Real.sqrt _)]

/-- Transporting the basis by an algebra equivalence preserves its norm region. -/
@[simp]
theorem regularNormRegion_map {E : Type*} [Ring E] [Algebra ℚ E]
    (b : Basis ι ℚ D) (e : D ≃ₐ[ℚ] E) :
    (b.map e.toLinearEquiv).regularNormRegion = b.regularNormRegion := by
  classical
  have he (y : D) : e.toLinearEquiv.symm (e y) = y := e.toLinearEquiv.symm_apply_apply y
  ext x
  simp only [mem_regularNormRegion, norm_baseChange_equivFun_symm, Basis.map_apply,
    AlgEquiv.toLinearEquiv_apply, ← map_mul e, Basis.map_repr, LinearEquiv.trans_apply, he]

/-- Transporting the basis by an algebra equivalence preserves its coordinate volume. -/
@[simp]
theorem regularNormBodyVolume_map {E : Type*} [Ring E] [Algebra ℚ E]
    (b : Basis ι ℚ D) (e : D ≃ₐ[ℚ] E) :
    (b.map e.toLinearEquiv).regularNormBodyVolume = b.regularNormBodyVolume := by
  apply le_antisymm
  · refine ((b.map e.toLinearEquiv).regularNormBodyVolume_le_iff).2 fun s hb hc hi hs hn => ?_
    exact b.volume_le_regularNormBodyVolume hb hc hi hs (by rwa [regularNormRegion_map] at hn)
  · refine b.regularNormBodyVolume_le_iff.2 fun s hb hc hi hs hn => ?_
    exact (b.map e.toLinearEquiv).volume_le_regularNormBodyVolume hb hc hi hs
      (by rwa [regularNormRegion_map])

end Module.Basis

namespace Module.Basis

variable {ι D : Type*} [DivisionRing D] [Algebra ℚ D]

/-- If every structure constant of `b` is an integer, the coordinate volume supremum is at most
`2 ^ Fintype.card ι`. -/
theorem regularNormBodyVolume_le_two_pow [Fintype ι] (b : Basis ι ℚ D)
    (h : ∀ i j k, ∃ z : ℤ, (z : ℚ) = b.repr (b k * b j) i) :
    b.regularNormBodyVolume ≤ 2 ^ Fintype.card ι := by
  classical
  refine (b.regularNormBodyVolume_le_iff).2 fun s _ hc _ hs hn => ?_
  by_contra! hvol
  let c := Pi.basisFun ℝ ι
  have hfund := ZSpan.isAddFundamentalDomain' c volume
  have hmeasure : volume (ZSpan.fundamentalDomain c) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp
  have hlarge : volume (ZSpan.fundamentalDomain c) * 2 ^ finrank ℝ (ι → ℝ) < volume s := by
    simpa [hmeasure, Module.finrank_pi] using hvol
  have : Countable (Submodule.span ℤ (range c)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (range c)))
  obtain ⟨y, hy, hys⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    hfund hs hc hlarge
  have hyint (i : ι) : ∃ z : ℤ, (z : ℝ) = (y : ι → ℝ) i := by
    obtain ⟨z, hz⟩ := (c.mem_span_iff_repr_mem ℤ (y : ι → ℝ)).mp y.property i
    exact ⟨z, by simpa [c] using hz⟩
  choose z hz using hyint
  have hz' : z ≠ 0 := by
    intro he
    apply hy
    apply Subtype.ext
    simp [← funext hz, he, Pi.zero_def]
  exact (not_lt_of_ge (b.one_le_abs_norm_baseChange_intCast h z hz'))
    (by simpa only [funext hz, mem_regularNormRegion] using hn hys)

/-- The volume supremum is finite for every rational basis of a division algebra. -/
theorem regularNormBodyVolume_ne_top [Fintype ι] (b : Basis ι ℚ D) :
    b.regularNormBodyVolume ≠ ⊤ := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun t : ι × ι × ι => b.repr (b t.2.2 * b t.2.1) t.1)
  have hd0 : (d : ℤ) ≠ 0 := nonZeroDivisors.ne_zero d.property
  let u := Units.mk0 ((d : ℤ) : ℚ) (Int.cast_ne_zero.mpr hd0)
  let c := b.unitsSMul (fun _ => u)
  have hc (i j k : ι) : ∃ z : ℤ, (z : ℚ) = c.repr (c k * c j) i := by
    obtain ⟨z, hz⟩ := hd (i, j, k)
    refine ⟨z, ?_⟩
    have hz' : (z : ℚ) = (u : ℚ) * b.repr (b k * b j) i := by
      simpa [Algebra.smul_def, u] using hz
    rw [hz']
    simp only [c, Basis.unitsSMul_apply, Basis.repr_unitsSMul, Units.smul_def, smul_mul_assoc,
      mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hu : (u : ℚ) * (↑u⁻¹ : ℚ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hcancel (q : ℚ) : (u : ℚ) * ((↑u⁻¹ : ℚ) * q) = q := by
      rw [← mul_assoc, hu, one_mul]
    simp only [hcancel]
  rw [b.regularNormBodyVolume_eq_det_mul c]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (c.regularNormBodyVolume_le_two_pow hc))

end Module.Basis

namespace TauCeti

open Module

variable (D : Type*) [DivisionRing D] [Algebra ℚ D] [FiniteDimensional ℚ D]

/-- Masser–Wüstholz's volume invariant of a rational division algebra. The discriminant
factor normalizes the supremal volume of a symmetric convex body in the norm region. -/
noncomputable def regularNormBodyInvariant : ℝ :=
  let b := Module.finBasis ℚ D
  Real.sqrt |(Algebra.regularDiscr ℚ b : ℝ)| * b.regularNormBodyVolume.toReal

variable {D}

/-- The normalized volume can be evaluated in any rational basis. -/
theorem regularNormBodyInvariant_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ D) :
    regularNormBodyInvariant D =
      Real.sqrt |(Algebra.regularDiscr ℚ b : ℝ)| * b.regularNormBodyVolume.toReal := by
  let σ := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  unfold regularNormBodyInvariant
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Basis.regularNormBodyVolume_reindex, Basis.coe_reindex, Algebra.regularDiscr_reindex] using
    congrArg ENNReal.toReal
      ((Module.finBasis ℚ D).sqrt_regularDiscr_mul_regularNormBodyVolume_eq (b.reindex σ))

/-- The normalized volume is strictly positive. -/
theorem regularNormBodyInvariant_pos : 0 < regularNormBodyInvariant D := by
  let b := Module.finBasis ℚ D
  have hb : Algebra.regularDiscr ℚ b ≠ 0 := by
    rw [Algebra.regularDiscr_eq_det_toMatrix_regularTraceForm,
      ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
    exact nondegenerate_regularTraceForm
  rw [regularNormBodyInvariant_eq b]
  exact mul_pos (Real.sqrt_pos.2 (abs_pos.2 (Rat.cast_ne_zero.mpr hb)))
    (ENNReal.toReal_pos b.regularNormBodyVolume_pos.ne' b.regularNormBodyVolume_ne_top)

/-- Isomorphic rational division algebras have the same normalized norm-body volume. -/
theorem regularNormBodyInvariant_congr {E : Type*} [DivisionRing E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] (e : D ≃ₐ[ℚ] E) :
    regularNormBodyInvariant D = regularNormBodyInvariant E := by
  let b := Module.finBasis ℚ D
  have hdiscr : Algebra.regularDiscr ℚ (b.map e.toLinearEquiv) = Algebra.regularDiscr ℚ b := by
    rw [Basis.coe_map, Algebra.regularDiscr_def, Algebra.regularDiscr_def]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, AlgEquiv.toLinearEquiv_apply]
    exact Algebra.regularTraceForm_algHom_apply e.toAlgHom e.injective
      e.toLinearEquiv.finrank_eq (b i) (b j)
  rw [regularNormBodyInvariant_eq b, regularNormBodyInvariant_eq (b.map e.toLinearEquiv),
    hdiscr, Basis.regularNormBodyVolume_map]

namespace IntegralOrder.IsOrder

/-- Minkowski's theorem bounds the normalized norm-body volume in terms of the regular
discriminant of any full order. -/
theorem regularNormBodyInvariant_le {O : Subalgebra ℤ D} (hO : IsOrder ℚ O)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ O) :
    regularNormBodyInvariant D ≤
      2 ^ finrank ℚ D * Real.sqrt |(Algebra.regularDiscr ℤ b : ℝ)| := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have hspan : Submodule.span ℚ (Set.range O.val) = ⊤ := by simpa using hO.span_eq_top
  let c := b.ofFractionRingOfSpan O.val.toLinearMap Subtype.val_injective hspan
  have hcoord (i : ι) : c i = O.val (b i) :=
    Basis.ofFractionRingOfSpan_apply b O.val.toLinearMap Subtype.val_injective hspan i
  have hdiscr : (Algebra.regularDiscr ℚ c : ℝ) = (Algebra.regularDiscr ℤ b : ℝ) := by
    have hval : O.val ∘ b = c := funext fun i => (hcoord i).symm
    rw [← hval, ← Algebra.algebraMap_regularDiscr O.val Subtype.val_injective hspan]
    norm_cast
  have hc (i j k : ι) : ∃ z : ℤ, (z : ℚ) = c.repr (c k * c j) i := by
    refine ⟨b.repr (b k * b j) i, ?_⟩
    have hmul : c k * c j = O.val (b k * b j) := by rw [hcoord, hcoord, map_mul]
    rw [hmul]
    exact (Basis.ofFractionRingOfSpan_repr_apply b O.val.toLinearMap Subtype.val_injective
      hspan (b k * b j) i).symm
  have hv : c.regularNormBodyVolume.toReal ≤ 2 ^ finrank ℚ D := by
    have h := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (c.regularNormBodyVolume_le_two_pow hc)
    simpa [finrank_eq_card_basis c, ENNReal.toReal_pow] using h
  rw [regularNormBodyInvariant_eq c, hdiscr, mul_comm]
  gcongr

end IntegralOrder.IsOrder

end TauCeti
