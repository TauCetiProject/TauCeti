/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import TauCeti.NumberTheory.Height.Arakelov.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Extension
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compatibility
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import TauCeti.NumberTheory.NumberField.Global.Places.Basic

/-!
# Adelic heights over number fields

For an invertible adelic matrix `A : GL ι (AdeleRing (𝓞 K) K)` and a vector `x : ι → L` over
a finite extension `L / K`, `TauCeti.adelicHeight A x` is the adelic twisted height combining the
`ℓ²` norms of `(A *ᵥ x)_w` at the infinite places `w` of `L` and the `ℓ^∞` norms at the finite
places `v` of `L`, degree-normalized by `[L : ℚ]`.

## Main definitions

* `TauCeti.adelicHeight`: the adelic height of `x : ι → L` twisted by
  `A : GL ι (AdeleRing (𝓞 K) K)`.

## Main results

* `TauCeti.adelicHeight_nonneg`, `TauCeti.adelicHeight_pos`: nonnegativity and strict positivity
  for nonzero vectors.
* `TauCeti.adelicHeight_zero`, `TauCeti.adelicHeight_eq_zero_iff`: characterization of vanishing
  at `x = 0`.
* `TauCeti.adelicHeight_smul`: projective invariance under `Lˣ`.
* `TauCeti.adelicHeight_one`: specialization to `L = K` and `A = 1` recovers `TauCeti.height2`.
* `TauCeti.adelicHeight_reindex`: invariance under simultaneous row and column reindexing.
* `TauCeti.adelicHeight_unique`: for `[Unique ι]`, `adelicHeight A x` equals
  `(ideleNorm (det A)) ^ ([K : ℚ]⁻¹)`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §2.8.
* J. Vaaler and E. Bombieri, *On Siegel's lemma*, Invent. Math. 73 (1983), 11–32.
-/

public section

open Function IsDedekindDomain Module NumberField TauCeti.GlobalNumberFields
open scoped NumberField NNReal

namespace TauCeti

private noncomputable def infPlaceHom (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (w : InfinitePlace L) :
    AdeleRing (𝓞 K) K →+* w.Completion :=
  (Pi.evalRingHom (fun w : InfinitePlace L ↦ w.Completion) w).comp
    ((RingHom.fst _ _).comp (adeleExtension (𝓞 K) K (𝓞 L) L))

private noncomputable def finPlaceHom (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 L)) :
    AdeleRing (𝓞 K) K →+* v.adicCompletion L :=
  (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L) ↦ v.adicCompletion L) v).comp
    ((RingHom.snd _ _).comp (adeleExtension (𝓞 K) K (𝓞 L) L))

/-- The adelic height of a vector `x : ι → L` twisted by an invertible adelic matrix
`A : GL ι (AdeleRing (𝓞 K) K)` over `K ⊆ L`: the product over infinite places `w` of `L` of the
`ℓ²` norm of `A_w x` raised to `w.mult / (2 [L : ℚ])` times the `finprod` over finite places `v`
of `L` of the `ℓ^∞` norm raised to `1 / [L : ℚ]`. -/
noncomputable def adelicHeight {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) : ℝ :=
  (∏ w : InfinitePlace L,
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
          (x j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L))) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 L),
      (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L)

/-- Defining equation of `TauCeti.adelicHeight`. -/
theorem adelicHeight_def {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) :
    adelicHeight A x =
      (∏ w : InfinitePlace L,
          (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
              (x j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L))) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 L),
          (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
            algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) :=
  (rfl)

/-- Every adelic height is nonnegative. -/
theorem adelicHeight_nonneg {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) :
    0 ≤ adelicHeight A x := by
  refine mul_nonneg (Finset.prod_nonneg fun w _ ↦ ?_) (finprod_nonneg fun v ↦ ?_)
  · exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) _
  · exact Real.rpow_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) _

/-- The adelic height of the zero vector is `0`. -/
@[simp]
theorem adelicHeight_zero {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) :
    adelicHeight (L := L) A 0 = 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have hexp : (w.mult : ℝ) / (2 * finrank ℚ L) ≠ 0 := by
    have hm : (0 : ℝ) < w.mult := Nat.cast_pos.mpr InfinitePlace.mult_pos
    have hD : (0 : ℝ) < finrank ℚ L := Nat.cast_pos.mpr finrank_pos
    positivity
  have hzero :
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
          ((0 : L) : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) = 0 := by
    simp [Real.zero_rpow hexp]
  rw [adelicHeight_def, Finset.prod_eq_zero (Finset.mem_univ w) hzero, zero_mul]

private theorem finprod_rpow {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (r : ℝ) :
    (∏ᶠ a, f a) ^ r = ∏ᶠ a, f a ^ r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  let g : α → ℝ≥0 := fun a ↦ ⟨f a, hf a⟩
  have hcoe : ((∏ᶠ a, g a : ℝ≥0) : ℝ) = ∏ᶠ a, f a :=
    (NNReal.toRealHom : ℝ≥0 →* ℝ).map_finprod_of_injective NNReal.coe_injective g
  have hcoe2 : ((∏ᶠ a, g a ^ r : ℝ≥0) : ℝ) = ∏ᶠ a, f a ^ r :=
    ((NNReal.toRealHom : ℝ≥0 →* ℝ).map_finprod_of_injective NNReal.coe_injective
      (fun a ↦ g a ^ r)).trans (finprod_congr fun a ↦ NNReal.coe_rpow (g a) r)
  have hpow : (∏ᶠ a, g a) ^ r = ∏ᶠ a, g a ^ r :=
    (NNReal.rpowMonoidHom r).map_finprod_of_injective (NNReal.rpow_left_injective hr) g
  rw [← hcoe, ← NNReal.coe_rpow, hpow, hcoe2]

private theorem hasFiniteMulSupport_norm_algebraMap {L : Type*} [Field L] [NumberField L]
    {c : L} (hc : c ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      ‖algebraMap L (v.adicCompletion L) c‖ := by
  simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply, ← normalizedAbsValue_inl_eq_norm_coe,
    normalizedAbsValue_inl] using hasFiniteMulSupport_adicAbv hc

private theorem eventually_norm_adeleExtension_le_one {K L ι : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Finite ι]
    (M : Matrix ι ι (AdeleRing (𝓞 K) K)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∀ i j, ‖(adeleExtension (𝓞 K) K (𝓞 L) L (M i j)).2 v‖ ≤ 1 := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  filter_upwards [(adeleExtension (𝓞 K) K (𝓞 L) L (M i j)).2.prop] with v hv
  exact Valued.toNormedField.norm_le_one_iff.mpr hv

private theorem eventually_norm_algebraMap_le_one {L ι : Type*} [Field L] [NumberField L]
    [Finite ι] (x : ι → L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∀ j, ‖algebraMap L (v.adicCompletion L) (x j)‖ ≤ 1 := by
  rw [Filter.eventually_all]
  intro j
  rcases eq_or_ne (x j) 0 with h0 | hne
  · simp [h0]
  · have hne_ev : ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
        ‖algebraMap L (v.adicCompletion L) (x j)‖ = 1 :=
      Filter.eventually_cofinite.mpr (hasFiniteMulSupport_norm_algebraMap hne)
    filter_upwards [hne_ev] with v hv
    exact hv.le

private theorem mulVec_infPlaceHom_eq {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (w : InfinitePlace L) (B : GL ι (AdeleRing (𝓞 K) K))
    (y : ι → w.Completion) (i : ι) :
    Matrix.mulVec (Matrix.GeneralLinearGroup.map (infPlaceHom K L w) B).val y i =
      ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (B.val i j)).1 w * y j :=
  rfl

private theorem mulVec_finPlaceHom_eq {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum (𝓞 L)) (B : GL ι (AdeleRing (𝓞 K) K))
    (y : ι → v.adicCompletion L) (i : ι) :
    Matrix.mulVec (Matrix.GeneralLinearGroup.map (finPlaceHom K L v) B).val y i =
      ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (B.val i j)).2 v * y j :=
  rfl

/-- For an invertible adelic matrix and a nonzero vector, the finite-place factors of `A *ᵥ x`
equal `1` at all but finitely many places. -/
theorem hasFiniteMulSupport_adelicHeight {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {x : ι → L} (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      ⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖ := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨j₀⟩
  have hj₀_ev : ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ‖algebraMap L (v.adicCompletion L) (x j₀)‖ = 1 :=
    Filter.eventually_cofinite.mpr (hasFiniteMulSupport_norm_algebraMap hj₀)
  refine Filter.eventually_cofinite.mp ?_
  filter_upwards [eventually_norm_adeleExtension_le_one (L := L) A.val,
    eventually_norm_adeleExtension_le_one (L := L) A⁻¹.val,
    eventually_norm_algebraMap_le_one x, hj₀_ev] with v hAv hBv hxv hvj₀
  let Av := Matrix.GeneralLinearGroup.map (finPlaceHom K L v) A
  let xv : ι → v.adicCompletion L := fun j ↦ algebraMap L (v.adicCompletion L) (x j)
  apply le_antisymm
  · refine ciSup_le fun i ↦ IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      zero_le_one fun j _ ↦ ?_
    rw [norm_mul]
    exact (mul_le_mul (hAv i j) (hxv j) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · have hmulVec : Matrix.mulVec Av⁻¹.val (Matrix.mulVec Av.val xv) = xv := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← hvj₀, show algebraMap L (v.adicCompletion L) (x j₀) = xv j₀ from rfl,
      ← congrFun hmulVec j₀, Matrix.mulVec, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (Real.iSup_nonneg fun _ ↦ norm_nonneg _) fun k _ ↦ ?_
    rw [norm_mul, show Av⁻¹.val j₀ k = finPlaceHom K L v (A⁻¹.val j₀ k) by
        rw [← map_inv]; rfl]
    refine (mul_le_mul (hBv j₀ k) ?_ (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    rw [mulVec_finPlaceHom_eq v A xv k]
    exact le_ciSup (Set.Finite.bddAbove (Set.finite_range fun i : ι ↦
      ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v * xv j‖)) k

private theorem exists_mulVec_map_ne_zero {K L F ι : Type*} [Field K] [NumberField K]
    [Field L] [Field F] [Fintype ι] [DecidableEq ι] (φ : AdeleRing (𝓞 K) K →+* F)
    (ψ : L →+* F) (A : GL ι (AdeleRing (𝓞 K) K)) {x : ι → L} (hx : x ≠ 0) :
    ∃ i₀, Matrix.mulVec (Matrix.GeneralLinearGroup.map φ A).val (fun j ↦ ψ (x j)) i₀ ≠ 0 := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  have hxy : (fun j ↦ ψ (x j)) ≠ 0 :=
    fun h ↦ hj₀ (ψ.injective ((congrFun h j₀).trans (map_zero _).symm))
  exact Function.ne_iff.mp fun h ↦ hxy <| Matrix.mulVec_injective_iff_isUnit.mpr
    (Matrix.GeneralLinearGroup.map φ A).isUnit (h.trans (Matrix.mulVec_zero _).symm)

/-- The adelic height of any nonzero vector is strictly positive. -/
theorem adelicHeight_pos {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {x : ι → L} (hx : x ≠ 0) :
    0 < adelicHeight A x := by
  have hinf : ∀ w : InfinitePlace L,
      0 < (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
        (x j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) := by
    intro w
    obtain ⟨i₀, hi₀⟩ :=
      exists_mulVec_map_ne_zero (infPlaceHom K L w) (algebraMap L w.Completion) A hx
    have hcongr : ∀ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
        (x j : w.Completion)‖ ^ 2 =
        ‖Matrix.mulVec (Matrix.GeneralLinearGroup.map (infPlaceHom K L w) A).val
          (fun j ↦ algebraMap L w.Completion (x j)) i‖ ^ 2 := fun i ↦ by
      simp_rw [InfinitePlace.Completion.algebraMap_apply_eq_coe]
      rw [← mulVec_infPlaceHom_eq w A (fun j ↦ (x j : w.Completion)) i]
    have hsum_pos : 0 < ∑ i, ‖Matrix.mulVec
        (Matrix.GeneralLinearGroup.map (infPlaceHom K L w) A).val
          (fun j ↦ algebraMap L w.Completion (x j)) i‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
        ⟨i₀, Finset.mem_univ i₀, sq_pos_iff.mpr (norm_ne_zero_iff.mpr hi₀)⟩
    simpa only [hcongr] using Real.rpow_pos_of_pos hsum_pos _
  have hsupp : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) :=
    HasFiniteMulSupport.fun_comp (hasFiniteMulSupport_adelicHeight A hx)
      (g := fun t : ℝ ↦ t ^ ((1 : ℝ) / finrank ℚ L)) (Real.one_rpow _)
  have hfin : ∀ v ∈ hsupp.toFinset,
      0 < (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) := by
    intro v _
    obtain ⟨i₀, hi₀⟩ := exists_mulVec_map_ne_zero (finPlaceHom K L v)
      (algebraMap L (v.adicCompletion L)) A hx
    have hnorm_pos : 0 < ⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L
        ((A : Matrix ι ι _) i j)).2 v * algebraMap L (v.adicCompletion L) (x j)‖ := by
      have hi₀' : 0 < ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i₀ j)).2 v *
          algebraMap L (v.adicCompletion L) (x j)‖ := by
        rw [← mulVec_finPlaceHom_eq v A (fun j ↦ algebraMap L (v.adicCompletion L) (x j)) i₀]
        exact norm_pos_iff.mpr hi₀
      exact hi₀'.trans_le <| le_ciSup (Set.Finite.bddAbove (Set.finite_range fun i : ι ↦
        ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
          algebraMap L (v.adicCompletion L) (x j)‖)) i₀
    exact Real.rpow_pos_of_pos hnorm_pos _
  rw [adelicHeight_def, finprod_eq_prod _ hsupp]
  exact mul_pos (Finset.prod_pos fun w _ ↦ hinf w) (Finset.prod_pos hfin)

/-- The adelic height of a vector vanishes if and only if the vector is `0`. -/
@[simp]
theorem adelicHeight_eq_zero_iff {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {x : ι → L} :
    adelicHeight A x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ (adelicHeight_pos A hx).ne' h, fun hx ↦ by simp [hx]⟩

private theorem adelicHeight_archimedean_smul {K L ι : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) (c : L) :
    (∏ w : InfinitePlace L,
        (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
            ((c • x) j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L))) =
      (∏ w : InfinitePlace L, normAbs (Sum.inr w) c) *
        ∏ w : InfinitePlace L,
          (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
              (x j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) := by
  have hc_term : ∀ w : InfinitePlace L,
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
          ((c • x) j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) =
        normAbs (Sum.inr w) c *
          (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
              (x j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) := by
    intro w
    let xw : ι → w.Completion := fun j ↦ (x j : w.Completion)
    have hsmul : (fun j ↦ ((c • x) j : w.Completion)) = (c : w.Completion) • xw := funext fun j ↦
      by simp [xw, ← InfinitePlace.Completion.algebraMap_apply_eq_coe]
    have hmul : ∀ i,
        ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w *
            ((c • x) j : w.Completion)‖ ^ 2 =
          ‖(c : w.Completion)‖ ^ 2 *
            ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).1 w * xw j‖ ^ 2 := by
      intro i
      rw [← mulVec_infPlaceHom_eq w A _ i, hsmul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
        mulVec_infPlaceHom_eq w A xw i, norm_mul, mul_pow]
    simp_rw [hmul, ← Finset.mul_sum]
    rw [Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), normAbs_inr,
      ← InfinitePlace.Completion.norm_algebraMap w c,
      InfinitePlace.Completion.algebraMap_apply_eq_coe, ← Real.rpow_natCast ‖(c : w.Completion)‖ 2,
      ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  simp_rw [hc_term, Finset.prod_mul_distrib]

private theorem adelicHeight_finite_smul {K L ι : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) {c : L} (hc : c ≠ 0)
    (hsupp : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      ⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 L),
        (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
          algebraMap L (v.adicCompletion L) ((c • x) j)‖) ^ ((1 : ℝ) / finrank ℚ L)) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 L), normAbs (Sum.inl v) c) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 L),
          (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
            algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) := by
  have hc_fin : ∀ v : HeightOneSpectrum (𝓞 L),
      (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
          algebraMap L (v.adicCompletion L) ((c • x) j)‖) ^ ((1 : ℝ) / finrank ℚ L) =
        normAbs (Sum.inl v) c *
          (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
              algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) := by
    intro v
    let xv : ι → v.adicCompletion L := fun j ↦ algebraMap L (v.adicCompletion L) (x j)
    have hsmul : (fun j ↦ algebraMap L (v.adicCompletion L) ((c • x) j)) =
        algebraMap L (v.adicCompletion L) c • xv := funext fun j ↦ by
      simp [xv, smul_eq_mul, map_mul]
    have hmul : ∀ i,
        ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v *
            algebraMap L (v.adicCompletion L) ((c • x) j)‖ =
          ‖algebraMap L (v.adicCompletion L) c‖ *
            ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) i j)).2 v * xv j‖ := by
      intro i
      rw [← mulVec_finPlaceHom_eq v A _ i, hsmul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
        mulVec_finPlaceHom_eq v A xv i, norm_mul]
    have hc_norm : ‖algebraMap L (v.adicCompletion L) c‖ ^ ((1 : ℝ) / finrank ℚ L) =
        normAbs (Sum.inl v) c := by
      rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply, ← normalizedAbsValue_inl_eq_norm_coe, normalizedAbsValue_inl,
        ← normAbs_inl]
    simp_rw [hmul, ← Real.mul_iSup_of_nonneg (norm_nonneg _),
      Real.mul_rpow (norm_nonneg _) (Real.iSup_nonneg fun _ ↦ norm_nonneg _), hc_norm]
    rfl
  have hsc₀ : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦ normAbs (Sum.inl v) c :=
    (hasFiniteMulSupport_normAbs hc).preimage Sum.inl_injective.injOn
  simp_rw [hc_fin]
  exact finprod_mul_distrib hsc₀ (HasFiniteMulSupport.fun_comp hsupp
    (g := fun t : ℝ ↦ t ^ ((1 : ℝ) / finrank ℚ L)) (Real.one_rpow _))

/-- Projective invariance of `TauCeti.adelicHeight` under nonzero scalar multiplication. -/
theorem adelicHeight_smul {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) {c : L} (hc : c ≠ 0) :
    adelicHeight A (c • x) = adelicHeight A x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpf : (∏ w : InfinitePlace L, normAbs (Sum.inr w) c) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 L), normAbs (Sum.inl v) c = 1 := by
    have hsupp : HasFiniteMulSupport ((fun v ↦ normAbs v c) ∘ Sum.inl) :=
      (hasFiniteMulSupport_normAbs hc).preimage Sum.inl_injective.injOn
    have h := finprod_normAbs_eq_one hc
    rw [finprod_sum_type _ hsupp (Set.toFinite _), mul_comm, finprod_eq_prod_of_fintype] at h
    exact h
  rw [adelicHeight_def, adelicHeight_archimedean_smul,
    adelicHeight_finite_smul A x hc (hasFiniteMulSupport_adelicHeight A hx),
    mul_mul_mul_comm, hpf, one_mul, ← adelicHeight_def]

/-- Over `K` itself, the untwisted adelic height agrees with the Euclidean height
`TauCeti.height2`. -/
theorem adelicHeight_one {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (x : ι → K) :
    adelicHeight (L := K) (1 : GL ι (AdeleRing (𝓞 K) K)) x = height2 x := by
  have hinf (w : InfinitePlace K) :
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
          (((1 : GL ι (AdeleRing (𝓞 K) K)) : Matrix ι ι _) i j)).1 w * (x j : w.Completion)‖ ^ 2) ^
        ((w.mult : ℝ) / (2 * finrank ℚ K)) =
      (∑ i, ‖w.embedding (x i)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ K)) := by
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ congrArg (· ^ 2) ?_
    have hsum : ∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
          (((1 : GL ι (AdeleRing (𝓞 K) K)) : Matrix ι ι _) i j)).1 w *
          (x j : w.Completion) = (x i : w.Completion) :=
      (mulVec_infPlaceHom_eq w (1 : GL ι (AdeleRing (𝓞 K) K))
        (fun j ↦ (x j : w.Completion)) i).symm.trans <| by
          rw [map_one, Units.val_one, Matrix.one_mulVec]
    rw [hsum, ← InfinitePlace.Completion.algebraMap_apply_eq_coe,
      InfinitePlace.Completion.norm_algebraMap, InfinitePlace.norm_embedding_eq]
  have hfin (v : HeightOneSpectrum (𝓞 K)) :
      (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
          (((1 : GL ι (AdeleRing (𝓞 K) K)) : Matrix ι ι _) i j)).2 v *
            algebraMap K (v.adicCompletion K) (x j)‖) ^ ((1 : ℝ) / finrank ℚ K) =
        (⨆ i, (FinitePlace.equivHeightOneSpectrum.symm v) (x i)) ^
          ((1 : ℝ) / finrank ℚ K) := by
    congr 1
    refine iSup_congr fun i ↦ ?_
    have hsum : ∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
          (((1 : GL ι (AdeleRing (𝓞 K) K)) : Matrix ι ι _) i j)).2 v *
          algebraMap K (v.adicCompletion K) (x j) =
        algebraMap K (v.adicCompletion K) (x i) :=
      (mulVec_finPlaceHom_eq v (1 : GL ι (AdeleRing (𝓞 K) K))
        (fun j ↦ algebraMap K (v.adicCompletion K) (x j)) i).symm.trans <| by
          rw [map_one, Units.val_one, Matrix.one_mulVec]
    rw [hsum, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, ← normalizedAbsValue_inl_eq_norm_coe, normalizedAbsValue_inl,
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  have hF (w : InfinitePlace K) :
      (@Finset.sum ι ℝ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i ↦ ‖w.embedding (x i)‖ ^ 2) =
        ∑ i, ‖w.embedding (x i)‖ ^ 2 :=
    congrArg (fun inst : Fintype ι ↦
      @Finset.sum ι ℝ _ (@Finset.univ ι inst) fun i ↦ ‖w.embedding (x i)‖ ^ 2)
      (Subsingleton.elim (Fintype.ofFinite ι) ‹Fintype ι›)
  rw [adelicHeight_def, height2_eq]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ (hinf w).trans (by rw [hF w]))
    ((finprod_congr hfin).trans (finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun v : FinitePlace K ↦ (⨆ i, v (x i)) ^ ((1 : ℝ) / finrank ℚ K))))

/-- Reindexing the rows and columns of an adelic matrix preserves `TauCeti.adelicHeight`. -/
theorem adelicHeight_reindex {K L ι₁ ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι] [DecidableEq ι]
    (e : ι₁ ≃ ι) (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) :
    adelicHeight (Units.map (Matrix.reindexAlgEquiv (AdeleRing (𝓞 K) K)
        (AdeleRing (𝓞 K) K) e.symm).toMonoidHom A) (x ∘ e) =
      adelicHeight A x := by
  let B : GL ι₁ (AdeleRing (𝓞 K) K) := Units.map (Matrix.reindexAlgEquiv (AdeleRing (𝓞 K) K)
    (AdeleRing (𝓞 K) K) e.symm).toMonoidHom A
  have hB : ∀ i j, B.val i j = A.val (e i) (e j) := fun i j ↦ by simp [B]
  rw [adelicHeight_def, adelicHeight_def]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ ?_) (finprod_congr fun v ↦ ?_)
  · congr 1
    refine Fintype.sum_equiv e _ _ fun i ↦ ?_
    let xw : ι → w.Completion := fun j ↦ (x j : w.Completion)
    have hBw : (Matrix.GeneralLinearGroup.map (infPlaceHom K L w) B).val =
        (Matrix.GeneralLinearGroup.map (infPlaceHom K L w) A).val.submatrix e e :=
      Matrix.ext fun i j ↦ congrArg (infPlaceHom K L w) (hB i j)
    have hs : ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((B : Matrix ι₁ ι₁ _) i j)).1 w *
          ((x ∘ e) j : w.Completion) =
        ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) (e i) j)).1 w * xw j := by
      have hsubvec : ∀ j, ((x ∘ e) j : w.Completion) = (xw ∘ e) j := fun _ ↦ rfl
      simp_rw [hsubvec]
      rw [← mulVec_infPlaceHom_eq w B (xw ∘ e) i, hBw, Matrix.submatrix_mulVec_equiv,
        Function.comp_apply, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
        mulVec_infPlaceHom_eq w A xw (e i)]
    rw [hs]
  · congr 1
    refine e.iSup_congr fun i ↦ ?_
    let xv : ι → v.adicCompletion L := fun j ↦ algebraMap L (v.adicCompletion L) (x j)
    have hBv : (Matrix.GeneralLinearGroup.map (finPlaceHom K L v) B).val =
        (Matrix.GeneralLinearGroup.map (finPlaceHom K L v) A).val.submatrix e e :=
      Matrix.ext fun i j ↦ congrArg (finPlaceHom K L v) (hB i j)
    have hs : ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((B : Matrix ι₁ ι₁ _) i j)).2 v *
          algebraMap L (v.adicCompletion L) ((x ∘ e) j) =
        ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L ((A : Matrix ι ι _) (e i) j)).2 v * xv j := by
      have hsubvec : ∀ j, algebraMap L (v.adicCompletion L) ((x ∘ e) j) = (xv ∘ e) j := fun _ ↦ rfl
      simp_rw [hsubvec]
      rw [← mulVec_finPlaceHom_eq v B (xv ∘ e) i, hBv, Matrix.submatrix_mulVec_equiv,
        Function.comp_apply, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
        mulVec_finPlaceHom_eq v A xv (e i)]
    rw [hs]

private theorem finrank_mul_inv_eq {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    (finrank K L : ℝ) * ((1 : ℝ) / finrank ℚ L) = (finrank ℚ K : ℝ)⁻¹ := by
  have hmul : (finrank ℚ K : ℝ) * (finrank K L : ℝ) = finrank ℚ L := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K L
  have hK0 : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hKL0 : (finrank K L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  rw [← hmul]
  field_simp

private theorem adelicHeight_unique_one {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι] [Unique ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) :
    adelicHeight A (fun _ : ι ↦ (1 : L)) =
      ((GlobalNumberFields.ideleNorm (Matrix.GeneralLinearGroup.det A) : ℝ≥0) : ℝ) ^
        ((finrank ℚ K : ℝ)⁻¹) := by
  rw [adelicHeight_def]
  set d : IdeleGroup (𝓞 K) K := Matrix.GeneralLinearGroup.det A
  set dL : IdeleGroup (𝓞 L) L := ideleExtension K L d
  have hAdet : (A : Matrix ι ι (AdeleRing (𝓞 K) K)) default default = (d : AdeleRing (𝓞 K) K) := by
    rw [show (d : AdeleRing (𝓞 K) K) = (A : Matrix ι ι (AdeleRing (𝓞 K) K)).det from rfl,
      Matrix.det_unique]
  have hinf : ∀ w : InfinitePlace L,
      (∑ i : ι, ‖∑ j : ι, (adeleExtension (𝓞 K) K (𝓞 L) L
          ((A : Matrix ι ι (AdeleRing (𝓞 K) K)) i j)).1 w * ((1 : L) : w.Completion)‖ ^ 2) ^
        ((w.mult : ℝ) / (2 * finrank ℚ L)) =
        (InfinitePlace.completionNormalizedAbsValue w (w.ideleInfiniteCoord dL)) ^
          ((1 : ℝ) / finrank ℚ L) := by
    intro w
    rw [Fintype.sum_unique, Fintype.sum_unique, hAdet, ← coe_ideleExtension K L d,
      ← InfinitePlace.coe_ideleInfiniteCoord, InfinitePlace.completionNormalizedAbsValue_apply]
    simp only [map_one, ← InfinitePlace.Completion.algebraMap_apply_eq_coe, mul_one]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_natCast _ w.mult, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hfin : ∀ v : HeightOneSpectrum (𝓞 L),
      (⨆ i : ι, ‖∑ j : ι, (adeleExtension (𝓞 K) K (𝓞 L) L
          ((A : Matrix ι ι (AdeleRing (𝓞 K) K)) i j)).2 v *
            algebraMap L (v.adicCompletion L) (1 : L)‖) ^ ((1 : ℝ) / finrank ℚ L) =
        ‖(v.ideleFiniteCoord dL : v.adicCompletion L)‖ ^ ((1 : ℝ) / finrank ℚ L) := by
    intro v
    rw [ciSup_unique, Fintype.sum_unique, hAdet, ← coe_ideleExtension K L d,
      ← HeightOneSpectrum.coe_ideleFiniteCoord, map_one, mul_one]
  simp_rw [hinf, hfin]
  rw [Real.finsetProd_rpow Finset.univ _ (fun w _ ↦ by
      simp [InfinitePlace.completionNormalizedAbsValue_apply]),
    ← finprod_rpow (fun _ ↦ norm_nonneg _),
    ← Real.mul_rpow (Finset.prod_nonneg fun _ _ ↦ by
      simp [InfinitePlace.completionNormalizedAbsValue_apply])
      (finprod_nonneg fun _ ↦ norm_nonneg _),
    ← coe_ideleNorm dL]
  have hid : ideleNorm dL = ideleNorm d ^ finrank K L := by
    rw [← ideleNorm_ideleNormMap (K := K) dL, show dL = ideleExtension K L d from rfl,
      ideleNormMap_ideleExtension, map_pow]
  rw [hid, Units.val_pow_eq_pow_val, NNReal.coe_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (NNReal.coe_nonneg _), finrank_mul_inv_eq]

/-- In dimension one (`[Unique ι]`), the adelic height of any nonzero vector twisted by
`A : GL ι (AdeleRing (𝓞 K) K)` equals `(ideleNorm (det A)) ^ ([K : ℚ]⁻¹)`. -/
theorem adelicHeight_unique {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι] [Unique ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {x : ι → L} (hx : x ≠ 0) :
    adelicHeight A x =
      ((GlobalNumberFields.ideleNorm (Matrix.GeneralLinearGroup.det A) : ℝ≥0) : ℝ) ^
        ((finrank ℚ K : ℝ)⁻¹) := by
  have hx0 : x default ≠ 0 := fun h ↦ hx (funext fun i ↦ by rw [Unique.eq_default i, h]; rfl)
  have hunit : (x default)⁻¹ • x = fun _ : ι ↦ (1 : L) := by
    ext i
    simp [Unique.eq_default i, inv_mul_cancel₀ hx0]
  rw [← adelicHeight_smul A x (inv_ne_zero hx0), hunit]
  exact adelicHeight_unique_one A

end TauCeti
