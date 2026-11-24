/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.NumberTheory.Height.Arakelov.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Extension
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compatibility
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import TauCeti.NumberTheory.NumberField.Global.Places.Basic

/-!
# Adelic heights over number fields

For a matrix `A` over `AdeleRing (𝓞 K) K` and a vector `x : ι → L` over a finite extension
`L / K`, `TauCeti.adelicHeight A x` is the adelic twisted height combining the `ℓ²` norms of
`(A *ᵥ x)_w` at the infinite places `w` of `L` and the `ℓ^∞` norms at the finite places `v` of `L`,
degree-normalized by `[L : ℚ]`.

## Main definitions

* `TauCeti.adelicHeight`: the adelic height of `x : ι → L` twisted by an adelic matrix `A`.

## Main results

* `TauCeti.adelicHeight_nonneg`: nonnegativity of `TauCeti.adelicHeight`.
* `TauCeti.adelicHeight_zero`: vanishing at `x = 0`.
* `TauCeti.adelicHeight_smul`: projective invariance under `Lˣ` for invertible matrices
  `A : GL ι (AdeleRing (𝓞 K) K)` (and `adelicHeight_smul_of_hasFiniteMulSupport` under finite
  multiplicative support of the local factors).
* `TauCeti.adelicHeight_one`: specialization to `L = K` and `A = 1` recovers `TauCeti.height2`.
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

/-- The adelic height of a vector `x : ι → L` twisted by an adelic matrix `A` over `K ⊆ L`:
the product over infinite places `w` of `L` of the `ℓ²` norm of `A_w x` raised to
`w.mult / (2 [L : ℚ])` times the `finprod` over finite places `v` of `L` of the `ℓ^∞` norm
raised to `1 / [L : ℚ]`. -/
@[expose]
noncomputable def adelicHeight {K L ι ι' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [Fintype ι']
    (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) (x : ι → L) : ℝ :=
  (∏ w : InfinitePlace L,
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w * (x j : w.Completion)‖ ^ 2) ^
        ((w.mult : ℝ) / (2 * finrank ℚ L))) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 L),
      (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L)

/-- Defining equation of `TauCeti.adelicHeight`. -/
theorem adelicHeight_def {K L ι ι' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [Fintype ι']
    (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) (x : ι → L) :
    adelicHeight A x =
      (∏ w : InfinitePlace L,
          (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w * (x j : w.Completion)‖ ^ 2) ^
            ((w.mult : ℝ) / (2 * finrank ℚ L))) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 L),
          (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
            algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) :=
  rfl

/-- Every adelic height is nonnegative. -/
theorem adelicHeight_nonneg {K L ι ι' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [Fintype ι']
    (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) (x : ι → L) :
    0 ≤ adelicHeight A x := by
  refine mul_nonneg (Finset.prod_nonneg fun w _ ↦ ?_) (finprod_nonneg fun v ↦ ?_)
  · exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) _
  · exact Real.rpow_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) _

/-- The adelic height of the zero vector is `0`. -/
@[simp]
theorem adelicHeight_zero {K L ι ι' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [Fintype ι']
    (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) :
    adelicHeight (L := L) A 0 = 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have hexp : (w.mult : ℝ) / (2 * finrank ℚ L) ≠ 0 := by
    have hm : (0 : ℝ) < w.mult := Nat.cast_pos.mpr InfinitePlace.mult_pos
    have hD : (0 : ℝ) < finrank ℚ L := Nat.cast_pos.mpr finrank_pos
    positivity
  have hzero :
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
          ((0 : L) : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) = 0 := by
    simp [Real.zero_rpow hexp]
  rw [adelicHeight_def, Finset.prod_eq_zero (Finset.mem_univ w) hzero, zero_mul]

private theorem finset_prod_rpow {α : Type*} (s : Finset α) (f : α → ℝ) (r : ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a ∈ s, f a) ^ r = ∏ a ∈ s, f a ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has, Real.mul_rpow (hf a (by simp))
      (Finset.prod_nonneg fun b hb ↦ hf b (by simp [hb])), ih fun b hb ↦ hf b (by simp [hb])]

private theorem hasFiniteMulSupport_rpow {α : Type*} {f : α → ℝ} (h : HasFiniteMulSupport f)
    (r : ℝ) :
    HasFiniteMulSupport fun a ↦ f a ^ r := by
  refine h.subset fun a ha ↦ ?_
  contrapose ha
  simp [notMem_mulSupport.mp ha]

private theorem finprod_rpow {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a)
    (hsupp : HasFiniteMulSupport f) (r : ℝ) :
    (∏ᶠ a, f a) ^ r = ∏ᶠ a, f a ^ r := by
  have hsupp' : (mulSupport f).Finite := hsupp
  rw [finprod_eq_prod _ hsupp', finset_prod_rpow _ _ _ fun a _ ↦ hf a,
    finprod_eq_prod_of_mulSupport_subset (fun a ↦ f a ^ r) (s := hsupp'.toFinset)]
  rw [Set.Finite.coe_toFinset hsupp']
  intro a ha h1
  exact ha (show f a ^ r = 1 by rw [h1, Real.one_rpow])

private theorem norm_algebraMap_adicCompletion {L : Type*} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) (c : L) :
    ‖algebraMap L (v.adicCompletion L) c‖ = NumberField.HeightOneSpectrum.adicAbv L v c := by
  rw [← FinitePlace.norm_embedding, HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, FinitePlace.embedding_apply]
  rfl

private theorem hasFiniteMulSupport_norm_algebraMap {L : Type*} [Field L] [NumberField L]
    {c : L} (hc : c ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      ‖algebraMap L (v.adicCompletion L) c‖ := by
  simpa only [norm_algebraMap_adicCompletion] using hasFiniteMulSupport_adicAbv hc

private theorem norm_coe_infinitePlace_prod_mul_finprod_eq_one {L : Type*} [Field L]
    [NumberField L] {c : L} (hc : c ≠ 0) :
    (∏ w : InfinitePlace L, ‖(c : w.Completion)‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 L), ‖algebraMap L (v.adicCompletion L) c‖ = 1 := by
  have hinf : ∀ w : InfinitePlace L, ‖(c : w.Completion)‖ ^ w.mult =
      normalizedAbsValue (Sum.inr w) c := by
    intro w
    rw [normalizedAbsValue_inr, ← InfinitePlace.Completion.norm_algebraMap w c,
      InfinitePlace.Completion.algebraMap_apply_eq_coe]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 L), ‖algebraMap L (v.adicCompletion L) c‖ =
      normalizedAbsValue (Sum.inl v) c := by
    intro v
    rw [norm_algebraMap_adicCompletion, normalizedAbsValue_inl]
  simp_rw [hinf, hfin]
  have hpf := finprod_normalizedAbsValue_eq_one hc
  have hsupp : HasFiniteMulSupport ((fun v ↦ normalizedAbsValue v c) ∘ Sum.inl) := by
    simpa only [Function.comp_def, normalizedAbsValue_inl] using hasFiniteMulSupport_adicAbv hc
  rw [finprod_sum_type _ hsupp (Set.toFinite _)] at hpf
  have hprod :=
    finprod_eq_prod_of_fintype (fun w : InfinitePlace L ↦ normalizedAbsValue (Sum.inr w) c)
  rw [hprod, mul_comm] at hpf
  exact hpf

private theorem adelicHeight_archimedean_smul {K L ι ι' : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [Fintype ι']
    (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) (x : ι → L) (c : L) :
    (∏ w : InfinitePlace L,
        (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
            ((c • x) j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L))) =
      (∏ w : InfinitePlace L, ‖(c : w.Completion)‖ ^ w.mult) ^ ((1 : ℝ) / finrank ℚ L) *
        ∏ w : InfinitePlace L,
          (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
              (x j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) := by
  have hc_term : ∀ w : InfinitePlace L,
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
          ((c • x) j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) =
        (‖(c : w.Completion)‖ ^ w.mult) ^ ((1 : ℝ) / finrank ℚ L) *
          (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
              (x j : w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) := by
    intro w
    have hmul : ∀ i,
        ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
            ((c • x) j : w.Completion)‖ ^ 2 =
          ‖(c : w.Completion)‖ ^ 2 *
            ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w * (x j : w.Completion)‖ ^ 2 := by
      intro i
      have hcast : ∀ j, ((c • x) j : w.Completion) = (c : w.Completion) * (x j : w.Completion) := by
        intro j
        simp [← InfinitePlace.Completion.algebraMap_apply_eq_coe]
      simp_rw [hcast]
      rw [show (∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
          ((c : w.Completion) * (x j : w.Completion))) =
            (c : w.Completion) * ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).1 w *
              (x j : w.Completion) by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ ?_; ring, norm_mul, mul_pow]
    simp_rw [hmul, ← Finset.mul_sum]
    rw [Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
      ← Real.rpow_natCast ‖(c : w.Completion)‖ 2, ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_natCast ‖(c : w.Completion)‖ w.mult, ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  simp_rw [hc_term, Finset.prod_mul_distrib,
    finset_prod_rpow Finset.univ _ _ fun _ _ ↦ pow_nonneg (norm_nonneg _) _]

private theorem adelicHeight_finite_smul {K L ι ι' : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι]
    (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) (x : ι → L) {c : L} (hc : c ≠ 0)
    (hsupp : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      ⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 L),
        (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
          algebraMap L (v.adicCompletion L) ((c • x) j)‖) ^ ((1 : ℝ) / finrank ℚ L)) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 L),
          ‖algebraMap L (v.adicCompletion L) c‖) ^ ((1 : ℝ) / finrank ℚ L) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 L),
          (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
            algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) := by
  have hc_fin : ∀ v : HeightOneSpectrum (𝓞 L),
      (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
          algebraMap L (v.adicCompletion L) ((c • x) j)‖) ^ ((1 : ℝ) / finrank ℚ L) =
        ‖algebraMap L (v.adicCompletion L) c‖ ^ ((1 : ℝ) / finrank ℚ L) *
          (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
              algebraMap L (v.adicCompletion L) (x j)‖) ^ ((1 : ℝ) / finrank ℚ L) := by
    intro v
    have hmul : ∀ i,
        ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
            algebraMap L (v.adicCompletion L) ((c • x) j)‖ =
          ‖algebraMap L (v.adicCompletion L) c‖ *
            ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
              algebraMap L (v.adicCompletion L) (x j)‖ := by
      intro i
      simp_rw [Pi.smul_apply, smul_eq_mul, map_mul]
      rw [show (∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
          (algebraMap L (v.adicCompletion L) c * algebraMap L (v.adicCompletion L) (x j))) =
            algebraMap L (v.adicCompletion L) c *
              ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
                algebraMap L (v.adicCompletion L) (x j) by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ ?_; ring, norm_mul]
    simp_rw [hmul, ← Real.mul_iSup_of_nonneg (norm_nonneg _),
      Real.mul_rpow (norm_nonneg _) (Real.iSup_nonneg fun _ ↦ norm_nonneg _)]
  have hsc₀ := hasFiniteMulSupport_norm_algebraMap hc
  simp_rw [hc_fin]
  rw [finprod_mul_distrib (hasFiniteMulSupport_rpow hsc₀ _) (hasFiniteMulSupport_rpow hsupp _),
    finprod_rpow (fun _ ↦ norm_nonneg _) hsc₀]

/-- Scalar invariance of `TauCeti.adelicHeight` whenever the finite-place suprema of `A *ᵥ x` have
finite multiplicative support. -/
theorem adelicHeight_smul_of_hasFiniteMulSupport {K L ι ι' : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [Fintype ι']
    (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) (x : ι → L) {c : L} (hc : c ≠ 0)
    (hsupp : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      ⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖) :
    adelicHeight A (c • x) = adelicHeight A x := by
  have hpf_rpow :
      (∏ w : InfinitePlace L, ‖(c : w.Completion)‖ ^ w.mult) ^ ((1 : ℝ) / finrank ℚ L) *
          (∏ᶠ v : HeightOneSpectrum (𝓞 L), ‖algebraMap L (v.adicCompletion L) c‖) ^
            ((1 : ℝ) / finrank ℚ L) = 1 := by
    rw [← Real.mul_rpow (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _)
      (finprod_nonneg fun _ ↦ norm_nonneg _), norm_coe_infinitePlace_prod_mul_finprod_eq_one hc,
      Real.one_rpow]
  rw [adelicHeight_def, adelicHeight_archimedean_smul, adelicHeight_finite_smul A x hc hsupp]
  calc ((∏ w : InfinitePlace L, ‖(c : w.Completion)‖ ^ w.mult) ^ ((1 : ℝ) / finrank ℚ L) *
          ∏ w : InfinitePlace L, _) *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 L), _) ^ ((1 : ℝ) / finrank ℚ L) * ∏ᶠ v, _)
      = ((∏ w : InfinitePlace L, ‖(c : w.Completion)‖ ^ w.mult) ^ ((1 : ℝ) / finrank ℚ L) *
          (∏ᶠ v : HeightOneSpectrum (𝓞 L), ‖algebraMap L (v.adicCompletion L) c‖) ^
            ((1 : ℝ) / finrank ℚ L)) *
          ((∏ w : InfinitePlace L, _) * ∏ᶠ v, _) := by ring
    _ = adelicHeight A x := by rw [hpf_rpow, one_mul, adelicHeight_def]

private theorem norm_sum_mul_le_of_nonarchimedean {F ι : Type*} [NormedField F]
    [IsUltrametricDist F] [Fintype ι] {a b : ι → F} {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ j, ‖a j‖ ≤ 1) (hb : ∀ j, ‖b j‖ ≤ r) :
    ‖∑ j, a j * b j‖ ≤ r := by
  classical
  have hterm : ∀ j, ‖a j * b j‖ ≤ r := fun j ↦ by
    rw [norm_mul]
    exact (mul_le_mul (ha j) (hb j) (norm_nonneg _) zero_le_one).trans_eq (one_mul r)
  have hfin : ∀ s : Finset ι, ‖∑ j ∈ s, a j * b j‖ ≤ r := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hr
    | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hterm j) ih)
  exact hfin Finset.univ

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

private theorem finset_sum_adele_snd_apply {K L κ : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (s : Finset κ) (f : κ → AdeleRing (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 L)) :
    (adeleExtension (𝓞 K) K (𝓞 L) L (∑ k ∈ s, f k)).2 v =
      ∑ k ∈ s, (adeleExtension (𝓞 K) K (𝓞 L) L (f k)).2 v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
    rw [Finset.sum_insert hks, Finset.sum_insert hks, map_add, ← ih]
    rfl

private theorem sum_adeleExtension_mul_self {K L ι : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (AdeleRing (𝓞 K) K)} (hBA : B * A = 1) (x : ι → L)
    (v : HeightOneSpectrum (𝓞 L)) (j₀ : ι) :
    ∑ k, (adeleExtension (𝓞 K) K (𝓞 L) L (B j₀ k)).2 v *
        ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A k j)).2 v *
          algebraMap L (v.adicCompletion L) (x j) =
      algebraMap L (v.adicCompletion L) (x j₀) := by
  have hmul : ∀ j, ∑ k, (adeleExtension (𝓞 K) K (𝓞 L) L (B j₀ k)).2 v *
      (adeleExtension (𝓞 K) K (𝓞 L) L (A k j)).2 v = if j₀ = j then 1 else 0 := by
    intro j
    have hEntry : (∑ k, B j₀ k * A k j) = (1 : Matrix ι ι (AdeleRing (𝓞 K) K)) j₀ j := by
      simpa only [Matrix.mul_apply] using congrFun (congrFun hBA j₀) j
    calc ∑ k, (adeleExtension (𝓞 K) K (𝓞 L) L (B j₀ k)).2 v *
          (adeleExtension (𝓞 K) K (𝓞 L) L (A k j)).2 v
        = ∑ k, (adeleExtension (𝓞 K) K (𝓞 L) L (B j₀ k * A k j)).2 v := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [map_mul]
          rfl
      _ = (adeleExtension (𝓞 K) K (𝓞 L) L (∑ k, B j₀ k * A k j)).2 v :=
          (finset_sum_adele_snd_apply Finset.univ _ v).symm
      _ = (adeleExtension (𝓞 K) K (𝓞 L) L ((1 : Matrix ι ι (AdeleRing (𝓞 K) K)) j₀ j)).2 v := by
          rw [hEntry]
      _ = if j₀ = j then 1 else 0 := by
          rw [Matrix.one_apply]
          split_ifs <;> simp
  calc ∑ k, (adeleExtension (𝓞 K) K (𝓞 L) L (B j₀ k)).2 v *
        ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A k j)).2 v *
          algebraMap L (v.adicCompletion L) (x j)
      = ∑ j, (∑ k, (adeleExtension (𝓞 K) K (𝓞 L) L (B j₀ k)).2 v *
          (adeleExtension (𝓞 K) K (𝓞 L) L (A k j)).2 v) *
            algebraMap L (v.adicCompletion L) (x j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ = algebraMap L (v.adicCompletion L) (x j₀) := by
        simp_rw [hmul, ite_mul, one_mul, zero_mul]
        simp

/-- Under a left-invertible adelic matrix `B * A = 1`, the finite-place factors of `A *ᵥ x` at
any nonzero `x` equal `1` at all but finitely many places. -/
theorem hasFiniteMulSupport_adelicHeight_of_left_inv {K L ι : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (AdeleRing (𝓞 K) K)} (hBA : B * A = 1) {x : ι → L} (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 L) ↦
      ⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
        algebraMap L (v.adicCompletion L) (x j)‖ := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨j₀⟩
  have hj₀_ev : ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ‖algebraMap L (v.adicCompletion L) (x j₀)‖ = 1 :=
    Filter.eventually_cofinite.mpr (hasFiniteMulSupport_norm_algebraMap hj₀)
  refine Filter.eventually_cofinite.mp ?_
  filter_upwards [eventually_norm_adeleExtension_le_one (L := L) A,
    eventually_norm_adeleExtension_le_one (L := L) B,
    eventually_norm_algebraMap_le_one x, hj₀_ev] with v hAv hBv hxv hvj₀
  apply le_antisymm
  · exact ciSup_le fun i ↦ norm_sum_mul_le_of_nonarchimedean zero_le_one (hAv i) hxv
  · rw [← hvj₀, ← sum_adeleExtension_mul_self hBA x v j₀]
    exact norm_sum_mul_le_of_nonarchimedean (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (hBv j₀)
      fun k ↦ le_ciSup (Set.Finite.bddAbove (Set.finite_range fun i : ι ↦
        ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A i j)).2 v *
          algebraMap L (v.adicCompletion L) (x j)‖)) k

/-- Projective invariance of `TauCeti.adelicHeight` under nonzero scalar multiplication for
invertible adelic matrices. -/
theorem adelicHeight_smul {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (x : ι → L) {c : L} (hc : c ≠ 0) :
    adelicHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (c • x) =
      adelicHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hinv : ((A⁻¹ : GL ι (AdeleRing (𝓞 K) K)) : Matrix ι ι _) *
        (A : Matrix ι ι (AdeleRing (𝓞 K) K)) = 1 := by
      simp
    exact adelicHeight_smul_of_hasFiniteMulSupport _ x hc
      (hasFiniteMulSupport_adelicHeight_of_left_inv hinv hx)

private theorem sum_adeleExtension_one_inf {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    [DecidableEq ι] (x : ι → K) (i : ι) (w : InfinitePlace K) :
    ∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
        ((1 : Matrix ι ι (AdeleRing (𝓞 K) K)) i j)).1 w * (x j : w.Completion) =
      (x i : w.Completion) := by
  rw [Finset.sum_eq_single i]
  · rw [RingHom.congr_fun (NumberField.adeleExtension_self (𝓞 K) K) _, Matrix.one_apply_eq]
    exact one_mul _
  · intro j _ hji
    rw [RingHom.congr_fun (NumberField.adeleExtension_self (𝓞 K) K) _,
      Matrix.one_apply_ne hji.symm]
    exact zero_mul _
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem sum_adeleExtension_one_fin {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    [DecidableEq ι] (x : ι → K) (i : ι) (v : HeightOneSpectrum (𝓞 K)) :
    ∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
        ((1 : Matrix ι ι (AdeleRing (𝓞 K) K)) i j)).2 v *
          algebraMap K (v.adicCompletion K) (x j) =
      algebraMap K (v.adicCompletion K) (x i) := by
  rw [Finset.sum_eq_single i]
  · rw [RingHom.congr_fun (NumberField.adeleExtension_self (𝓞 K) K) _, Matrix.one_apply_eq]
    exact one_mul _
  · intro j _ hji
    rw [RingHom.congr_fun (NumberField.adeleExtension_self (𝓞 K) K) _,
      Matrix.one_apply_ne hji.symm]
    exact zero_mul _
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Over `K` itself, the untwisted adelic height agrees with the Euclidean height
`TauCeti.height2`. -/
theorem adelicHeight_one {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (x : ι → K) :
    adelicHeight (L := K) (1 : Matrix ι ι (AdeleRing (𝓞 K) K)) x = height2 x := by
  have hinf (w : InfinitePlace K) :
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
          ((1 : Matrix ι ι (AdeleRing (𝓞 K) K)) i j)).1 w * (x j : w.Completion)‖ ^ 2) ^
        ((w.mult : ℝ) / (2 * finrank ℚ K)) =
      (∑ i, ‖w.embedding (x i)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ K)) := by
    congr 1
    convert Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦ ?_
    exact congrArg (· ^ 2) (by
      rw [sum_adeleExtension_one_inf x i w, ← InfinitePlace.Completion.algebraMap_apply_eq_coe,
        InfinitePlace.Completion.norm_algebraMap, InfinitePlace.norm_embedding_eq])
  have hfin (v : HeightOneSpectrum (𝓞 K)) :
      (⨆ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
          ((1 : Matrix ι ι (AdeleRing (𝓞 K) K)) i j)).2 v *
            algebraMap K (v.adicCompletion K) (x j)‖) ^ ((1 : ℝ) / finrank ℚ K) =
        (⨆ i, (FinitePlace.equivHeightOneSpectrum.symm v) (x i)) ^
          ((1 : ℝ) / finrank ℚ K) := by
    congr 1
    refine iSup_congr fun i ↦ ?_
    rw [sum_adeleExtension_one_fin x i v, norm_algebraMap_adicCompletion,
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  have hF (w : InfinitePlace K) :
      (@Finset.sum ι ℝ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i ↦ ‖w.embedding (x i)‖ ^ 2) =
        ∑ i, ‖w.embedding (x i)‖ ^ 2 :=
    congrArg (fun inst : Fintype ι ↦
      @Finset.sum ι ℝ _ (@Finset.univ ι inst) fun i ↦ ‖w.embedding (x i)‖ ^ 2)
      (Subsingleton.elim (Fintype.ofFinite ι) ‹Fintype ι›)
  have hinf' (w : InfinitePlace K) :
      (∑ i, ‖∑ j, (adeleExtension (𝓞 K) K (𝓞 K) K
          ((1 : Matrix ι ι (AdeleRing (𝓞 K) K)) i j)).1 w * (x j : w.Completion)‖ ^ 2) ^
        ((w.mult : ℝ) / (2 * finrank ℚ K)) =
      (@Finset.sum ι ℝ _ (@Finset.univ ι (Fintype.ofFinite ι))
          fun i ↦ ‖w.embedding (x i)‖ ^ 2) ^
        ((w.mult : ℝ) / (2 * finrank ℚ K)) := by
    rw [hF w]
    exact hinf w
  rw [adelicHeight_def, height2_eq]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ hinf' w)
    ((finprod_congr hfin).trans (finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun v : FinitePlace K ↦ (⨆ i, v (x i)) ^ ((1 : ℝ) / finrank ℚ K))))

/-- Reindexing the rows and columns of an adelic matrix preserves `TauCeti.adelicHeight`. -/
theorem adelicHeight_reindex {K L ι₁ ι₂ ι ι' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι₁] [Fintype ι₂] [Fintype ι] [Fintype ι']
    (e₁ : ι₁ ≃ ι) (e₂ : ι₂ ≃ ι') (A : Matrix ι' ι (AdeleRing (𝓞 K) K)) (x : ι → L) :
    adelicHeight (A.submatrix e₂ e₁) (x ∘ e₁) = adelicHeight A x := by
  rw [adelicHeight_def, adelicHeight_def]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ ?_) (finprod_congr fun v ↦ ?_)
  · congr 1
    refine Fintype.sum_equiv e₂ _ _ fun i ↦ ?_
    have hs : ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A.submatrix e₂ e₁ i j)).1 w *
          ((x ∘ e₁) j : w.Completion) =
        ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A (e₂ i) j)).1 w * (x j : w.Completion) := by
      simp only [Matrix.submatrix_apply, Function.comp_apply]
      exact Fintype.sum_equiv e₁ _ (fun j ↦ (adeleExtension (𝓞 K) K (𝓞 L) L
        (A (e₂ i) j)).1 w * (x j : w.Completion)) fun j ↦ rfl
    rw [hs]
  · congr 1
    refine e₂.iSup_congr fun i ↦ ?_
    have hs : ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A.submatrix e₂ e₁ i j)).2 v *
          algebraMap L (v.adicCompletion L) ((x ∘ e₁) j) =
        ∑ j, (adeleExtension (𝓞 K) K (𝓞 L) L (A (e₂ i) j)).2 v *
          algebraMap L (v.adicCompletion L) (x j) := by
      simp only [Matrix.submatrix_apply, Function.comp_apply]
      exact Fintype.sum_equiv e₁ _ (fun j ↦ (adeleExtension (𝓞 K) K (𝓞 L) L
        (A (e₂ i) j)).2 v * algebraMap L (v.adicCompletion L) (x j)) fun j ↦ rfl
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
    adelicHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (fun _ : ι ↦ (1 : L)) =
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
  rw [← finset_prod_rpow Finset.univ _ ((1 : ℝ) / finrank ℚ L) (fun w _ ↦ by
      simp [InfinitePlace.completionNormalizedAbsValue_apply]),
    ← finprod_rpow (fun _ ↦ norm_nonneg _) (hasFiniteMulSupport_norm_ideleFiniteCoord dL),
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
    adelicHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) x =
      ((GlobalNumberFields.ideleNorm (Matrix.GeneralLinearGroup.det A) : ℝ≥0) : ℝ) ^
        ((finrank ℚ K : ℝ)⁻¹) := by
  have hx0 : x default ≠ 0 := fun h ↦ hx (funext fun i ↦ by rw [Unique.eq_default i, h]; rfl)
  have hunit : (x default)⁻¹ • x = fun _ : ι ↦ (1 : L) := by
    ext i
    simp [Unique.eq_default i, inv_mul_cancel₀ hx0]
  rw [← adelicHeight_smul A x (inv_ne_zero hx0), hunit]
  exact adelicHeight_unique_one A

end TauCeti
