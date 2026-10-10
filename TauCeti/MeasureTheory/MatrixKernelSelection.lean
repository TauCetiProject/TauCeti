/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Measurable selection of a kernel vector

**A measurable family of strictly wide matrices admits a measurable family of unit kernel
vectors**: if `A x` is an `m × n` complex matrix depending measurably on `x` and `m < n`, there
is a measurable `w` with `∑ⱼ ‖w x j‖² = 1` and `∑ⱼ A x i j * w x j = 0` for every row `i`.

Pointwise this is nothing -- `m` vectors cannot span `ℂⁿ` -- and the entire content is doing it
*measurably*, with no continuity in `x` whatsoever.  The rank of `A x` can jump arbitrarily from
point to point, so no formula built from a fixed set of minors works globally.

## The construction

Set `B = Aᴴ A`, a positive semidefinite `n × n` matrix with `ker B = ker A` and `det B = 0`.
The resolvent trick produces the kernel projection as a **pointwise limit of measurable
functions**:

```text
t (B + t·1)⁻¹  →  orthogonal projection onto ker B   as t ↓ 0,
```

because in an eigenbasis of `B` the left side is diagonal with entries `t / (λᵢ + t)`, which
tend to `1` on the kernel eigenvalues and to `0` on the rest.  Each approximant is measurable in
`x` -- the inverse is `det⁻¹ • adjugate`, a rational function of the entries -- so the limit `Q`
is measurable, and it is nonzero because `det B = 0` forces a zero eigenvalue.  A kernel vector
is then read off `Q` by taking its first nonzero column, a finite measurable case split, and
normalised.

The eigendecomposition is used **only pointwise**, inside the limit argument; it never needs to
be chosen measurably.  That is what makes this proof short where a direct measurable-selection
argument would need a partition by rank and by pivot pattern.

## Main results

* `TauCeti.exists_tendsto_kernel_matrix`: the pointwise limit statement for one positive
  semidefinite singular matrix.
* `TauCeti.exists_measurable_unit_nullVector`: **the measurable selection.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

open MeasureTheory Matrix

open scoped ComplexOrder

namespace TauCeti

section Measurability

variable {α : Type*} [MeasurableSpace α]

/-- The determinant of a measurable family of matrices is measurable: it is a polynomial in the
entries. -/
theorem measurable_matrix_det {d : ℕ} {M : α → Matrix (Fin d) (Fin d) ℂ}
    (hM : ∀ i j, Measurable fun x => M x i j) : Measurable fun x => (M x).det := by
  simp only [Matrix.det_apply']
  refine Finset.measurable_sum _ fun σ _ => ?_
  exact (Finset.measurable_prod _ fun i _ => hM (σ i) i).const_mul _

/-- Each entry of the adjugate of a measurable family of matrices is measurable: it is a
determinant of a matrix whose entries are entries of the original or constants. -/
theorem measurable_matrix_adjugate {d : ℕ} {M : α → Matrix (Fin d) (Fin d) ℂ}
    (hM : ∀ i j, Measurable fun x => M x i j) (i j : Fin d) :
    Measurable fun x => (M x).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine measurable_matrix_det fun i' j' => ?_
  by_cases h : i' = j
  · simp [Matrix.updateRow_apply, h]
  · simpa [Matrix.updateRow_apply, h] using hM i' j'

/-- Each entry of the inverse of a measurable family of matrices is measurable, by the formula
`M⁻¹ = det M⁻¹ • adjugate M` -- no invertibility hypothesis is needed, the junk value being
just as measurable. -/
theorem measurable_matrix_inv {d : ℕ} {M : α → Matrix (Fin d) (Fin d) ℂ}
    (hM : ∀ i j, Measurable fun x => M x i j) (i j : Fin d) :
    Measurable fun x => (M x)⁻¹ i j := by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  exact ((measurable_matrix_det hM).inv).mul (measurable_matrix_adjugate hM i j)

end Measurability

section Pointwise

/-- **The resolvent limit onto the kernel.**  For a positive semidefinite singular matrix `B`,
the family `t • (B + t • 1)⁻¹` converges as `t = 1/(k+1) ↓ 0` to a nonzero matrix annihilated
by `B` -- in an eigenbasis its entries are `t / (λᵢ + t)`, tending to the indicator of the
kernel eigenvalues, of which singularity guarantees at least one. -/
theorem exists_tendsto_kernel_matrix {d : ℕ} {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hdet : B.det = 0) :
    ∃ Q : Matrix (Fin d) (Fin d) ℂ,
      Filter.Tendsto
        (fun k : ℕ => ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) •
          (B + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) • 1)⁻¹)
        Filter.atTop (nhds Q) ∧ B * Q = 0 ∧ Q ≠ 0 := by
  classical
  have hH : B.IsHermitian := hB.1
  set lam : Fin d → ℝ := hH.eigenvalues with hlam
  set V : Matrix (Fin d) (Fin d) ℂ := ↑hH.eigenvectorUnitary with hV
  have hVsV : star V * V = 1 := by simp [hV]
  have hVVs : V * star V = 1 := by simp [hV]
  -- The spectral theorem, with the coercions arranged once and for all.
  have hcoe : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
      = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) := rfl
  have hspec : B = V * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * star V := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [h, hcoe, hV]
  -- Conjugation by `V` is multiplicative on diagonals.
  have hsandwich : ∀ f g : Fin d → ℂ,
      (V * Matrix.diagonal f * star V) * (V * Matrix.diagonal g * star V)
        = V * Matrix.diagonal (fun i => f i * g i) * star V := by
    intro f g
    calc (V * Matrix.diagonal f * star V) * (V * Matrix.diagonal g * star V)
        = V * Matrix.diagonal f * ((star V * V) * (Matrix.diagonal g * star V)) := by
          simp only [mul_assoc]
      _ = V * Matrix.diagonal f * (Matrix.diagonal g * star V) := by rw [hVsV, one_mul]
      _ = V * (Matrix.diagonal f * Matrix.diagonal g) * star V := by simp only [mul_assoc]
      _ = V * Matrix.diagonal (fun i => f i * g i) * star V := by
          rw [Matrix.diagonal_mul_diagonal]
  -- Singularity produces a kernel eigenvalue.
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, lam i₀ = 0 := by
    have hprod := hH.det_eq_prod_eigenvalues
    rw [hdet] at hprod
    obtain ⟨i₀, _, hi₀⟩ := Finset.prod_eq_zero_iff.mp hprod.symm
    refine ⟨i₀, ?_⟩
    rw [hlam]
    simpa using hi₀
  -- The shifted matrix, diagonalised.
  have hBt : ∀ t : ℝ, 0 < t → B + ((t : ℝ) : ℂ) • 1
      = V * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ) + ((t : ℝ) : ℂ)) * star V := by
    intro t ht
    have h1 : Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ) + ((t : ℝ) : ℂ))
        = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) + ((t : ℝ) : ℂ) • 1 := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_add]
    rw [h1, Matrix.mul_add, Matrix.add_mul, ← hspec]
    congr 1
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hVVs]
  -- Its inverse, diagonalised: the shifted eigenvalues are strictly positive.
  have hne : ∀ (t : ℝ), 0 < t → ∀ i, ((lam i : ℝ) : ℂ) + ((t : ℝ) : ℂ) ≠ 0 := by
    intro t ht i
    rw [← Complex.ofReal_add, Ne, Complex.ofReal_eq_zero]
    have h0 := hB.eigenvalues_nonneg i
    rw [← hlam] at h0
    positivity
  have hinv : ∀ t : ℝ, 0 < t → (B + ((t : ℝ) : ℂ) • 1)⁻¹
      = V * Matrix.diagonal (fun i => (((lam i : ℝ) : ℂ) + ((t : ℝ) : ℂ))⁻¹) * star V := by
    intro t ht
    refine Matrix.inv_eq_right_inv ?_
    rw [hBt t ht, hsandwich]
    have hone : (fun i => (((lam i : ℝ) : ℂ) + ((t : ℝ) : ℂ))
        * (((lam i : ℝ) : ℂ) + ((t : ℝ) : ℂ))⁻¹) = fun _ => (1 : ℂ) :=
      funext fun i => mul_inv_cancel₀ (hne t ht i)
    rw [hone, Matrix.diagonal_one, mul_one, hVVs]
  -- The approximants, diagonalised.
  have hterm : ∀ k : ℕ, ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) •
        (B + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) • 1)⁻¹
      = V * Matrix.diagonal (fun i => ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ)
          * (((lam i : ℝ) : ℂ) + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ))⁻¹) * star V := by
    intro k
    have htpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    rw [hinv _ htpos, ← smul_mul_assoc, ← mul_smul_comm, ← Matrix.diagonal_smul]
    exact rfl
  set ind : Fin d → ℂ := fun i => if lam i = 0 then 1 else 0 with hind
  refine ⟨V * Matrix.diagonal ind * star V, ?_, ?_, ?_⟩
  · -- Convergence: continuous image of the entrywise scalar limits.
    have hφ : Continuous fun c : Fin d → ℂ => V * Matrix.diagonal c * star V :=
      (continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul continuous_const
    have hc : Filter.Tendsto
        (fun k : ℕ => fun i => ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ)
          * (((lam i : ℝ) : ℂ) + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ))⁻¹)
        Filter.atTop (nhds ind) := by
      rw [tendsto_pi_nhds]
      intro i
      by_cases h0 : lam i = 0
      · have hval : ∀ k : ℕ, ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ)
            * (((lam i : ℝ) : ℂ) + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ))⁻¹ = 1 := by
          intro k
          rw [h0, Complex.ofReal_zero, zero_add,
            mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (by positivity))]
        simp only [hind, ite_eq_left h0]
        exact Filter.Tendsto.congr (fun k => (hval k).symm) tendsto_const_nhds
      · have h1 : Filter.Tendsto (fun k : ℕ => ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ))
            Filter.atTop (nhds 0) := by
          have h2 := (Complex.continuous_ofReal.tendsto 0).comp
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa [one_div, Function.comp_def] using h2
        have h3 : Filter.Tendsto
            (fun k : ℕ => (((lam i : ℝ) : ℂ) + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ))⁻¹)
            Filter.atTop (nhds (((lam i : ℝ) : ℂ))⁻¹) := by
          refine Filter.Tendsto.inv₀ ?_ (Complex.ofReal_ne_zero.mpr h0)
          simpa using tendsto_const_nhds.add h1
        have h4 := h1.mul h3
        rw [zero_mul] at h4
        simpa only [hind, ite_eq_right h0] using h4
    exact Filter.Tendsto.congr (fun k => (hterm k).symm) ((hφ.tendsto ind).comp hc)
  · -- Annihilation: the eigenvalue and its kernel indicator never overlap.
    rw [hspec, hsandwich]
    have hzero : (fun i => ((lam i : ℝ) : ℂ) * ind i) = fun _ => (0 : ℂ) := by
      funext i
      by_cases h0 : lam i = 0
      · simp [hind, h0]
      · simp [hind, h0]
    rw [hzero, Matrix.diagonal_zero, mul_zero, zero_mul]
  · -- Nonvanishing: the limit fixes the eigenvector of the kernel eigenvalue.
    intro hQ0
    have hv := congrArg (fun M => M *ᵥ ⇑(hH.eigenvectorBasis i₀)) hQ0
    simp only [Matrix.zero_mulVec] at hv
    have hs : star V *ᵥ ⇑(hH.eigenvectorBasis i₀) = Pi.single i₀ 1 := by
      simpa [hV] using hH.star_eigenvectorUnitary_mulVec i₀
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs,
      Matrix.diagonal_mulVec_single] at hv
    have hone : ind i₀ * 1 = 1 := by simp [hind, hi₀]
    rw [hone] at hv
    have hV1 : V *ᵥ Pi.single i₀ 1 = ⇑(hH.eigenvectorBasis i₀) := by
      simp [hV]
    rw [hV1] at hv
    refine hH.eigenvectorBasis.orthonormal.ne_zero i₀ ?_
    ext i
    exact congrFun hv i

end Pointwise

section Selection

variable {α : Type*} [MeasurableSpace α]

/-- **Measurable selection of a unit kernel vector for a strictly wide matrix family.**

If `A x` is an `m × n` matrix depending measurably on `x` and `m < n`, then some measurable
`w` satisfies `∑ⱼ ‖w x j‖² = 1` and `∑ⱼ A x i j * w x j = 0` at *every* point.  No continuity
in `x` is assumed and the rank of `A x` may vary arbitrarily.

This is the dimension count behind the uniqueness of spectral multiplicity: a direct integral
of fibres of dimension `n` cannot be generated by `m < n` vectors, because the defect `w`
assembled here is orthogonal to everything the generators produce. -/
theorem exists_measurable_unit_nullVector {m n : ℕ} (hmn : m < n)
    {A : α → Matrix (Fin m) (Fin n) ℂ} (hA : ∀ i j, Measurable fun x => A x i j) :
    ∃ w : α → Fin n → ℂ, (∀ j, Measurable fun x => w x j) ∧
      (∀ x, ∑ j, ‖w x j‖ ^ 2 = 1) ∧ ∀ x i, ∑ j, A x i j * w x j = 0 := by
  classical
  -- The Gram matrix: positive semidefinite, measurable, singular.
  set B : α → Matrix (Fin n) (Fin n) ℂ := fun x => (A x)ᴴ * A x with hBdef
  have hBm : ∀ i j, Measurable fun x => B x i j := by
    intro i j
    simp only [hBdef, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.measurable_sum _ fun l _ =>
      (Complex.continuous_conj.measurable.comp (hA l i)).mul (hA l j)
  have hBpsd : ∀ x, (B x).PosSemidef := fun x => Matrix.posSemidef_conjTranspose_mul_self (A x)
  have hBdet : ∀ x, (B x).det = 0 := by
    intro x
    by_contra hne
    have hu : IsUnit (B x) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
    have hr : (B x).rank = n := by
      have h := Matrix.rank_of_isUnit _ hu
      simpa using h
    have hle : (B x).rank ≤ m := by
      rw [hBdef, Matrix.rank_conjTranspose_mul_self]
      simpa using (A x).rank_le_card_height
    omega
  -- The resolvent approximants and their measurable limit.
  set Qk : ℕ → α → Matrix (Fin n) (Fin n) ℂ := fun k x =>
    ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) • (B x + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) • 1)⁻¹ with hQkdef
  have hQkm : ∀ k i j, Measurable fun x => Qk k x i j := by
    intro k i j
    simp only [hQkdef, Matrix.smul_apply, smul_eq_mul]
    refine measurable_const.mul (measurable_matrix_inv (fun i' j' => ?_) i j)
    simp only [Matrix.add_apply]
    exact (hBm i' j').add measurable_const
  have hQx : ∀ x, ∃ Q : Matrix (Fin n) (Fin n) ℂ,
      Filter.Tendsto (fun k => Qk k x) Filter.atTop (nhds Q) ∧ B x * Q = 0 ∧ Q ≠ 0 :=
    fun x => exists_tendsto_kernel_matrix (hBpsd x) (hBdet x)
  set QL : α → Matrix (Fin n) (Fin n) ℂ := fun x =>
    Matrix.of fun i j => Filter.limUnder Filter.atTop fun k => Qk k x i j with hQLdef
  have hQLeq : ∀ x, QL x = (hQx x).choose := by
    intro x
    obtain ⟨htend, -, -⟩ := (hQx x).choose_spec
    refine Matrix.ext fun i j => ?_
    have hev : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M i j :=
      (continuous_apply j).comp (continuous_apply i)
    have hentry := (hev.tendsto ((hQx x).choose)).comp htend
    exact hentry.limUnder_eq
  have hQLm : ∀ i j, Measurable fun x => QL x i j := by
    intro i j
    refine measurable_of_tendsto_metrizable (f := fun k x => Qk k x i j)
      (fun k => hQkm k i j) ?_
    rw [tendsto_pi_nhds]
    intro x
    obtain ⟨htend, -, -⟩ := (hQx x).choose_spec
    rw [hQLeq x]
    have hev : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M i j :=
      (continuous_apply j).comp (continuous_apply i)
    exact (hev.tendsto ((hQx x).choose)).comp htend
  have hBQL : ∀ x, B x * QL x = 0 := by
    intro x
    rw [hQLeq x]
    exact (hQx x).choose_spec.2.1
  have hQLne : ∀ x, QL x ≠ 0 := by
    intro x
    rw [hQLeq x]
    exact (hQx x).choose_spec.2.2
  -- Select the first nonzero column, measurably.
  set Z : Fin n → Set α := fun j => {x | ∀ i, QL x i j = 0} with hZdef
  have hZm : ∀ j, MeasurableSet (Z j) := by
    intro j
    have : Z j = ⋂ i, (fun x => QL x i j) ⁻¹' {0} := by
      refine Set.ext fun x => ?_
      simp [hZdef, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [this]
    exact MeasurableSet.iInter fun i => (hQLm i j) (measurableSet_singleton 0)
  set Asel : Fin n → Set α := fun j =>
    (⋂ (j' : Fin n) (_ : j' < j), Z j') ∩ (Z j)ᶜ with hAseldef
  have hAselm : ∀ j, MeasurableSet (Asel j) :=
    fun j => (MeasurableSet.iInter fun j' => MeasurableSet.iInter fun _ => hZm j').inter
      (hZm j).compl
  -- Every point lies in exactly one selection cell.
  have hcell : ∀ x, ∃ j₀, x ∈ Asel j₀ ∧ ∀ j, j ≠ j₀ → x ∉ Asel j := by
    intro x
    have hexj : ∃ j, x ∉ Z j := by
      by_contra hall
      push Not at hall
      simp only [hZdef, Set.mem_ofPred_eq] at hall
      refine hQLne x ?_
      refine Matrix.ext fun i j => ?_
      rw [Matrix.zero_apply]
      exact hall j i
    obtain ⟨j, hj⟩ := hexj
    set S : Finset (Fin n) := Finset.univ.filter (fun j => x ∉ Z j) with hS
    have hSne : S.Nonempty := ⟨j, by simp [hS, hj]⟩
    set j₀ := S.min' hSne with hj₀
    have hj₀S : j₀ ∈ S := S.min'_mem hSne
    have hj₀Z : x ∉ Z j₀ := by
      have := hj₀S
      simp only [hS, Finset.mem_filter] at this
      exact this.2
    have hlt : ∀ j', j' < j₀ → x ∈ Z j' := by
      intro j' hj'
      by_contra hj'Z
      have hj'S : j' ∈ S := by simp [hS, hj'Z]
      exact absurd (S.min'_le j' hj'S) (not_le.mpr hj')
    have hmem : x ∈ Asel j₀ := by
      refine ⟨?_, hj₀Z⟩
      simp only [Set.mem_iInter]
      exact fun j' hj' => hlt j' hj'
    refine ⟨j₀, hmem, fun j hne hj => ?_⟩
    rcases lt_trichotomy j j₀ with h | h | h
    · exact hj.2 (hlt j h)
    · exact hne h
    · have := hj.1
      simp only [Set.mem_iInter] at this
      exact hj₀Z (this j₀ h)
  -- The unnormalised kernel vector: the selected column.
  set w₀ : α → Fin n → ℂ := fun x i => ∑ j, (Asel j).indicator (fun x => QL x i j) x
    with hw₀def
  have hw₀m : ∀ i, Measurable fun x => w₀ x i := by
    intro i
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (hQLm i j).indicator (hAselm j)
  have hw₀col : ∀ x, ∃ j₀, x ∉ Z j₀ ∧ ∀ i, w₀ x i = QL x i j₀ := by
    intro x
    obtain ⟨j₀, hmem, hnot⟩ := hcell x
    refine ⟨j₀, hmem.2, fun i => ?_⟩
    simp only [hw₀def]
    rw [Finset.sum_eq_single j₀]
    · exact Set.indicator_of_mem hmem _
    · intro j _ hne
      exact Set.indicator_of_notMem (hnot j hne) _
    · intro habs
      exact absurd (Finset.mem_univ j₀) habs
  have hw₀ne : ∀ x, ∃ i, w₀ x i ≠ 0 := by
    intro x
    obtain ⟨j₀, hj₀, hcol⟩ := hw₀col x
    simp only [hZdef, Set.mem_ofPred_eq, not_forall] at hj₀
    obtain ⟨i, hi⟩ := hj₀
    exact ⟨i, by rw [hcol i]; exact hi⟩
  -- The selected column is annihilated by the Gram matrix, hence by `A` itself.
  have hAw₀ : ∀ x, (A x) *ᵥ (w₀ x) = 0 := by
    intro x
    obtain ⟨j₀, -, hcol⟩ := hw₀col x
    have hw₀eq : w₀ x = fun i => QL x i j₀ := funext hcol
    have hB0 : B x *ᵥ (w₀ x) = 0 := by
      rw [hw₀eq]
      funext i
      have hentry := congrFun (congrFun (hBQL x) i) j₀
      simp only [Matrix.zero_apply] at hentry
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using hentry
    have h1 : star (w₀ x) ⬝ᵥ (B x *ᵥ (w₀ x)) = 0 := by
      rw [hB0, dotProduct_zero]
    simp only [hBdef] at h1
    rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec] at h1
    exact dotProduct_star_self_eq_zero.mp h1
  -- Normalise.
  set r : α → ℝ := fun x => Real.sqrt (∑ j, ‖w₀ x j‖ ^ 2) with hrdef
  have hrsum : ∀ x, 0 < ∑ j, ‖w₀ x j‖ ^ 2 := by
    intro x
    obtain ⟨i, hi⟩ := hw₀ne x
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
    positivity
  have hrpos : ∀ x, 0 < r x := fun x => Real.sqrt_pos.mpr (hrsum x)
  have hrm : Measurable r := by
    refine Real.continuous_sqrt.measurable.comp ?_
    exact Finset.measurable_sum _ fun j _ => ((hw₀m j).norm.pow_const 2)
  refine ⟨fun x j => (((r x)⁻¹ : ℝ) : ℂ) * w₀ x j, fun j => ?_, fun x => ?_, fun x i => ?_⟩
  · exact (Complex.continuous_ofReal.measurable.comp hrm.inv).mul (hw₀m j)
  · have hsq : ∀ j, ‖(((r x)⁻¹ : ℝ) : ℂ) * w₀ x j‖ ^ 2
        = ((r x)⁻¹) ^ 2 * ‖w₀ x j‖ ^ 2 := by
      intro j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (hrpos x).le), mul_pow]
    calc ∑ j, ‖(((r x)⁻¹ : ℝ) : ℂ) * w₀ x j‖ ^ 2
        = ∑ j, ((r x)⁻¹) ^ 2 * ‖w₀ x j‖ ^ 2 := Finset.sum_congr rfl fun j _ => hsq j
      _ = ((r x)⁻¹) ^ 2 * ∑ j, ‖w₀ x j‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = ((r x)⁻¹) ^ 2 * (r x) ^ 2 := by rw [hrdef, Real.sq_sqrt (hrsum x).le]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (hrpos x).ne', one_pow]
  · have h0 := congrFun (hAw₀ x) i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h0
    calc ∑ j, A x i j * ((((r x)⁻¹ : ℝ) : ℂ) * w₀ x j)
        = (((r x)⁻¹ : ℝ) : ℂ) * ∑ j, A x i j * w₀ x j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]

end Selection

end TauCeti
