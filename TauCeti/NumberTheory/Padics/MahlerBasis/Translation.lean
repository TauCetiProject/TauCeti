/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.TranslationDifference.Basic

/-!
# Translation in Mahler coordinates

For a continuous function with Mahler coefficients `a n`, translation by `z : ℤ_[p]` has
coefficients `∑' k, mahler k z • a (n + k)`. The sum converges for every `n`: it is the Mahler
expansion of the `n`-th forward difference evaluated at `z`.

`PadicInt.mahlerTranslate` realizes this upper triangular coefficient operation as a linear
isometry of the native null-sequence space. Its inverse is translation by `-z`, and composing
translations adds their parameters. Scalars may be any semiring acting continuously on the
coefficient module, as in `PadicInt.mahlerLinearIsometryEquiv`.

Use `ContinuousMap.hasSum_mahlerEquiv_comp_add` to obtain both convergence and the value of
each translated coefficient. For operations on null sequences, use `PadicInt.mahlerTranslate`
and `PadicInt.hasSum_mahlerTranslate`. Natural translations admit the finite binomial formula
`PadicInt.mahlerTranslate_natCast_apply`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Mahler expansions.
* Formal sources: Mathlib's `PadicInt.hasSum_mahler` and `fwdDiff_iter_comp_add`, and
  `PadicInt.mahlerLinearIsometryEquiv` from `TauCeti.NumberTheory.Padics.MahlerBasis.Basic`.
-/

public section

open scoped ZeroAtInfty Topology

namespace ContinuousMap

open PadicInt

variable {p : ℕ} [Fact p.Prime]

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

/-- The translated Mahler coefficient is a convergent binomial-weighted tail of the original
coefficients. This statement includes translations by arbitrary p-adic integers. -/
theorem hasSum_mahlerEquiv_comp_add (f : C(ℤ_[p], E)) (z : ℤ_[p]) (n : ℕ) :
    HasSum (fun k ↦ mahler k z • mahlerEquiv E f (n + k))
      (mahlerEquiv E (f.comp ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩) n) := by
  have hcoeff (k : ℕ) :
      (fwdDiff 1)^[k] ((TauCeti.fwdDiffCLM E)^[n] f) 0 =
        mahlerEquiv E f (n + k) :=
    f.mahlerEquiv_iterate_fwdDiffCLM n k
  have h := (ContinuousMap.evalCLM ℤ_[p] z).hasSum
    (hasSum_mahler ((TauCeti.fwdDiffCLM E)^[n] f))
  have hval :
      mahlerEquiv E (f.comp ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩) n =
        (fwdDiff 1)^[n] f z := by
    simp only [mahlerEquiv_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk,
      Function.comp_def, fwdDiff_iter_comp_add, zero_add]
  rw [hval]
  simp only [ContinuousMap.evalCLM_apply, mahlerTerm_apply] at h
  simp_rw [hcoeff] at h
  simpa only [ContinuousMap.coe_iterate_fwdDiffCLM] using h

/-- Translation by `z` acts on Mahler coefficients by a binomial-weighted tail sum. -/
theorem mahlerEquiv_comp_add (f : C(ℤ_[p], E)) (z : ℤ_[p]) (n : ℕ) :
    mahlerEquiv E (f.comp ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩) n =
      ∑' k, mahler k z • mahlerEquiv E f (n + k) :=
  (hasSum_mahlerEquiv_comp_add f z n).tsum_eq.symm

end ContinuousMap

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]
variable (S E : Type*) [Semiring S] [NormedAddCommGroup E] [Module ℤ_[p] E]
  [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
  [Module S E] [ContinuousConstSMul S E]

/-- Translation on the p-adic integers, transported through Mahler's isometry to the space of
null coefficient sequences. Its coordinates are given by `mahlerTranslate_apply`. -/
noncomputable def mahlerTranslate (z : ℤ_[p]) : C₀(ℕ, E) ≃ₗᵢ[S] C₀(ℕ, E) where
  toFun a := mahlerLinearIsometryEquiv (p := p) S E
    (((mahlerLinearIsometryEquiv (p := p) S E).symm a).comp
      ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩)
  invFun a := mahlerLinearIsometryEquiv (p := p) S E
    (((mahlerLinearIsometryEquiv (p := p) S E).symm a).comp
      ⟨fun x ↦ x - z, continuous_id.sub continuous_const⟩)
  left_inv a := by
    simp only [coe_mahlerLinearIsometryEquiv, coe_mahlerLinearIsometryEquiv_symm,
      LinearIsometryEquiv.symm_apply_apply]
    convert (mahlerEquiv (p := p) E).apply_symm_apply a using 1
    congr 1
    ext x
    simp
  right_inv a := by
    simp only [coe_mahlerLinearIsometryEquiv, coe_mahlerLinearIsometryEquiv_symm,
      LinearIsometryEquiv.symm_apply_apply]
    convert (mahlerEquiv (p := p) E).apply_symm_apply a using 1
    congr 1
    ext x
    simp
  map_add' a b := by simp
  map_smul' c a := by simp
  norm_map' a := by
    dsimp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [(mahlerLinearIsometryEquiv (p := p) S E).norm_map,
      ContinuousMap.norm_eq_iSup_norm, ← (mahlerLinearIsometryEquiv (p := p) S E).symm.norm_map a,
      ContinuousMap.norm_eq_iSup_norm]
    exact (Equiv.addRight z).iSup_congr fun _ ↦ rfl

variable {S E}

/-- Evaluating a translated coefficient sequence gives the translated original function. -/
@[simp]
theorem mahlerEquiv_symm_mahlerTranslate (z : ℤ_[p]) (a : C₀(ℕ, E)) :
    (mahlerEquiv E).symm (mahlerTranslate S E z a) =
      ((mahlerEquiv E).symm a).comp ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩ := by
  simp [mahlerTranslate]

/-- Every coordinate of a translated null sequence is the sum of a convergent
binomial-weighted tail. -/
theorem hasSum_mahlerTranslate (z : ℤ_[p]) (a : C₀(ℕ, E)) (n : ℕ) :
    HasSum (fun k ↦ mahler k z • a (n + k)) (mahlerTranslate S E z a n) := by
  simpa [mahlerTranslate] using
    ContinuousMap.hasSum_mahlerEquiv_comp_add ((mahlerEquiv E).symm a) z n

/-- The explicit coefficient formula for translation in Mahler coordinates. -/
theorem mahlerTranslate_apply (z : ℤ_[p]) (a : C₀(ℕ, E)) (n : ℕ) :
    mahlerTranslate S E z a n = ∑' k, mahler k z • a (n + k) :=
  (hasSum_mahlerTranslate z a n).tsum_eq.symm

/-- For a natural translation, the coefficient formula is the finite binomial transform. -/
theorem mahlerTranslate_natCast_apply (m : ℕ) (a : C₀(ℕ, E)) (n : ℕ) :
    mahlerTranslate S E (m : ℤ_[p]) a n =
      ∑ k ∈ Finset.range (m + 1), m.choose k • a (n + k) := by
  rw [mahlerTranslate_apply, tsum_eq_sum (s := Finset.range (m + 1))]
  · simp only [mahler_natCast_eq, Nat.cast_smul_eq_nsmul]
  · intro k hk
    have hmk : m < k := by simpa using hk
    simp [mahler_natCast_eq, Nat.choose_eq_zero_of_lt hmk]

/-- The columns of Mahler translation are finite: a coordinate vector at `j` has output
`binom(z, j - n) • v` for `n ≤ j` and zero for `j < n`. -/
@[simp]
theorem mahlerTranslate_single_apply (z : ℤ_[p]) (j n : ℕ) (v : E) :
    mahlerTranslate S E z (ZeroAtInftyContinuousMap.single j v) n =
      if n ≤ j then mahler (j - n) z • v else 0 := by
  classical
  rw [mahlerTranslate_apply]
  by_cases hnj : n ≤ j
  · rw [ite_eq_left hnj, tsum_eq_single (j - n)]
    · simp [ZeroAtInftyContinuousMap.single_apply, Nat.add_sub_of_le hnj]
    · intro k hk
      have hne : n + k ≠ j := by omega
      simp [ZeroAtInftyContinuousMap.single_apply, hne]
  · rw [ite_eq_right hnj]
    have hne (k : ℕ) : n + k ≠ j := by omega
    simp [ZeroAtInftyContinuousMap.single_apply, hne]

/-- Translation by zero fixes every coefficient sequence. -/
@[simp]
theorem mahlerTranslate_zero : mahlerTranslate S E (0 : ℤ_[p]) = .refl S _ := by
  apply LinearIsometryEquiv.ext
  intro a
  apply (mahlerEquiv (p := p) E).symm.injective
  ext x
  simp

/-- The composition law for translations in Mahler coordinates. -/
theorem mahlerTranslate_add (z w : ℤ_[p]) :
    mahlerTranslate S E (z + w) = (mahlerTranslate S E z).trans (mahlerTranslate S E w) := by
  apply LinearIsometryEquiv.ext
  intro a
  apply (mahlerEquiv (p := p) E).symm.injective
  ext x
  simp [add_comm, add_left_comm]

/-- Negating the parameter gives the inverse translation. -/
@[simp]
theorem mahlerTranslate_symm (z : ℤ_[p]) :
    (mahlerTranslate S E z).symm = mahlerTranslate S E (-z) := by
  apply LinearIsometryEquiv.ext
  intro a
  apply (mahlerTranslate S E z).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := congrArg (fun e : C₀(ℕ, E) ≃ₗᵢ[S] C₀(ℕ, E) ↦ e a)
    (mahlerTranslate_add (S := S) (E := E) (-z) z)
  simpa using h

end PadicInt
