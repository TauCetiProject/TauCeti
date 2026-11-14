/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Ext
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Matrix

/-!
# The Cartan–Betti alternating Euler identity `C(q) · B(q, -1) = I`

Let `A` be a graded `k`-algebra with graded Cartan map `c : K₀^gr(proj A) → G₀^gr(mod A)`. Because a
projective resolution of `M` decomposes `[M]` directly in `G₀^gr(mod A)` without passing through
`Hom(-, Sᵢ)`, the graded Cartan matrix `C(q)` and Betti Poincaré matrix `B(q, t)` satisfy the
**uncorrected** inverse equation `C(q) · B(q, -1) = I` (with no division-ring factor):

1. **Finite projective resolutions (Laurent identity over any `CommRing k`):** exactness telescopes
   `∑_{n < b} (-1)ⁿ c([Pₙ]) = [M] - (-1)^b [K_b]` in `G₀^gr(mod A)`, giving `C(q) · B(q, -1) = 1`
   in `Matrix I I (LaurentPolynomial ℤ)` when `rⱼ.X b` vanishes.
2. **Unbounded minimal resolutions (formal power-series identity over any `Field k`):** combining
   `C_psᵀ * E_ps = diag(dᵢ)` with `diag(dᵢ) * B(q, -1) = E_psᵀ` cancels `dᵢ ≠ 0` in `PowerSeries ℤ`
   to give `C_ps * B(q, -1) = 1` and `B(q, -1) = C_ps⁻¹` without splitting.
3. **Koszul specialization (`C(q) · P(-q) = I`):** minimal resolutions of `S` are all linear iff
   `(bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries` inverts `C_ps`; writing `P(q)`
   for the diagonal Betti power-series matrix with `(i, j)` entry
   `∑_{n ≥ 0} ([qⁿ][tⁿ] B_{i,j}(q, t)) Xⁿ`, linear resolutions satisfy `C(q) · P(-q) = I`.

## Main results

* `TauCeti.GradedProjectiveResolution.sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_of` and
  `TauCeti.gradedCartanMatrix_mul_bettiAlternatingSum_eq_one`: finite-resolution Laurent identity.
* `TauCeti.gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one`,
  `TauCeti.eulerPowerSeries_bettiPoincareMatrix_mul_gradedCartanMatrix_trunc_eq_one`, and
  `TauCeti.eulerPowerSeries_bettiPoincareMatrix_eq_inv_gradedCartanMatrix_trunc`: formal
  power-series Cartan–Betti inversion over arbitrary fields.
* `TauCeti.forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_eq_one` and
  `TauCeti.gradedCartanMatrix_trunc_mul_diagonalBettiPowerSeries_eq_one`: Koszul linearity criterion
  and diagonal `P(-q)` specialization.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Theorem 7.6.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *JCTA* **185** (2022), Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI

/-! ### Finite resolutions: exactness telescoping in `LaurentK0` -/

section FiniteResolution

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

namespace GradedProjectiveResolution

variable (M : (gradedFiniteModules 𝒜).FullSubcategory)
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.obj.grading) [∀ n, Module.Finite A (r.X n)]

/-- The `n`th syzygy of `r` in `(gradedFiniteModules 𝒜).FullSubcategory`: `syzygy 0 = M`,
`syzygy 1 = ker π`, and `syzygy (n + 2) = ker (d n)`, finite over `A` by exactness. -/
def syzygy : ℕ → (gradedFiniteModules 𝒜).FullSubcategory
  | 0 => M
  | 1 => ⟨GradedModuleCat.kernelObj r.augmentation,
      gradedFiniteModules_iff.mpr
        (GradedModuleCat.finite_kernelObj_of_exact
          (r.differential 0) r.augmentation r.exact_d_π)⟩
  | n + 2 => ⟨GradedModuleCat.kernelObj (r.differential n),
      gradedFiniteModules_iff.mpr
        (GradedModuleCat.finite_kernelObj_of_exact
          (r.differential (n + 1)) (r.differential n) (r.exact_d_d n))⟩

/-- The `0`th syzygy of `r` is `M`. -/
@[simp] theorem syzygy_zero : r.syzygy M 0 = M := (rfl)

/-- The `1`st syzygy of `r` has underlying object `ker r.augmentation`. -/
@[simp] theorem syzygy_one_obj : (r.syzygy M 1).obj = GradedModuleCat.kernelObj r.augmentation :=
  (rfl)

/-- The `(n + 2)`nd syzygy of `r` has underlying object `ker (r.differential n)`. -/
@[simp] theorem syzygy_add_two_obj (n : ℕ) :
    (r.syzygy M (n + 2)).obj = GradedModuleCat.kernelObj (r.differential n) := (rfl)

/-- If `r.X b` is a subsingleton, then the `b`th syzygy `(r.syzygy M b).obj` is a subsingleton. -/
theorem subsingleton_syzygy_of_subsingleton_X {b : ℕ} (hb : Subsingleton (r.X b)) :
    Subsingleton (r.syzygy M b).obj := by
  rcases b with _ | _ | k
  · exact r.surjective_π.subsingleton
  · exact GradedModuleCat.subsingleton_kernelObj_of_exact
      (r.differential 0) r.augmentation r.exact_d_π
  · exact GradedModuleCat.subsingleton_kernelObj_of_exact
      (r.differential (k + 1)) (r.differential k) (r.exact_d_d k)

private theorem gradedCartanMap_finiteProjectiveTerm_eq_syzygy_add (n : ℕ) :
    gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.syzygy M (n + 1)) +
        LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.syzygy M n) := by
  let X₂ : (gradedFiniteModules 𝒜).FullSubcategory := ⟨r.termObj n,
    r.finiteProjectiveTerm_obj n ▸
      gradedFiniteProjectiveModules_le_finiteModules _ (r.finiteProjectiveTerm n).property⟩
  have hcartan : gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) X₂ :=
    (gradedCartanMap_of (r.finiteProjectiveTerm n).property).trans (congrArg (LaurentK0.of.{uA} _)
      (ObjectProperty.FullSubcategory.ext (r.finiteProjectiveTerm_obj n)))
  rw [hcartan]
  suffices ∃ (f : (r.syzygy M (n + 1)).obj ⟶ X₂.obj) (g : X₂.obj ⟶ (r.syzygy M n).obj)
      (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact by
    obtain ⟨f, g, hfg, hse⟩ := this
    exact LaurentK0.of_conflation.{uA} (gradedFiniteModulesExactStructure 𝒜)
      ((gradedFiniteModulesExactStructure_conflation_iff
        (ShortComplex.mk (ObjectProperty.homMk f) (ObjectProperty.homMk g)
          (ObjectProperty.hom_ext _ hfg))).mpr hse)
  rcases n with _ | _ | k
  · have : Epi r.augmentation := (GradedModuleCat.epi_iff_surjective _).mpr r.surjective_π
    exact ⟨_, _, _, GradedModuleCat.shortExact_kernelι r.augmentation⟩
  · exact ⟨_, _, _, GradedModuleCat.shortExact_kernelι_kernelIsLimit_lift
      (r.differential 0) r.augmentation r.exact_d_π⟩
  · exact ⟨_, _, _, GradedModuleCat.shortExact_kernelι_kernelIsLimit_lift
      (r.differential (k + 1)) (r.differential k) (r.exact_d_d k)⟩

/-- **Partial alternating Euler sum of a graded projective resolution** in `G₀^gr(mod A)`. -/
theorem sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_sub (b : ℕ) :
    (∑ n ∈ Finset.range b,
        (-1 : ℤ) ^ n • gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M -
        (-1 : ℤ) ^ b • LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.syzygy M b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, r.gradedCartanMap_finiteProjectiveTerm_eq_syzygy_add M b,
      smul_add, pow_succ, mul_neg, mul_one, neg_zsmul]
    abel

/-- **Alternating Euler decomposition of a finite graded projective resolution.** -/
theorem sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_of {b : ℕ}
    (hb : Subsingleton (r.X b)) :
    (∑ n ∈ Finset.range b,
        (-1 : ℤ) ^ n • gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M := by
  have := r.subsingleton_syzygy_of_subsingleton_X M hb
  rw [r.sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_sub M b,
    ← LaurentK0.ofExactK0_exactK0_of.{uA} _ (r.syzygy M b),
    ExactK0.of_eq_zero_of_isZero.{uA}
      (GradedModuleCat.isZero_fullSubcategory_of_subsingleton (r.syzygy M b)),
    map_zero, smul_zero, sub_zero]

end GradedProjectiveResolution

section Matrix

variable {I : Type uI} [Fintype I] [DecidableEq I]
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (bM : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
  (M : I → (gradedFiniteModules 𝒜).FullSubcategory)
  (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
  (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
  [∀ j n, Module.Finite A ((r j).X n)]

include hbM in
/-- **Finite-resolution Cartan–Betti identity `C(q) · B(q, -1) = 1`** in
`Matrix I I (LaurentPolynomial ℤ)`. -/
theorem gradedCartanMatrix_mul_bettiAlternatingSum_eq_one {b : ℕ}
    (hb : ∀ j, Subsingleton ((r j).X b)) :
    gradedCartanMatrix 𝒜 bP bM * Matrix.of (fun i j ↦ ∑ n ∈ Finset.range b,
      (-1 : LaurentPolynomial ℤ) ^ n * PowerSeries.coeff n (bettiPoincareMatrix bP r i j)) = 1 := by
  refine Matrix.ext fun m j ↦ ?_
  have htel := congrArg (fun z ↦ bM.repr z m)
    ((r j).sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_of (M j) (hb j))
  rw [← hbM j, bM.repr_self, Finsupp.single_apply] at htel
  simp only [eq_comm (a := j)] at htel
  rw [Matrix.one_apply, ← htel, map_sum, Finsupp.finsetSum_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply, Finset.mul_sum, bettiPoincareMatrix_apply,
    GradedProjectiveResolution.coeff_bettiPoincareSeries, gradedCartanMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  conv_rhs => rw [← bP.sum_repr (LaurentK0.of.{uA} _ ((r j).finiteProjectiveTerm n))]
  rw [map_sum, map_zsmul, Finsupp.smul_apply, map_sum, Finsupp.finsetSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, zsmul_eq_mul, smul_eq_mul]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]; ring

include hbM in
/-- Left-inverse companion `B(q, -1) · C(q) = 1` in `Matrix I I (LaurentPolynomial ℤ)` for finite
resolutions. -/
theorem bettiAlternatingSum_mul_gradedCartanMatrix_eq_one {b : ℕ}
    (hb : ∀ j, Subsingleton ((r j).X b)) :
    Matrix.of (fun i j ↦ ∑ n ∈ Finset.range b,
      (-1 : LaurentPolynomial ℤ) ^ n * PowerSeries.coeff n (bettiPoincareMatrix bP r i j)) *
        gradedCartanMatrix 𝒜 bP bM = 1 :=
  mul_eq_one_comm.mp (gradedCartanMatrix_mul_bettiAlternatingSum_eq_one bP bM M hbM r hb)

end Matrix

end FiniteResolution

/-! ### Unbounded minimal resolutions: formal power-series identity `C_ps * B(q, -1) = 1` -/

section PowerSeries

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)] {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
  (bM : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
  (hbM : ∀ i, bM i = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i))

include hS hbP hbM in
/-- **The unbounded Cartan–Betti formal power-series identity `C(q) · B(q, -1) = 1`** in
`Matrix I I (PowerSeries ℤ)`, over an arbitrary field without splitting. -/
theorem gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) := fun i j ↦
      bettiPoincareMatrix_apply bP r i j ▸ (hr j).hasEulerPowerSeries_bettiPoincareSeries
        S he he₀ hI hne bP hbP (hself i) (fun p hp ↦ hconc j p hp.ne) (hconc i)) :
    ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) = 1 := by
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := Module.Finite.trans A ((r i).X n)
  have hbM_eq : bM = gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS :=
    Module.Basis.eq_of_apply_eq fun i ↦
      (hbM i).trans (gradedSimpleClassBasisOfNeZero_apply S he he₀ hne hself hS i).symm
  subst hbM_eq
  let hExt (i j : I) := GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj
    (S j).obj
  let d : I → PowerSeries ℤ := fun i ↦
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ)
  let Cps := (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
    fun p ↦ (p.trunc : PowerSeries ℤ)
  let Beul := Matrix.of fun i j ↦ Bigraded.eulerPowerSeries (hB i j)
  let Eeul := Matrix.of fun i j ↦ Bigraded.eulerPowerSeries
    ((hr i).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
      (fun p hp ↦ hconc i p hp.ne) (hconc j) (hExt i j))
  have hCE : Eeulᵀ * Cps = Matrix.diagonal d := by
    have htr := congrArg Matrix.transpose
      (gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
        S he he₀ hI hne hself hS bP hbP r hr hneg hconc hExt)
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose] at htr
  have hDB : Matrix.diagonal d * Beul = Eeulᵀ := Matrix.ext fun i j ↦ by
    have hB' := bettiPoincareMatrix_apply bP r i j ▸ hB i j
    dsimp only [Beul, Eeul]
    rw [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply,
      Bigraded.eulerPowerSeries_congr (hB i j) hB' (bettiPoincareMatrix_apply bP r i j)]
    exact (hr j).C_finrank_mul_eulerPowerSeries_bettiPoincareSeries S he he₀ hI hne bP hbP
      (hself i) (fun p hp ↦ hconc j p hp.ne) (hconc i) hB' (hExt j i)
  have hDBC : Matrix.diagonal d * (Beul * Cps) = Matrix.diagonal d * 1 := by
    rw [← Matrix.mul_assoc, hDB, hCE, mul_one]
  refine mul_eq_one_comm.mp (Matrix.ext fun i j ↦ ?_)
  have hij := congrFun (congrFun hDBC i) j
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul] at hij
  have hd_ne : d i ≠ 0 := fun h0 ↦
    ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i)).ne' <|
      Int.ofNat.inj (by simpa [d] using congrArg PowerSeries.constantCoeff h0)
  exact mul_left_cancel₀ hd_ne hij

include hS hbP hbM in
/-- Left-inverse companion `B(q, -1) · C(q) = 1` in `Matrix I I (PowerSeries ℤ)`. -/
theorem eulerPowerSeries_bettiPoincareMatrix_mul_gradedCartanMatrix_trunc_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) := fun i j ↦
      bettiPoincareMatrix_apply bP r i j ▸ (hr j).hasEulerPowerSeries_bettiPoincareSeries
        S he he₀ hI hne bP hbP (hself i) (fun p hp ↦ hconc j p hp.ne) (hconc i)) :
    Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) *
      ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) = 1 :=
  mul_eq_one_comm.mp (gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
    S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB)

include hS hbP hbM in
/-- **The alternating Betti formal power-series matrix `B(q, -1)` is `C_ps⁻¹`** in
`Matrix I I (PowerSeries ℤ)`. -/
theorem eulerPowerSeries_bettiPoincareMatrix_eq_inv_gradedCartanMatrix_trunc
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) := fun i j ↦
      bettiPoincareMatrix_apply bP r i j ▸ (hr j).hasEulerPowerSeries_bettiPoincareSeries
        S he he₀ hI hne bP hbP (hself i) (fun p hp ↦ hconc j p hp.ne) (hconc i)) :
    Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) =
      (((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
      S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB)).symm

include he₀ hne hself hS hbP hbM in
/-- **Koszul linearity equivalence via the Cartan–Betti identity.** Minimal resolutions `rⱼ` of `S`
are all linear iff `(bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries` inverts
`C_ps`. -/
theorem forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ j, (r j).IsLinear) ↔
      ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) *
        (bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries = 1 := by
  let hB (i j : I) := bettiPoincareMatrix_apply bP r i j ▸
    (hr j).hasEulerPowerSeries_bettiPoincareSeries S he he₀ hI hne bP hbP (hself i)
      (fun p hp ↦ hconc j p hp.ne) (hconc i)
  have hCB := gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
    S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB
  have hBC := eulerPowerSeries_bettiPoincareMatrix_mul_gradedCartanMatrix_trunc_eq_one
    S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB
  have hiff (i j : I) := Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff (hB i j)
    (fun n d ↦ bettiPoincareMatrix_apply bP r i j ▸
      (r j).coeff_coeff_bettiPoincareSeries_nonneg S he he₀ hI hne bP hbP (hself i) (hconc i) n d)
    (fun n d hdn ↦ bettiPoincareMatrix_apply bP r i j ▸
      (hr j).coeff_coeff_bettiPoincareSeries_eq_zero_of_lt S he he₀ hI hne bP hbP (hself i)
        (fun p hp ↦ hconc j p hp.ne) (hconc i) (by simpa using hdn))
  rw [forall_isLinear_iff_diagonal_bettiPoincareMatrix S he he₀ hI hne bP hbP r hr hself hS
    hconc hneg]
  refine ⟨fun hdiag ↦ hCB ▸ congrArg _ (Matrix.ext fun i j ↦ ((hiff i j).mpr (hdiag i j)).symm),
    fun hCM i j ↦ ?_⟩
  have heq : (bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries =
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) := by
    rw [← one_mul ((bettiPoincareMatrix bP r).map _), ← hBC, Matrix.mul_assoc, hCM, mul_one]
  exact (hiff i j).mp (congrFun (congrFun heq i) j).symm

include he₀ hne hself hS hbP hbM in
/-- **The Koszul diagonal Betti equation `C(q) · P(-q) = I` for linear resolutions**, where `P(q)`
has `(i, j)` entry `∑_{n ≥ 0} ([qⁿ][tⁿ] B_{i,j}(q, t)) Xⁿ`. -/
theorem gradedCartanMatrix_trunc_mul_diagonalBettiPowerSeries_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hlin : ∀ i, (r i).IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ PowerSeries.mk fun n ↦
        (-1 : ℤ) ^ n * (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff (n : ℤ)) = 1 := by
  have hr : ∀ i, (r i).IsMinimal := fun i ↦ (hlin i).isMinimal hneg
  have hdiag := (forall_isLinear_iff_diagonal_bettiPoincareMatrix S he he₀ hI hne bP hbP r hr
    hself hS hconc hneg).mp hlin
  convert (forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_eq_one
    S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc).mp hlin using 2
  refine Matrix.ext fun i j ↦ PowerSeries.ext fun n ↦ ?_
  rw [Matrix.of_apply, PowerSeries.coeff_mk, Matrix.map_apply,
    Bigraded.coeff_maslovEulerPowerSeries_of_diagonal (hdiag i j) n]

end PowerSeries

end TauCeti
