/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Ideal
public import TauCeti.Algebra.Category.GradedModuleCat.Ext.EulerAdmissible
public import TauCeti.Algebra.Category.GradedModuleCat.SimpleFamily
import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Duality

/-!
# Betti–Ext comparison and diagonal support criterion for linearity

Over a finite-dimensional nonnegatively graded algebra `A`, let `Sᵢ` be degree-zero finite graded
modules cut out by degree-zero idempotents `eᵢ` whose projective covers `A eᵢ` form a Laurent basis
`bP` of `K₀^gr(proj A)`. For a minimal graded projective resolution `r` of a graded module `M` with
finitely generated terms, this file identifies the bigraded Betti Poincaré series with the bigraded
Ext Poincaré series against `Sᵢ`, proves positivity, lower-triangularity, and Euler-finiteness of
`Bᵢ(q, t)`, and deduces the diagonal support criterion for linearity.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal`
  `.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincareSeries`:
  `dim_k(eᵢ • (Sᵢ)₀) · [qᵈ][tⁿ] Bᵢ(q, t) = dim_k Extⁿ(M, Sᵢ{d})`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.smulGradedDimension_mul_bettiPoincareSeries` and
  `TauCeti.GradedProjectiveResolution.IsMinimal`
  `.bettiPoincareSeries_eq_bigradedExtPoincarePowerSeries`:
  the power-series comparison `gdim(eᵢ • Sᵢ) · Bᵢ(q, t) = P_Ext(M, Sᵢ)(q, t)`, specializing to
  equality when `gdim(eᵢ • Sᵢ) = 1`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.coeff_coeff_bettiPoincareSeries_nonneg`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.coeff_coeff_bettiPoincareSeries_eq_zero_of_lt`, and
  `TauCeti.GradedProjectiveResolution.IsMinimal.hasEulerPowerSeries_bettiPoincareSeries`:
  nonnegativity, lower-triangularity (`d < c + n`), and slicewise Euler finiteness of `Bᵢ(q, t)`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_diagonal_bettiPoincareSeries` and
  `TauCeti.forall_isLinear_iff_diagonal_bettiPoincareMatrix`: a minimal resolution is linear if and
  only if its Betti Poincaré series is supported on the diagonal `n = d`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *Journal of Combinatorial Theory,
  Series A* **185** (2022), Sections 2.2 and 3.1--3.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Pointwise

universe uk uA uI

/-! ### Betti–Ext comparison, positivity, and lower-triangularity -/

namespace GradedProjectiveResolution

section BettiExt

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
  {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r.X n)]

private noncomputable def IsMinimal.termHomShiftObjEquivGradedExt
    (hr : r.IsMinimal) {T : GradedModuleCat.{uA} 𝒜}
    (hconcT : ∀ p, p ≠ 0 → T.grading.piece p = ⊥) (n : ℕ) (d : ℤ) :
    (r.termObj n ⟶ T.shiftObj d) ≃ₗ[k]
      GradedExt.{uA} (GradedModuleCat.shift 𝒜) M T n d :=
  have hconcShift : ∀ q, q ≠ d → (T.shiftObj d).grading.piece q = ⊥ := fun q hq => by
    simpa [InternalGrading.shift_piece, sub_eq_add_neg] using hconcT (q - d) (sub_ne_zero.mpr hq)
  (hr.extLinearEquiv ((T.shiftObj d).positive_smul_top_eq_bot_of_concentrated d hconcShift)
    n).trans
    (extLinearEquivOfIso k (Iso.refl M) ((GradedModuleCat.shiftPowIso 𝒜 d).app T).symm n)

include he he₀ hne hbP in
/-- **Coefficientwise Betti–Ext comparison.** For a minimal resolution `r` with finitely generated
terms and a degree-zero target `Sᵢ` cut out by `eᵢ`, the `(n, d)` Betti number multiplied by
`dim_k(eᵢ • (Sᵢ)₀)` equals `dim_k Extⁿ(M, Sᵢ{d})`. -/
theorem IsMinimal.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincareSeries
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (i : I) (n : ℕ) (d : ℤ) :
    (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d =
      Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) := by
  let P := r.finiteProjectiveTerm n
  let _ : Module.Projective A P.obj := (gradedFiniteProjectiveModules_iff.mp P.property).2
  have hpair := congrArg (fun p : LaurentPolynomial ℤ => p.coeff (-d))
    (gradedProjectiveExtEuler_simple_eq_mul_invert_repr S he he₀ hI hne bP hbP
      (LaurentK0.of.{uA} _ P) i)
  rw [gradedProjectiveExtEuler_of_of, gradedExtEuler_projective,
    coeff_targetShiftGradedDimension, neg_neg,
    GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i),
    coeff_C_mul, invert_apply, neg_neg] at hpair
  have hhom :
      Module.finrank k (P.obj ⟶ ((GradedModuleCat.shift 𝒜) ^ d).functor.obj (S i).obj) =
        Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) := by
    rw [r.finiteProjectiveTerm_obj n]
    exact ((GradedModuleCat.homShiftPowEquiv 𝒜 (r.termObj n) (S i).obj d).trans
      (hr.termHomShiftObjEquivGradedExt (hconc i) n d)).finrank_eq
  rw [r.coeff_bettiPoincareSeries]
  exact hpair.symm.trans (congrArg Nat.cast hhom)

include he he₀ hne hbP in
/-- **Power-series Betti–Ext comparison.** Multiplying the `i`-th Betti Poincaré series of a minimal
resolution by `gdim(eᵢ • Sᵢ)` recovers the full bigraded Ext Poincaré power series against `Sᵢ`. -/
theorem IsMinimal.smulGradedDimension_mul_bettiPoincareSeries
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (i : I)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * r.bettiPoincareSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  ext n d
  rw [PowerSeries.coeff_C_mul,
    GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i),
    coeff_C_mul, coeff_coeff_bigradedExtPoincarePowerSeries]
  exact hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincareSeries
    S he he₀ hI hne bP hbP hconc i n d

include he he₀ hne hbP in
/-- Over a splitting field where `gdim(eᵢ • Sᵢ) = 1`, the `i`-th Betti Poincaré series of a minimal
resolution coincides with the bigraded Ext Poincaré power series against `Sᵢ`. -/
theorem IsMinimal.bettiPoincareSeries_eq_bigradedExtPoincarePowerSeries
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) = 1)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    r.bettiPoincareSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  simpa only [hself, map_one, one_mul] using
    hr.smulGradedDimension_mul_bettiPoincareSeries S he he₀ hI hne bP hbP hconc i h

section NeZero

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)

include he he₀ hne hself hbP in
/-- Every Betti coefficient `[qᵈ][tⁿ] Bᵢ(q, t)` of a minimal resolution is nonnegative. -/
theorem IsMinimal.coeff_coeff_bettiPoincareSeries_nonneg
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (i : I) (n : ℕ) (d : ℤ) :
    0 ≤ (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d := by
  have hpos : (0 : ℤ) < Module.finrank k ↥(e i • (S i).obj.grading.piece 0) :=
    Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i))
  have hmul :
      0 ≤ (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d := by
    rw [hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincareSeries
      S he he₀ hI hne bP hbP hconc i n d]
    exact Int.natCast_nonneg _
  exact nonneg_of_mul_nonneg_right hmul hpos

include he he₀ hne hself hbP in
/-- **Lower-triangularity of the Betti Poincaré series.** If `M` has no nonzero graded pieces below
internal degree `c`, then `[qᵈ][tⁿ] Bᵢ(q, t) = 0` for all `d < c + n`. -/
theorem IsMinimal.coeff_coeff_bettiPoincareSeries_eq_zero_of_lt
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    {c : ℤ} (hM : ∀ p < c, M.grading.piece p = ⊥)
    (i : I) {n : ℕ} {d : ℤ} (hdn : d < c + n) :
    (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 := by
  have _ : ∀ m, Module.Finite k (r.X m) := fun m => Module.Finite.trans A (r.X m)
  have hpos : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 :=
    ne_of_gt (Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i)))
  have hmul := hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincareSeries
    S he he₀ hI hne bP hbP hconc i n d
  have _ : Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) :=
    hr.subsingleton_gradedExt_of_lt hM (hconc i) hdn
  have h0 : Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [h0, Nat.cast_zero] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hpos

include he he₀ hne hself hbP in
/-- For a minimally resolved module supported in nonnegative internal degrees, every Betti Poincaré
series satisfies `Bigraded.HasEulerPowerSeries`. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincareSeries
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hM : ∀ p < 0, M.grading.piece p = ⊥) (i : I) :
    Bigraded.HasEulerPowerSeries (r.bettiPoincareSeries bP i) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun n a han =>
    hr.coeff_coeff_bettiPoincareSeries_eq_zero_of_lt S he he₀ hI hne bP hbP hself hconc hM i
      (by omega)

include he he₀ hne hself hbP in
/-- Multiplying the Alexander-graded Euler power series of `Bᵢ(q, t)` by `dim_k(eᵢ • (Sᵢ)₀)`
recovers the Alexander-graded Euler power series of the bigraded Ext Poincaré series against
`Sᵢ`. -/
theorem IsMinimal.finrank_smul_piece_zero_mul_eulerPowerSeries_bettiPoincareSeries
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hM : ∀ p < 0, M.grading.piece p = ⊥) (i : I)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        Bigraded.eulerPowerSeries
          (hr.hasEulerPowerSeries_bettiPoincareSeries
            S he he₀ hI hne bP hbP hself hconc hM i) =
      Bigraded.eulerPowerSeries
        (let _ : ∀ m, Module.Finite k (r.X m) := fun m => Module.Finite.trans A (r.X m);
          hr.hasEulerPowerSeries_bigradedExtPoincarePowerSeries hM (hconc i) h) := by
  let _ : ∀ m, Module.Finite k (r.X m) := fun m => Module.Finite.trans A (r.X m)
  ext a
  rw [PowerSeries.coeff_C_mul,
    Bigraded.coeff_eulerPowerSeries_of_lowerTriangular _
      (fun n d hdn => hr.coeff_coeff_bettiPoincareSeries_eq_zero_of_lt
        S he he₀ hI hne bP hbP hself hconc hM i (by omega)),
    Bigraded.coeff_eulerPowerSeries_of_lowerTriangular _
      (fun n d hdn => hr.coeff_coeff_bigradedExtPoincarePowerSeries_eq_zero_of_lt
        hM (hconc i) h (by omega)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_coeff_bigradedExtPoincarePowerSeries, ← mul_assoc,
    mul_comm (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ((-1 : ℤ) ^ n),
    mul_assoc, hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincareSeries
      S he he₀ hI hne bP hbP hconc i n a]

include he he₀ hne hbP in
/-- Multiplying the Maslov-graded Euler power series of `Bᵢ(q, t)` by `dim_k(eᵢ • (Sᵢ)₀)` recovers
the Maslov-graded Euler power series of the bigraded Ext Poincaré series against `Sᵢ`. -/
theorem IsMinimal.finrank_smul_piece_zero_mul_maslovEulerPowerSeries_bettiPoincareSeries
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (i : I)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        Bigraded.maslovEulerPowerSeries (r.bettiPoincareSeries bP i) =
      Bigraded.maslovEulerPowerSeries
        (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h) := by
  have hmul := congrArg Bigraded.maslovEulerPowerSeries
    (hr.smulGradedDimension_mul_bettiPoincareSeries S he he₀ hI hne bP hbP hconc i h)
  rw [map_mul] at hmul
  have hC : Bigraded.maslovEulerPowerSeries
      (PowerSeries.C ((S i).obj.smulGradedDimension (e i))) =
      PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) := by
    ext n
    rw [Bigraded.coeff_maslovEulerPowerSeries, PowerSeries.coeff_C, PowerSeries.coeff_C]
    split_ifs with hn
    · subst hn
      rw [pow_zero, one_mul,
        GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i)]
      simp
    · rw [map_zero, mul_zero]
  rwa [hC] at hmul

/-! ### Diagonal support criterion for linearity -/

include he he₀ hne hself hbP in
/-- A Betti coefficient `[qᵈ][tⁿ] Bᵢ(q, t)` of a minimal resolution vanishes if and only if
`Extⁿ(M, Sᵢ{d})` vanishes. -/
theorem IsMinimal.coeff_coeff_bettiPoincareSeries_eq_zero_iff
    (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (i : I) (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 ↔
      Subsingleton (Ext.{uA} M ((S i).obj.shiftObj d) n) := by
  let _ : ∀ m, Module.Finite k (r.X m) := fun m => Module.Finite.trans A (r.X m)
  have hpos : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 :=
    ne_of_gt (Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i)))
  let _ : Module.Finite A (S i).obj := gradedFiniteModules_iff.mp (S i).property
  have _ : Module.Finite k (S i).obj := Module.Finite.trans A (S i).obj
  have hExtFin : Module.Finite k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) :=
    Module.Finite.equiv (hr.termHomShiftObjEquivGradedExt (hconc i) n d)
  rw [← mul_eq_zero_iff_left hpos,
    hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincareSeries
      S he he₀ hI hne bP hbP hconc i n d,
    Nat.cast_eq_zero, Module.finrank_eq_zero_iff_of_free]
  exact (extLinearEquivOfIso k (Iso.refl M)
    ((GradedModuleCat.shiftPowIso 𝒜 d).app (S i).obj) n).toEquiv.subsingleton_congr

include he he₀ hne hself hbP in
/-- **Diagonal Betti support criterion for linearity.** Over a finite-dimensional nonnegatively
graded algebra, a minimal resolution `r` with finitely generated terms is linear if and only if
every Betti Poincaré series `Bᵢ(q, t)` is supported on the diagonal `n = d`. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincareSeries
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hr : r.IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    r.IsLinear ↔
      ∀ i (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 := by
  let _ : ∀ m, Module.Finite k (r.X m) := fun m => Module.Finite.trans A (r.X m)
  constructor
  · intro hlin i n d hnd
    exact (hr.coeff_coeff_bettiPoincareSeries_eq_zero_iff
      S he he₀ hI hne bP hbP hself hconc i n d).mpr
        (hlin.subsingleton_ext_shiftObj_of_ne (hconc i) n d hnd)
  · intro hdiag
    apply (hr.isLinear_iff_subsingleton_ext_shiftObj_simple hneg).mpr
    intro N hNfin hNsimple hNzero n d hnd
    let _ : Module.Finite k N := hNfin
    let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    let N' : (gradedFiniteModules 𝒜).FullSubcategory :=
      ⟨N, gradedFiniteModules_iff.mpr inferInstance⟩
    obtain ⟨i, ⟨eN : N'.obj ≅ (S i).obj⟩⟩ :=
      hS.exists_iso_of_concentrated S hconc N' hNsimple hNzero
    have hSsub := (hr.coeff_coeff_bettiPoincareSeries_eq_zero_iff
      S he he₀ hI hne bP hbP hself hconc i n d).mp (hdiag i n d hnd)
    rw [← GradedModuleCat.shiftFunctor_obj] at hSsub ⊢
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftFunctor (𝒜 := 𝒜) d).mapIso eN) n).injective.subsingleton

end NeZero

end BettiExt

end GradedProjectiveResolution

/-! ### Diagonal support for the Betti Poincaré matrix -/

section DiagonalMatrix

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}
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

include he he₀ hne hself hS hbP in
/-- Chosen minimal resolutions with finitely generated terms of an exhaustive degree-zero simple
family are all linear if and only if the Betti Poincaré matrix `B(q, t)` has diagonal support in
every entry. -/
theorem forall_isLinear_iff_diagonal_bettiPoincareMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ j, (r j).IsLinear) ↔
      ∀ i j (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff d = 0 := by
  constructor
  · intro hlin i j n d hnd
    rw [bettiPoincareMatrix_apply]
    exact ((hr j).isLinear_iff_diagonal_bettiPoincareSeries
      S he he₀ hI hne bP hbP hself hS hneg hconc).mp (hlin j) i n d hnd
  · intro hdiag j
    exact ((hr j).isLinear_iff_diagonal_bettiPoincareSeries
      S he he₀ hI hne bP hbP hself hS hneg hconc).mpr fun i n d hnd => by
        simpa only [bettiPoincareMatrix_apply] using hdiag i j n d hnd

end DiagonalMatrix

end TauCeti
