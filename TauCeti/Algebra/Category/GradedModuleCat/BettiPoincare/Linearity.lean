/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective.Decomposition
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries
public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Diagonal support of the Betti Poincaré series and Ext duality

This file proves two complementary bridges for `TauCeti.bettiPoincareSeries` and
`TauCeti.bettiPoincareMatrix`:

1. **Diagonal-support linearity criterion without finite-dimensionality over `k`.** Over any
   nonnegatively graded `k`-algebra `A` whose degree-zero piece `𝒜 0` is spanned by complete
   orthogonal nonzero idempotents `eᵢ` with homogeneous left ideals `A eᵢ`, a finite-term graded
   projective resolution `r` is linear (`r.X n` generated in internal degree `n` for all `n`) if
   and only if every entry of its Betti Poincaré series relative to `[A eᵢ]` is supported on the
   internal/homological diagonal `p = n`. No `[Module.Finite k A]` hypothesis is needed, so the
   criterion applies directly to polynomial rings `k[X]` as well as finite-dimensional algebras.

2. **Ext–Betti identity for minimal resolutions over finite-dimensional graded algebras.** When
   `A` is finite-dimensional over `k` and the degree-zero targets `Sᵢ` are paired orthogonally
   against the idempotents `eᵢ`, any minimal resolution `r` (linear or not, bounded or infinite)
   satisfies

   `C(gdim(eᵢ • Sᵢ)) * bettiPoincareSeries bP r i = bigradedExtPoincarePowerSeries(M, Sᵢ)`.

   When `gdim(eᵢ • Sᵢ) = 1` (split simples), the Betti Poincaré series of a minimal resolution
   equals the bigraded Ext Poincaré power series on the nose; when merely `gdim(eᵢ • Sᵢ) ≠ 0`
   (e.g. nonsplitting fields), cancelling in the domain `ℤ[q,q⁻¹]` recovers the diagonal-support
   linearity criterion for non-split degree-zero parts as well.

## Main results

* `TauCeti.GradedProjectiveResolution.isLinear_iff_diagonal_bettiPoincareSeries`: `r.IsLinear`
  holds iff `(PowerSeries.coeff n (bettiPoincareSeries bP r i)).coeff p = 0` for all `p ≠ n`,
  without `[Module.Finite k A]`.
* `TauCeti.forall_isLinear_iff_diagonal_bettiPoincareMatrix`: matrix-level diagonal criterion for
  an arbitrary family of finite-term graded projective resolutions.
* `IsMinimal.C_smulGradedDimension_mul_bettiPoincareSeries_eq_bigradedExtPoincarePowerSeries`:
  `C(gdim(eᵢ • Sᵢ)) * bettiPoincareSeries bP r i = bigradedExtPoincarePowerSeries(M, Sᵢ)` for any
  minimal resolution `r`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_extPoincare`:
  unweighted equality when `gdim(eᵢ • Sᵢ) = 1`.
* `TauCeti.forall_isLinear_iff_diagonal_bettiPoincareMatrix_of_exhaustiveSimpleFamily`:
  diagonal-support linearity criterion over finite-dimensional algebras with possibly non-split
  semisimple degree-zero part (`gdim(eᵢ • Sᵢ) ≠ 0`).

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *J. Amer. Math. Soc.* **9** (1996), Sections 1.2 and 2.11.
* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge University Press (2016),
  Proposition 7.4.1, for the endomorphism-dimension factor over nonsplitting fields.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe uk uA uI uJ

/-! ### Diagonal-support linearity criterion without finite-dimensionality over `k` -/

section SplitDegreeZero

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {I : Type uI} [Fintype I] {e : I → A}
  (he : CompleteOrthogonalIdempotents e)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hneg : ∀ p < 0, 𝒜 p = ⊥)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))
  (hne : ∀ i, e i ≠ 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩)

namespace GradedProjectiveResolution

include he hI hneg hspan hne hbP in
/-- **Diagonal-support criterion for linearity of a graded projective resolution.** Over any
nonnegatively graded `k`-algebra whose degree-zero piece is spanned by complete orthogonal nonzero
idempotents `eᵢ`, a finite-term graded projective resolution `r` is linear if and only if every
entry of `bettiPoincareSeries bP r` is supported on the diagonal `p = n`. -/
theorem isLinear_iff_diagonal_bettiPoincareSeries {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] :
    r.IsLinear ↔
      ∀ (i : I) (n : ℕ) (p : ℤ), p ≠ (n : ℤ) →
        (PowerSeries.coeff n (bettiPoincareSeries bP r i)).coeff p = 0 := by
  rw [r.isLinear_iff]
  refine ⟨fun hlin i n p hpn => ?_, fun hdiag n => ?_⟩
  · rw [coeff_bettiPoincareSeries]
    have hgen : (r.finiteProjectiveTerm n).obj.grading.IsGeneratedInDegree A (n : ℤ) := by
      rw [r.finiteProjectiveTerm_obj n]
      exact hlin n
    exact (isGeneratedInDegree_iff_coeff_repr_eq_zero he hI hneg hspan hne bP hbP
      (r.finiteProjectiveTerm n) (n : ℤ)).mp hgen i p hpn
  · have hgen : (r.finiteProjectiveTerm n).obj.grading.IsGeneratedInDegree A (n : ℤ) :=
      (isGeneratedInDegree_iff_coeff_repr_eq_zero he hI hneg hspan hne bP hbP
        (r.finiteProjectiveTerm n) (n : ℤ)).mpr fun i p hpn => by
        simpa only [coeff_bettiPoincareSeries] using hdiag i n p hpn
    rwa [r.finiteProjectiveTerm_obj n] at hgen

end GradedProjectiveResolution

include he hI hneg hspan hne hbP in
/-- **Matrix-level diagonal-support criterion for linearity.** An indexed family of finite-term
graded projective resolutions is simultaneously linear if and only if every entry of its Betti
Poincaré matrix `B(q, t)` is supported on the diagonal `p = n`. -/
theorem forall_isLinear_iff_diagonal_bettiPoincareMatrix {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] :
    (∀ j, (r j).IsLinear) ↔
      ∀ (i : I) (j : J) (n : ℕ) (p : ℤ), p ≠ (n : ℤ) →
        (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff p = 0 := by
  refine ⟨fun hlin i j n p hpn => ?_, fun hdiag j => ?_⟩
  · rw [bettiPoincareMatrix_apply]
    exact ((r j).isLinear_iff_diagonal_bettiPoincareSeries he hI hneg hspan hne bP hbP).mp
      (hlin j) i n p hpn
  · refine ((r j).isLinear_iff_diagonal_bettiPoincareSeries he hI hneg hspan hne bP hbP).mpr
      fun i n p hpn => ?_
    simpa only [bettiPoincareMatrix_apply] using hdiag i j n p hpn

end SplitDegreeZero

/-! ### Ext–Betti duality for minimal resolutions over finite-dimensional algebras -/

section ExtDuality

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [Module.Finite k A] [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
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

namespace GradedProjectiveResolution

include he₀ hne hbP in
/-- **Ext–Betti identity for minimal resolutions.** Over a finite-dimensional graded `k`-algebra,
for any minimal graded projective resolution `r` of `M` (linear or not, bounded or infinite) and
degree-zero targets `Sᵢ` paired orthogonally with `eᵢ`, multiplying `bettiPoincareSeries bP r i` by
`gdim(eᵢ • Sᵢ)` gives the bigraded Ext Poincaré power series of `(M, Sᵢ)`. -/
theorem IsMinimal.C_smulGradedDimension_mul_bettiPoincareSeries_eq_bigradedExtPoincarePowerSeries
    {M : GradedModuleCat.{uA} 𝒜}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (i : I)
    (hfin : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * bettiPoincareSeries bP r i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) hfin := by
  ext n p
  rw [PowerSeries.coeff_C_mul, coeff_bettiPoincareSeries,
    coeff_coeff_bigradedExtPoincarePowerSeries]
  let P := r.finiteProjectiveTerm n
  have hpair := gradedProjectiveExtEuler_simple_eq_mul_invert_repr
    S he he₀ hI hne bP hbP (LaurentK0.of.{uA} _ P) i
  rw [gradedProjectiveExtEuler_of_of] at hpair
  have hinv := congrArg (LaurentPolynomial.invert (R := ℤ)) hpair
  have hfixed : invert ((S i).obj.smulGradedDimension (e i)) =
      (S i).obj.smulGradedDimension (e i) := by
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i), invert_C]
  rw [map_mul, hfixed, involutive_invert] at hinv
  rw [← hinv, invert_apply, gradedExtEuler_projective, coeff_targetShiftGradedDimension, neg_neg]
  have hann := GradedModuleCat.positive_smul_top_eq_bot_of_concentrated ((S i).obj.shiftObj p) p
    fun q hq => Submodule.ext fun x => by
      rw [GradedModuleCat.mem_shiftObj_piece_iff, hconc i (q - p) (sub_ne_zero.mpr hq)]
  have heq1 : Module.finrank k (P.obj ⟶ ((GradedModuleCat.shift 𝒜) ^ p).functor.obj (S i).obj) =
      Module.finrank k (r.termObj n ⟶ (S i).obj.shiftObj p) :=
    (Linear.homCongr k (eqToIso (r.finiteProjectiveTerm_obj n))
      ((GradedModuleCat.shiftPowIso 𝒜 p).app (S i).obj)).finrank_eq
  have heq2 : Module.finrank k (r.termObj n ⟶ (S i).obj.shiftObj p) =
      Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n p) :=
    ((hr.extLinearEquiv hann n).trans (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 p).app (S i).obj).symm n)).finrank_eq
  exact_mod_cast heq1.trans heq2

include he₀ hne hbP in
/-- When `gdim(eᵢ • Sᵢ) = 1` (split simple head), the `i`th Betti Poincaré series of a minimal
resolution equals the bigraded Ext Poincaré power series of `(M, Sᵢ)`. -/
theorem IsMinimal.bettiPoincareSeries_eq_extPoincare
    {M : GradedModuleCat.{uA} 𝒜}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (i : I)
    (hone : (S i).obj.smulGradedDimension (e i) = 1)
    (hfin : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    bettiPoincareSeries bP r i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) hfin := by
  simpa [hone] using
    hr.C_smulGradedDimension_mul_bettiPoincareSeries_eq_bigradedExtPoincarePowerSeries
      S he he₀ hI hne bP hbP hconc i hfin

end GradedProjectiveResolution

include he₀ hne hbP in
/-- **Diagonal-support linearity criterion over nonsplitting fields.** For a finite-dimensional
nonnegatively graded algebra and an exhaustive family of degree-zero simples `Sᵢ` with
`gdim(eᵢ • Sᵢ) ≠ 0`, chosen finite-term minimal resolutions of `Sⱼ` are simultaneously linear iff
every entry of `bettiPoincareMatrix bP r` is supported on the diagonal `p = n`. -/
theorem forall_isLinear_iff_diagonal_bettiPoincareMatrix_of_exhaustiveSimpleFamily
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal) :
    (∀ j, (r j).IsLinear) ↔
      ∀ (i j : I) (n : ℕ) (p : ℤ), p ≠ (n : ℤ) →
        (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff p = 0 := by
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  let _ (j : I) (n : ℕ) : Module.Finite k ((r j).X n) :=
    Module.Finite.trans A ((r j).X n)
  let hfin : ∀ j i, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜)
      (S j).obj (S i).obj :=
    fun j i => GradedModuleCat.isGradedExtInternallyFinite_of_finite (S j).obj (S i).obj
  rw [forall_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix S hS hconc hfin r hr hneg]
  have hentry : ∀ (i j : I) (n : ℕ) (p : ℤ),
      ((PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff p = 0) ↔
        ((PowerSeries.coeff n
          (bigradedExtPoincarePowerSeriesMatrix (fun l => (S l).obj) hfin j i)).coeff p = 0) :=
    fun i j n p => by
      obtain ⟨c, hc⟩ : ∃ c : ℤ, (S i).obj.smulGradedDimension (e i) = C c :=
        ⟨_, GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i)⟩
      have hc0 : c ≠ 0 := fun h0 => hself i (by simp [hc, h0])
      have hid := congrArg (fun f => (PowerSeries.coeff n f).coeff p)
        ((hr j).C_smulGradedDimension_mul_bettiPoincareSeries_eq_bigradedExtPoincarePowerSeries
          S he he₀ hI hne bP hbP hconc i (hfin j i))
      rw [PowerSeries.coeff_C_mul, hc, LaurentPolynomial.coeff_C_mul] at hid
      rw [bettiPoincareMatrix_apply, bigradedExtPoincarePowerSeriesMatrix_apply, ← hid,
        mul_eq_zero, or_iff_right hc0]
  exact ⟨fun h i j n p hpn => (hentry i j n p).mpr (h j i n p hpn.symm),
    fun h j i n p hnp => (hentry i j n p).mp (h i j n p hnp.symm)⟩

end ExtDuality

end TauCeti
