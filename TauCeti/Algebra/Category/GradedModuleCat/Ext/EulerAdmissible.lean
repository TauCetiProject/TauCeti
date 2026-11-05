/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Ext.Finite
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.MinimalResolution
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Converse
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.FiniteLength
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Poincare.Euler

/-!
# Slicewise Euler-admissibility of finite graded modules without finite global dimension

Over a graded algebra of infinite global dimension (such as `k[ε]/(ε²)` with `deg ε > 0` or an
exterior algebra), a pair of finite graded modules need not satisfy
`TauCeti.IsGradedEulerAdmissible`: no single cohomological bound kills `Extⁿ(M, N{j})` across all
internal shifts `j : ℤ` simultaneously.

Nevertheless, in the graded module category `GradedModuleCat 𝒜`, any *fixed* pair `(M, N)` of
finite-dimensional graded modules has bounded grading support on both sides. Whenever `M` admits a
minimal graded projective resolution with finite-dimensional terms and `N` is concentrated in
degree zero, `Extⁿ(M, N{j})` vanishes for all `n` with `j < c + n`, where `c` is a lower grading
bound for `M`. Each fixed internal slice `(M, N{j})` is therefore Ext-bounded (by `(j - c + 1)₊`)
and hence ordinarily `TauCeti.IsEulerAdmissible` when internally finite, and its Euler
characteristic `χ(M, N{j})` vanishes for all `j < c`.

Propagating this property through internal shifts and graded composition series shows that over a
finite-dimensional graded algebra, **every pair of finite graded modules is ordinarily
`IsEulerAdmissible` in `GradedModuleCat 𝒜`** whenever an exhaustive degree-zero simple family admits
minimal resolutions with finite-dimensional terms — in particular whenever the algebra is
nonnegatively graded with semisimple degree-zero part — with no cohomological global-dimension
hypothesis.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.subsingleton_gradedExt_of_lt` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.hasEulerPowerSeries_bigradedExtPoincarePowerSeries`:
  Ext and the full Poincaré formal power series of a minimally resolved module vanish below a
  shifted diagonal `j = c + n`, yielding `Bigraded.HasEulerPowerSeries` when `c = 0`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.isEulerAdmissible_shiftPow` and
  `TauCeti.GradedProjectiveResolution.IsLinear.isEulerAdmissible_shiftPow`: each internal target
  shift is ordinarily Euler-admissible for minimally or linearly resolved sources, with no
  cohomological global-dimension hypothesis.
* `TauCeti.isEulerAdmissibleOn_gradedFiniteModules_of_isMinimal`,
  `TauCeti.isEulerAdmissibleOn_gradedFiniteModules_of_isLinear`, and
  `TauCeti.isEulerAdmissibleOn_gradedFiniteModules_of_semisimple`: every pair of finite graded
  modules is ordinarily `IsEulerAdmissible` in `GradedModuleCat 𝒜`, without assuming uniform
  graded Ext vanishing.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Sections 2.3--2.4.
-/

public section

namespace TauCeti.GradedProjectiveResolution

open CategoryTheory CategoryTheory.Abelian

universe w v uk uA

section CommRing

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {M : GradedModuleCat.{v} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{v} 𝒜)] [∀ n, Module.Finite k (r.X n)]

/-- **Bigraded Ext out of a minimally resolved module vanishes below a shifted diagonal.** Here
`r.IsMinimal` requires differentials to land in the strictly positive-degree action `A₊` (`0 < i`),
and `[∀ n, Module.Finite k (r.X n)]` bounds each resolution term's grading below. If `M` vanishes in
internal degrees below `c` and `N` is concentrated in degree zero, then
`GradedExt (shift 𝒜) M N n j` is a subsingleton whenever `j < c + n`, with no nonnegative algebra
grading or field hypothesis (cf. `IsMinimal.subsingleton_ext_of_lt`). -/
theorem IsMinimal.subsingleton_gradedExt_of_lt (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) {n : ℕ} {j : ℤ} (hjn : j < c + n) :
    Subsingleton (GradedExt.{w} (GradedModuleCat.shift 𝒜) M N n j) := by
  classical
  choose lb hlb using fun m ↦ (r.grading m).finite_piece_ne_bot.bddBelow
  exact GradedModuleCat.subsingleton_gradedExt_iff_subsingleton_ext_shiftObj.2 <|
    hr.subsingleton_ext_of_lt hM lb
      (fun m p hp ↦ by
        by_contra hne
        have := hlb m hne
        omega)
      (p := j) hjn _ fun q hq ↦ by
        simpa [sub_eq_add_neg] using hN (q - j) (sub_ne_zero.mpr hq)

/-- Each fixed internal shift `N{j}` of a degree-zero target is Ext-bounded against `M` by the
explicit cutoff `(j - c + 1).toNat`. -/
theorem IsMinimal.isExtBoundedBy_shiftPow (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) (j : ℤ) :
    IsExtBoundedBy.{w} M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N)
      (j - c + 1).toNat :=
  ⟨fun _ hn ↦ hr.subsingleton_gradedExt_of_lt hM hN (by omega)⟩

/-- Each fixed internal shift `N{j}` of a degree-zero target is Ext-bounded against `M`. -/
theorem IsMinimal.isExtBounded_shiftPow (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) (j : ℤ) :
    IsExtBounded.{w} M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N) :=
  ⟨_, hr.isExtBoundedBy_shiftPow hM hN j⟩

/-- Below the starting internal degree `c` of `M`, every Ext group `Extⁿ(M, N{j})` vanishes. -/
theorem IsMinimal.isExtBoundedBy_zero_shiftPow_of_lt (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) {j : ℤ} (hj : j < c) :
    IsExtBoundedBy.{w} M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N) 0 :=
  ⟨fun _ _ ↦ hr.subsingleton_gradedExt_of_lt hM hN (by omega)⟩

end CommRing

section Field

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {M : GradedModuleCat.{v} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{v} 𝒜)] [∀ n, Module.Finite k (r.X n)]

/-- **The unbounded bigraded Ext Poincaré power series of a minimally resolved module vanishes
below a shifted diagonal.** For `c = 0`, all coefficients strictly below `j = n` vanish. -/
theorem IsMinimal.coeff_coeff_bigradedExtPoincarePowerSeries_eq_zero_of_lt (hr : r.IsMinimal)
    {c : ℤ} (hM : ∀ p < c, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥)
    (h : IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift 𝒜) M N)
    {n : ℕ} {j : ℤ} (hjn : j < c + n) :
    (PowerSeries.coeff n
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h)).coeff j = 0 := by
  let _ := hr.subsingleton_gradedExt_of_lt hM hN hjn
  rw [coeff_coeff_bigradedExtPoincarePowerSeries, Module.finrank_zero_of_subsingleton,
    Nat.cast_zero]

/-- For a minimally resolved module supported in nonnegative degrees and a target concentrated in
degree zero, the unbounded Ext Poincaré power series satisfies `Bigraded.HasEulerPowerSeries`. -/
theorem IsMinimal.hasEulerPowerSeries_bigradedExtPoincarePowerSeries (hr : r.IsMinimal)
    (hM : ∀ p < 0, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥)
    (h : IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift 𝒜) M N) :
    Bigraded.HasEulerPowerSeries
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun n a han ↦
    hr.coeff_coeff_bigradedExtPoincarePowerSeries_eq_zero_of_lt hM hN h (by omega)

/-- For an internally finite pair `(M, N)` with `M` minimally resolved by finite-dimensional terms
and `N` concentrated in degree zero, every fixed target shift `(M, N{j})` is ordinarily
Euler-admissible in `GradedModuleCat 𝒜`. -/
theorem IsMinimal.isEulerAdmissible_shiftPow (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥)
    (h : IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift 𝒜) M N) (j : ℤ) :
    IsEulerAdmissible.{w} k M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N) :=
  ⟨h.isExtFinite j, hr.isExtBounded_shiftPow hM hN j⟩

/-- Below the starting internal degree `c` of `M`, the Ext-Euler characteristic `χ(M, N{j})`
vanishes for any admissibility witness. -/
theorem IsMinimal.extEuler_shiftPow_eq_zero_of_lt (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) {j : ℤ} (hj : j < c)
    (ha : IsEulerAdmissible.{w} k M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N)) :
    extEuler.{w} k ha = 0 :=
  extEuler_eq_zero_of_isExtBoundedBy_zero k ha (hr.isExtBoundedBy_zero_shiftPow_of_lt hM hN hj)

end Field

section Linear

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜]
  {M : GradedModuleCat.{v} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- Off-diagonal bigraded Ext out of a linearly resolved module against a degree-zero target
vanishes, with no minimality or termwise finite-dimensionality assumption. -/
theorem IsLinear.subsingleton_gradedExt_of_ne (hr : r.IsLinear) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) {n : ℕ} {j : ℤ} (hnj : (n : ℤ) ≠ j) :
    Subsingleton (GradedExt.{w} (GradedModuleCat.shift 𝒜) M N n j) :=
  GradedModuleCat.subsingleton_gradedExt_iff_subsingleton_ext_shiftObj.2
    (hr.subsingleton_ext_shiftObj_of_ne hN n j hnj)

/-- Each fixed internal shift `N{j}` of a degree-zero target is Ext-bounded against a linearly
resolved module `M` by `(j + 1).toNat`. -/
theorem IsLinear.isExtBoundedBy_shiftPow (hr : r.IsLinear) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) (j : ℤ) :
    IsExtBoundedBy.{w} M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N) (j + 1).toNat :=
  ⟨fun _ hn ↦ hr.subsingleton_gradedExt_of_ne hN (by omega)⟩

/-- Each fixed internal shift `N{j}` of a degree-zero target is Ext-bounded against a linearly
resolved module `M`. -/
theorem IsLinear.isExtBounded_shiftPow (hr : r.IsLinear) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) (j : ℤ) :
    IsExtBounded.{w} M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N) :=
  ⟨_, hr.isExtBoundedBy_shiftPow hN j⟩

/-- Negative internal shifts `N{j}` (`j < 0`) of a degree-zero target have no Ext against a
linearly resolved module `M`. -/
theorem IsLinear.isExtBoundedBy_zero_shiftPow_of_neg (hr : r.IsLinear) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) {j : ℤ} (hj : j < 0) :
    IsExtBoundedBy.{w} M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N) 0 :=
  ⟨fun _ _ ↦ hr.subsingleton_gradedExt_of_ne hN (by omega)⟩

end Linear

section LinearField

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜]
  {M : GradedModuleCat.{v} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- For a linearly resolved source and degree-zero target, the unbounded Ext Poincaré power series
satisfies `Bigraded.HasEulerPowerSeries`, with no minimality or termwise finite-dimensionality
hypothesis. -/
theorem IsLinear.hasEulerPowerSeries_bigradedExtPoincarePowerSeries (hr : r.IsLinear)
    {N : GradedModuleCat.{v} 𝒜} (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥)
    (h : IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift 𝒜) M N) :
    Bigraded.HasEulerPowerSeries
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h) :=
  TauCeti.hasEulerPowerSeries_bigradedExtPoincarePowerSeries h
    (fun _ _ hj ↦ hr.subsingleton_gradedExt_of_ne hN (by omega))
    (fun a ↦ hr.isExtBounded_shiftPow hN a)

/-- For a linearly resolved source and degree-zero target, every fixed target shift `(M, N{j})` is
ordinarily Euler-admissible when internally finite. -/
theorem IsLinear.isEulerAdmissible_shiftPow (hr : r.IsLinear) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥)
    (h : IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift 𝒜) M N) (j : ℤ) :
    IsEulerAdmissible.{w} k M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N) :=
  ⟨h.isExtFinite j, hr.isExtBounded_shiftPow hN j⟩

/-- For a linearly resolved source and degree-zero target, `χ(M, N{j}) = 0` for all `j < 0`. -/
theorem IsLinear.extEuler_shiftPow_eq_zero_of_neg (hr : r.IsLinear) {N : GradedModuleCat.{v} 𝒜}
    (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) {j : ℤ} (hj : j < 0)
    (ha : IsEulerAdmissible.{w} k M (((GradedModuleCat.shift 𝒜) ^ j).functor.obj N)) :
    extEuler.{w} k ha = 0 :=
  extEuler_eq_zero_of_isExtBoundedBy_zero k ha (hr.isExtBoundedBy_zero_shiftPow_of_neg hN hj)

/-- For a linearly resolved source and degree-zero target, the Alexander-graded Euler power series
coincides with the signed diagonal Ext formal power series `∑ n, (-1)ⁿ dim_k Extⁿ(M, N{n}) tⁿ`. -/
theorem IsLinear.eulerPowerSeries_bigradedExtPoincarePowerSeries_eq (hr : r.IsLinear)
    {N : GradedModuleCat.{v} 𝒜} (hN : ∀ q, q ≠ 0 → N.grading.piece q = ⊥)
    (h : IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift 𝒜) M N) :
    Bigraded.eulerPowerSeries
        (hr.hasEulerPowerSeries_bigradedExtPoincarePowerSeries hN h) =
      PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.mk fun n ↦
          (Module.finrank k (GradedExt.{w} (GradedModuleCat.shift 𝒜) M N n n) : ℤ)) := by
  have hdiag : ∀ (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
      (PowerSeries.coeff n
        (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h)).coeff j = 0 :=
    (diagonal_bigradedExtPoincarePowerSeries_iff h).2 fun _ _ hnj ↦
      hr.subsingleton_gradedExt_of_ne hN hnj
  rw [((eulerPowerSeries_eq_maslovEulerPowerSeries_bigradedExtPoincarePowerSeries_iff h
    (hr.hasEulerPowerSeries_bigradedExtPoincarePowerSeries hN h)
    (fun n j hjn ↦ hdiag n j (by omega))).2 fun _ _ hnj ↦
      hr.subsingleton_gradedExt_of_ne hN hnj),
    maslovEulerPowerSeries_bigradedExtPoincarePowerSeries_of_diagonal h hdiag]

end LinearField

end TauCeti.GradedProjectiveResolution

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v uk uA uI

section CompositionSeries

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- Ordinary Euler-admissibility in `GradedModuleCat 𝒜` against a fixed target can be tested on
finite-dimensional simple graded sources. -/
theorem isEulerAdmissible_of_finite_of_forall_simple (Y : GradedModuleCat.{v} 𝒜)
    (h : ∀ S : GradedModuleCat.{v} 𝒜, Module.Finite k S → Simple S → IsEulerAdmissible.{w} k S Y)
    (X : GradedModuleCat.{v} 𝒜) [Module.Finite k X] :
    IsEulerAdmissible.{w} k X Y :=
  X.finite_induction (fun M ↦ IsEulerAdmissible.{w} k M Y)
    (fun _ hM ↦ IsEulerAdmissible.of_isZero_left k hM) h
    (fun hS h₁ h₃ ↦ h₁.of_shortExact₂' hS h₃)

/-- Ordinary Euler-admissibility in `GradedModuleCat 𝒜` from a fixed source can be tested on
finite-dimensional simple graded targets. -/
theorem isEulerAdmissible_of_finite_of_forall_simple_right (X : GradedModuleCat.{v} 𝒜)
    (h : ∀ T : GradedModuleCat.{v} 𝒜, Module.Finite k T → Simple T → IsEulerAdmissible.{w} k X T)
    (Y : GradedModuleCat.{v} 𝒜) [Module.Finite k Y] :
    IsEulerAdmissible.{w} k X Y :=
  Y.finite_induction (fun M ↦ IsEulerAdmissible.{w} k X M)
    (fun _ hM ↦ IsEulerAdmissible.of_isZero_right k hM) h
    (fun hS h₁ h₃ ↦ h₁.of_shortExact₂ hS h₃)

end CompositionSeries

section FiniteAlgebra

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  {I : Type uI} [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]

omit [GradedAlgebra 𝒜] in
/-- If every internal shift between members of an exhaustive graded simple family is ordinarily
Euler-admissible, then every pair of finite graded modules is ordinarily Euler-admissible. -/
theorem isEulerAdmissibleOn_gradedFiniteModules_of_simple_shiftPow
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hbase : ∀ i m (j : ℤ),
      IsEulerAdmissible.{uA} k (S i).obj (((GradedModuleCat.shift 𝒜) ^ j).functor.obj (S m).obj)) :
    IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) := by
  refine ⟨fun X Y hX hY ↦ ?_⟩
  have hall : IsSlicewiseEulerAdmissible.{uA} k (GradedModuleCat.shift 𝒜) X Y := by
    refine hS.prop_on_pairs
      (IsSlicewiseEulerAdmissible.{uA} k (GradedModuleCat.shift 𝒜))
      (fun h i j ↦ h.of_iso i j) (fun h d ↦ h.shiftObj d)
      (fun h d ↦ h.shiftObjTarget d) ?_ ?_ (fun i m ↦ ⟨hbase i m⟩) hX hY
    · intro Z hZ W hW
      have := hW
      exact isSlicewiseEulerAdmissible_of_finite_of_forall_simple _ Z hZ W
    · intro Z hZ W hW
      have := hW
      exact isSlicewiseEulerAdmissible_of_finite_of_forall_simple_right _ Z hZ W
  exact (hall.isEulerAdmissible 0).of_iso (Iso.refl X)
    (((GradedModuleCat.shiftPowIso 𝒜 0).app Y) ≪≫ (GradedModuleCat.shiftFunctorZeroIso 𝒜).app Y)

/-- **Every pair of finite graded modules is ordinarily Euler-admissible in `GradedModuleCat 𝒜`**,
provided an exhaustive family of degree-zero graded simples admits minimal graded projective
resolutions with finite-dimensional terms. Unlike `IsGradedEulerAdmissibleOn`, this holds even when
the algebra has infinite global dimension and unbounded total Ext. -/
theorem isEulerAdmissibleOn_gradedFiniteModules_of_isMinimal
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)] (hr : ∀ i, (r i).IsMinimal) :
    IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) :=
  isEulerAdmissibleOn_gradedFiniteModules_of_simple_shiftPow S hS fun i m j ↦
    (hr i).isEulerAdmissible_shiftPow (c := 0) (fun p hp ↦ hconc i p hp.ne) (hconc m)
      (GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S m).obj) j

/-- **Every pair of finite graded modules is ordinarily Euler-admissible in `GradedModuleCat 𝒜`**,
provided an exhaustive family of degree-zero graded simples admits linear graded projective
resolutions. Neither minimality, finite-dimensionality of resolution terms, nor finite global
dimension is needed. -/
theorem isEulerAdmissibleOn_gradedFiniteModules_of_isLinear
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear) :
    IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) :=
  isEulerAdmissibleOn_gradedFiniteModules_of_simple_shiftPow S hS fun i m j ↦
    let ⟨_, hr⟩ := hlin i
    hr.isEulerAdmissible_shiftPow (hconc m)
      (GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S m).obj) j

/-- **Over a finite-dimensional nonnegatively graded algebra with semisimple degree-zero part,
every pair of finite graded modules is ordinarily Euler-admissible in `GradedModuleCat 𝒜`**,
assuming an exhaustive degree-zero simple family exists. No cohomological Ext bound is needed. -/
theorem isEulerAdmissibleOn_gradedFiniteModules_of_semisimple [IsSemisimpleRing (𝒜 0)]
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) := by
  classical
  choose r hr hfinite using fun i ↦
    GradedProjectiveResolution.exists_isMinimal_of_finite hneg (S i).obj
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := hfinite i n
  exact isEulerAdmissibleOn_gradedFiniteModules_of_isMinimal S hS hconc r hr

end FiniteAlgebra

end TauCeti
