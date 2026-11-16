/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.MinimalResolution
public import TauCeti.Algebra.Category.GradedModuleCat.Ext.Finite
public import TauCeti.Algebra.Category.GradedModuleCat.SimpleFamily
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Poincare.PowerSeries

/-!
# Unbounded Ext Poincaré series detect linear resolutions

For a minimal graded projective resolution with finite-dimensional terms, linearity is
equivalent to diagonal support of its full Ext Poincaré power series against finite simple
targets concentrated in degree zero. The cohomological support may be infinite. Only finite
internal support of each Ext degree is needed to form the Laurent coefficients.

The family criterion tests all entries of the power-series matrix of an exhaustive simple
family. Both criteria reuse the simple-target Ext-vanishing criterion for minimal resolutions;
they require neither graded Euler-admissibility nor a common cohomological bound.
For a finite-dimensional nonnegatively graded algebra with semisimple degree-zero part,
internal finiteness and the existence of finite-term minimal resolutions follow from the
algebra hypotheses, giving a criterion without preselected resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for the diagonal Ext criterion and linear resolutions.
-/

public section

namespace TauCeti.GradedProjectiveResolution

open CategoryTheory CategoryTheory.Abelian

universe w v uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {M : GradedModuleCat.{v} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{v} 𝒜)] [∀ n, Module.Finite k (r.X n)]

/-- A minimal resolution is linear exactly when its full simple-target Ext Poincaré series
have diagonal support. This remains valid for infinite cohomological support. -/
theorem IsMinimal.isLinear_iff_diagonal_bigradedExtPoincarePowerSeries (hr : r.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hfinite : ∀ (N : GradedModuleCat.{v} 𝒜), Module.Finite k N → Simple N →
      (∀ q, q ≠ 0 → N.grading.piece q = ⊥) →
        IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift 𝒜) M N) :
    r.IsLinear ↔
      ∀ (N : GradedModuleCat.{v} 𝒜) (hNfinite : Module.Finite k N) (hNsimple : Simple N)
        (hNzero : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
          (PowerSeries.coeff n (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜)
            (hfinite N hNfinite hNsimple hNzero))).coeff j = 0 := by
  constructor
  · intro hlinear N hNfinite hNsimple hNzero
    apply (diagonal_bigradedExtPoincarePowerSeries_iff _).2
    intro n j hnj
    have hshift : Subsingleton (Ext.{w} M (N.shiftObj j) n) :=
      hlinear.subsingleton_ext_shiftObj_of_ne hNzero n j hnj
    rw [← GradedModuleCat.shiftFunctor_obj] at hshift
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 j).app N) n).injective.subsingleton
  · intro hdiag
    apply (hr.isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    intro N hNfinite hNsimple hNzero n j hnj
    have hpow := ((diagonal_bigradedExtPoincarePowerSeries_iff
      (hfinite N hNfinite hNsimple hNzero)).1 (hdiag N hNfinite hNsimple hNzero)) n j hnj
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 j).app N) n).symm.injective.subsingleton

end TauCeti.GradedProjectiveResolution

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)] {I : Type uI}

/-- Chosen finite-term minimal resolutions of an exhaustive degree-zero simple family are
simultaneously linear exactly when the full Ext Poincaré matrix has diagonal support in
each entry. Internal finiteness is required only for the tested pairs of family members. -/
theorem forall_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hSzero : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜)
      (S i).obj (S j).obj)
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    (∀ i, (r i).IsLinear) ↔ ∀ i j (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      (PowerSeries.coeff n
        (bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj) h i j)).coeff p = 0 := by
  constructor
  · intro hlin i j
    simp only [bigradedExtPoincarePowerSeriesMatrix_apply]
    apply (diagonal_bigradedExtPoincarePowerSeries_iff _).2
    intro n p hnp
    have hshift : Subsingleton (Ext.{uA} (S i).obj ((S j).obj.shiftObj p) n) :=
      (hlin i).subsingleton_ext_shiftObj_of_ne (hSzero j) n p hnp
    rw [← GradedModuleCat.shiftFunctor_obj] at hshift
    exact (extLinearEquivOfIso k (Iso.refl (S i).obj)
      ((GradedModuleCat.shiftPowIso 𝒜 p).app (S j).obj) n).injective.subsingleton
  · intro hdiag i
    apply ((hr i).isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    intro N hNfinite hNsimple hNzero n p hnp
    let _ : Module.Finite k N := hNfinite
    let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    let N' : (gradedFiniteModules 𝒜).FullSubcategory :=
      ⟨N, gradedFiniteModules_iff.2 inferInstance⟩
    obtain ⟨j, ⟨eN : N'.obj ≅ (S j).obj⟩⟩ :=
      hS.exists_iso_of_concentrated S hSzero N' hNsimple hNzero
    have hij := hdiag i j
    simp only [bigradedExtPoincarePowerSeriesMatrix_apply] at hij
    have hExt := ((diagonal_bigradedExtPoincarePowerSeries_iff (h i j)).1 hij) n p hnp
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl (S i).obj)
      ((GradedModuleCat.shiftFunctor (𝒜 := 𝒜) p).mapIso eN ≪≫
        ((GradedModuleCat.shiftPowIso 𝒜 p).app (S j).obj).symm) n).injective.subsingleton

/-- Over a finite-dimensional nonnegatively graded algebra with semisimple degree-zero part,
every member of an exhaustive degree-zero simple family admits a linear resolution exactly
when the full Ext Poincaré matrix has diagonal support. Internal finiteness and finite-term
minimal resolutions are derived from these algebra hypotheses; Ext may survive in all degrees. -/
theorem forall_exists_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix
    [IsSemisimpleRing (𝒜 0)] [Module.Finite k A]
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hSzero : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    (∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear) ↔ ∀ i j (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
        (PowerSeries.coeff n (bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj)
          (fun i j ↦ (by
            let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
            exact GradedModuleCat.isGradedExtInternallyFinite_of_finite (S i).obj (S j).obj :
              IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj))
          i j)).coeff p = 0 := by
  classical
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  choose r hr hfinite using fun i ↦
    GradedProjectiveResolution.exists_isMinimal_of_finite hneg (S i).obj
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := hfinite i n
  rw [← forall_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix S hS hSzero
    (fun i j ↦ GradedModuleCat.isGradedExtInternallyFinite_of_finite (S i).obj (S j).obj)
    r hr hneg]
  constructor
  · intro hlinear i
    apply ((hr i).isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    intro N _ _ hNzero n p hnp
    obtain ⟨r', hr'⟩ := hlinear i
    exact hr'.subsingleton_ext_shiftObj_of_ne hNzero n p hnp
  · intro hlinear i
    exact ⟨r i, hlinear i⟩

end TauCeti
