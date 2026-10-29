/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.MinimalResolution
public import TauCeti.Algebra.Category.GradedModuleCat.SimpleFamily
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Poincare

/-!
# Detecting linear resolutions by bigraded Ext Poincaré series

For a minimal graded projective resolution with finite-dimensional terms over a nonnegatively
graded algebra, linearity is equivalent to diagonal support of the full bigraded Ext Poincaré
series against every finite simple target concentrated in degree zero.  The coefficient in
bidegree `(n,j)` is `dim_k Extⁿ(M,S{j})`, so diagonal support retains precisely the off-diagonal
vanishing data needed for the converse; the one-variable diagonal Poincaré polynomial alone does
not retain that data.

The statement assumes graded Euler-admissibility for the simple targets being tested.  This makes
the Poincaré series finite without replacing Ext-vanishing by a totalized infinite sum.

For an exhaustive family of finite simple modules concentrated in degree zero, the pointwise
criterion assembles into simultaneous linearity exactly when every entry of the family's full
bigraded Ext Poincaré matrix is diagonal.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_isDiagonal_bigradedExtPoincareSeries`:
  diagonal support of the bigraded Ext Poincaré series detects linearity.
* `TauCeti.forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal`: simultaneous linearity of
  chosen minimal resolutions is equivalent to diagonal support of every matrix entry.
* `TauCeti.forall_exists_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal`: over a semisimple
  degree-zero part, the same criterion without a preselected family of resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for the diagonal bigraded Ext criterion for linear resolutions.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for minimal graded
  projective resolutions and graded Nakayama.
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

/-- **A minimal resolution is linear exactly when its simple-target bigraded Ext Poincaré
series are diagonal.**  The targets range over finite simple graded modules concentrated in
degree zero.  Graded Euler-admissibility makes each full bigraded series finite; any valid
cohomological truncation bound computes the same series. -/
theorem IsMinimal.isLinear_iff_isDiagonal_bigradedExtPoincareSeries (hr : r.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hadm : ∀ (N : GradedModuleCat.{v} 𝒜), Module.Finite k N → Simple N →
      (∀ q, q ≠ 0 → N.grading.piece q = ⊥) →
        IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) M N) :
    r.IsLinear ↔
      ∀ (N : GradedModuleCat.{v} 𝒜) (hNfinite : Module.Finite k N) (hNsimple : Simple N)
        (hNzero : ∀ q, q ≠ 0 → N.grading.piece q = ⊥) (b : ℕ)
        (_hb : IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) M N b),
          Bigraded.IsDiagonal (bigradedExtPoincareSeries.{w} k (GradedModuleCat.shift 𝒜)
            (hadm N hNfinite hNsimple hNzero).internallyFinite b) := by
  constructor
  · intro hlinear N hNfinite hNsimple hNzero b hb
    apply (isDiagonal_bigradedExtPoincareSeries_iff _ hb).2
    intro n j hnj
    have hshift : Subsingleton (Ext.{w} M (N.shiftObj j) n) :=
      hlinear.subsingleton_ext_shiftObj_of_ne hNzero n j hnj
    rw [← GradedModuleCat.shiftFunctor_obj] at hshift
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 j).app N) n).injective.subsingleton
  · intro hdiag
    apply (hr.isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    intro N hNfinite hNsimple hNzero n j hnj
    let h := hadm N hNfinite hNsimple hNzero
    obtain ⟨b, hb⟩ := h.bounded.exists_bound
    have hpow : Subsingleton
        (GradedExt.{w} (GradedModuleCat.shift 𝒜) M N n j) :=
      ((isDiagonal_bigradedExtPoincareSeries_iff h.internallyFinite hb).1
        (hdiag N hNfinite hNsimple hNzero b hb)) n j hnj
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 j).app N) n).symm.injective.subsingleton

end TauCeti.GradedProjectiveResolution

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}

/-- **Chosen minimal resolutions of an exhaustive simple family are linear exactly when every
entry of its full bigraded Ext Poincaré matrix is diagonal.** The family is exhaustive up to
internal shift, while its chosen representatives are concentrated in degree zero. The matrix
uses any common cohomological Ext bound. -/
theorem forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hSzero : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (∀ i, (r i).IsLinear) ↔
      ∀ i j, Bigraded.IsDiagonal
        (bigradedExtPoincareMatrix (fun i ↦ (S i).obj)
          (fun i j ↦ (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite)
          b i j) := by
  constructor
  · intro hlin i j
    rw [bigradedExtPoincareMatrix_apply]
    apply (isDiagonal_bigradedExtPoincareSeries_iff _ (hb i j)).2
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
    rw [bigradedExtPoincareMatrix_apply] at hij
    have hExt : Subsingleton
        (GradedExt.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj n p) :=
      ((isDiagonal_bigradedExtPoincareSeries_iff
        (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite
        (hb i j)).1 hij) n p hnp
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl (S i).obj)
      ((GradedModuleCat.shiftFunctor (𝒜 := 𝒜) p).mapIso eN ≪≫
        ((GradedModuleCat.shiftPowIso 𝒜 p).app (S j).obj).symm) n).injective.subsingleton

/-- **Bigraded Ext detects linear resolutions over a semisimple degree-zero part.** Suppose that
`A` is finite-dimensional and nonnegatively graded, with semisimple degree-zero part. For an
exhaustive family of finite simple modules concentrated in degree zero, every simple admits a
linear graded projective resolution if and only if every entry of the full bigraded Ext Poincare
matrix has diagonal support.

Unlike `TauCeti.forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal`, this statement does not
take a preselected family of minimal resolutions: their existence, with finite-dimensional terms,
follows from semisimplicity of the degree-zero part. -/
theorem forall_exists_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal
    [IsSemisimpleRing (𝒜 0)] [Module.Finite k A]
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hSzero : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear) ↔
      ∀ i j, Bigraded.IsDiagonal
        (bigradedExtPoincareMatrix (fun i ↦ (S i).obj)
          (fun i j ↦ (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite)
          b i j) := by
  classical
  choose r hr hfinite using fun i ↦
    GradedProjectiveResolution.exists_isMinimal_of_finite hneg (S i).obj
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := hfinite i n
  rw [← forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal
    S hS hSzero h r hr hneg hb]
  constructor
  · intro hlinear i
    apply ((hr i).isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    intro N hNfinite hNsimple hNzero n p hnp
    obtain ⟨r', hr'⟩ := hlinear i
    exact hr'.subsingleton_ext_shiftObj_of_ne hNzero n p hnp
  · intro hlinear i
    exact ⟨r i, hlinear i⟩

end TauCeti
