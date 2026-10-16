/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Simple
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

## Main result

* `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_isDiagonal_bigradedExtPoincareSeries`:
  diagonal support of the bigraded Ext Poincaré series detects linearity.

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
