/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution

/-!
# Diagonal Ext from linear graded resolutions

A linear graded projective resolution has its term in homological degree `n` generated in
internal degree `n`. Against a graded module concentrated in degree `j`, that term has no
nonzero degree-zero map unless `n = j`. Consequently `Extⁿ(M,N)` vanishes off the diagonal.
In positive diagonal degrees it is naturally the module of graded maps from the corresponding
resolution term to `N`: both adjacent differentials of the Hom complex vanish.

For a target concentrated in degree zero, its shift `N{j}` is concentrated in degree `j`.
Thus the convention here is `Extⁿ(M,N{j}) = 0` for `n ≠ j`. These results require neither a
field nor a nonnegative algebra grading, and do not assert the converse existence of a linear
resolution from diagonal Ext vanishing.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for linear resolutions and the diagonal Ext criterion.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.4, for computation of
  Ext by projective resolutions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜]
  {M N : GradedModuleCat.{v} 𝒜}

namespace GradedProjectiveResolution

variable {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}

omit [DirectSum.Decomposition 𝒜] in
/-- A term of a linear resolution has no nonzero graded map to a target whose piece in the
term's generating degree vanishes. -/
theorem IsLinear.hom_eq_zero (hr : r.IsLinear) (n : ℕ)
    (hN : N.grading.piece n = ⊥) (f : r.termObj n ⟶ N) : f = 0 := by
  apply GradedModuleCat.hom_ext
  rw [GradedModuleCat.hom_zero]
  exact (r.grading n).linearMap_eq_zero_of_isGeneratedInDegree (isLinear_iff.mp hr n)
    f.isHomogeneous (by simpa using hN)

variable [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- The `n`th Ext group vanishes if the target piece in degree `n` vanishes and the source
has a linear resolution. -/
theorem IsLinear.subsingleton_ext_of_piece_eq_bot (hr : r.IsLinear) (n : ℕ)
    (hN : N.grading.piece n = ⊥) : Subsingleton (Ext.{w} M N n) := by
  let : Subsingleton (r.termObj n ⟶ N) :=
    subsingleton_of_forall_eq 0 (hr.hom_eq_zero n hN)
  let : Subsingleton (r.toProjectiveResolution.complex.X n ⟶ N) :=
    (r.toProjectiveResolutionXIso n).homCongr (Iso.refl N) |>.injective.subsingleton
  exact r.toProjectiveResolution.subsingleton_ext_of_subsingleton_hom n

/-- A linear resolution forces Ext against a target concentrated in degree `j` to vanish
outside cohomological degree `j`. -/
theorem IsLinear.subsingleton_ext_of_ne (hr : r.IsLinear) (j : ℤ)
    (hN : ∀ p, p ≠ j → N.grading.piece p = ⊥) (n : ℕ) (hn : (n : ℤ) ≠ j) :
    Subsingleton (Ext.{w} M N n) :=
  hr.subsingleton_ext_of_piece_eq_bot n (hN n hn)

/-- With the convention `(N{j})ₚ = Nₚ₋ⱼ`, a target concentrated in degree zero satisfies
`Extⁿ(M,N{j}) = 0` whenever `n ≠ j` and `M` has a linear resolution. -/
theorem IsLinear.subsingleton_ext_shiftObj_of_ne (hr : r.IsLinear)
    (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (n : ℕ) (j : ℤ)
    (hn : (n : ℤ) ≠ j) : Subsingleton (Ext.{w} M (N.shiftObj j) n) := by
  apply hr.subsingleton_ext_of_piece_eq_bot
  simpa [sub_eq_add_neg] using hN ((n : ℤ) - j) (sub_ne_zero.mpr hn)

/-- In positive degree, if the two adjacent target pieces vanish, a linear resolution computes
Ext as the graded Hom module from its corresponding term. -/
noncomputable def IsLinear.extLinearEquiv (hr : r.IsLinear) (n : ℕ)
    (hprev : N.grading.piece n = ⊥) (hnext : N.grading.piece (n + 2) = ⊥) :
    (r.termObj (n + 1) ⟶ N) ≃ₗ[k] Ext.{w} M N (n + 1) :=
  (Linear.homCongr k (r.toProjectiveResolutionXIso (n + 1)).symm (Iso.refl N)).trans
    (r.toProjectiveResolution.extLinearEquiv n
      (fun f ↦ by
        rw [r.toProjectiveResolution_complex_d]
        have hz := hr.hom_eq_zero (n + 2) hnext
          (r.differential (n + 1) ≫ (r.toProjectiveResolutionXIso (n + 1)).inv ≫ f)
        simp only [Category.assoc, hz, Limits.comp_zero])
      (fun g ↦ by
        have hz := hr.hom_eq_zero n hprev ((r.toProjectiveResolutionXIso n).inv ≫ g)
        rw [r.toProjectiveResolution_complex_d]
        simp only [Category.assoc, hz, Limits.comp_zero]))

/-- The diagonal Ext identification sends a graded map to its projective-resolution class. -/
@[simp]
theorem IsLinear.extLinearEquiv_apply (hr : r.IsLinear) (n : ℕ)
    (hprev : N.grading.piece n = ⊥) (hnext : N.grading.piece (n + 2) = ⊥)
    (f : r.termObj (n + 1) ⟶ N) :
    hr.extLinearEquiv n hprev hnext f =
      r.toProjectiveResolution.extMk ((r.toProjectiveResolutionXIso (n + 1)).hom ≫ f)
        (n + 2) rfl (by
          rw [r.toProjectiveResolution_complex_d]
          have hz := hr.hom_eq_zero (n + 2) hnext (r.differential (n + 1) ≫ f)
          simp only [Category.assoc, Iso.inv_hom_id_assoc, hz, Limits.comp_zero]) := by
  simp [IsLinear.extLinearEquiv, Linear.homCongr_apply]

/-- Against a degree-zero target, positive diagonal Ext is the graded Hom module from the
resolution term to the target shifted by its homological degree. -/
noncomputable def IsLinear.extLinearEquivShiftObj (hr : r.IsLinear)
    (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (n : ℕ) :
    (r.termObj (n + 1) ⟶ N.shiftObj (n + 1)) ≃ₗ[k]
      Ext.{w} M (N.shiftObj (n + 1)) (n + 1) :=
  hr.extLinearEquiv n
    (by simpa [sub_eq_add_neg] using hN ((n : ℤ) - (n + 1)) (by omega))
    (by simpa [sub_eq_add_neg] using hN ((n : ℤ) + 2 - (n + 1)) (by omega))

/-- The shift-diagonal identification sends a graded map to its projective-resolution class. -/
@[simp]
theorem IsLinear.extLinearEquivShiftObj_apply (hr : r.IsLinear)
    (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (n : ℕ)
    (f : r.termObj (n + 1) ⟶ N.shiftObj (n + 1)) :
    hr.extLinearEquivShiftObj hN n f =
      r.toProjectiveResolution.extMk ((r.toProjectiveResolutionXIso (n + 1)).hom ≫ f)
        (n + 2) rfl (by
          rw [r.toProjectiveResolution_complex_d]
          have hnext : (N.shiftObj (n + 1)).grading.piece (n + 2) = ⊥ := by
            simpa [sub_eq_add_neg] using hN ((n : ℤ) + 2 - (n + 1)) (by omega)
          have hz := hr.hom_eq_zero (n + 2) hnext (r.differential (n + 1) ≫ f)
          simp only [Category.assoc, Iso.inv_hom_id_assoc, hz, Limits.comp_zero]) := by
  simp [IsLinear.extLinearEquivShiftObj]

end GradedProjectiveResolution

end TauCeti
