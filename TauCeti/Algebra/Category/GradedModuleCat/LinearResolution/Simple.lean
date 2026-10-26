/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution
public import TauCeti.Algebra.Category.GradedModuleCat.Concentrated
public import TauCeti.Algebra.Category.GradedModuleCat.DegreeQuotient
public import TauCeti.Algebra.Module.GradedModule.Linearity
public import TauCeti.Algebra.Category.GradedModuleCat.FiniteLength
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Homology.Ext.Basic

/-!
# Simple targets detect linearity of minimal resolutions with finite-dimensional terms

For a nonnegatively graded algebra over a field, a minimal graded projective resolution with
finite-dimensional terms is linear exactly when Ext against finite simple objects concentrated
in one internal degree vanishes off the diagonal. Thus arbitrary concentrated targets in the
diagonal criterion can be replaced by simple ones.
The equivalent formulation tests internal shifts of degree-zero simple modules.

Neither semisimplicity of the degree-zero algebra nor a splitting-field assumption is needed.
The statement concerns a given minimal resolution, and does not assert existence of such a
resolution or eventual Ext vanishing.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for the simple-target diagonal Ext criterion.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded Nakayama.
-/

public section

namespace TauCeti.GradedProjectiveResolution

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {M : GradedModuleCat.{v} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{v} 𝒜)] [∀ n, Module.Finite k (r.X n)]

/-- A minimal resolution with finite-dimensional terms is linear exactly when Ext against every
finite simple graded module concentrated in degree `p` vanishes in cohomological degrees
different from `p`. This includes degree zero and works over arbitrary fields. -/
theorem IsMinimal.isLinear_iff_subsingleton_ext_simple (hr : r.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) :
    r.IsLinear ↔ ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      ∀ N : GradedModuleCat.{v} 𝒜, Module.Finite k N → Simple N →
        (∀ q, q ≠ p → N.grading.piece q = ⊥) →
        Subsingleton (Ext.{w} M N n) := by
  constructor
  · intro hlinear n p hnp N _ _ hN
    exact hlinear.subsingleton_ext_of_ne p hN n hnp
  · intro hExt
    apply (isLinear_iff_piece_le_positive_smul_top_of_finite hneg).mpr
    intro n p hpn
    let Q := (r.termObj n).degreeQuotient p
    have : Module.Finite k Q := Module.Finite.of_surjective
      (((r.termObj n).degreeQuotientπ p).hom.restrictScalars k)
      ((r.termObj n).degreeQuotientπ_surjective p)
    have hQ : IsZero Q := by
      by_contra hQ
      obtain ⟨N, f, hNfinite, hsN, hf⟩ := Q.exists_simple_quotient hQ
      have : Epi f := hf
      have : Simple N := hsN
      have hN (q : ℤ) (hq : q ≠ p) : N.grading.piece q = ⊥ :=
        GradedModuleCat.piece_eq_bot_of_surjective f
          ((GradedModuleCat.epi_iff_surjective f).mp hf) q
          ((r.termObj n).degreeQuotient_piece_eq_bot hq)
      have hHom := (hr.subsingleton_ext_iff
        (N.positive_smul_top_eq_bot_of_concentrated p hN) n).mp
        (hExt n p hpn.symm N hNfinite hsN hN)
      have : Epi ((r.termObj n).degreeQuotientπ p) :=
        (GradedModuleCat.epi_iff_surjective _).mpr
          ((r.termObj n).degreeQuotientπ_surjective p)
      exact Simple.not_isZero N (IsZero.of_epi_eq_zero
        ((r.termObj n).degreeQuotientπ p ≫ f) (hHom.elim _ 0))
    exact (r.termObj n).piece_le_positive_smul_top_of_subsingleton_hom hneg p
      (subsingleton_of_forall_eq 0 fun f ↦ hQ.eq_of_tgt f 0)

/-- Equivalently, test internal shifts of finite simple modules concentrated in degree zero.
The shift convention is `Extⁿ(M,S{p}) = 0` for `n ≠ p`. -/
theorem IsMinimal.isLinear_iff_subsingleton_ext_shiftObj_simple (hr : r.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) :
    r.IsLinear ↔ ∀ N : GradedModuleCat.{v} 𝒜, Module.Finite k N → Simple N →
      (∀ q, q ≠ 0 → N.grading.piece q = ⊥) →
        ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
          Subsingleton (Ext.{w} M (N.shiftObj p) n) := by
  constructor
  · intro hlinear N _ _ hN n p hnp
    exact hlinear.subsingleton_ext_shiftObj_of_ne hN n p hnp
  · intro hExt
    apply (hr.isLinear_iff_subsingleton_ext_simple hneg).mpr
    intro n p hnp N hNfinite hsN hN
    have : Module.Finite k N := hNfinite
    have : Simple N := hsN
    have : Simple (((GradedModuleCat.shift 𝒜) ^ (-p)).functor.obj N) := simple_obj _ N
    have hs : Simple (N.shiftObj (-p)) :=
      Simple.of_iso ((GradedModuleCat.shiftPowIso 𝒜 (-p)).app N).symm
    have hzero (q : ℤ) (hq : q ≠ 0) : (N.shiftObj (-p)).grading.piece q = ⊥ := by
      simpa [sub_eq_add_neg] using hN (q + p) (by omega)
    have : Subsingleton (Ext.{w} M ((N.shiftObj (-p)).shiftObj p) n) :=
      hExt _ inferInstance hs hzero n p hnp
    let e₁ : (N.shiftObj (-p)).shiftObj p ≅ N.shiftObj 0 := by
      simpa using (GradedModuleCat.shiftFunctorAddIso 𝒜 (-p) p).app N
    let e := e₁ ≪≫ (GradedModuleCat.shiftFunctorZeroIso 𝒜).app N
    exact (extAddEquivOfIso (Iso.refl M) e n).symm.toEquiv.subsingleton

end TauCeti.GradedProjectiveResolution
