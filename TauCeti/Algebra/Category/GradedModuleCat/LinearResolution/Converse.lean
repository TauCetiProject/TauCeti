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

/-!
# Detecting linearity of minimal resolutions by diagonal Ext

Over a nonnegatively graded algebra, a bounded-below minimal graded projective resolution is
linear exactly when Ext against modules concentrated in a single internal degree vanishes off
the diagonal. Such targets are automatically annihilated by positive-degree scalars.
This formulation requires neither a field nor semisimplicity of the degree-zero part; it tests
all such targets,
rather than only simple targets.

The converse uses the universal degree quotient of each resolution term to detect its pieces
modulo positive-degree action. Graded Nakayama then recovers generation in the homological degree.
For terms finite over the scalar ring, lower bounds follow from finite grading support.
The statements concern a given minimal resolution; they do not construct minimal resolutions.

Below the diagonal no test is needed: Ext out of a minimally resolved module that starts in degree
`c` vanishes in cohomological degree `n` against every target concentrated below degree `c + n`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for the diagonal Ext criterion.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded Nakayama.
-/

public section

namespace TauCeti.GradedProjectiveResolution

open CategoryTheory CategoryTheory.Abelian

universe w v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {M : GradedModuleCat.{v} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- **Ext out of a minimally resolved module vanishes below the diagonal.** If `M` has no nonzero
homogeneous elements below degree `c` and the terms of its minimal resolution are bounded below,
then `Extⁿ(M,N) = 0` for every target `N` concentrated in a degree below `c + n`. The algebra
grading need not be nonnegative. -/
theorem IsMinimal.subsingleton_ext_of_lt (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) (b : ℕ → ℤ)
    (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥) {n : ℕ} {p : ℤ} (hp : p < c + n)
    (N : GradedModuleCat.{v} 𝒜) (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) :
    Subsingleton (Ext.{w} M N n) := by
  refine (hr.subsingleton_ext_iff (N.positive_smul_top_eq_bot_of_concentrated p hN) n).mpr
    (subsingleton_of_forall_eq 0 fun f ↦ GradedModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  -- `f x` is its own degree-`p` component, the image of the vanishing component of `x`.
  have hx : (DirectSum.decompose (r.grading n).piece x p : r.X n) = 0 := by
    simpa only [hr.piece_eq_bot_of_lt hM b hbelow n hp, Submodule.mem_bot] using
      (DirectSum.decompose (r.grading n).piece x p).property
  have hfx : f.hom x ∈ N.grading.piece p := by
    rw [GradedModuleCat.piece_eq_top_of_concentrated hN]
    exact Submodule.mem_top
  have h := f.isHomogeneous.map_decompose p x
  rw [add_zero, DirectSum.decompose_of_mem_same N.grading.piece hfx] at h
  rw [← h, hx, map_zero, GradedModuleCat.hom_zero, LinearMap.zero_apply]

/-- **Diagonal Ext detects a bounded-below minimal resolution's linearity.** Test every module
concentrated in degree `p`. Neither semisimplicity nor
finite generation is needed when termwise lower bounds are supplied. -/
theorem IsMinimal.isLinear_iff_subsingleton_ext (hr : r.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (b : ℕ → ℤ)
    (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥) :
    r.IsLinear ↔ ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      ∀ N : GradedModuleCat.{v} 𝒜,
        (∀ q, q ≠ p → N.grading.piece q = ⊥) →
        Subsingleton (Ext.{w} M N n) := by
  constructor
  · intro hlinear n p hnp N hN
    exact hlinear.subsingleton_ext_of_ne p hN n hnp
  · intro hExt
    apply (isLinear_iff_piece_le_positive_smul_top hneg b hbelow).mpr
    intro n p hpn
    have hN := fun q hq ↦ (r.termObj n).degreeQuotient_piece_eq_bot (p := p) (q := q) hq
    exact (r.termObj n).piece_le_positive_smul_top_of_subsingleton_hom hneg p
      ((hr.subsingleton_ext_iff
        (((r.termObj n).degreeQuotient p).positive_smul_top_eq_bot_of_concentrated p hN) n).mp
        (hExt n p hpn.symm _ hN))

/-- For a minimal resolution with terms finite over the scalar ring, diagonal Ext vanishing
against all concentrated targets is equivalent to linearity.
Finiteness replaces the explicit termwise lower bounds. -/
theorem IsMinimal.isLinear_iff_subsingleton_ext_of_finite (hr : r.IsMinimal)
    [∀ n, Module.Finite k (r.X n)] (hneg : ∀ i < 0, 𝒜 i = ⊥) :
    r.IsLinear ↔ ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      ∀ N : GradedModuleCat.{v} 𝒜,
        (∀ q, q ≠ p → N.grading.piece q = ⊥) →
        Subsingleton (Ext.{w} M N n) := by
  classical
  choose b hb using fun n ↦ (r.grading n).finite_piece_ne_bot.bddBelow
  apply hr.isLinear_iff_subsingleton_ext hneg b
  intro n p hp
  by_contra hne
  have := hb n hne
  omega

end TauCeti.GradedProjectiveResolution
