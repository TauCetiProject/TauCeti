/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head

import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution
import TauCeti.Algebra.Category.GradedModuleCat.Concentrated
import TauCeti.Algebra.Category.GradedModuleCat.DegreeQuotient
import TauCeti.Algebra.Module.GradedModule.Linearity

/-!
# The degree-zero Ext criterion for linear resolutions

Over a nonnegatively graded algebra with semisimple degree-zero part, a bounded-below minimal
graded projective resolution is linear exactly when Ext against shifts of `A / A₊` vanishes off
the diagonal. Here `A / A₊` is the regular head `gradedPositiveMulQuotient` at `1`.
No finite-generation, field, or finite-dimensionality hypothesis is needed.
Finitely generated resolution terms supply the lower bounds automatically.

Minimality identifies Ext with graded maps from each term. The regular module of the semisimple
degree-zero algebra detects every nonzero degree quotient of a term; graded Nakayama then
recovers generation in the homological degree.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for the degree-zero Ext criterion.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded Nakayama.
-/

public section

namespace TauCeti.GradedProjectiveResolution

open CategoryTheory CategoryTheory.Abelian

universe w uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [HasExt.{w} (GradedModuleCat.{uA} 𝒜)]

/-- **The degree-zero quotient detects linearity of a minimal resolution.** If the algebra is
nonnegatively graded with semisimple degree-zero part and the resolution terms are bounded
below, linearity is equivalent to off-diagonal Ext vanishing against shifts of `A / A₊`.
The quotient `gradedPositiveMulQuotient` at `1` is the head of the regular module. -/
theorem IsMinimal.isLinear_iff_subsingleton_ext_shiftObj_gradedPositiveMulQuotient_one
    [IsSemisimpleRing (𝒜 0)] (hr : r.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (b : ℕ → ℤ)
    (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥) :
    r.IsLinear ↔ ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      Subsingleton (Ext.{w} M
        ((gradedPositiveMulQuotient 𝒜 (SetLike.one_mem_graded 𝒜)).shiftObj p) n) := by
  let H := gradedPositiveMulQuotient 𝒜 (SetLike.one_mem_graded 𝒜)
  have hHzero : ∀ q, q ≠ 0 → H.grading.piece q = ⊥ :=
    fun q hq => gradedPositiveMulQuotient_piece_eq_bot hneg IsIdempotentElem.one
      (SetLike.one_mem_graded 𝒜) hq
  have hH (p q : ℤ) (hqp : q ≠ p) : (H.shiftObj p).grading.piece q = ⊥ :=
    H.shiftObj_piece_eq_bot_of_concentrated p hHzero q (by simpa using hqp)
  constructor
  · intro hlinear n p hnp
    exact hlinear.subsingleton_ext_shiftObj_of_ne hHzero n p hnp
  · intro hExt
    apply (isLinear_iff_piece_le_positive_smul_top hneg b hbelow).2
    intro n p hpn
    let Q := (r.termObj n).degreeQuotient p
    have hQ : ∀ q, q ≠ p → Q.grading.piece q = ⊥ :=
      fun q hq => (r.termObj n).degreeQuotient_piece_eq_bot hq
    have hHom : Subsingleton (r.termObj n ⟶ H.shiftObj p) :=
      (hr.subsingleton_ext_iff
        ((H.shiftObj p).positive_smul_top_eq_bot_of_concentrated p (hH p)) n).1
        (hExt n p hpn.symm)
    have : Subsingleton Q :=
      GradedModuleCat.subsingleton_of_subsingleton_hom_shiftObj_gradedPositiveMulQuotient_one
        hneg p hQ (subsingleton_of_forall_eq
          (GradedModuleCat.degreeQuotientLift p (hH p) (0 : r.termObj n ⟶ H.shiftObj p))
          fun f => GradedModuleCat.degreeQuotientLift_unique p (hH p) 0 f
            (hHom.elim _ _))
    exact (r.termObj n).piece_le_positive_smul_top_of_subsingleton_hom hneg p
      GradedModuleCat.hom_injective.subsingleton

/-- For a minimal resolution with terms finitely generated over the graded algebra,
off-diagonal Ext vanishing against shifts of `A / A₊` is equivalent to linearity. -/
theorem IsMinimal.isLinear_iff_subsingleton_ext_shiftObj_gradedPositiveMulQuotient_one_of_finite
    [IsSemisimpleRing (𝒜 0)] [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) :
    r.IsLinear ↔ ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      Subsingleton (Ext.{w} M
        ((gradedPositiveMulQuotient 𝒜 (SetLike.one_mem_graded 𝒜)).shiftObj p) n) := by
  classical
  choose b hb using fun n ↦
    (r.grading n).bddBelow_setOf_piece_ne_bot 𝒜 hneg
  apply hr.isLinear_iff_subsingleton_ext_shiftObj_gradedPositiveMulQuotient_one hneg b
  intro n p hp
  by_contra hne
  have := hb n hne
  omega

end TauCeti.GradedProjectiveResolution
