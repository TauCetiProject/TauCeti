/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Subring
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for the untilt along an ideal of `𝕎 R⁺`

These checks take for `(R, R⁺)` the tilt `ℂ_p♭` of `ℂ_p` with its power-bounded subring, a
perfect complete Hausdorff Tate ring of characteristic `p`.

* Compatibility: `p` is primitive, so the untilt along `(p)` is a complete Hausdorff Tate ring
  into which `𝕎 R⁺ ⧸ (p)` embeds.
* Degenerate case: the untilt along the unit ideal is the zero ring.
* Computation: for every ideal `J`, the class of `[ϖ]` of a pseudouniformiser `ϖ ∈ R⁺` is a
  pseudouniformiser of the untilt, which is `(𝕎 R⁺ ⧸ J)[1/[ϖ]]`.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.PrimitiveUntilt

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

private noncomputable def parameter : PseudoUniformizerRoots p ℂ_[p] :=
  Classical.choice (nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p))

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  uniformTilt.isTateRing_of_sharp (ϖ := (parameter p).toTilt)
    (by simpa using (parameter p).isPseudoUniformizer_root_zero)

/-- The Huber pair `(ℂ_p♭, ℂ_p♭°)`. -/
private noncomputable abbrev pair : Pair (uniformTilt p ℂ_[p]) := Pair.powerBounded _

-- Compatibility: the untilt along the primitive ideal `(p)` is complete and Hausdorff.
example : CompleteSpace (untilt p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)})) :=
  untilt.completeSpace WittVector.isPrimitive_p

example : T2Space (untilt p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)})) :=
  untilt.t2Space WittVector.isPrimitive_p

-- Compatibility: `𝕎 R⁺ ⧸ (p)` embeds into the untilt along `(p)`.
example : Function.Injective
    (algebraMap (WittVector p (pair p).plus ⧸ Ideal.span {(p : WittVector p (pair p).plus)})
      (untilt p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)}))) :=
  untilt.algebraMap_injective WittVector.isPrimitive_p

-- Degenerate case: the untilt along the unit ideal is the zero ring.
example : Subsingleton (untilt p (pair p) ⊤) := by
  refine IsLocalization.subsingleton
    (M := (untiltDenominators p (pair p)).map (Ideal.Quotient.mk ⊤)) ?_
  exact ⟨1, one_mem _, Ideal.Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩

-- Computation: the class of `[ϖ]` is a pseudouniformiser, and the untilt is `(𝕎 R⁺ ⧸ J)[1/[ϖ]]`.
example (J : Ideal (WittVector p (pair p).plus)) (ϖ : (pair p).plus)
    (hϖ : IsPseudoUniformizer (ϖ : uniformTilt p ℂ_[p])) :
    IsPseudoUniformizer (algebraMap _ (untilt p (pair p) J)
      (Ideal.Quotient.mk J (WittVector.teichmuller p ϖ))) ∧
    IsLocalization.Away (Ideal.Quotient.mk J (WittVector.teichmuller p ϖ)) (untilt p (pair p) J) :=
  ⟨untilt.isPseudoUniformizer_algebraMap hϖ, untilt.isLocalizationAway hϖ⟩

end TauCeti.Examples.PrimitiveUntilt
