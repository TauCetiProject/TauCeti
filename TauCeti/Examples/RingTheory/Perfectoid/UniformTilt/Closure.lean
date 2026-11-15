/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Closure
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.RingTheory.Huber.Prod
public import Mathlib.Algebra.CharP.Basic

/-!
# Checks for perfectoid closures

The closure theorem applies to the tilt of `ℂ_p`. Its perfectness input also applies to a
proper diagonal subring of a product: taking the closure does not force the image to be the
whole ambient ring.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltClosure

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

local instance : IsTateRing (uniformTilt p ℂ_[p]) := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p)
  apply uniformTilt.isTateRing_of_sharp (ϖ := uniformTilt.mk ϖ.root ϖ.root_succ_pow)
  simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero

-- Perfectness survives closure even for a proper image in a non-domain.
example : PerfectRing
    ((RingHom.id (uniformTilt p ℂ_[p])).prod
      (RingHom.id (uniformTilt p ℂ_[p]))).range.topologicalClosure p := by
  let : CharP (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) p := Prod.charP _ _ p
  exact RingHom.perfectRing_topologicalClosure_range _ p

-- In particular this closure omits the idempotent (0, 1).
example : (0, 1) ∉
    ((RingHom.id (uniformTilt p ℂ_[p])).prod
      (RingHom.id (uniformTilt p ℂ_[p]))).range.topologicalClosure := by
  intro hx
  have hd : (0 : uniformTilt p ℂ_[p]) = 1 :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; rfl) isClosed_diagonal hx
  exact zero_ne_one hd

-- Exercise the perfectoid conclusion and its inferred subspace structures on an actual tilt.
example (u : (uniformTilt p ℂ_[p])ˣ)
    (hu : IsPseudoUniformizer (uniformTilt.coeff p ℂ_[p] 0 u.val)) :
    let f := RingHom.id (uniformTilt p ℂ_[p])
    let S := f.range.topologicalClosure
    letI := S.isTateRing_of_isPseudoUniformizer u
      (isPseudoUniformizer_iff.mpr ⟨u.isUnit,
        uniformTilt.isTopologicallyNilpotent_iff_coeff_zero.mpr hu.isTopologicallyNilpotent⟩)
      (f.range.le_topologicalClosure ⟨_, rfl⟩) (f.range.le_topologicalClosure ⟨_, rfl⟩)
    letI : CompleteSpace S := f.range.isClosed_topologicalClosure.completeSpace_coe
    IsPerfectoidTateRing p S :=
  RingHom.isPerfectoidTateRing_topologicalClosure_range _ u hu ⟨_, rfl⟩ ⟨_, rfl⟩

-- The input unit really exists, rather than merely being assumed in the preceding check.
example : ∃ u : (uniformTilt p ℂ_[p])ˣ,
    IsPseudoUniformizer (uniformTilt.coeff p ℂ_[p] 0 u.val) := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p)
  let x := uniformTilt.mk ϖ.root ϖ.root_succ_pow
  have hx : IsUnit x := uniformTilt.isUnit_iff_coeff_zero.mpr
    (by simpa only [x, uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero.isUnit)
  exact ⟨hx.unit, by simpa only [hx.unit_spec, x, uniformTilt.coeff_mk] using
    ϖ.isPseudoUniformizer_root_zero⟩

end TauCeti.Examples.UniformTiltClosure
