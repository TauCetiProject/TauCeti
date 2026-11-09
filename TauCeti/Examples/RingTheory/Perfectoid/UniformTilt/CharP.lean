/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.CharP
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Tate
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.RingTheory.Huber.Prod
public import Mathlib.Algebra.CharP.Basic
import TauCeti.RingTheory.Huber.Perfect

/-!
# Characteristic-`p` self-identification on an actual tilt

The tilt of `ℂ_p` is a perfect Tate ring of characteristic `p`. Tilting it again recovers
its elements and their compatible roots. These importing-only checks also exercise a
nontrivial idempotent in its square, the chosen power-bounded integral subring, and convergence
under the inverse homeomorphism. The mixed-characteristic ring `ℂ_p` itself cannot satisfy
the same self-identification.
-/

public section

open Filter Topology TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltCharP

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

local instance : IsTateRing (uniformTilt p ℂ_[p]) := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p)
  apply uniformTilt.isTateRing_of_sharp (ϖ := uniformTilt.mk ϖ.root ϖ.root_succ_pow)
  simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero

local instance : IsUniform (uniformTilt p ℂ_[p]) := IsUniform.of_perfectRing p

local instance : Fact (IsTopologicallyNilpotent (p : uniformTilt p ℂ_[p])) :=
  ⟨by rw [CharP.cast_eq_zero]; exact IsTopologicallyNilpotent.zero⟩

-- Every coordinate of the inverse recovers the corresponding tail of a nonzero root system.
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) (n m : ℕ) :
    uniformTilt.coeff p ℂ_[p] m
      (uniformTilt.coeff p (uniformTilt p ℂ_[p]) n
        ((uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p])).symm
          (uniformTilt.mk ϖ.root ϖ.root_succ_pow))) = ϖ.root (m + n) := by
  let roots (k : ℕ) : uniformTilt p ℂ_[p] :=
    uniformTilt.mk (fun i ↦ ϖ.root (i + k)) (fun i ↦ by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ϖ.root_succ_pow (i + k))
  have hroots (k : ℕ) : roots (k + 1) ^ p = roots k := by
    apply uniformTilt.ext
    intro i
    simpa [roots, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ϖ.root_succ_pow (i + k)
  let y := uniformTilt.mk roots hroots
  have hy : uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p]) y =
      uniformTilt.mk ϖ.root ϖ.root_succ_pow := by
    apply uniformTilt.ext
    intro i
    simp [y, roots]
  have hinv : (uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p])).symm
      (uniformTilt.mk ϖ.root ϖ.root_succ_pow) = y := by
    apply (uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p])).injective
    simp [hy]
  simp [hinv, y, roots]

-- The inverse homeomorphism carries the powers of a pseudouniformiser to a null sequence.
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    Tendsto (fun n : ℕ ↦ (uniformTilt.homeomorphOfCharP p (uniformTilt p ℂ_[p])).symm
      ((uniformTilt.mk ϖ.root ϖ.root_succ_pow) ^ n)) atTop (𝓝 0) := by
  have hx : IsTopologicallyNilpotent (uniformTilt.mk ϖ.root ϖ.root_succ_pow) :=
    uniformTilt.isTopologicallyNilpotent_iff_coeff_zero.mpr
      (by simpa using ϖ.isPseudoUniformizer_root_zero.isTopologicallyNilpotent)
  have hc := (uniformTilt.homeomorphOfCharP p (uniformTilt p ℂ_[p])).symm.continuous
  simpa [Function.comp_def] using (hc.tendsto 0).comp hx

-- A genuinely topologically nilpotent integral element remains a pseudouniformiser upstairs.
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    ∃ b : powerBoundedSubring (uniformTilt p ℂ_[p]),
      (b : uniformTilt p ℂ_[p]) = uniformTilt.mk ϖ.root ϖ.root_succ_pow ∧
      IsPseudoUniformizer
        (((uniformTilt.plusEquivOfCharP p
          (isRingOfIntegralElements_powerBoundedSubring _)).symm b :
            uniformTilt p (uniformTilt p ℂ_[p]))) := by
  let x := uniformTilt.mk ϖ.root ϖ.root_succ_pow
  have hx : IsTopologicallyNilpotent x :=
    uniformTilt.isTopologicallyNilpotent_iff_coeff_zero.mpr
      (by simpa only [x, uniformTilt.coeff_mk] using
        ϖ.isPseudoUniformizer_root_zero.isTopologicallyNilpotent)
  refine ⟨⟨x, mem_powerBoundedSubring.mpr (IsPowerBounded.of_isTopologicallyNilpotent hx)⟩,
    rfl, ?_⟩
  rw [isPseudoUniformizer_iff, uniformTilt.isUnit_iff_coeff_zero,
    uniformTilt.isTopologicallyNilpotent_iff_coeff_zero]
  simp only [uniformTilt.coe_plusEquivOfCharP_symm, uniformTilt.coeff_equivOfCharP_symm,
    Function.iterate_zero, id_eq]
  exact ⟨uniformTilt.isUnit_iff_coeff_zero.mpr
    (by simpa only [x, uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero.isUnit), hx⟩

-- Inverting that pseudouniformiser gives a unit outside the chosen integral tilt.
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    (uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p])).symm
      (uniformTilt.mk (fun n ↦ (ϖ.root n)⁻¹)
        (fun n ↦ by rw [inv_pow, ϖ.root_succ_pow])) ∉
      uniformTilt.plusSubring p
        (isRingOfIntegralElements_powerBoundedSubring (uniformTilt p ℂ_[p])) := by
  rw [uniformTilt.mem_plusSubring_iff_coeff_zero]
  simp only [uniformTilt.coeff_equivOfCharP_symm, Function.iterate_zero, id_eq]
  have hϖ : IsPseudoUniformizer
      (uniformTilt.coeff p ℂ_[p] 0 (uniformTilt.mk ϖ.root ϖ.root_succ_pow)) := by
    simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero
  rw [uniformTilt.mem_powerBoundedSubring_iff hϖ, uniformTilt.coeff_mk,
    mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, norm_inv, not_le]
  obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
  exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1

section Product

local instance : CharP (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) p := Prod.charP _ _ p

local instance : Fact
    (IsTopologicallyNilpotent (p : uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])) :=
  ⟨by rw [CharP.cast_eq_zero]; exact IsTopologicallyNilpotent.zero⟩

-- A nontrivial idempotent has a constant root system; neither product factor is collapsed.
example (n : ℕ) :
    uniformTilt.coeff p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) n
      ((uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])).symm
        (0, 1)) = (0, 1) := by
  let y : uniformTilt p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) :=
    uniformTilt.mk (fun _ ↦ (0, 1)) (fun _ ↦ by simp [(Fact.out : p.Prime).ne_zero])
  have hy : (uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])).symm
      (0, 1) = y := by
    apply (uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])).injective
    simp [y]
  simp [hy, y]

example (x : uniformTilt p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]))
    (b : uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) :
    (uniformTilt.equivOfCharP p _).symm (uniformTilt.equivOfCharP p _ x) = x ∧
      uniformTilt.equivOfCharP p _ ((uniformTilt.equivOfCharP p _).symm b) = b := by
  simp

-- Naturality applies to an actual noninjective projection, preserving its selected factor.
example (x : uniformTilt p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])) :
    uniformTilt.equivOfCharP p (uniformTilt p ℂ_[p])
      (uniformTilt.map (RingHom.fst _ _)
        (by simpa only [RingHom.coe_fst] using
          (continuous_fst : Continuous
            (Prod.fst : (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) → uniformTilt p ℂ_[p]))) x) =
        (uniformTilt.equivOfCharP p _ x).1 := by
  simp

-- Both inverse laws simplify through the public homeomorphism on this non-domain.
example (x : uniformTilt p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]))
    (b : uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) :
    (uniformTilt.homeomorphOfCharP p _).symm (uniformTilt.homeomorphOfCharP p _ x) = x ∧
      uniformTilt.homeomorphOfCharP p _ ((uniformTilt.homeomorphOfCharP p _).symm b) = b := by
  simp

-- The inverse integral map uses precisely the ambient inverse, including its zeroth coordinate.
example (b : powerBoundedSubring (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])) :
    uniformTilt.coeff p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) 0
      (((uniformTilt.plusEquivOfCharP p
        (isRingOfIntegralElements_powerBoundedSubring _)).symm b :
          uniformTilt p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]))) = b := by
  simp

-- In particular, the integral inverse retains the nontrivial product idempotent at every level.
example (n : ℕ) :
    uniformTilt.coeff p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) n
      (((uniformTilt.plusEquivOfCharP p
        (isRingOfIntegralElements_powerBoundedSubring
          (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]))).symm
          ⟨(0, 1), by simp [Subring.mem_prod]⟩ :
              uniformTilt p (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]))) = (0, 1) := by
  simp only [uniformTilt.coe_plusEquivOfCharP_symm, uniformTilt.coeff_equivOfCharP_symm]
  apply Function.iterate_fixed
  apply (frobeniusEquiv (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p]) p).injective
  simp [frobenius_def, (Fact.out : p.Prime).ne_zero]

example (x : uniformTilt.plusSubring p
    (isRingOfIntegralElements_powerBoundedSubring
      (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])))
    (b : powerBoundedSubring (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])) :
    (uniformTilt.plusEquivOfCharP p (isRingOfIntegralElements_powerBoundedSubring _)).symm
      (uniformTilt.plusEquivOfCharP p (isRingOfIntegralElements_powerBoundedSubring _) x) = x ∧
    uniformTilt.plusEquivOfCharP p (isRingOfIntegralElements_powerBoundedSubring _)
      ((uniformTilt.plusEquivOfCharP p
        (isRingOfIntegralElements_powerBoundedSubring _)).symm b) = b := by
  simp

end Product

-- The characteristic hypothesis is necessary: the mixed-characteristic untilt has no such map.
example : IsEmpty (uniformTilt p ℂ_[p] ≃+* ℂ_[p]) := by
  refine ⟨fun e ↦ ?_⟩
  have hp : (p : ℂ_[p]) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg e (CharP.cast_eq_zero (uniformTilt p ℂ_[p]) p)
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

end TauCeti.Examples.UniformTiltCharP
