/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RingTheory.Perfectoid.UniformTilt.Plus
public import TauCeti.RingTheory.Huber.Pair.Complete
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.ZMod

/-!
# Checks for the topology on integral tilts

The integral tilt of `ℂ_p` is homeomorphic to the perfection of its discrete residue ring
modulo `p`. Powers of a nonzero compatible-root parameter converge to zero under that
comparison. The inverse-limit topology itself is also tested with constant sequences
(`p = 1`), where it retains the nondiscrete topology of the real line, and with the zero ring.
-/

public section

open Filter Topology TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltIntegralTopology

-- For exponent one, all compatible sequences are constant, with the topology of the factor.
example : IsHomeomorph (Perfection.coeffMonoidHom ℝ 1 0) := by
  let e : Perfection ℝ 1 ≃ ℝ :=
    { toFun := Perfection.coeffMonoidHom ℝ 1 0
      invFun := fun r ↦ ⟨fun _ ↦ r, by simp⟩
      left_inv := fun x ↦ Perfection.extMonoid fun n ↦ by
        simp only [Perfection.coeffMonoidHom_mk]
        induction n with
        | zero => rfl
        | succ n ih =>
          simpa only [pow_one] using ih.trans (Perfection.coeffMonoidHom_pow_p' x n).symm
      right_inv := fun _ ↦ rfl }
  exact e.isHomeomorph_iff.mpr ⟨Perfection.continuous_coeffMonoidHom 0,
    Perfection.continuous_iff.mpr fun _ ↦ continuous_id⟩

-- The new topology does not make all perfections discrete.
example : ¬ DiscreteTopology (Perfection ℝ 1) := by
  intro h
  have hc : Continuous (fun r : ℝ ↦ (⟨fun _ ↦ r, by simp⟩ : Perfection ℝ 1)) :=
    Perfection.continuous_iff.mpr fun _ ↦ continuous_id
  have : DiscreteTopology ℝ := .of_continuous_injective (β := Perfection ℝ 1) hc
    (fun x y hxy ↦ congrArg (Perfection.coeffMonoidHom ℝ 1 0) hxy)
  exact not_isOpen_singleton (0 : ℝ) (isOpen_discrete _)

-- The zero ring has just one compatible sequence, so its inverse-limit topology is trivial.
example (p : ℕ) : DiscreteTopology (Perfection (ZMod 1) p) := by
  have : Subsingleton (Perfection (ZMod 1) p) :=
    ⟨fun x y ↦ Perfection.extMonoid fun _ ↦ Subsingleton.elim _ _⟩
  infer_instance

-- A computed nonzero constant sequence is retained, rather than collapsed by the topology.
example : Perfection.coeffMonoidHom ℝ 1 7 (⟨fun _ ↦ 2, by simp⟩ : Perfection ℝ 1) = 2 := rfl

section PadicComplex

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

local instance : CharP (powerBoundedSubring ℂ_[p] ⧸ Ideal.span {(p : powerBoundedSubring ℂ_[p])})
    p :=
  CharP.quotient _ p <|
    (UniformTiltPlus.isRingOfIntegralElements_padicComplex p).not_isUnit_of_isTopologicallyNilpotent
      (by simpa using (Fact.out : IsTopologicallyNilpotent (p : ℂ_[p])))

local instance :
    IsAdicComplete (Ideal.span {(p : powerBoundedSubring ℂ_[p])}) (powerBoundedSubring ℂ_[p]) :=
  IsUniform.isAdicComplete_span_singleton _ (isPseudoUniformizer_natCast_padicComplex p)

/-- Give the residue factors the discrete topology, not the inverse limit itself. -/
local instance : TopologicalSpace
    (powerBoundedSubring ℂ_[p] ⧸ Ideal.span {(p : powerBoundedSubring ℂ_[p])}) := ⊥

local instance : DiscreteTopology
    (powerBoundedSubring ℂ_[p] ⧸ Ideal.span {(p : powerBoundedSubring ℂ_[p])}) := ⟨rfl⟩

example : IsTopologicalRing (Perfection
    (powerBoundedSubring ℂ_[p] ⧸ Ideal.span {(p : powerBoundedSubring ℂ_[p])}) p) :=
  inferInstance

example : IsHomeomorph (uniformTilt.plusEquiv
    (UniformTiltPlus.isRingOfIntegralElements_padicComplex p)
    (Ideal.span {(p : powerBoundedSubring ℂ_[p])})) := by
  apply uniformTilt.isHomeomorph_plusEquiv
  exact (powerBoundedSubring ℂ_[p]).isAdic_span_singleton_of_isOpen_of_isBounded
    (isOpen_powerBoundedSubring _) IsUniform.isBounded_powerBoundedSubring
    (isPseudoUniformizer_natCast_padicComplex p) (natCast_mem _ p)

-- A genuine, nonzero compatible-root parameter gives a null sequence after reduction.
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    Tendsto (fun n : ℕ ↦ uniformTilt.plusEquiv
      (UniformTiltPlus.isRingOfIntegralElements_padicComplex p)
      (Ideal.span {(p : powerBoundedSubring ℂ_[p])})
      ((⟨uniformTilt.mk ϖ.root ϖ.root_succ_pow,
        UniformTiltPlus.mk_root_mem_plusSubring p ϖ⟩) ^ n)) atTop (𝓝 0) := by
  have he := uniformTilt.isHomeomorph_plusEquiv
    (UniformTiltPlus.isRingOfIntegralElements_padicComplex p)
    (Ideal.span {(p : powerBoundedSubring ℂ_[p])})
    ((powerBoundedSubring ℂ_[p]).isAdic_span_singleton_of_isOpen_of_isBounded
      (isOpen_powerBoundedSubring _) IsUniform.isBounded_powerBoundedSubring
      (isPseudoUniformizer_natCast_padicComplex p) (natCast_mem _ p))
  have ht : IsTopologicallyNilpotent (uniformTilt.mk ϖ.root ϖ.root_succ_pow) :=
    uniformTilt.isTopologicallyNilpotent_iff_coeff_zero.mpr
      (by simpa using ϖ.isPseudoUniformizer_root_zero.isTopologicallyNilpotent)
  have hs : Tendsto (fun n : ℕ ↦
      (⟨uniformTilt.mk ϖ.root ϖ.root_succ_pow,
        UniformTiltPlus.mk_root_mem_plusSubring p ϖ⟩ :
        uniformTilt.plusSubring p (UniformTiltPlus.isRingOfIntegralElements_padicComplex p)) ^ n)
      atTop (𝓝 0) := by
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    simpa only [IsTopologicallyNilpotent, Function.comp_def, Subring.coe_pow,
      Subring.coe_zero] using ht
  simpa only [Function.comp_def, map_zero] using (he.continuous.tendsto 0).comp hs

end PadicComplex

end TauCeti.Examples.UniformTiltIntegralTopology
