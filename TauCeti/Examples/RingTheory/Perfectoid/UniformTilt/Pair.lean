/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.OfHom
public import TauCeti.RingTheory.Perfectoid.UniformTilt.CharP
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for tilted Huber pairs

We test the plus ring on `ℂ_p` using a compatible-root parameter and its inverse, compare it
with the original plus ring in characteristic `p`, and include the zero ring. The two projections
of `ℂ_p × ℂ_p` remain distinct after tilting: they send the compatible idempotent `(1, 0)` to
`1` and `0`, respectively. Thus the pair-morphism construction retains both the coordinates
and the variance of the original map.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltPair

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  (RingHom.id ℂ_[p]).isTateRing_uniformTilt (p := p) continuous_id

-- A compatible-root parameter belongs to the new plus ring; its inverse does not.
example (P : Pair ℂ_[p]) (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    uniformTilt.mk ϖ.root ϖ.root_succ_pow ∈ (P.tilt (p := p)).plus := by
  rw [Pair.tilt_plus, uniformTilt.mem_plusSubring_iff_coeff_zero, uniformTilt.coeff_mk]
  exact P.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
    ϖ.isPseudoUniformizer_root_zero.isTopologicallyNilpotent

example (P : Pair ℂ_[p]) (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    uniformTilt.mk (fun n ↦ (ϖ.root n)⁻¹) (fun n ↦ by rw [inv_pow, ϖ.root_succ_pow]) ∉
      (P.tilt (p := p)).plus := by
  rw [Pair.tilt_plus, uniformTilt.mem_plusSubring_iff_coeff_zero, uniformTilt.coeff_mk]
  intro hx
  have hnorm := isPowerBounded_iff_norm_le_one.mp
    (P.isRingOfIntegralElements.isPowerBounded_of_mem hx)
  obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
  rw [norm_inv] at hnorm
  exact (not_le.mpr ((one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1)) hnorm

section CharacteristicP

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Fact (IsTopologicallyNilpotent (p : B))] [CharP B p] [PerfectRing B p]
  [IsTateRing (uniformTilt p B)]

-- Under the characteristic-p identification, the pair's plus ring is exactly the old one.
example (P : Pair B) :
    (P.tilt (p := p)).plus.map (uniformTilt.equivOfCharP p B).toRingHom = P.plus := by
  ext b
  rw [RingEquiv.toRingHom_eq_coe, Subring.mem_map_equiv, Pair.tilt_plus,
    uniformTilt.mem_plusSubring_iff_coeff_zero, uniformTilt.coeff_equivOfCharP_symm]
  simp

end CharacteristicP

section Zero

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Subsingleton B] [Fact (IsTopologicallyNilpotent (p : B))]
  [IsTateRing (uniformTilt p B)]

-- The zero ring is allowed without the inconsistent characteristic-exactly-p assumption.
example (P : Pair B) : (P.tilt (p := p)).plus = ⊤ := by
  ext x
  simp [Subsingleton.elim x 0]

end Zero

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p] × ℂ_[p])) :=
  ⟨Prod.isTopologicallyNilpotent_iff.mpr (by
    simpa using And.intro (Fact.out : IsTopologicallyNilpotent (p : ℂ_[p]))
      (Fact.out : IsTopologicallyNilpotent (p : ℂ_[p])))⟩

local instance : IsTateRing (uniformTilt p (ℂ_[p] × ℂ_[p])) :=
  (RingHom.id (ℂ_[p] × ℂ_[p])).isTateRing_uniformTilt (p := p) continuous_id

/-- The first projection preserves the maximal rings of integral elements. -/
private noncomputable def fstPair : Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p]))
    (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.fst _ _
  continuous_toRingHom := continuous_fst
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).1

/-- The second projection preserves the maximal rings of integral elements. -/
private noncomputable def sndPair : Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p]))
    (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.snd _ _
  continuous_toRingHom := continuous_snd
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).2

example (x : uniformTilt p (ℂ_[p] × ℂ_[p])) (n : ℕ) :
    uniformTilt.coeff p ℂ_[p] n ((fstPair p).tilt.toRingHom x) =
      (uniformTilt.coeff p (ℂ_[p] × ℂ_[p]) n x).1 := by
  simp [fstPair]

example : (fstPair p).tilt (p := p) ≠ (sndPair p).tilt (p := p) := by
  intro h
  let e : uniformTilt p (ℂ_[p] × ℂ_[p]) :=
    uniformTilt.mk (fun _ ↦ (1, 0)) (fun _ ↦ by simp [(Fact.out : p.Prime).ne_zero])
  have he := congrArg (fun f ↦ uniformTilt.coeff p ℂ_[p] 0 (f.toRingHom e)) h
  simp [fstPair, sndPair, e] at he

end TauCeti.Examples.UniformTiltPair
