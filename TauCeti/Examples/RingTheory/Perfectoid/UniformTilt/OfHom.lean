/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.OfHom
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for perfectoid tilts of uniform algebras

The homomorphism criterion applies to the identity of `ℂ_p`, to a noninjective projection
`ℂ_p × ℂ_p → ℂ_p`, and to a map to the zero ring. The final checks use an arbitrary complete
uniform target without assuming that it is perfectoid, and exercise its tilted Frobenius.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltOfHom

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

-- No choice of algebraically closed roots is needed at the call site.
example : IsTateRing (uniformTilt p ℂ_[p]) :=
  (RingHom.id ℂ_[p]).isTateRing_uniformTilt (p := p) continuous_id

example :
    letI := (RingHom.id ℂ_[p]).isTateRing_uniformTilt (p := p) continuous_id
    IsPerfectoidTateRing p (uniformTilt p ℂ_[p]) :=
  (RingHom.id ℂ_[p]).isPerfectoidTateRing_uniformTilt (p := p) continuous_id

-- The source can have zero divisors, and the homomorphism need not be injective.
example :
    letI := (RingHom.fst ℂ_[p] ℂ_[p]).isTateRing_uniformTilt (p := p) continuous_fst
    IsPerfectoidTateRing p (uniformTilt p ℂ_[p]) :=
  (RingHom.fst ℂ_[p] ℂ_[p]).isPerfectoidTateRing_uniformTilt (p := p) continuous_fst

example : ¬ Function.Injective (RingHom.fst ℂ_[p] ℂ_[p]) := by
  intro h
  have he : ((0, 0) : ℂ_[p] × ℂ_[p]) = (0, 1) := h rfl
  have h01 : (0 : ℂ_[p]) = 1 := congrArg Prod.snd he
  exact zero_ne_one h01

section UniformTarget

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Fact (IsTopologicallyNilpotent (p : B))]
  (f : ℂ_[p] →+* B) (hf : Continuous f)

-- There is no perfectoidness assumption on B in these signatures.
example :
    letI := f.isTateRing_uniformTilt (p := p) hf
    IsUniform (uniformTilt p B) := by
  let := f.isTateRing_uniformTilt (p := p) hf
  let := f.isPerfectoidTateRing_uniformTilt (p := p) hf
  exact IsPerfectoidTateRing.isUniform p

example [Nontrivial B] :
    letI := f.isTateRing_uniformTilt (p := p) hf
    Function.Bijective (frobenius (uniformTilt p B) p) := by
  let := f.isTateRing_uniformTilt (p := p) hf
  exact (frobeniusEquiv (uniformTilt p B) p).bijective

-- The zero target is included, without asking for characteristic exactly p.
example [Subsingleton B] :
    letI := f.isTateRing_uniformTilt (p := p) hf
    IsPerfectoidTateRing p (uniformTilt p B) :=
  f.isPerfectoidTateRing_uniformTilt (p := p) hf

end UniformTarget

end TauCeti.Examples.UniformTiltOfHom
