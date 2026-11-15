/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Equiv
public import TauCeti.RingTheory.Perfectoid.UniformTilt.CharP
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for isomorphisms of tilts

The identity fixes the tilt of `ℂ_p`, and swapping the two factors of `ℂ_p × ℂ_p`
swaps every coordinate in its tilt. The latter is not the identity: it exchanges the
nontrivial idempotents. In characteristic `p`, the induced isomorphism agrees with the
original one under the zeroth-coordinate identifications. The checks use only the public API.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltEquiv

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

-- The identity isomorphism fixes every compatible system, not just its sharp image.
example (x : uniformTilt p ℂ_[p]) :
    (RingEquiv.refl ℂ_[p]).uniformTilt continuous_id continuous_id x = x := by
  rw [RingEquiv.uniformTilt_refl]
  rfl

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p] × ℂ_[p])) :=
  ⟨Prod.isTopologicallyNilpotent_iff.mpr (by
    simpa using And.intro (Fact.out : IsTopologicallyNilpotent (p : ℂ_[p]))
      (Fact.out : IsTopologicallyNilpotent (p : ℂ_[p])))⟩

-- A genuinely mixed-characteristic, non-domain example with both factors retained.
example (x : uniformTilt p (ℂ_[p] × ℂ_[p])) (n : ℕ) :
    uniformTilt.coeff p (ℂ_[p] × ℂ_[p]) n
      ((RingEquiv.prodComm : ℂ_[p] × ℂ_[p] ≃+* ℂ_[p] × ℂ_[p]).uniformTilt
        (by simpa only [RingEquiv.coe_prodComm] using continuous_swap)
        (by simpa only [RingEquiv.coe_prodComm_symm] using continuous_swap) x) =
        (uniformTilt.coeff p (ℂ_[p] × ℂ_[p]) n x).swap := by
  rw [RingEquiv.coeff_uniformTilt, RingEquiv.coe_prodComm]

example :
    (RingEquiv.prodComm : ℂ_[p] × ℂ_[p] ≃+* ℂ_[p] × ℂ_[p]).uniformTilt
      (p := p) (by simpa only [RingEquiv.coe_prodComm] using continuous_swap)
      (by simpa only [RingEquiv.coe_prodComm_symm] using continuous_swap) ≠
      RingEquiv.refl (uniformTilt p (ℂ_[p] × ℂ_[p])) := by
  intro h
  let x : uniformTilt p (ℂ_[p] × ℂ_[p]) :=
    uniformTilt.mk (fun _ ↦ (1, 0)) (fun _ ↦ by simp [(Fact.out : p.Prime).ne_zero])
  have hx := congrArg (fun e ↦ (uniformTilt.coeff p (ℂ_[p] × ℂ_[p]) 0 (e x)).1) h
  simp [x] at hx

-- Inversion is computationally usable without unfolding the constructed equivalence.
example (x : uniformTilt p (ℂ_[p] × ℂ_[p])) (n : ℕ) :
    uniformTilt.coeff p (ℂ_[p] × ℂ_[p]) n
      (((RingEquiv.prodComm : ℂ_[p] × ℂ_[p] ≃+* ℂ_[p] × ℂ_[p]).uniformTilt
        (by simpa only [RingEquiv.coe_prodComm] using continuous_swap)
        (by simpa only [RingEquiv.coe_prodComm_symm] using continuous_swap)).symm x) =
        (uniformTilt.coeff p (ℂ_[p] × ℂ_[p]) n x).swap := by
  rw [RingEquiv.coeff_uniformTilt_symm, RingEquiv.coe_prodComm_symm]

example : IsHomeomorph
    ((RingEquiv.prodComm : ℂ_[p] × ℂ_[p] ≃+* ℂ_[p] × ℂ_[p]).uniformTilt
      (p := p) (by simpa only [RingEquiv.coe_prodComm] using continuous_swap)
      (by simpa only [RingEquiv.coe_prodComm_symm] using continuous_swap)) :=
  RingEquiv.isHomeomorph_uniformTilt _ _ _

section CharacteristicP

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Fact (IsTopologicallyNilpotent (p : B))] [CharP B p] [PerfectRing B p]
  {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))] [CharP C p] [PerfectRing C p]

-- The characteristic-p identification conjugates the tilted map to the original map.
example (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm) (x : uniformTilt p B) :
    uniformTilt.equivOfCharP p C (e.uniformTilt he he' x) =
      e (uniformTilt.equivOfCharP p B x) := by
  simp

example (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm) (x : C) :
    e.uniformTilt he he' ((uniformTilt.equivOfCharP p B).symm (e.symm x)) =
      (uniformTilt.equivOfCharP p C).symm x := by
  apply (uniformTilt.equivOfCharP p C).injective
  simp

end CharacteristicP

end TauCeti.Examples.UniformTiltEquiv
