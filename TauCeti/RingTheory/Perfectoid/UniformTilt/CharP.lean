/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
import TauCeti.RingTheory.Huber.Perfect

/-!
# Self-identification of the tilt in characteristic `p`

For a perfect complete Hausdorff uniform Tate ring `B` of characteristic `p`, the zeroth
coordinate identifies `uniformTilt p B` with `B` as a ring and a topological space. Its inverse
assigns to an element its unique compatible system of iterated Frobenius roots. This
identification is natural in continuous ring homomorphisms and restricts to every ring of
integral elements `B⁺`.

The algebraic identification reuses Mathlib's `PerfectionMap.id` and its equivalence with
`Perfection`; the limit addition agrees with coordinatewise addition in characteristic `p`.
The inverse is continuous because Frobenius is open on a perfect complete Tate ring.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 (the characteristic-`p` case).
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable (p : ℕ) (B : Type*) [CommRing B] [Fact p.Prime] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))] [CharP B p] [PerfectRing B p]

-- Although characteristic `p` and perfectness imply these two Prop-valued assumptions, retain
-- the native tilt API's instance parameters so callers can synthesize its ring operations.

-- Rebuild the compatible system through the public coordinate API: the tilt's ring and
-- coefficient bodies are hidden, so its carrier equality alone cannot identify the operations.
private noncomputable def perfectionEquiv : uniformTilt p B ≃+* Perfection B p where
  toFun x := ⟨fun n ↦ coeff p B n x, coeff_pow_p x⟩
  invFun x := mk (fun n ↦ Perfection.coeff B p n x) (Perfection.coeff_pow_p' x)
  left_inv := mk_coeff
  right_inv _ := Perfection.ext fun n ↦ by simp
  map_mul' _ _ := Perfection.ext fun n ↦ by
    simp only [map_mul, Perfection.coeff_mk]
    rfl
  map_add' _ _ := Perfection.ext fun n ↦ by
    simp only [Perfection.coeff_mk, coeff_add_of_charP]
    rfl

/-- The zeroth coordinate identifies the tilt of a perfect ring of characteristic `p` with
that ring. Its inverse takes all iterated Frobenius roots. -/
noncomputable def equivOfCharP : uniformTilt p B ≃+* B :=
  (perfectionEquiv p B).trans (PerfectionMap.id p B).equiv.symm

/-- The characteristic-`p` identification is the zeroth coordinate. -/
@[simp]
theorem equivOfCharP_apply (x : uniformTilt p B) :
    equivOfCharP p B x = coeff p B 0 x :=
  (PerfectionMap.id p B).comp_symm_equiv (perfectionEquiv p B x)

/-- The zeroth coordinate determines the original compatible system in characteristic `p`. -/
@[simp]
theorem equivOfCharP_symm_coeff_zero (x : uniformTilt p B) :
    (equivOfCharP p B).symm (coeff p B 0 x) = x := by
  rw [← equivOfCharP_apply]
  exact (equivOfCharP p B).symm_apply_apply x

/-- The inverse identification consists of the unique iterated Frobenius roots. -/
@[simp]
theorem coeff_equivOfCharP_symm (b : B) (n : ℕ) :
    coeff p B n ((equivOfCharP p B).symm b) = (frobeniusEquiv B p).symm^[n] b := by
  -- The private bridge reconstructs a system with `mk`; the public constructor equation
  -- then reduces the coordinate to Mathlib's iterated-root construction.
  change coeff p B n (mk _ _) = _
  rw [coeff_mk]
  rfl

/-- The characteristic-`p` identification is continuous. -/
@[fun_prop, continuity]
theorem continuous_equivOfCharP : Continuous (equivOfCharP p B) := by
  exact (continuous_coeff (p := p) (B := B) 0).congr fun x ↦
    (equivOfCharP_apply p B x).symm

/-- The inverse characteristic-`p` identification is continuous. -/
@[fun_prop, continuity]
theorem continuous_equivOfCharP_symm : Continuous (equivOfCharP p B).symm := by
  have hroot : Continuous (frobeniusEquiv B p).symm :=
    (frobeniusEquiv B p).toEquiv.continuous_symm_iff.mpr
      (Huber.isOpenMap_frobenius p)
  exact continuous_iff.mpr fun n ↦ by
    simpa only [coeff_equivOfCharP_symm] using hroot.iterate n

/-- The self-identification of a characteristic-`p` tilt as a homeomorphism. -/
noncomputable def homeomorphOfCharP : uniformTilt p B ≃ₜ B where
  toEquiv := (equivOfCharP p B).toEquiv
  continuous_toFun := continuous_equivOfCharP p B
  continuous_invFun := continuous_equivOfCharP_symm p B

/-- The homeomorphism uses the same zeroth-coordinate map as the ring equivalence. -/
@[simp]
theorem homeomorphOfCharP_apply (x : uniformTilt p B) :
    homeomorphOfCharP p B x = equivOfCharP p B x := (rfl)

/-- The inverse homeomorphism is the inverse ring equivalence. -/
@[simp]
theorem homeomorphOfCharP_symm_apply (b : B) :
    (homeomorphOfCharP p B).symm b = (equivOfCharP p B).symm b := (rfl)

variable {p B}

variable (p) {Bplus : Subring B}

/-- The characteristic-`p` self-identification restricts to the original ring of integral
elements, without changing the chosen plus subring. -/
noncomputable def plusEquivOfCharP (h : IsRingOfIntegralElements Bplus) :
    plusSubring p h ≃+* Bplus :=
  (equivOfCharP p B).restrict (plusSubring p h) Bplus fun _ ↦
    mem_plusSubring_iff_coeff_zero.trans (by rw [equivOfCharP_apply])

/-- The integral self-identification is the zeroth coordinate in the original ring. -/
@[simp]
theorem coe_plusEquivOfCharP (h : IsRingOfIntegralElements Bplus) (x : plusSubring p h) :
    (plusEquivOfCharP p h x : B) = coeff p B 0 x :=
  equivOfCharP_apply p B x

/-- The inverse integral identification is the restriction of the inverse ring equivalence. -/
@[simp]
theorem coe_plusEquivOfCharP_symm (h : IsRingOfIntegralElements Bplus) (b : Bplus) :
    ((plusEquivOfCharP p h).symm b : uniformTilt p B) = (equivOfCharP p B).symm (b : B) :=
  (rfl)

end TauCeti.Perfectoid.uniformTilt
