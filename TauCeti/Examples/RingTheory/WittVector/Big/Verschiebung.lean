/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.WittVector.Big.Verschiebung

/-!
# Checks for the big Witt Verschiebung

On the truncation set `Div(2) = {1, 2}`, the Verschiebung `V_2 : W_{Div(1)}(R) → W_{Div(2)}(R)`
sends `(a)` to `(0, a)`. Over `ℤ` it is additive but not multiplicative: `V_2(1)` has ghost
components `(0, 2)`, whereas its square has ghost components `(0, 4)`.
-/

open TauCeti BigWitt

-- `V_2(a) = (0, a)` in `W_{Div(2)}(R)`.
example {R : Type*} [CommRing R] (x : BigWittVector (TruncationSet.divisors 2 / 2) R) :
    (BigWittVector.verschiebung 2 x).coeff 1 = 0 ∧
      (BigWittVector.verschiebung 2 x).coeff 2 = x.coeff 1 :=
  ⟨BigWittVector.coeff_verschiebung_of_not_dvd 2 x (by decide),
    BigWittVector.coeff_verschiebung_mul 2 x 1⟩

-- `V_2` is not multiplicative: `V_2(1) * V_2(1) ≠ V_2(1)` in `W_{Div(2)}(ℤ)`, since their second
-- ghost components are `4` and `2`.
example : (BigWittVector.verschiebung 2 1 : BigWittVector (TruncationSet.divisors 2) ℤ) *
    BigWittVector.verschiebung 2 1 ≠ BigWittVector.verschiebung 2 1 := by
  intro h
  have hk : 1 ∈ TruncationSet.divisors 2 / 2 := by simp
  have h2 := congrArg (BigWittVector.ghostMap · ⟨2 * 1, TruncationSet.mem_div.mp hk⟩) h
  simp only [map_mul, Pi.mul_apply] at h2
  rw [BigWittVector.ghostMap_verschiebung_mul 2 1 ⟨1, hk⟩, map_one, Pi.one_apply] at h2
  norm_num at h2
