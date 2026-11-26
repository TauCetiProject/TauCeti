/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Operations

/-!
# Checks for operations on raw Weil–Deligne parameters

* Duality changes `N` to `-Nᵗ`, and double duality recovers `N` through the evaluation map.
* Tensoring two rank-one parameters gives the product character with zero monodromy, since a
  nilpotent endomorphism of a line is zero.
* The sum has monodromy `N ⊕ N'`, and twisting by a character leaves the monodromy unchanged.
-/

public section

open Module TensorProduct

namespace TauCeti.WeilDeligneParameter.OperationsChecks

variable {E W V V' : Type*} [Field E] [Group W] [TopologicalSpace W] [SeparatelyContinuousMul W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- Duality changes the monodromy `N` to `-Nᵗ`. -/
example (D : WeilDeligneParameter E W V deg q) (φ : Module.Dual E V) (v : V) :
    D.dual.N φ v = -φ (D.N v) := by
  simp

/-- Double duality recovers `N`: the evaluation at `N v` is the double-dual monodromy applied to
the evaluation at `v`. -/
example (D : WeilDeligneParameter E W V deg q) [FiniteDimensional E V] (v : V) :
    D.dual.dual.N (Module.Dual.eval E V v) = Module.Dual.eval E V (D.N v) := by
  simpa using (D.dualDualIso.map_N_apply v).symm

/-- Tensoring two rank-one parameters gives zero monodromy and the product character:
`r(w) (1 ⊗ 1) = (r₁(w) 1 · r₂(w) 1) • (1 ⊗ 1)`. -/
example (D D' : WeilDeligneParameter E W E deg q) (w : W) :
    (D.tensor D').N = 0 ∧
      (D.tensor D').r w (1 ⊗ₜ 1) = (D.r w 1 * D'.r w 1) • ((1 : E) ⊗ₜ[E] (1 : E)) := by
  -- A nilpotent endomorphism of the line `E` is zero, as `Module.End E E` is the field `Eᵐᵒᵖ`.
  have h (N : Module.End E E) (hN : IsNilpotent N) : N = 0 := by
    exact (map_eq_zero_iff _ (RingEquiv.moduleEndSelf E).symm.injective).mp
      (isNilpotent_iff_eq_zero.mp (hN.map (RingEquiv.moduleEndSelf E).symm))
  refine ⟨by simp [h _ D.isNilpotent_N, h _ D'.isNilpotent_N], ?_⟩
  rw [← TensorProduct.smul_tmul_smul]
  simp [Representation.tprod_apply]

/-- The sum has monodromy `N ⊕ N'`. -/
example (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)
    (v : V) (v' : V') : (D.prod D').N (v, v') = (D.N v, D'.N v') := by
  simp

/-- Twisting by a character leaves the monodromy unchanged and rescales the Weil action. -/
example (D : WeilDeligneParameter E W V deg q) (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W))
    (w : W) (v : V) :
    (D.twist χ hχ).N = D.N ∧ (D.twist χ hχ).r w v = (χ w : E) • D.r w v := by
  simp

end TauCeti.WeilDeligneParameter.OperationsChecks
