/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Pulling back and completing multiplicative seminorms

The composite `p ∘ f` of a multiplicative seminorm `p` on `S` with a ring homomorphism
`f : R →+* S` is a multiplicative seminorm on `R`, `MulRingSeminorm.comp p f`. This is the
multiplicative analogue of Mathlib's `AddGroupSeminorm.comp`, and it is how a ring homomorphism
acts contravariantly on spaces of multiplicative seminorms such as Berkovich spectra.

A uniformly continuous multiplicative seminorm on a uniform ring extends by continuity to a
multiplicative seminorm on the completion, `MulRingSeminorm.completion`, since the seminorm laws
are closed conditions and the ring is dense in its completion.
-/

public section

open UniformSpace

namespace MulRingSeminorm

section comp

variable {R S T : Type*} [NonAssocRing R] [NonAssocRing S] [NonAssocRing T]

/-- The composite of a multiplicative seminorm on `S` with a ring homomorphism `R →+* S`. -/
def comp (p : MulRingSeminorm S) (f : R →+* S) : MulRingSeminorm R where
  __ := p.toAddGroupSeminorm.comp f.toAddMonoidHom
  map_one' := by simp
  map_mul' x y := by simp

@[simp]
theorem comp_apply (p : MulRingSeminorm S) (f : R →+* S) (x : R) : p.comp f x = p (f x) :=
  (rfl)

@[simp]
theorem comp_id (p : MulRingSeminorm S) : p.comp (RingHom.id S) = p :=
  ext fun _ => rfl

theorem comp_comp (p : MulRingSeminorm T) (g : S →+* T) (f : R →+* S) :
    p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

end comp

section completion

variable {R : Type*} [Ring R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- The extension by continuity of a uniformly continuous multiplicative seminorm on a uniform
ring to its completion. -/
noncomputable def completion (p : MulRingSeminorm R) (hp : UniformContinuous p) :
    MulRingSeminorm (Completion R) where
  toFun := Completion.extension p
  map_zero' := by rw [← Completion.coe_zero, Completion.extension_coe hp, map_zero]
  add_le' a b := by
    induction a, b using Completion.induction_on₂ with
    | hp =>
      exact isClosed_le (Completion.continuous_extension.comp (continuous_fst.add continuous_snd))
        ((Completion.continuous_extension.comp continuous_fst).add
          (Completion.continuous_extension.comp continuous_snd))
    | ih a b =>
      simpa only [← Completion.coe_add, Completion.extension_coe hp] using map_add_le_add p a b
  neg' a := by
    induction a using Completion.induction_on with
    | hp =>
      exact isClosed_eq (Completion.continuous_extension.comp continuous_neg)
        Completion.continuous_extension
    | ih a => simp only [← Completion.coe_neg, Completion.extension_coe hp, map_neg_eq_map]
  map_one' := by rw [← Completion.coe_one, Completion.extension_coe hp, map_one]
  map_mul' a b := by
    induction a, b using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq (Completion.continuous_extension.comp (continuous_fst.mul continuous_snd))
        ((Completion.continuous_extension.comp continuous_fst).mul
          (Completion.continuous_extension.comp continuous_snd))
    | ih a b => simp only [← Completion.coe_mul, Completion.extension_coe hp, map_mul]

theorem coe_completion (p : MulRingSeminorm R) (hp : UniformContinuous p) :
    ⇑(p.completion hp) = Completion.extension p :=
  (rfl)

@[simp]
theorem completion_coe (p : MulRingSeminorm R) (hp : UniformContinuous p) (a : R) :
    p.completion hp a = p a := by
  rw [coe_completion, Completion.extension_coe hp]

theorem continuous_completion (p : MulRingSeminorm R) (hp : UniformContinuous p) :
    Continuous (p.completion hp) := by
  rw [coe_completion]
  exact Completion.continuous_extension

end completion

end MulRingSeminorm
