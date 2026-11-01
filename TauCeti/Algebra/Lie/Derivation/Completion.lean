/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Extending derivations to complete algebras

A derivation extends along a dense uniform-inducing algebra map into a complete Hausdorff
algebra, provided its composite with that map is uniformly continuous. The extension is unique
among continuous maps with the prescribed values on the dense image. In particular this applies
to completions defined by left ideals; no quotient-ring structure on their stages is needed.

The construction uses Mathlib's `IsDenseInducing.extend`. Linearity and the Leibniz rule
are transported by density and continuity of the operations in the target algebra.
-/

public section

noncomputable section

namespace TauCeti.derivationLieAlgebra

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [UniformSpace A] [UniformSpace B] [IsTopologicalRing B]
  [ContinuousConstSMul R B] [CompleteSpace B] [T2Space B]
  (D : derivationLieAlgebra R A) (i : A →ₐ[R] B) (hi : IsUniformInducing i)
  (hd : DenseRange i) (hD : UniformContinuous fun a ↦ i ((D : Module.End R A) a))

/-- Extend a uniformly continuous derivation along a dense uniform-inducing algebra map to a
complete Hausdorff algebra. -/
def extend : derivationLieAlgebra R B := by
  let f := hi.isDenseInducing hd |>.extend (fun a ↦ i ((D : Module.End R A) a))
  have hf : Continuous f := (uniformContinuous_uniformly_extend hi hd hD).continuous
  have he (a : A) : f (i a) = i ((D : Module.End R A) a) :=
    (hi.isDenseInducing hd).extend_eq hD.continuous a
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, mem_derivationLieAlgebra.mpr ?_⟩
  · intro x y
    induction x, y using hd.induction_on₂ with
    | hp => exact isClosed_eq (hf.comp continuous_add) ((hf.comp continuous_fst).add
        (hf.comp continuous_snd))
    | h a b => rw [← map_add i a b, he]; simp only [he, map_add]
  · intro r x
    induction x using hd.induction_on with
    | hp => exact isClosed_eq (hf.comp (continuous_const_smul r)) (hf.const_smul r)
    | ih a => rw [← map_smul i r a, he]; simp only [he, map_smul, RingHom.id_apply]
  · intro x y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    induction x, y using hd.induction_on₂ with
    | hp =>
      exact isClosed_eq (hf.comp continuous_mul)
        (((hf.comp continuous_fst).mul continuous_snd).add
          (continuous_fst.mul (hf.comp continuous_snd)))
    | h a b => rw [← map_mul i a b, he]; simp only [he, leibniz, map_add, map_mul]

/-- The extended derivation has the prescribed values on the original algebra. -/
@[simp]
theorem extend_apply (a : A) :
    (extend D i hi hd hD : Module.End R B) (i a) = i ((D : Module.End R A) a) :=
  (hi.isDenseInducing hd).extend_eq hD.continuous a

/-- The extended derivation is continuous. -/
theorem continuous_extend : Continuous (extend D i hi hd hD : Module.End R B) :=
  (uniformContinuous_uniformly_extend hi hd hD).continuous

/-- A continuous map extending the original derivation equals its extension. -/
theorem eq_extend {f : B → B} (hf : Continuous f)
    (h : ∀ a, f (i a) = i ((D : Module.End R A) a)) :
    f = (extend D i hi hd hD : Module.End R B) :=
  hd.equalizer hf (continuous_extend D i hi hd hD)
    (funext fun a ↦ (h a).trans (extend_apply D i hi hd hD a).symm)

end TauCeti.derivationLieAlgebra
