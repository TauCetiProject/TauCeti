/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

/-!
# Extending derivations to complete algebras

A derivation extends along a dense uniform-inducing algebra map into a complete Hausdorff
algebra, provided its composite with that map is uniformly continuous. The extension is unique
among continuous maps with the prescribed values on the dense image. In particular this applies
to completions defined by left ideals; no quotient-ring structure on their stages is needed.

The construction uses Mathlib's `ContinuousLinearMap.extend` for linearity and continuity.
The Leibniz rule is transported by density and continuity of multiplication in the target.
Neither algebra needs a unit or associative multiplication.
-/

public section

noncomputable section

namespace TauCeti.derivationLieAlgebra

variable {R A B : Type*} [CommRing R]
  [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [UniformSpace A] [IsUniformAddGroup A] [UniformSpace B] [IsUniformAddGroup B]
  [ContinuousMul B] [ContinuousConstSMul R B] [CompleteSpace B] [T2Space B]
  (D : derivationLieAlgebra R A) (i : A →ₙₐ[R] B) (hi : IsUniformInducing i)
  (hd : DenseRange i) (hD : UniformContinuous fun a ↦ i ((D : Module.End R A) a))

/-- Extend a uniformly continuous derivation along a dense uniform-inducing algebra map to a
complete Hausdorff algebra. -/
def extend : derivationLieAlgebra R B := by
  let f : B →L[R] B := ContinuousLinearMap.extend
    ⟨LinearMap.ofClass i ∘ₗ (D : Module.End R A), hD.continuous⟩
    ⟨LinearMap.ofClass i, hi.uniformContinuous.continuous⟩
  have he (a : A) : f (i a) = i ((D : Module.End R A) a) :=
    ContinuousLinearMap.extend_eq _ hd hi a
  refine ⟨f.toLinearMap, mem_derivationLieAlgebra.mpr fun x y ↦ ?_⟩
  simp only [ContinuousLinearMap.coe_coe]
  induction x, y using hd.induction_on₂ with
  | hp =>
    exact isClosed_eq (f.continuous.comp continuous_mul)
      (((f.continuous.comp continuous_fst).mul continuous_snd).add
        (continuous_fst.mul (f.continuous.comp continuous_snd)))
  | h a b => rw [← map_mul i a b, he]; simp only [he, leibniz, map_add, map_mul]

/-- The extended derivation has the prescribed values on the original algebra. -/
@[simp]
theorem extend_apply (a : A) :
    (extend D i hi hd hD : Module.End R B) (i a) = i ((D : Module.End R A) a) :=
  ContinuousLinearMap.extend_eq _ hd hi a

/-- The extended derivation is continuous. -/
theorem continuous_extend : Continuous (extend D i hi hd hD : Module.End R B) :=
  (ContinuousLinearMap.extend
    (⟨LinearMap.ofClass i ∘ₗ (D : Module.End R A), hD.continuous⟩ : A →L[R] B)
    ⟨LinearMap.ofClass i, hi.uniformContinuous.continuous⟩).continuous

/-- A continuous map extending the original derivation equals its extension. -/
theorem eq_extend {f : B → B} (hf : Continuous f)
    (h : ∀ a, f (i a) = i ((D : Module.End R A) a)) :
    f = (extend D i hi hd hD : Module.End R B) :=
  hd.equalizer hf (continuous_extend D i hi hd hD)
    (funext fun a ↦ (h a).trans (extend_apply D i hi hd hD a).symm)

end TauCeti.derivationLieAlgebra
