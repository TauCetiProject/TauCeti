/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Topology.Algebra.LinearMapCompletion

/-!
# Algebraic comparison with a metric completion

An isometric algebra homomorphism with dense range into a complete normed algebra identifies
that algebra with the metric completion of its source. The comparison extends the given map
and preserves distances. This allows completion comparisons for dense subalgebras and their
presentation quotients to share the same construction.

For a continuous nonunital algebra or `⋆`-algebra homomorphism into a complete separated
seminormed target, any linear norm bound `‖f x‖ ≤ C * ‖x‖` extends by density to the completion
(`NonUnitalAlgHom.norm_fromCompletion_le` and `NonUnitalStarAlgHom.norm_fromCompletion_le`).

The construction factors the one used for the Monsky–Washnitzer algebra in
`TauCeti.RingTheory.Dagger.Completion`.
-/

public section

noncomputable section

open UniformSpace

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [SeminormedRing A] [NormedRing B]
  [Algebra R A] [Algebra R B] [UniformContinuousConstSMul R A] [CompleteSpace B]

/-- An isometric algebra homomorphism with dense range identifies the metric completion of
its source with its complete target. -/
def completionAlgEquiv (f : A →ₐ[R] B) (hf : Isometry f) (hd : DenseRange f) :
    Completion A ≃ₐ[R] B :=
  let g : Completion A →ₐ[R] B :=
    { __ := Completion.extensionHom f.toRingHom hf.continuous
      commutes' r :=
        (Completion.extensionHom_coe _ hf.continuous (algebraMap R A r)).trans (f.commutes r) }
  have hg : Isometry g := hf.completion_extension
  have hgd : DenseRange g := hd.mono <| by
    rintro _ ⟨a, rfl⟩
    exact ⟨(a : Completion A), Completion.extensionHom_coe _ hf.continuous a⟩
  AlgEquiv.ofBijective g ⟨hg.injective, fun b ↦ by
    have hb := hgd b
    rwa [hg.isClosedEmbedding.isClosed_range.closure_eq] at hb⟩

/-- The completion comparison extends the original algebra homomorphism. -/
@[simp]
theorem completionAlgEquiv_coe (f : A →ₐ[R] B) (hf : Isometry f) (hd : DenseRange f) (a : A) :
    f.completionAlgEquiv hf hd (a : Completion A) = f a :=
  Completion.extensionHom_coe _ hf.continuous a

/-- The inverse comparison sends the image of an element to its completion class. -/
@[simp]
theorem completionAlgEquiv_symm_apply (f : A →ₐ[R] B) (hf : Isometry f) (hd : DenseRange f)
    (a : A) : (f.completionAlgEquiv hf hd).symm (f a) = (a : Completion A) := by
  rw [← completionAlgEquiv_coe f hf hd, AlgEquiv.symm_apply_apply]

/-- The algebraic completion comparison preserves distances. -/
theorem isometry_completionAlgEquiv (f : A →ₐ[R] B) (hf : Isometry f) (hd : DenseRange f) :
    Isometry (f.completionAlgEquiv hf hd) :=
  hf.completion_extension

/-- The algebraic completion comparison preserves norms. -/
@[simp]
theorem norm_completionAlgEquiv (f : A →ₐ[R] B) (hf : Isometry f) (hd : DenseRange f)
    (x : Completion A) : ‖f.completionAlgEquiv hf hd x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm _).mp (isometry_completionAlgEquiv f hf hd) x

end AlgHom

namespace NonUnitalAlgHom

variable {R E F : Type*} [Semiring R]
  [NonUnitalSeminormedRing E] [Module R E] [UniformContinuousConstSMul R E]
  [NonUnitalSeminormedRing F] [Module R F] [UniformContinuousConstSMul R F]
  [T0Space F] [CompleteSpace F]

/-- If a continuous nonunital algebra homomorphism `f : E →ₙₐ[R] F` into a complete separated
seminormed target satisfies `‖f x‖ ≤ C * ‖x‖` for all `x`, then its extension
`f.fromCompletion hf` to the completion satisfies `‖f.fromCompletion hf y‖ ≤ C * ‖y‖` for all
`y`. -/
theorem norm_fromCompletion_le (f : E →ₙₐ[R] F) (hf : Continuous f) {C : ℝ}
    (hC : ∀ x : E, ‖f x‖ ≤ C * ‖x‖) (y : Completion E) :
    ‖f.fromCompletion hf y‖ ≤ C * ‖y‖ := by
  induction y using Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp (f.continuous_fromCompletion hf))
      (continuous_const.mul continuous_norm)
  | ih x => simpa only [fromCompletion_apply_coe, Completion.norm_coe] using hC x

end NonUnitalAlgHom

namespace NonUnitalStarAlgHom

variable {R E F : Type*} [Semiring R]
  [NonUnitalSeminormedRing E] [StarAddMonoid E] [ContinuousStar E]
  [Module R E] [UniformContinuousConstSMul R E]
  [NonUnitalSeminormedRing F] [Star F] [ContinuousStar F]
  [Module R F] [UniformContinuousConstSMul R F] [T0Space F] [CompleteSpace F]

/-- If a continuous nonunital `⋆`-algebra homomorphism `f : E →⋆ₙₐ[R] F` into a complete
separated seminormed target satisfies `‖f x‖ ≤ C * ‖x‖` for all `x`, then its extension
`f.fromCompletion hf` to the completion satisfies `‖f.fromCompletion hf y‖ ≤ C * ‖y‖` for all
`y`. -/
theorem norm_fromCompletion_le (f : E →⋆ₙₐ[R] F) (hf : Continuous f) {C : ℝ}
    (hC : ∀ x : E, ‖f x‖ ≤ C * ‖x‖) (y : Completion E) :
    ‖f.fromCompletion hf y‖ ≤ C * ‖y‖ := by
  simpa only [← NonUnitalStarAlgHom.coe_toNonUnitalAlgHom, toNonUnitalAlgHom_fromCompletion] using
    f.toNonUnitalAlgHom.norm_fromCompletion_le hf hC y

end NonUnitalStarAlgHom
