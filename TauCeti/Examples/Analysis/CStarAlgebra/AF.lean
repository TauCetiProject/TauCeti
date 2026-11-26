/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.CantorSet
public import TauCeti.Analysis.CStarAlgebra.AF.Connected
public import TauCeti.Analysis.CStarAlgebra.AF.ContinuousMap
public import TauCeti.Analysis.CStarAlgebra.AF.InductiveLimit
public import TauCeti.Analysis.CStarAlgebra.CARAlgebra
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Examples of AF algebras

These examples check the AF predicate `TauCeti.IsAF` on the zero algebra, the matrix algebras
`M_n`, the CAR algebra and the continuous functions on the Cantor set, and its closure under
products and minimal unitizations. The continuous functions on `[0, 1]` do not form an AF algebra:
the finite-dimensional C⋆-subalgebras of `C([0, 1], ℂ)` consist of constants, so the identity
function is not within `1 / 2` of any of them.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti

/-- The zero algebra is AF, with every stage `⊥`. -/
example {A : Type*} [NonUnitalCStarAlgebra A] [Subsingleton A] : IsAF A :=
  isAF_iff.2 ⟨fun _ ↦ ⊥, monotone_const, fun _ ↦ inferInstance,
    by convert dense_univ; ext a; simp [Subsingleton.elim a 0]⟩

/-- In the zero algebra the local approximation condition holds trivially. -/
example {A : Type*} [NonUnitalCStarAlgebra A] [Subsingleton A] (F : Finset A) (ε : ℝ)
    (hε : 0 < ε) : ∃ S : NonUnitalStarSubalgebra ℂ A, FiniteDimensional ℂ S ∧
      ∀ a ∈ F, ∃ b ∈ S, ‖a - b‖ < ε :=
  ⟨⊥, inferInstance, fun a _ ↦ ⟨0, zero_mem _, by simpa [Subsingleton.elim a 0] using hε⟩⟩

/-- The matrix algebra `M_n` is AF, being finite-dimensional. -/
example (n : ℕ) : IsAF (CStarMatrix (Fin n) (Fin n) ℂ) := isAF_of_finiteDimensional

/-- The CAR algebra is AF: it is the C⋆-inductive limit of the finite-dimensional algebras
`M_{2^n}`. -/
example : IsAF CARAlgebra := CStarInductiveLimit.isAF

/-- The CAR algebra is ⋆-isomorphic to a sequential C⋆-inductive limit of finite-dimensional
C⋆-algebras. -/
example : ∃ (A : ℕ → Type) (_ : ∀ n, NonUnitalCStarAlgebra (A n))
    (_ : ∀ n, FiniteDimensional ℂ (A n)) (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)),
    Nonempty (CARAlgebra ≃⋆ₐ[ℂ] CStarInductiveLimit A (fun _ _ h ↦ seqTransHom α h)) :=
  isAF_iff_nonempty_starAlgEquiv_cStarInductiveLimit.1 CStarInductiveLimit.isAF

/-- An AF algebra is separable; for the CAR algebra this recovers its separability. -/
example : TopologicalSpace.SeparableSpace CARAlgebra :=
  (CStarInductiveLimit.isAF : IsAF CARAlgebra).separableSpace

/-- The continuous functions on the Cantor space `ℕ → Bool` form an AF algebra. -/
example : IsAF C(ℕ → Bool, ℂ) := isAF_continuousMap_pi

/-- The continuous functions on the Cantor set form an AF algebra: the Cantor set is homeomorphic
to the Cantor space `ℕ → Bool`. -/
example : letI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
    IsAF C(cantorSet, ℂ) :=
  letI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  (Homeomorph.compStarAlgEquiv' ℂ ℂ cantorSetHomeomorphNatToBool).isAF_iff.1
    isAF_continuousMap_pi

/-- The product `M_n × CAR` is AF. -/
example (n : ℕ) : IsAF (CStarMatrix (Fin n) (Fin n) ℂ × CARAlgebra) :=
  isAF_of_finiteDimensional.prod CStarInductiveLimit.isAF

/-- The minimal unitization of an AF algebra is AF, here for the CAR algebra. -/
example : IsAF (Unitization ℂ CARAlgebra) :=
  (CStarInductiveLimit.isAF : IsAF CARAlgebra).unitization

/-- The identity function of `[0, 1]` is at distance at least `1 / 2` from every element of a
finite-dimensional C⋆-subalgebra of `C([0, 1], ℂ)`: such elements are constant. -/
example (S : NonUnitalStarSubalgebra ℂ C(unitInterval, ℂ)) [FiniteDimensional ℂ S]
    (b : C(unitInterval, ℂ)) (hb : b ∈ S) :
    1 / 2 ≤ ‖(⟨fun t ↦ ((t : ℝ) : ℂ), by fun_prop⟩ - b : C(unitInterval, ℂ))‖ := by
  set f : C(unitInterval, ℂ) := ⟨fun t ↦ ((t : ℝ) : ℂ), by fun_prop⟩ with hf
  have hc : b 1 = b 0 :=
    ContinuousMap.apply_eq_apply_of_mem_finiteDimensional S.toNonUnitalSubalgebra hb 1 0
  have h₀ : ‖b 0‖ ≤ ‖f - b‖ := by
    simpa [hf] using (f - b).norm_coe_le_norm 0
  have h₁ : ‖1 - b 0‖ ≤ ‖f - b‖ := by
    simpa [hf, hc] using (f - b).norm_coe_le_norm 1
  have : (1 : ℝ) ≤ ‖b 0‖ + ‖1 - b 0‖ := by
    simpa using norm_add_le (b 0) (1 - b 0)
  linarith

/-- `C([0, 1], ℂ)` is not AF: on the connected space `[0, 1]` an AF algebra of continuous
functions would consist of constants. -/
example : ¬ IsAF C(unitInterval, ℂ) := fun h ↦ by
  have h₀₁ : (((0 : unitInterval) : ℝ) : ℂ) = (((1 : unitInterval) : ℝ) : ℂ) :=
    h.continuousMap_apply_eq_apply ⟨fun t ↦ ((t : ℝ) : ℂ), by fun_prop⟩ 0 1
  norm_num at h₀₁

end TauCeti
