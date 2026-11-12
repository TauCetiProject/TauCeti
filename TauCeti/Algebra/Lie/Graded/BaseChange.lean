/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.BaseChange
public import Mathlib.Algebra.Lie.Graded
public import TauCeti.Algebra.PositiveDegrees.BaseChange
public import TauCeti.Algebra.Lie.Graded.Truncation
public import TauCeti.Algebra.Lie.BaseChange.Quotient
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Extension of scalars for graded Lie algebras

Extending each homogeneous piece gives a Lie grading on the scalar extension,
and extending the pieces of a graded representation preserves its graded action.
The decomposition is Mathlib's `DirectSum.Decomposition.baseChange`; homogeneous
projections commute with pure tensors by
`DirectSum.coe_decompose_baseChange_tmul`. No flatness, freeness, or dimension
hypothesis is imposed on the pieces or the coefficient algebra. For positive gradings,
the degree ideals extend to the degree ideals of the scalar extension. The resulting
finite-truncation Lie equivalence preserves homogeneous pieces and commutes with
quotient projections and transitions between cutoffs. Its construction transports
`LieIdeal.quotientBaseChangeEquiv` along the equality of degree ideals.

Adapted from `Mei/Algebra/Lie/Graded/BaseChange.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open TensorProduct

variable {N R S L M ι κ : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [LieRing L] [LieAlgebra R L]

/-- Scalar extension preserves a graded bracket action, independently of any decomposition. -/
instance SetLike.GradedBracket.baseChange [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] [VAdd ι κ]
    (ℒ : ι → Submodule R L) (ℳ : κ → Submodule R M)
    [SetLike.GradedBracket ℒ ℳ] :
    SetLike.GradedBracket (fun i => (ℒ i).baseChange S)
      (fun j => (ℳ j).baseChange S) where
  bracket_mem := by
    intro i j x y hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      induction y using TensorProduct.inductionOn with
      | tmul t y =>
        simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
          LieAlgebra.ExtendScalars.bracket_tmul] using
          Submodule.tmul_mem_baseChange_of_mem (s * t)
            (SetLike.GradedBracket.bracket_mem x.property y.property)
      | add y z hy hz =>
        rw [map_add, lie_add]
        exact Submodule.add_mem _ hy hz
    | add x z hx hz =>
      rw [map_add, add_lie ((ℒ i).subtype.baseChange S x)
        ((ℒ i).subtype.baseChange S z) ((ℳ j).subtype.baseChange S y)]
      exact Submodule.add_mem _ hx hz

variable [AddCommMonoid N] [DecidableEq N] (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]

/-- The extended homogeneous pieces form a Lie grading on the scalar extension. -/
instance GradedLieAlgebra.baseChange :
    GradedLieAlgebra (fun n => (ℒ n).baseChange S) where
  toDecomposition := inferInstance
  toGradedBracket := inferInstance

/-- Scalar extension preserves the grading of a representation of a graded Lie algebra. -/
instance GradedLieModule.baseChange [DecidableEq ι] [AddCommMonoid ι]
    [DecidableEq κ] [VAdd ι κ] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M]
    (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]
    (ℳ : κ → Submodule R M) [DirectSum.Decomposition ℳ] [GradedLieModule ℒ ℳ] :
    GradedLieModule (fun i => (ℒ i).baseChange S) (fun j => (ℳ j).baseChange S) where
  toGradedBracket := inferInstance

namespace TauCeti.PositiveDegrees

variable {N : Type} [AddCommMonoid N] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Extending scalars commutes with the Lie ideal above a degree cutoff. -/
@[simp]
theorem degreeIdeal_baseChange (k : ℕ) :
    (d.degreeIdeal ℒ k).baseChange S =
      d.degreeIdeal (fun n => (ℒ n).baseChange S) k := by
  apply LieSubmodule.toSubmodule_injective
  simp only [LieSubmodule.coe_baseChange, degreeIdeal_toSubmodule, degreeSubmodule_baseChange]

variable (S) in
/-- Truncation and extension of scalars commute as Lie algebras. -/
noncomputable def truncatedBaseChangeEquiv (k : ℕ) :
    d.truncatedLie (fun n => (ℒ n).baseChange S) k ≃ₗ⁅S⁆
      S ⊗[R] d.truncatedLie ℒ k :=
  (LieIdeal.quotEquivOfEq _ _ (d.degreeIdeal_baseChange ℒ k).symm).trans
    (LieIdeal.quotientBaseChangeEquiv S (d.degreeIdeal ℒ k))

/-- The comparison commutes with the scalar extension of the quotient projection. -/
@[simp]
theorem truncatedBaseChangeEquiv_mk (k : ℕ) (z : S ⊗[R] L) :
    d.truncatedBaseChangeEquiv S ℒ k (LieSubmodule.Quotient.mk z) =
      LieHom.baseChange S (d.degreeIdeal ℒ k).mkQ z := by
  simp [truncatedBaseChangeEquiv]

/-- The comparison sends the class of a pure tensor to the tensor of the class. -/
theorem truncatedBaseChangeEquiv_mk_tmul (k : ℕ) (s : S) (x : L) :
    d.truncatedBaseChangeEquiv S ℒ k (LieSubmodule.Quotient.mk (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k) := by
  simp only [truncatedBaseChangeEquiv_mk, LieHom.baseChange_tmul, LieIdeal.mkQ_apply]

/-- The linear comparison commutes with the scalar extension of the quotient projection. -/
@[simp]
theorem truncatedBaseChangeEquiv_comp_mkQ (k : ℕ) :
    (d.truncatedBaseChangeEquiv S ℒ k).toLinearMap.comp
        (d.degreeIdeal (fun n => (ℒ n).baseChange S) k).toSubmodule.mkQ =
      (d.degreeIdeal ℒ k).toSubmodule.mkQ.baseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LieHom.coe_toLinearMap, LieEquiv.coe_coe]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact d.truncatedBaseChangeEquiv_mk_tmul ℒ k s x

/-- The inverse comparison sends a tensor of a class to the class of the tensor. -/
@[simp]
theorem truncatedBaseChangeEquiv_symm_tmul (k : ℕ) (s : S) (x : L) :
    (d.truncatedBaseChangeEquiv S ℒ k).symm
        (s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k)) =
      LieSubmodule.Quotient.mk (s ⊗ₜ[R] x) :=
  (d.truncatedBaseChangeEquiv S ℒ k).symm_apply_eq.mpr
    (d.truncatedBaseChangeEquiv_mk_tmul ℒ k s x).symm

/-- Extending scalars intertwines the transitions between finite degree quotients. -/
@[simp]
theorem truncatedBaseChangeEquiv_truncationMap {k l : ℕ} (hkl : k ≤ l)
    (x : d.truncatedLie (fun n => (ℒ n).baseChange S) l) :
    d.truncatedBaseChangeEquiv S ℒ k
        (d.truncationMap (fun n => (ℒ n).baseChange S) hkl x) =
      LieHom.baseChange S (d.truncationMap ℒ hkl) (d.truncatedBaseChangeEquiv S ℒ l x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal (fun n => (ℒ n).baseChange S) l).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, truncationMap_mk, truncatedBaseChangeEquiv_mk]
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp [LieIdeal.mkQ_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The finite-order comparisons intertwine the transition homomorphisms. -/
theorem truncatedBaseChangeEquiv_comp_truncationMap {k l : ℕ} (h : k ≤ l) :
    (d.truncatedBaseChangeEquiv S ℒ k).toLieHom.comp
        (d.truncationMap (fun n => (ℒ n).baseChange S) h) =
      (LieHom.baseChange S (d.truncationMap ℒ h)).comp
        (d.truncatedBaseChangeEquiv S ℒ l).toLieHom := by
  apply LieHom.ext
  intro x
  exact d.truncatedBaseChangeEquiv_truncationMap ℒ h x

/-- The truncation comparison identifies each extended homogeneous piece. -/
theorem map_truncatedGrading_baseChange (k : ℕ) (n : N) :
    (d.truncatedGrading (fun n => (ℒ n).baseChange S) k n).map
        (d.truncatedBaseChangeEquiv S ℒ k).toLinearMap =
      (d.truncatedGrading ℒ k n).baseChange S := by
  rw [truncatedGrading_eq, ← Submodule.map_comp, truncatedBaseChangeEquiv_comp_mkQ,
    truncatedGrading_eq, Submodule.baseChange_map]

/-- The comparison identifies membership in the extended homogeneous pieces. -/
@[simp]
theorem truncatedBaseChangeEquiv_mem_iff (k : ℕ) (n : N)
    (x : d.truncatedLie (fun n => (ℒ n).baseChange S) k) :
    d.truncatedBaseChangeEquiv S ℒ k x ∈ (d.truncatedGrading ℒ k n).baseChange S ↔
      x ∈ d.truncatedGrading (fun n => (ℒ n).baseChange S) k n := by
  rw [← d.map_truncatedGrading_baseChange ℒ k n]
  constructor
  · rintro ⟨y, hy, h⟩
    exact (d.truncatedBaseChangeEquiv S ℒ k).injective h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Homogeneous projection commutes with the scalar-extension comparison. -/
@[simp]
theorem truncatedBaseChangeEquiv_decompose (k : ℕ) (n : N)
    (x : d.truncatedLie (fun n => (ℒ n).baseChange S) k) :
    d.truncatedBaseChangeEquiv S ℒ k
        (DirectSum.decompose (d.truncatedGrading (fun n => (ℒ n).baseChange S) k) x n :
          d.truncatedLie (fun n => (ℒ n).baseChange S) k) =
      (DirectSum.decompose (fun n => (d.truncatedGrading ℒ k n).baseChange S)
        (d.truncatedBaseChangeEquiv S ℒ k x) n : S ⊗[R] d.truncatedLie ℒ k) :=
  DirectSum.map_decompose_shift _ _ (d.truncatedBaseChangeEquiv S ℒ k).toLinearMap.toAddMonoidHom
    id Function.injective_id
    (fun n x hx => (d.truncatedBaseChangeEquiv_mem_iff ℒ k n x).mpr hx) n x

end TauCeti.PositiveDegrees
