/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.RepresentationTheory.InvariantForm.BaseChange
public import TauCeti.RepresentationTheory.Symmetric.Specht.Module

/-!
# Self-duality of the Specht modules

The Specht module `S^μ` sits inside the Young permutation module `M^μ`, which carries the tabloid
form `TauCeti.tabloidForm`: the symmetric form for which the tabloids are orthonormal.  The
symmetric group permutes the tabloids, so the form is invariant, and so is its restriction to
`S^μ` (`TauCeti.spechtModuleForm`).  Over an ordered commutative ring the tabloid form is
positive definite, and therefore so is its restriction to any submodule.  In particular the
restriction to `S^μ` is nondegenerate, and over an ordered field `v ↦ B(v, ·)` is an isomorphism
of `S^μ` with its contragredient, the dual space on which `σ` acts by `φ ↦ φ ∘ σ⁻¹`
(`TauCeti.spechtModuleEquivDual`).

Positive definiteness is what makes nondegeneracy free here.  In characteristic `p` the
restricted form can be degenerate, already for `S^((2,1))` when `p = 3`, and its radical is
James's `S^μ ∩ S^μ⊥`.

Extending scalars from an ordered field `R` to any field `K` over `R` keeps the duality: the base
change of the form is invariant and nondegenerate, so the base-changed Specht module is self-dual
by a `K`-bilinear pairing (`TauCeti.spechtModuleBaseChangeEquivDual`).  This pairing is
`a * b * B(v, w)` on pure tensors `a ⊗ v` and `b ⊗ w`.  With `R = ℚ` and `K = ℂ` the base-changed
module is the complex Specht module `TauCeti.spechtModuleℂ`, and the duality is complex-bilinear
rather than Hermitian.

## Main definitions

* `TauCeti.spechtModuleForm`: the restriction of the tabloid form to the Specht module.
* `TauCeti.spechtModuleEquivDual`: over an ordered field, the isomorphism of the Specht module with
  its dual representation given by that form.
* `TauCeti.spechtModuleBaseChangeEquivDual`: its scalar extension to a field `K` over `R`.

## Main results

* `TauCeti.isSymm_spechtModuleForm` and `TauCeti.isInvariantForm_spechtModuleForm`: the
  restricted tabloid form is symmetric and invariant.
* `TauCeti.nondegenerate_spechtModuleForm`: over an ordered commutative ring, such as `ℤ` or `ℚ`,
  it is nondegenerate.
* `TauCeti.spechtModuleBaseChangeEquivDual_tmul`: the scalar-extended duality is the base change
  of the duality over `R`.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4, where
  the tabloid form is restricted to `S^μ`, and Chapter 8, where the dual of a Specht module is
  compared with a Specht module.
-/

public section

namespace TauCeti

open _root_.LinearMap (BilinForm)

variable {n : ℕ}

section CommRing

variable {R : Type*} [CommRing R]

/-- The **form on the Specht module** `S^μ`: the restriction of the tabloid form of `M^μ` to the
span of the polytabloids. -/
noncomputable def spechtModuleForm (μ : n.Partition) : BilinForm R (spechtModule (R := R) μ) :=
  (tabloidForm (shapePartition (YoungDiagram.ofPartition μ))).restrict
    (spechtSubrepresentation (R := R) (YoungDiagram.ofPartition μ)).toSubmodule

/-- The form on the Specht module is the tabloid form of the ambient Young permutation module. -/
@[simp]
theorem spechtModuleForm_apply (μ : n.Partition) (v w : spechtModule (R := R) μ) :
    spechtModuleForm μ v w =
      tabloidForm (R := R) (shapePartition (YoungDiagram.ofPartition μ))
        (v : MonoidAlgebra R _) (w : MonoidAlgebra R _) := (rfl)

/-- The form on the Specht module is symmetric. -/
theorem isSymm_spechtModuleForm (μ : n.Partition) : (spechtModuleForm (R := R) μ).IsSymm :=
  permutationForm_isSymm.restrict _

/-- **The form on the Specht module is invariant** under the symmetric group, because the
symmetric group permutes the tabloids. -/
theorem isInvariantForm_spechtModuleForm (μ : n.Partition) :
    Representation.IsInvariantForm (spechtModule (R := R) μ).ρ (spechtModuleForm μ) :=
  ((Representation.isInvariantForm_iff.mpr fun σ v w => tabloidForm_invariant _ σ v w).restrict
    _).comp _

end CommRing

section Ordered

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Over an ordered commutative ring the form on the Specht module is nondegenerate**, since the
tabloid form is positive definite. -/
theorem nondegenerate_spechtModuleForm (μ : n.Partition) :
    (spechtModuleForm (R := R) μ).Nondegenerate :=
  permutationForm_restrict_nondegenerate _

end Ordered

section OrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Specht self-duality.**  Over an ordered field such as `ℚ`, the form on the Specht module
identifies `S^μ` with its dual representation, on which `σ` acts by `φ ↦ φ ∘ σ⁻¹`: the map
`v ↦ B(v, ·)` is a bijective intertwiner. -/
noncomputable def spechtModuleEquivDual (μ : n.Partition) :
    _root_.Representation.Equiv (spechtModule (R := R) μ).ρ
      (_root_.Representation.dual (spechtModule (R := R) μ).ρ) :=
  (isInvariantForm_spechtModuleForm μ).equivDual (nondegenerate_spechtModuleForm μ)

/-- The Specht self-duality sends `v` to the functional `w ↦ B(v, w)`. -/
@[simp]
theorem spechtModuleEquivDual_apply (μ : n.Partition) (v w : spechtModule (R := R) μ) :
    spechtModuleEquivDual μ v w = spechtModuleForm μ v w :=
  Representation.IsInvariantForm.equivDual_apply _ _ v w

variable (K : Type*) [Field K] [Algebra R K]

/-- **Specht self-duality after extending scalars** from an ordered field `R` to a field `K` over
`R`.  The base change of the form on the Specht module is invariant and still nondegenerate, so it
identifies `K ⊗_R S^μ` with its dual representation over `K`.  For `R = ℚ` and `K = ℂ` this is a
complex-bilinear self-duality of `TauCeti.spechtModuleℂ`. -/
noncomputable def spechtModuleBaseChangeEquivDual (μ : n.Partition) :
    _root_.Representation.Equiv (_root_.Representation.baseChange K (spechtModule (R := R) μ).ρ)
      (_root_.Representation.baseChange K (spechtModule (R := R) μ).ρ).dual :=
  ((isInvariantForm_spechtModuleForm μ).baseChange (A := K)).equivDual
    (((spechtModuleForm μ).nondegenerate_baseChange_iff (A := K)
      (Module.Free.chooseBasis R _)).mpr (nondegenerate_spechtModuleForm μ))

/-- **The scalar-extended self-duality is the base change of the self-duality over `R`**: on pure
tensors it pairs `a ⊗ v` with `b ⊗ w` to `a * b * B(v, w)`. -/
@[simp]
theorem spechtModuleBaseChangeEquivDual_tmul (μ : n.Partition) (a b : K)
    (v w : spechtModule (R := R) μ) :
    spechtModuleBaseChangeEquivDual K μ (a ⊗ₜ v) (b ⊗ₜ w) =
      a * b * algebraMap R K (spechtModuleForm μ v w) := by
  rw [spechtModuleBaseChangeEquivDual, Representation.IsInvariantForm.equivDual_apply,
    LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, mul_comm]

end OrderedField

end TauCeti
