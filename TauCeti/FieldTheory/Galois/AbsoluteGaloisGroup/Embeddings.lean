/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import TauCeti.FieldTheory.Normal.Embeddings

/-!
# The absolute Galois group acting on embeddings into an algebraic closure

For a field `k` and a `k`-algebra `A`, the absolute Galois group `Gal(k^al/k)` acts on the
embeddings `A →ₐ[k] k^al` by postcomposition. This is the action of `AlgEquiv.mulActionAlgHom` for
`M = AlgebraicClosure k`, transported across Mathlib's opaque definition
`Field.absoluteGaloisGroup k`, so that the embeddings of a field form a `Gal(k^al/k)`-set as used
for Galois lattices.

An algebraic `k`-domain has at least one embedding. When `A = L` is a field the action is
transitive, and when `L` is finite over `k` the stabilizer of an embedding `φ`, the subgroup fixing
`φ(L)`, is open in the Krull topology.

## Main results

* `TauCeti.instMulActionAbsoluteGaloisGroupAlgHom`: the postcomposition action, computed by
  `Field.absoluteGaloisGroup.smul_algHom_apply`.
* `Field.absoluteGaloisGroup.smul_algHom_comp`: it commutes with precomposition.
* `AlgHom.isOpen_stabilizer_absoluteGaloisGroup`: stabilizers of embeddings of a finite extension
  are open.
-/

public section

namespace TauCeti

variable {k : Type*} [Field k]

-- `Field.absoluteGaloisGroup k` is by definition `AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k`,
-- so `AlgEquiv.mulActionAlgHom` is reused through that definitional equality. The lemmas below
-- about this action, and the transitivity instance, rely on it as well.
/-- `Gal(k^al/k)` acts on the embeddings `A →ₐ[k] k^al` by postcomposition, `σ • φ = σ ∘ φ`. -/
noncomputable abbrev instMulActionAbsoluteGaloisGroupAlgHom (A : Type*) [Semiring A]
    [Algebra k A] : MulAction (Field.absoluteGaloisGroup k) (A →ₐ[k] AlgebraicClosure k) :=
  inferInstanceAs (MulAction (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) _)

attribute [instance] instMulActionAbsoluteGaloisGroupAlgHom

/-- The action is postcomposition: `(σ • φ) x = σ (φ x)`. -/
@[simp]
theorem _root_.Field.absoluteGaloisGroup.smul_algHom_apply {A : Type*} [Semiring A]
    [Algebra k A] (σ : Field.absoluteGaloisGroup k) (φ : A →ₐ[k] AlgebraicClosure k) (x : A) :
    (σ • φ) x = DFunLike.coe (F := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) σ (φ x) :=
  (rfl)

/-- The action by postcomposition commutes with precomposition. -/
theorem _root_.Field.absoluteGaloisGroup.smul_algHom_comp {A B : Type*} [Semiring A] [Algebra k A]
    [Semiring B] [Algebra k B] (σ : Field.absoluteGaloisGroup k) (φ : A →ₐ[k] AlgebraicClosure k)
    (ψ : B →ₐ[k] A) : σ • φ.comp ψ = (σ • φ).comp ψ :=
  (rfl)

/-- An algebraic `k`-algebra embeds into the algebraic closure of `k`. -/
instance (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.IsAlgebraic k A] :
    Nonempty (A →ₐ[k] AlgebraicClosure k) :=
  ⟨IsAlgClosed.lift⟩

/-- The absolute Galois group acts transitively on the embeddings of a field. -/
instance (L : Type*) [Field L] [Algebra k L] :
    MulAction.IsPretransitive (Field.absoluteGaloisGroup k) (L →ₐ[k] AlgebraicClosure k) :=
  AlgEquiv.isPretransitiveAlgHom

/-- The stabilizer of an embedding of a finite extension is open in the Krull topology. -/
theorem _root_.AlgHom.isOpen_stabilizer_absoluteGaloisGroup {L : Type*} [Field L] [Algebra k L]
    [FiniteDimensional k L] (φ : L →ₐ[k] AlgebraicClosure k) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) φ :
      Set (Field.absoluteGaloisGroup k)) := by
  have : FiniteDimensional k φ.fieldRange :=
    LinearMap.finiteDimensional_range φ.toLinearMap
  exact (FieldTheory.stabilizer_algHom_eq_fixingSubgroup φ) ▸
    IntermediateField.fixingSubgroup_isOpen φ.fieldRange

end TauCeti
