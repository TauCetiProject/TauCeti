/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Action.Rigid
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Symmetric

/-!
# Traces of actions in a symmetric rigid category

Let `V` be a symmetric rigid monoidal category and `H` a group. Then `Action V H` is again
symmetric and rigid, so both `V` and `Action V H` carry their canonical spherical structures,
whose pivotal isomorphisms are the Drinfeld isomorphisms. Since the duals, the evaluations, the
coevaluations and the braiding of `Action V H` are those of `V` on underlying objects, so are the
pivotal isomorphisms (`Action.drinfeldIso_hom_hom`), the traces and the dimensions: the
categorical trace of an equivariant endomorphism is the trace of the underlying endomorphism in
`V`.

For `V = FGModuleCat k` this computes the traces of `FDRep k G`.

## Main results

* `Action.rightTrace_hom`, `Action.leftTrace_hom`, `Action.trace_hom`: the traces of an
  endomorphism of an action are those of the underlying endomorphism;
* `Action.quantumDim_hom`: the quantum dimension of an action is that of its underlying object.
-/

public section

open CategoryTheory MonoidalCategory TauCeti

namespace Action

variable {V : Type*} [Category* V] [MonoidalCategory V] [SymmetricCategory V] [RigidCategory V]
  {H : Type*} [Group H]

/-- The right trace of an endomorphism of an action is the right trace of the underlying
endomorphism. -/
@[simp]
theorem rightTrace_hom {X : Action V H} (f : X ⟶ X) : (rightTrace f).hom = rightTrace f.hom := by
  simp [rightTrace_eq_braiding]

/-- The left trace of an endomorphism of an action is the left trace of the underlying
endomorphism. -/
@[simp]
theorem leftTrace_hom {X : Action V H} (f : X ⟶ X) : (leftTrace f).hom = leftTrace f.hom := by
  rw [leftTrace_eq_rightTrace_of_symmetric, leftTrace_eq_rightTrace_of_symmetric, rightTrace_hom]

/-- The trace of an endomorphism of an action is the trace of the underlying endomorphism. -/
@[simp]
theorem trace_hom {X : Action V H} (f : X ⟶ X) : (trace f).hom = trace f.hom := by
  rw [trace_eq_rightTrace, trace_eq_rightTrace, rightTrace_hom]

/-- The quantum dimension of an action is the quantum dimension of its underlying object. -/
@[simp]
theorem quantumDim_hom (X : Action V H) : (quantumDim X).hom = quantumDim X.V := by
  rw [← trace_id, ← trace_id, trace_hom, id_hom]

end Action
