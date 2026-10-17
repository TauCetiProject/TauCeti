/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Hopf ideals under a trivial field extension

When the ground-field map is surjective, every Hopf ideal after scalar extension comes
from a Hopf ideal over the original field. The coefficient Hopf ideal for the one-element
basis supplies the descent. This applies to an algebraic extension of an algebraically
closed field and allows geometric subgroup conditions to be checked over that field itself.
-/

public section

open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- Every Hopf ideal descends along a surjective map of ground fields. -/
theorem baseChangeHopfIdeal_surjective (h : Function.Surjective (algebraMap k K)) :
    Function.Surjective (baseChangeHopfIdeal (H := H) (K := K)) := by
  classical
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    ⟨(algebraMap k K).injective, h⟩
  let b := (Module.Basis.singleton Unit k).map e.toLinearEquiv
  intro I
  refine ⟨b.coefficientHopfIdeal I, le_antisymm ?_ ?_⟩
  · rw [← HopfIdeal.toIdeal_le_toIdeal, baseChangeHopfIdeal_toIdeal,
      Ideal.map_le_iff_le_comap, Module.Basis.coefficientHopfIdeal_toIdeal_le_iff]
    intro z hz j
    obtain ⟨x, rfl⟩ := Algebra.TensorProduct.includeRight_surjective (T := H) h z
    simpa [b, e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] using hz
  · exact (b.coefficientHopfIdeal_le_iff_le_baseChangeHopfIdeal I _).mp le_rfl

end TauCeti.CommHopfAlgCat
