/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.SchurWeyl

/-!
# Schur-Weyl duality between the images of `k[GLₙ]` and `k[S_d]`

The symmetric group `S_d` acts on `(kⁿ)^{⊗d}` by permuting the tensor factors
(`TauCeti.permTensorAction`) and the general linear group acts diagonally by the tensor power
`TauCeti.tensorPowerRep` of its standard representation; the two actions commute, by
`TauCeti.commute_permTensorAction_tensorPowerRep`. Schur-Weyl duality says that inside
`End_k ((kⁿ)^{⊗d})` the **images of the two group algebras** `k[GLₙ]` and `k[S_d]` are each other's
centralizers.

`TauCeti/RepresentationTheory/Symmetric/TensorAction/SchurWeyl.lean` proves the duality with the
span of *all* the diagonal operators `f^{⊗d}`, for `f` an arbitrary endomorphism of `kⁿ`, in place
of the image of `k[GLₙ]`. The imported module
`TauCeti/RepresentationTheory/ClassicalGroups/TensorPower.lean` identifies the two: the image of a
monoid algebra is the span of the image of the monoid, and over an infinite field the invertible
diagonal operators already span all diagonal operators. This file combines that identification
with the span-level duality to obtain both mutual-commutant statements.

The two hypotheses on the field play different roles: that `d !` is nonzero is Maschke's theorem for
`S_d`, which the semisimple half of the duality needs, while the infinitude of `k` is what the
density argument identifying the two spans needs.

## Main results

* `TauCeti.centralizer_range_tensorPowerRep_asAlgebraHom_eq_range_permTensorActionAlgHom` and
  `TauCeti.centralizer_range_permTensorActionAlgHom_eq_range_tensorPowerRep_asAlgebraHom`: **the
  images of `k[GLₙ]` and of `k[S_d]` are each other's centralizers.**
* `TauCeti.centralizer_range_tensorPowerRep_eq_range_permTensorActionAlgHom` and
  `TauCeti.centralizer_range_permTensorAction_eq_range_tensorPowerRep_asAlgebraHom`: the same
  mutual-commutant result stated directly for the ranges of the two group actions.
* `TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep` and
  `TauCeti.mem_range_tensorPowerRep_asAlgebraHom_iff_forall_commute_permTensorAction`: the same as
  membership criteria, an endomorphism acting as an element of `k[S_d]` exactly when it commutes
  with the whole general linear group, and as an element of `k[GLₙ]` exactly when it commutes with
  every factor permutation.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6 and Appendix B.1.
* C. Procesi, *Lie Groups: An Approach through Invariants and Representations*, Chapter 9.
-/

public section

open scoped Nat TensorProduct

open PiTensorProduct

namespace TauCeti

variable {k : Type*} {n d : ℕ} [Field k] [Infinite k]

variable [NeZero (d ! : k)]

/-- **Schur-Weyl duality: the commutant of the image of `k[GLₙ]` is the image of `k[S_d]`.** -/
@[simp]
theorem centralizer_range_tensorPowerRep_asAlgebraHom_eq_range_permTensorActionAlgHom :
    Subalgebra.centralizer k
        (Set.range ⇑(tensorPowerRep k n d).asAlgebraHom) =
      (permTensorActionAlgHom k n d).range := by
  rw [← AlgHom.coe_range, ← Subalgebra.coe_toSubmodule,
    toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const,
    centralizer_span_range_map_const_eq_range_permTensorActionAlgHom]

/-- **Schur-Weyl duality: the commutant of the image of `k[S_d]` is the image of `k[GLₙ]`.** -/
@[simp]
theorem centralizer_range_permTensorActionAlgHom_eq_range_tensorPowerRep_asAlgebraHom :
    Subalgebra.centralizer k
        (Set.range ⇑(permTensorActionAlgHom k n d)) =
      (tensorPowerRep k n d).asAlgebraHom.range :=
  SetLike.coe_injective <| by
    rw [← AlgHom.coe_range,
      coe_centralizer_range_permTensorActionAlgHom_eq_span_range_map_const
        (isUnit_iff_ne_zero.2 (NeZero.ne _)),
      ← Subalgebra.coe_toSubmodule,
      toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const]

/-- **Schur-Weyl duality, as a membership criterion.** An endomorphism of `(kⁿ)^{⊗d}` is the action
of an element of the group algebra `k[S_d]` exactly when it commutes with the diagonal action of
every element of `GLₙ`. -/
theorem mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep
    (x : Module.End k (⨂[k] _ : Fin d, Fin n → k)) :
    x ∈ (permTensorActionAlgHom k n d).range ↔
      ∀ g : GL (Fin n) k, Commute x (tensorPowerRep k n d g) := by
  rw [mem_range_permTensorActionAlgHom_iff_forall_commute]
  constructor
  · intro hx g
    rw [tensorPowerRep_apply]
    exact hx (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))
  · intro hx f
    have hf : map (fun _ : Fin d => f) ∈
        Subalgebra.toSubmodule (tensorPowerRep k n d).asAlgebraHom.range := by
      rw [toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const]
      exact Submodule.subset_span ⟨f, rfl⟩
    obtain ⟨a, ha⟩ := hf
    rw [← ha]
    exact Representation.commute_asAlgebraHom_of_forall_commute (tensorPowerRep k n d) hx a

/-- **Schur-Weyl duality, as a membership criterion.** An endomorphism of `(kⁿ)^{⊗d}` is the
diagonal action of an element of the group algebra `k[GLₙ]` exactly when it commutes with the
permutation of the tensor factors by every element of `S_d`. This is the companion of
`TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep` with the roles of the
two groups exchanged. -/
theorem mem_range_tensorPowerRep_asAlgebraHom_iff_forall_commute_permTensorAction
    (x : Module.End k (⨂[k] _ : Fin d, Fin n → k)) :
    x ∈ (tensorPowerRep k n d).asAlgebraHom.range ↔
      ∀ σ : Equiv.Perm (Fin d), Commute x (permTensorAction k n d σ) := by
  rw [← centralizer_range_permTensorActionAlgHom_eq_range_tensorPowerRep_asAlgebraHom,
    mem_centralizer_range_permTensorActionAlgHom_iff_forall_commute]

/-- **Schur-Weyl duality for the group ranges:** the commutant of the general-linear group action
is the image of `k[S_d]`. -/
@[simp]
theorem centralizer_range_tensorPowerRep_eq_range_permTensorActionAlgHom :
    Subalgebra.centralizer k (Set.range (tensorPowerRep k n d)) =
      (permTensorActionAlgHom k n d).range := by
  ext x
  rw [mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep,
    Subalgebra.mem_centralizer_iff]
  refine ⟨fun hx g => (hx _ ⟨g, rfl⟩).symm, fun hx _ hy => ?_⟩
  obtain ⟨g, rfl⟩ := hy
  exact (hx g).symm

/-- **Schur-Weyl duality for the group ranges:** the commutant of the symmetric-group action is
the image of `k[GLₙ]`. -/
@[simp]
theorem centralizer_range_permTensorAction_eq_range_tensorPowerRep_asAlgebraHom :
    Subalgebra.centralizer k (Set.range (permTensorAction k n d)) =
      (tensorPowerRep k n d).asAlgebraHom.range := by
  ext x
  rw [mem_range_tensorPowerRep_asAlgebraHom_iff_forall_commute_permTensorAction,
    Subalgebra.mem_centralizer_iff]
  refine ⟨fun hx σ => (hx _ ⟨σ, rfl⟩).symm, fun hx _ hy => ?_⟩
  obtain ⟨σ, rfl⟩ := hy
  exact (hx σ).symm

end TauCeti
