/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.GeneralLinear
public import TauCeti.RepresentationTheory.AsAlgebraHom
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
of the image of `k[GLₙ]`. This file identifies the two. The image of a group algebra is the span of
the image of the group (`Representation.toSubmodule_range_asAlgebraHom`), and over an infinite field
the span of the invertible diagonal operators is already the span of all of them
(`PiTensorProduct.span_range_map_const_units_eq_span_range_map_const`, the Zariski density of the
invertible endomorphisms). Both mutual-commutant statements follow.

The two hypotheses on the field play different roles: that `d !` is nonzero is Maschke's theorem for
`S_d`, which the semisimple half of the duality needs, while the infinitude of `k` is what the
density argument identifying the two spans needs.

## Main results

* `TauCeti.span_range_tensorPowerRep_eq_span_range_map_const` and
  `TauCeti.toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const`: the image of
  `k[GLₙ]` is the span of all the diagonal operators, not only of the invertible ones.
* `TauCeti.centralizer_range_tensorPowerRep_asAlgebraHom_eq_range_permTensorActionAlgHom` and
  `TauCeti.centralizer_range_permTensorActionAlgHom_eq_range_tensorPowerRep_asAlgebraHom`: **the
  images of `k[GLₙ]` and of `k[S_d]` are each other's centralizers.**
* `TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep`: the same as a
  membership criterion, an endomorphism acting as an element of `k[S_d]` exactly when it commutes
  with the whole general linear group.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8, "The double centralizer (image-level)", which asks for the mutual commutant of the two
  group-algebra images.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6 and Appendix B.1.
* C. Procesi, *Lie Groups: An Approach through Invariants and Representations*, Chapter 9.
-/

public section

open scoped Nat TensorProduct

open PiTensorProduct

namespace TauCeti

variable {k : Type*} {n d : ℕ} [Field k] [Infinite k]

/-- **The general linear group spans the same operators on `(kⁿ)^{⊗d}` as the whole endomorphism
algebra of `kⁿ`**: the span of the diagonal operators `g^{⊗d}` for `g` invertible is the span of all
the diagonal operators `f^{⊗d}`. This is the Zariski density of the invertible endomorphisms of
`kⁿ`, and it needs the field to be infinite. -/
theorem span_range_tensorPowerRep_eq_span_range_map_const :
    Submodule.span k (Set.range (tensorPowerRep k n d)) =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        map fun _ : Fin d => f) := by
  have hrange : Set.range (tensorPowerRep k n d) =
      Set.range fun u : ((Fin n → k) →ₗ[k] Fin n → k)ˣ =>
        map fun _ : Fin d => (u : (Fin n → k) →ₗ[k] Fin n → k) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨Matrix.GeneralLinearGroup.toLin g, ?_⟩
      simp [Matrix.GeneralLinearGroup.coe_toLin]
    · rintro ⟨u, rfl⟩
      obtain ⟨g, rfl⟩ := Matrix.GeneralLinearGroup.toLin.surjective u
      refine ⟨g, ?_⟩
      simp [Matrix.GeneralLinearGroup.coe_toLin]
  rw [hrange, PiTensorProduct.span_range_map_const_units_eq_span_range_map_const]

/-- **The image of the group algebra `k[GLₙ]` in `End ((kⁿ)^{⊗d})` is the span of all the diagonal
operators `f^{⊗d}`**, with `f` ranging over every endomorphism of `kⁿ` and not only the invertible
ones. This is what turns the Schur-Weyl duality of
`TauCeti/RepresentationTheory/Symmetric/TensorAction/SchurWeyl.lean` into a statement about the
image of `k[GLₙ]`. -/
theorem toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const :
    Subalgebra.toSubmodule (tensorPowerRep k n d).asAlgebraHom.range =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        map fun _ : Fin d => f) := by
  rw [Representation.toSubmodule_range_asAlgebraHom,
    span_range_tensorPowerRep_eq_span_range_map_const]

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
    simpa using hx (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))
  · intro hx f
    refine Commute.span_right (R := k) (s := Set.range (tensorPowerRep k n d))
      (fun y hy => ?_) _ ?_
    · obtain ⟨g, rfl⟩ := hy
      exact hx g
    · rw [span_range_tensorPowerRep_eq_span_range_map_const]
      exact Submodule.subset_span ⟨f, rfl⟩

end TauCeti
