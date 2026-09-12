/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.GeneralLinear
public import TauCeti.RepresentationTheory.AsAlgebraHom
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# Tensor powers of the standard representation

This file specializes the diagonal tensor-power construction to the standard representation of
the general linear group. It supplies the tensor powers that underpin the Weyl construction for
polynomial representations, together with the description of their monoid-algebra image over an
infinite field.

## Main results

* `TauCeti.tensorPowerRep` is the `d`-fold tensor power of `stdRep`.
* `TauCeti.tensorPowerFDRep` is its bundled finite-dimensional form.
* `TauCeti.commute_permTensorAction_tensorPowerRep` proves that the general-linear and
  symmetric-group actions commute, and `TauCeti.commute_permTensorActionAlgHom_tensorPowerRep`
  extends that to the whole group algebra `k[S_d]`.
* `TauCeti.toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const` identifies the
  image of `k[GLₙ]` with the span of all diagonal tensor operators over an infinite field.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md), Layer 1, “The tensor power representation”.
-/

public section

open Matrix
open scoped TensorProduct

open PiTensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The diagonal action of `GL n k` on the `d`-fold tensor power of its standard representation. -/
noncomputable abbrev tensorPowerRep :
    Representation k (GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (stdRep k n).tensorPower d

/-- The tensor-power representation acts by applying the matrix of a general-linear element in
every tensor factor.

This is intentionally not a simp lemma: `Representation.tensorPower_apply` and `stdRep_apply`
already prove the same simplification, so the `simpNF` linter rejects this specialization. -/
theorem tensorPowerRep_apply (g : GL (Fin n) k) :
    tensorPowerRep k n d g =
      PiTensorProduct.map fun _ : Fin d => Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply]

/-- The tensor power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev tensorPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (tensorPowerRep k n d)

/-- The actions of `GL n k` and the symmetric group on the tensor power commute.

This is the commuting-actions half of Schur--Weyl duality, the first Layer 2 target of the
classical-groups roadmap; it makes no double-centralizer claim. -/
theorem commute_permTensorAction_tensorPowerRep (σ : Equiv.Perm (Fin d)) (g : GL (Fin n) k) :
    Commute (permTensorAction k n d σ) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_map k (Fin n → k) (Fin d) σ (stdRep k n g)

/-- The whole group algebra `k[S_d]` commutes with the general-linear action on the tensor power,
so a Young symmetrizer cuts out a `GL n k`-subrepresentation. -/
theorem commute_permTensorActionAlgHom_tensorPowerRep
    (a : MonoidAlgebra k (Equiv.Perm (Fin d))) (g : GL (Fin n) k) :
    Commute (permTensorActionAlgHom k n d a) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorActionAlgHom_def,
    permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_asAlgebraHom_map k (Fin n → k) (Fin d) a
    (stdRep k n g)

end CommRing

section InfiniteField

variable [Field k] [Infinite k]

/-- **The general linear group spans the same operators on `(kⁿ)^{⊗d}` as the whole endomorphism
algebra of `kⁿ`**: the span of the diagonal operators `g^{⊗d}` for `g` invertible is the span of all
the diagonal operators `f^{⊗d}`. This is the Zariski density of the invertible endomorphisms of
`kⁿ`, and it needs the field to be infinite. -/
theorem span_range_tensorPowerRep_eq_span_range_map_const :
    Submodule.span k (Set.range (tensorPowerRep k n d)) =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        PiTensorProduct.map fun _ : Fin d => f) := by
  have hrange : Set.range (tensorPowerRep k n d) =
      Set.range fun u : ((Fin n → k) →ₗ[k] Fin n → k)ˣ =>
        PiTensorProduct.map fun _ : Fin d => (u : (Fin n → k) →ₗ[k] Fin n → k) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨Matrix.GeneralLinearGroup.toLin g, ?_⟩
      rw [tensorPowerRep_apply]
      simp [Matrix.GeneralLinearGroup.coe_toLin]
    · rintro ⟨u, rfl⟩
      obtain ⟨g, rfl⟩ := Matrix.GeneralLinearGroup.toLin.surjective u
      refine ⟨g, ?_⟩
      rw [tensorPowerRep_apply]
      simp [Matrix.GeneralLinearGroup.coe_toLin]
  rw [hrange, PiTensorProduct.span_range_map_const_units_eq_span_range_map_const]

/-- **The image of the monoid algebra `k[GLₙ]` in `End ((kⁿ)^{⊗d})` is the span of all the
diagonal operators `f^{⊗d}`**, with `f` ranging over every endomorphism of `kⁿ` and not only the
invertible ones. -/
theorem toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const :
    Subalgebra.toSubmodule (tensorPowerRep k n d).asAlgebraHom.range =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        PiTensorProduct.map fun _ : Fin d => f) := by
  rw [Representation.toSubmodule_range_asAlgebraHom,
    span_range_tensorPowerRep_eq_span_range_map_const]

end InfiniteField

section Field

variable [Field k]

/-- The character of the tensor power is the corresponding power of the standard character.

This is intentionally not a simp lemma: `Representation.char_tensorPower` and `char_stdRep`
already normalize its left-hand side, so registering this specialization would violate `simpNF`. -/
theorem char_tensorPowerRep (g : GL (Fin n) k) : (tensorPowerRep k n d).character g =
      Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ d := by
  rw [Representation.char_tensorPower, char_stdRep]

/-- The character of the bundled tensor power is the corresponding power of the matrix trace. -/
@[simp]
theorem char_tensorPowerFDRep (g : GL (Fin n) k) : (tensorPowerFDRep k n d).character g =
      Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ d := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_tensorPowerRep k n d g

end Field

end TauCeti
