/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.RepresentationTheory.Intertwining
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
* `TauCeti.permTensorPowerRep` combines the two commuting actions into one representation of
  `S_d × GL n k`, and `TauCeti.range_asAlgebraHom_permTensorAction_le_comap` says that the image of
  any element of `k[S_d]`, such as a Young symmetrizer, is a `GL n k`-subrepresentation.
* `TauCeti.map_reindex_range_asAlgebraHom`: relabeling the tensor factors along `Fin m ≃ Fin d`
  carries the image of an element of `k[S_m]` onto the image of its transport to `k[S_d]`.
* `TauCeti.trace_permTensorAction_conj_mul_tensorPowerRep`: for any `g ∈ GL n k`, the trace of a
  permutation of the tensor factors composed with `g^{⊗d}` is a class function of the permutation.
* `TauCeti.tensorPowerPermIntertwiningMap` packages `g^{⊗d}` as an intertwining map of the
  symmetric-group action, and `TauCeti.tensorPowerIntertwiningRep` is the resulting action of
  `GL n k` on the `S_d`-intertwining maps into the tensor power, by composition.
* `TauCeti.toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const` identifies the
  image of `k[GLₙ]` with the span of all diagonal tensor operators over an infinite field.
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

/-- The tensor power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev tensorPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (tensorPowerRep k n d)

/-- The actions of `GL n k` and the symmetric group on the tensor power commute.

This is the commuting-actions half of Schur--Weyl duality; it makes no double-centralizer claim. -/
theorem commute_permTensorAction_tensorPowerRep (σ : Equiv.Perm (Fin d)) (g : GL (Fin n) k) :
    Commute (permTensorAction k n d σ) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_map k (Fin n → k) (Fin d) σ (stdRep k n g)

variable {k n d} in
/-- **The trace of a permutation of the tensor factors composed with `g^{⊗d}` is a class function
of the permutation**, because the two actions commute. -/
theorem trace_permTensorAction_conj_mul_tensorPowerRep (σ τ : Equiv.Perm (Fin d))
    (g : GL (Fin n) k) :
    LinearMap.trace k _ (permTensorAction k n d (τ * σ * τ⁻¹) * tensorPowerRep k n d g) =
      LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d g) := by
  set P := permTensorAction k n d
  set G := tensorPowerRep k n d g
  have hc : P τ⁻¹ * G = G * P τ⁻¹ := (commute_permTensorAction_tensorPowerRep k n d τ⁻¹ g).eq
  have hinv : P τ⁻¹ * P τ = 1 := by rw [← map_mul P, inv_mul_cancel, map_one]
  calc LinearMap.trace k _ (P (τ * σ * τ⁻¹) * G)
      _ = LinearMap.trace k _ (P τ * (P σ * G * P τ⁻¹)) := by
        rw [map_mul P, map_mul P, mul_assoc, hc]
        simp only [mul_assoc]
      _ = LinearMap.trace k _ (P σ * G * (P τ⁻¹ * P τ)) := by
        rw [LinearMap.trace_mul_comm, mul_assoc]
      _ = LinearMap.trace k _ (P σ * G) := by rw [hinv, mul_one]

/-- The whole group algebra `k[S_d]` commutes with the general-linear action on the tensor power,
so a Young symmetrizer cuts out a `GL n k`-subrepresentation. -/
theorem commute_permTensorActionAlgHom_tensorPowerRep
    (a : MonoidAlgebra k (Equiv.Perm (Fin d))) (g : GL (Fin n) k) :
    Commute (permTensorActionAlgHom k n d a) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorActionAlgHom_def,
    permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_asAlgebraHom_map k (Fin n → k) (Fin d) a
    (stdRep k n g)

/-- **The image of an element of `k[S_d]` in `(kⁿ)^{⊗d}` is stable under `GL n k`**, because the
two actions commute.  In particular a Young symmetrizer cuts out a subrepresentation. -/
theorem range_asAlgebraHom_permTensorAction_le_comap (a : MonoidAlgebra k (Equiv.Perm (Fin d)))
    (g : GL (Fin n) k) :
    LinearMap.range ((permTensorAction k n d).asAlgebraHom a) ≤
      (LinearMap.range ((permTensorAction k n d).asAlgebraHom a)).comap
        (tensorPowerRep k n d g) := by
  rintro _ ⟨x, rfl⟩
  have h := commute_permTensorActionAlgHom_tensorPowerRep k n d a g
  rw [permTensorActionAlgHom_def] at h
  exact ⟨tensorPowerRep k n d g x, LinearMap.congr_fun h.eq x⟩

/-- **Relabeling the tensor factors transports the image of an element of `k[S_m]`**: along
`Fin m ≃ Fin d`, it carries the image of `a` in `(kⁿ)^{⊗m}` onto the image in `(kⁿ)^{⊗d}` of the
transport of `a` to `k[S_d]`. -/
theorem map_reindex_range_asAlgebraHom {m : ℕ} (h : m = d)
    (a : MonoidAlgebra k (Equiv.Perm (Fin m))) :
    (LinearMap.range ((permTensorAction k n m).asAlgebraHom a)).map
        (PiTensorProduct.reindex k (fun _ => Fin n → k) (finCongr h) :
          ⨂[k]^m (Fin n → k) →ₗ[k] ⨂[k]^d (Fin n → k)) =
      LinearMap.range ((permTensorAction k n d).asAlgebraHom
        (MonoidAlgebra.domCongr k k (finCongr h).permCongrHom a)) := by
  subst h
  have he : (Equiv.refl (Fin m)).permCongrHom = MulEquiv.refl _ := by
    ext
    simp
  simp [he]

/-- **The joint action of `S_d × GL n k` on `(kⁿ)^{⊗d}`**: a pair `(σ, g)` acts by permuting the
tensor factors by `σ` after applying `g` in every factor.  It is a representation of the product
group because the two actions commute. -/
noncomputable def permTensorPowerRep :
    Representation k (Equiv.Perm (Fin d) × GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (permTensorAction k n d).noncommCoprod (tensorPowerRep k n d)
    (commute_permTensorAction_tensorPowerRep k n d)

/-- The pair `(σ, g)` acts on `(kⁿ)^{⊗d}` as `σ ∘ g^{⊗d}`. -/
@[simp]
theorem permTensorPowerRep_apply (σ : Equiv.Perm (Fin d)) (g : GL (Fin n) k) :
    permTensorPowerRep k n d (σ, g) = permTensorAction k n d σ * tensorPowerRep k n d g :=
  (rfl)

/-- The operator `g^{⊗d}` on `(kⁿ)^{⊗d}` as an intertwining map of the symmetric-group action:
the diagonal action of `GL n k` commutes with permuting the tensor factors. -/
noncomputable def tensorPowerPermIntertwiningMap (g : GL (Fin n) k) :
    Representation.IntertwiningMap (permTensorAction k n d) (permTensorAction k n d) where
  toLinearMap := tensorPowerRep k n d g
  isIntertwining' σ := (commute_permTensorAction_tensorPowerRep k n d σ g).eq.symm

@[simp]
theorem tensorPowerPermIntertwiningMap_apply (g : GL (Fin n) k) (x : ⨂[k]^d (Fin n → k)) :
    tensorPowerPermIntertwiningMap k n d g x = tensorPowerRep k n d g x :=
  (rfl)

variable {k n d} in
/-- The representation of `GL n k` on the `S_d`-intertwining maps from `ρ` into `(kⁿ)^{⊗d}`, by
composition with `g^{⊗d}`. In a split semisimple setting, when `ρ` is irreducible, this is the
multiplicity space of `ρ` in the tensor power, with its residual action of the general linear
group. -/
noncomputable def tensorPowerIntertwiningRep {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k (Equiv.Perm (Fin d)) W) :
    Representation k (GL (Fin n) k)
      (Representation.IntertwiningMap ρ (permTensorAction k n d)) where
  toFun g := Representation.IntertwiningMap.llcomp ρ _ _ (tensorPowerPermIntertwiningMap k n d g)
  map_one' := by
    ext f x
    simp only [← Representation.IntertwiningMap.comp_def,
      Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.comp_apply,
      tensorPowerPermIntertwiningMap_apply, map_one, Module.End.one_apply]
  map_mul' g h := by
    ext f x
    simp only [← Representation.IntertwiningMap.comp_def,
      Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.comp_apply,
      tensorPowerPermIntertwiningMap_apply, map_mul, Module.End.mul_apply]

variable {k n d} in
@[simp]
theorem tensorPowerIntertwiningRep_apply_apply {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k (Equiv.Perm (Fin d)) W) (g : GL (Fin n) k)
    (f : Representation.IntertwiningMap ρ (permTensorAction k n d)) (w : W) :
    tensorPowerIntertwiningRep ρ g f w = tensorPowerRep k n d g (f w) :=
  (rfl)

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
      rw [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply]
      simp [Matrix.GeneralLinearGroup.coe_toLin]
    · rintro ⟨u, rfl⟩
      obtain ⟨g, rfl⟩ := Matrix.GeneralLinearGroup.toLin.surjective u
      refine ⟨g, ?_⟩
      rw [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply]
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
