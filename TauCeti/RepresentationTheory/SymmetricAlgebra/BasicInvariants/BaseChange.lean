/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SymmetricAlgebra.BaseChange
public import TauCeti.RepresentationTheory.SymmetricAlgebra.BasicInvariants.Basic
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# Scalar extension of basic invariants

`Representation.IsBasicInvariants.baseChange_of_bijective` transports a system of basic
invariants and its degrees along a bijective invariant-algebra comparison.
`Representation.IsBasicInvariants.baseChange_of_free` applies when the coefficient algebra
is free over the base commutative semiring, and `Representation.IsBasicInvariants.baseChange`
applies to flat extensions of commutative rings for a finitely generated acting monoid. The
polynomial presentation is transported using `MvPolynomial.algebraTensorAlgEquiv`.
-/

public section

open SymmetricAlgebra TensorProduct TauCeti.SymmetricAlgebra

namespace Representation

variable {R S G M ι : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S] [Monoid G] [AddCommMonoid M]
  [Module R M] {ρ : Representation R G M}

/-- If the invariant algebra comparison is bijective, the scalar extensions of basic invariants
are basic invariants of the same degrees. -/
theorem IsBasicInvariants.baseChange_of_bijective
    {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ} (h : ρ.IsBasicInvariants f d)
    (hbij : Function.Bijective (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S))) :
    (ρ.baseChange S).IsBasicInvariants
      (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeMap (1 ⊗ₜ[R] f i)) d := by
  constructor
  · intro i
    simp only [coe_symmetricAlgebraInvariantsBaseChangeMap, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Subalgebra.coe_val]
    exact scalarTensorBialgEquiv_mem_homogeneousSubmodule
      (Submodule.tmul_mem_baseChange_of_mem 1 (h.homogeneous i))
  · -- The evaluation factorization uses Mathlib's `MvPolynomial.algebraTensorAlgEquiv` to
    -- change the coefficient ring.
    rw [← MvPolynomial.comp_aeval,
      MvPolynomial.aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm f]
    have ht : Function.Bijective (Algebra.TensorProduct.lTensor (S := S) S
        (MvPolynomial.aeval (R := R) f)) := by
      rw [AlgHom.coe_tensorProduct_map_id (S := S), ← AlgHom.coe_tensorProduct_map_id (S := R)]
      exact Algebra.TensorProduct.map_bijective
        (f := AlgHom.id R S) Function.bijective_id h.bijective_aeval
    simpa only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom] using
      hbij.comp (ht.comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R S).symm.bijective)

/-- If `S` is free as an `R`-module, the scalar extensions of basic invariants for any monoid
are basic invariants of the same degrees. -/
theorem IsBasicInvariants.baseChange_of_free [Module.Free R S]
    {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ} (h : ρ.IsBasicInvariants f d) :
    (ρ.baseChange S).IsBasicInvariants
      (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeMap (1 ⊗ₜ[R] f i)) d :=
  h.baseChange_of_bijective ρ.symmetricAlgebraInvariantsBaseChangeMap_bijective_of_free

end CommSemiring

variable [CommRing R] [CommRing S] [Algebra R S] [Monoid G] [Monoid.FG G] [AddCommMonoid M]
  [Module R M] [Module.Flat R S] {ρ : Representation R G M}

/-- Under a flat extension of commutative rings for a finitely generated acting monoid, basic
invariants remain basic invariants of the same degrees. -/
theorem IsBasicInvariants.baseChange {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ}
    (h : ρ.IsBasicInvariants f d) :
    (ρ.baseChange S).IsBasicInvariants
      (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeMap (1 ⊗ₜ[R] f i)) d :=
  h.baseChange_of_bijective ρ.symmetricAlgebraInvariantsBaseChangeMap_bijective

end Representation
