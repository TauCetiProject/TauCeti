/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Invariants
import TauCeti.RepresentationTheory.GaloisDescent.Span
import TauCeti.RepresentationTheory.GaloisDescent.Injective

/-!
# Scalar extension of an invariant group algebra

The natural map from `L ⊗[k] (L[M])^Gal(L/k)` to `L[M]` is surjective when the
automorphism group of `L/k` is finite. Here the action twists both the coefficients and the
exponents, with the latter specified by an integral representation on the abelian group `M`.
The scalar-extension map is Mathlib's `AlgHom.liftEquiv` applied to the invariant-subalgebra
inclusion; it sends `a ⊗ x` to `a • x`.

For a finite Galois extension this map is an algebra equivalence. This identifies the scalar
extension of the descended coordinate algebra with the split group algebra, as needed for
groups of multiplicative type and non-split tori. Transporting the Hopf structure additionally
requires the analogous identification on tensor squares.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]

/-- Scalar extension of the invariant group-algebra inclusion is surjective. In particular,
this holds over every finite Galois extension, without a characteristic restriction or a
finite-generation hypothesis on the exponent group. -/
theorem liftEquiv_groupAlgebraInvariants_surjective
    [Finite (L ≃ₐ[k] L)] (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Function.Surjective
      (AlgHom.liftEquiv k L (groupAlgebraInvariants rho)
        (MonoidAlgebra L (Multiplicative M)) (groupAlgebraInvariants rho).val) := by
  let ρ : Representation k (L ≃ₐ[k] L) (MonoidAlgebra L (Multiplicative M)) :=
    { toFun := fun σ ↦ (groupAlgebraAction rho σ).toLinearMap
      map_one' := by ext x; simp
      map_mul' := by intros; ext x; simp }
  have hspan : Submodule.span L (groupAlgebraInvariants rho :
      Set (MonoidAlgebra L (Multiplicative M))) = ⊤ := by
    have hinv : (ρ.invariants : Set (MonoidAlgebra L (Multiplicative M))) =
        (groupAlgebraInvariants rho : Set (MonoidAlgebra L (Multiplicative M))) := by
      ext x
      simp [Representation.mem_invariants, ρ]
    rw [← hinv]
    exact span_invariants_eq_top (ρ := ρ) (groupAlgebraAction_smul rho)
  let f := AlgHom.liftEquiv k L (groupAlgebraInvariants rho)
    (MonoidAlgebra L (Multiplicative M)) (groupAlgebraInvariants rho).val
  apply (LinearMap.range_eq_top (f := f.toLinearMap)).mp
  apply top_unique
  rw [← hspan, Submodule.span_le]
  intro x hx
  exact ⟨1 ⊗ₜ[k] (⟨x, hx⟩ : groupAlgebraInvariants rho), by
    simp [f]⟩

variable [FiniteDimensional k L] [IsGalois k L]

/-- Over a finite Galois extension, scalar extension of the invariant group-algebra inclusion
is injective. The exponent group need not be finitely generated. -/
theorem liftEquiv_groupAlgebraInvariants_injective
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Function.Injective
      (AlgHom.liftEquiv k L (groupAlgebraInvariants rho)
        (MonoidAlgebra L (Multiplicative M)) (groupAlgebraInvariants rho).val) := by
  let ρ : Representation k (L ≃ₐ[k] L) (MonoidAlgebra L (Multiplicative M)) :=
    { toFun := fun σ ↦ (groupAlgebraAction rho σ).toLinearMap
      map_one' := by ext x; simp
      map_mul' := by intros; ext x; simp }
  let f := (groupAlgebraInvariants rho).val
  have h := liftBaseChange_injective_of_invariant (ρ := ρ)
    f.toLinearMap Subtype.val_injective (fun σ a x ↦ by
      -- Expand the local representation and inclusion to apply the action's scalar law.
      change groupAlgebraAction rho σ (a • x.val) = σ a • x.val
      rw [groupAlgebraAction_smul,
        (mem_groupAlgebraInvariants_iff rho x).mp x.property σ])
  have heq : (AlgHom.liftEquiv k L _ _ f).toLinearMap =
      f.toLinearMap.liftBaseChange L := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    simp
  rw [← heq] at h
  exact h

/-- The invariant group algebra descends the split coordinate algebra along a finite Galois
extension: extending its scalars recovers the original group algebra. -/
noncomputable def groupAlgebraInvariantsBaseChangeEquiv
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    L ⊗[k] groupAlgebraInvariants rho ≃ₐ[L] MonoidAlgebra L (Multiplicative M) :=
  AlgEquiv.ofBijective
    (AlgHom.liftEquiv k L (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) (groupAlgebraInvariants rho).val)
    ⟨liftEquiv_groupAlgebraInvariants_injective rho,
      liftEquiv_groupAlgebraInvariants_surjective rho⟩

/-- The descent equivalence is scalar multiplication on pure tensors. -/
@[simp]
theorem groupAlgebraInvariantsBaseChangeEquiv_tmul
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (a : L) (x : groupAlgebraInvariants rho) :
    groupAlgebraInvariantsBaseChangeEquiv rho (a ⊗ₜ[k] x) =
      a • (x : MonoidAlgebra L (Multiplicative M)) := by
  exact (AlgEquiv.ofBijective_apply _ _ _).trans (AlgHom.liftEquiv_tmul _ a x)

/-- The inverse descent equivalence sends an invariant element to its tensor with one. -/
@[simp]
theorem groupAlgebraInvariantsBaseChangeEquiv_symm_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsBaseChangeEquiv rho).symm
      (x : MonoidAlgebra L (Multiplicative M)) = 1 ⊗ₜ[k] x := by
  apply (groupAlgebraInvariantsBaseChangeEquiv rho).injective
  simp

end TauCeti.GaloisDescent
