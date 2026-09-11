/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Invariants
import TauCeti.RepresentationTheory.GaloisDescent.Span

/-!
# Scalar extension of an invariant group algebra

The natural map from `L ⊗[k] (L[M])^Gal(L/k)` to `L[M]` is surjective when the
automorphism group of `L/k` is finite. Here the action twists both the coefficients and the
exponents, with the latter specified by an integral representation on the abelian group `M`.
The scalar-extension map is Mathlib's `AlgHom.liftEquiv` applied to the invariant-subalgebra
inclusion; it sends `a ⊗ x` to `a • x`.

This supplies the surjectivity part of the coordinate descent for groups of multiplicative
type, including non-split tori. Identifying the scalar extension with the split coordinate
algebra additionally requires injectivity; transporting the Hopf structure requires the analogous
identification on tensor squares.

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
theorem groupAlgebraInvariantsBaseChange_surjective
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

end TauCeti.GaloisDescent
