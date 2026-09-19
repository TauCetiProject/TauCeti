/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Character
import TauCeti.Algebra.Bialgebra.GroupLike.ScalarTower

/-!
# Geometric characters of a descended group algebra

The characters of a group algebra descended along a finite Galois extension `L/k`
recover its exponent group over every `L`-algebra `K` with connected prime spectrum. Compatible
scalar automorphisms of `K` and `L` act on those characters by the prescribed action
on exponents. In particular, taking `K` to be an algebraic closure recovers the
absolute-Galois module of geometric characters, not just the characters over `L`.

No finite generation or torsion-freeness assumption on the exponent group is needed.
The comparison uses `groupAlgebraInvariantsCharacterEquiv` over `L` and the
scalar-tower equivalence for characters.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L K M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
  [FiniteDimensional k L] [IsGalois k L]
  [CommRing K] [ConnectedSpace (PrimeSpectrum K)] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
  (ρ : Representation ℤ (L ≃ₐ[k] L) M)

private theorem splitting_groupLike_span_eq_top :
    Submodule.span L (Set.range (_root_.GroupLike.val
      (R := L) (A := L ⊗[k] groupAlgebraInvariants ρ))) = ⊤ := by
  rw [← Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  exact GroupLike.groupLikeSetSpan_eq_top_of_surjective
    (groupAlgebraInvariantsBaseChangeBialgEquiv ρ).symm.toBialgHom
    (groupAlgebraInvariantsBaseChangeBialgEquiv ρ).symm.surjective
    (TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top L _)

/-- Characters of a descended group algebra over any algebra over the splitting field
with connected prime spectrum are its original exponent group. -/
noncomputable def groupAlgebraInvariantsGeometricCharacterEquiv :
    GroupLike K (K ⊗[k] groupAlgebraInvariants ρ) ≃* Multiplicative M :=
  (groupLikeScalarTowerEquiv (K := K) (splitting_groupLike_span_eq_top ρ)).symm.trans
    (groupAlgebraInvariantsCharacterEquiv ρ)

/-- The inverse character comparison is the coefficient extension of the character
with the same exponent over the splitting field. -/
@[simp]
theorem groupAlgebraInvariantsGeometricCharacterEquiv_symm_apply_val (m : Multiplicative M) :
    ((groupAlgebraInvariantsGeometricCharacterEquiv (K := K) ρ).symm m).val =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L K)
        (AlgHom.id k (groupAlgebraInvariants ρ))
        ((groupAlgebraInvariantsBaseChangeBialgEquiv ρ).symm
          (MonoidAlgebra.single m 1)) := by
  simp only [groupAlgebraInvariantsGeometricCharacterEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, val_groupLikeScalarTowerEquiv,
    groupAlgebraInvariantsCharacterEquiv_symm_apply_val]

/-- A geometric character has exponent `m` exactly when it is the extension of the
splitting-field character indexed by `m`. -/
@[simp]
theorem groupAlgebraInvariantsGeometricCharacterEquiv_apply_eq_iff
    (x : GroupLike K (K ⊗[k] groupAlgebraInvariants ρ)) (m : Multiplicative M) :
    groupAlgebraInvariantsGeometricCharacterEquiv (K := K) ρ x = m ↔
      x.val = Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L K)
        (AlgHom.id k (groupAlgebraInvariants ρ))
        ((groupAlgebraInvariantsBaseChangeBialgEquiv ρ).symm
          (MonoidAlgebra.single m 1)) := by
  rw [← groupAlgebraInvariantsGeometricCharacterEquiv_symm_apply_val]
  exact (groupAlgebraInvariantsGeometricCharacterEquiv (K := K) ρ).toEquiv.eq_symm_apply.symm.trans
    _root_.GroupLike.val_injective.eq_iff.symm

/-- The character comparison intertwines compatible scalar automorphisms with the
given action on exponents. -/
theorem groupAlgebraInvariantsGeometricCharacterEquiv_smul
    (σ : K ≃ₐ[k] K) (τ : L ≃ₐ[k] L)
    (hστ : ∀ a, σ (algebraMap L K a) = algebraMap L K (τ a))
    (x : GroupLike K (K ⊗[k] groupAlgebraInvariants ρ)) :
    groupAlgebraInvariantsGeometricCharacterEquiv (K := K) ρ (σ • x) =
      Multiplicative.ofAdd
        (ρ τ (groupAlgebraInvariantsGeometricCharacterEquiv (K := K) ρ x).toAdd) := by
  obtain ⟨y, rfl⟩ :=
    (groupLikeScalarTowerEquiv (K := K) (splitting_groupLike_span_eq_top ρ)).surjective x
  rw [← groupLikeScalarTowerEquiv_smul _ σ τ hστ]
  simp only [groupAlgebraInvariantsGeometricCharacterEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, groupAlgebraInvariantsCharacterEquiv_smul]

end TauCeti.GaloisDescent
