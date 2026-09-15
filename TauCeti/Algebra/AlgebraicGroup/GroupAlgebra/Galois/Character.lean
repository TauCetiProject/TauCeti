/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Splitting
public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarAut
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Characters of a descended group algebra

For a finite Galois extension `L/k` and an integral representation `rho` on an abelian
group `M`, let `B` be the invariant algebra of `L[M]` under the simultaneous action on
coefficients and exponents. The characters over `L` of the affine group with coordinate
algebra `B` recover `M`, including its prescribed Galois action.

The characters are realized as the group-like elements of `L ⊗[k] B`. The canonical
splitting sends each such element to a unique monomial `X^m`; the resulting equivalence
intertwines the scalar-factor action with `rho`. In particular this comparison applies
to the character lattices of tori obtained by Galois descent, without needing finite
generation or torsion-freeness for the comparison itself.

The construction composes `GroupLike.mapEquiv` for the Hopf splitting with
`MonoidAlgebra.groupLikeEquiv` for the split group algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
variable [FiniteDimensional k L] [IsGalois k L]
variable (rho : Representation ℤ (L ≃ₐ[k] L) M)

/-- The characters over the splitting field of the descended group recover its exponent group.
The character indexed by `m` is the inverse image of `X^m` under the Hopf splitting. -/
noncomputable def groupAlgebraInvariantsCharacterEquiv :
    GroupLike L (L ⊗[k] groupAlgebraInvariants rho) ≃* Multiplicative M :=
  (TauCeti.GroupLike.mapEquiv (groupAlgebraInvariantsBaseChangeBialgEquiv rho)).trans
    (TauCeti.MonoidAlgebra.groupLikeEquiv (R := L))

/-- A character corresponds to `m` precisely when the splitting sends it to `X^m`. -/
@[simp]
theorem groupAlgebraInvariantsCharacterEquiv_apply_eq_iff
    (x : GroupLike L (L ⊗[k] groupAlgebraInvariants rho)) (m : Multiplicative M) :
    groupAlgebraInvariantsCharacterEquiv rho x = m ↔
      groupAlgebraInvariantsBaseChangeBialgEquiv rho x.val = MonoidAlgebra.single m 1 := by
  simp only [groupAlgebraInvariantsCharacterEquiv, MulEquiv.trans_apply,
    TauCeti.MonoidAlgebra.groupLikeEquiv_apply_eq_iff, TauCeti.GroupLike.val_mapEquiv]

/-- The value of the character indexed by `m` is the inverse splitting of its monomial. -/
@[simp]
theorem groupAlgebraInvariantsCharacterEquiv_symm_apply_val (m : Multiplicative M) :
    ((groupAlgebraInvariantsCharacterEquiv rho).symm m).val =
      (groupAlgebraInvariantsBaseChangeBialgEquiv rho).symm (MonoidAlgebra.single m 1) := by
  apply EquivLike.injective (groupAlgebraInvariantsBaseChangeBialgEquiv rho)
  rw [BialgEquiv.apply_symm_apply]
  exact (groupAlgebraInvariantsCharacterEquiv_apply_eq_iff rho _ m).mp
    ((groupAlgebraInvariantsCharacterEquiv rho).apply_symm_apply m)

/-- Recovering an exponent from a character intertwines the scalar-factor Galois action
with the original action on exponents. -/
@[simp]
theorem groupAlgebraInvariantsCharacterEquiv_smul (sigma : L ≃ₐ[k] L)
    (x : GroupLike L (L ⊗[k] groupAlgebraInvariants rho)) :
    groupAlgebraInvariantsCharacterEquiv rho (sigma • x) =
      Multiplicative.ofAdd (rho sigma (groupAlgebraInvariantsCharacterEquiv rho x).toAdd) := by
  rw [groupAlgebraInvariantsCharacterEquiv_apply_eq_iff, ScalarAut.val_smul,
    groupAlgebraInvariantsBaseChangeBialgEquiv_smul]
  have hx := (groupAlgebraInvariantsCharacterEquiv_apply_eq_iff rho x _).mp rfl
  rw [hx, groupAlgebraAction_single, map_one]

/-- Galois conjugation of the character indexed by `m` gives the character indexed by
`rho sigma m`. -/
@[simp]
theorem smul_groupAlgebraInvariantsCharacterEquiv_symm_apply (sigma : L ≃ₐ[k] L)
    (m : Multiplicative M) :
    sigma • (groupAlgebraInvariantsCharacterEquiv rho).symm m =
      (groupAlgebraInvariantsCharacterEquiv rho).symm
        (Multiplicative.ofAdd (rho sigma m.toAdd)) := by
  apply (groupAlgebraInvariantsCharacterEquiv rho).injective
  simp

end TauCeti.GaloisDescent
