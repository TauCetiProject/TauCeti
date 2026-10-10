/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.DegreeTwo
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Formula
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.Tensor

/-!
# The local Euler characteristic of an inflated representation

Let `F` be a field, `V` an open normal subgroup of `G_F` with finite quotient `G = G_F ⧸ V`, and
`A` a finite-dimensional representation of `G`, inflated to `G_F` by `fdGalRepOfQuotient`. This
file computes the cohomology of the inflation in degrees zero and one in terms of the
representation theory of `G`:

```text
dim H⁰(F, A) = dim A^G,
dim H¹(F, A) = dim (H¹(V, 𝔽_ℓ) ⊗ A)^G        (ℓ prime, ℓ ∤ #G),
```

where `G` acts on `H¹(V, 𝔽_ℓ)` by conjugation (`h1ConjRepresentation`). The first is the
identification of `H⁰` with the invariants (`ContinuousCohomology.zeroIso`); the second is the
prime-to-`ℓ` descent of `H¹` to `V` followed by the tensor comparison
`H¹(V, 𝔽_ℓ) ⊗ A ≅ H¹(V, A)` (`finrank_H1_eq_finrank_representationInvariants`).

Over a finite extension `F` of `ℚ_p`, together with the computation of `H²` by local duality
(`finrank_continuousCohomology_two_fdGalRepOfQuotient`), this turns Tate's local Euler
characteristic formula `χ_F(A) = φ_F(A)` for the inflation of `A` into an identity between
invariant dimensions of representations of the finite group `G`: if `M` is a representation of `G`
inflating to `μ_ℓ`, then `χ_F(A) = φ_F(A)` holds exactly when

```text
dim (H¹(V, 𝔽_ℓ) ⊗ A)^G = dim A^G + dim (M^∨ ⊗ A)^G + [F : ℚ_p] v_p(#A)
```

(`localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_iff`). The left side is then
computed by equivariant Kummer theory (`kummerH1ConjRepresentationEquiv`), which identifies
`H¹(V, 𝔽_ℓ)` with `M^∨ ⊗ Lˣ ⧸ (Lˣ)^ℓ` for the fixed field `L` of `V`.

## Main results

* `TauCeti.ClassFieldTheory.finrank_continuousCohomology_zero_fdGalRepOfQuotient`:
  `dim H⁰(F, A) = dim A^G`.
* `TauCeti.ClassFieldTheory.finrank_continuousCohomology_one_fdGalRepOfQuotient`:
  `dim H¹(F, A) = dim (H¹(V, 𝔽_ℓ) ⊗ A)^G` for a prime `ℓ` not dividing `#G`.
* `TauCeti.ClassFieldTheory.localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_iff`:
  `χ_F(A) = φ_F(A)` for the inflation of `A` as an identity of invariant dimensions.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology Module

attribute [local instance] TopRep.distribMulAction trivialZModAction continuousSMulTrivialZMod

-- Instance diamond: over `ZMod ℓ` with `Fact ℓ.Prime`, instance search first derives
-- `AddCommGroup (ZMod ℓ)` from Mathlib's `[IsSimpleAddGroup G] [AddGroup.IsNilpotent G]`
-- instance. That structure is equal to the ring path but not reducibly so, and the trivial action
-- `trivialZModAction` on `ZMod ℓ`, through which `H¹(V, ZMod ℓ)` is formed, is stated along the
-- ring path. Raising the priority of the ring path locally restores the instances on
-- `H¹(V, ZMod ℓ)`. The statements below are elaborated with it, so importers applying them do not
-- need this attribute.
attribute [local instance 2000] Ring.toAddCommGroup

variable {F : Type} [Field F] {V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)}

/-- **`dim H⁰(F, A) = dim A^G` for an inflated representation.** The invariants of the inflation
of a representation `A` of `G = G_F ⧸ V` under `G_F` are its invariants under `G`. -/
theorem finrank_continuousCohomology_zero_fdGalRepOfQuotient {n : ℕ}
    (A : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    finrank (ZMod n) (continuousCohomology 0 ((fdGalRepOfQuotient n F V).obj A)) =
      finrank (ZMod n) (Representation.invariants A.ρ) := by
  rw [fdGalRepOfQuotient_obj, ← FDRep.forget₂_ρ A]
  set B := (forget₂ (FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))
    (Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))).obj A
  rw [(ContinuousCohomology.zeroIso ((galRepOfQuotient n F V).obj B)).toContinuousLinearEquiv
    |>.toLinearEquiv.finrank_eq]
  refine (LinearEquiv.ofEq _ (B.ρ.invariants : Submodule (ZMod n) B.V) ?_).finrank_eq
  ext x
  refine ⟨fun h q ↦ ?_, fun h g ↦ (galRepOfQuotient_ρ_apply n F V B g x).trans (h _)⟩
  induction q using QuotientGroup.induction_on with
  | H g => exact (galRepOfQuotient_ρ_apply n F V B g x).symm.trans (h g)

/-- **`dim H¹(F, A) = dim (H¹(V, 𝔽_ℓ) ⊗ A)^G` for an inflated representation.** Let `ℓ` be a
prime not dividing the index of `V`. For every finite-dimensional representation `A` of
`G = G_F ⧸ V` over `𝔽_ℓ`, restriction identifies `H¹(F, A)` with the `G`-invariants of
`H¹(V, A) ≅ H¹(V, 𝔽_ℓ) ⊗ A`, where `G` acts on `H¹(V, 𝔽_ℓ)` by conjugation. -/
theorem finrank_continuousCohomology_one_fdGalRepOfQuotient {ℓ : ℕ} [Fact ℓ.Prime]
    (hV : V.toSubgroup.index.Coprime ℓ)
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    finrank (ZMod ℓ) (continuousCohomology 1 ((fdGalRepOfQuotient ℓ F V).obj A)) =
      finrank (ZMod ℓ) (Representation.invariants
        ((h1ConjRepresentation (p := ℓ) (G := Field.absoluteGaloisGroup F)
          (N := V.toSubgroup)).tprod A.ρ)) := by
  have : V.toSubgroup.FiniteIndex :=
    ⟨fun h ↦ (Fact.out : ℓ.Prime).one_lt.ne' (Nat.coprime_zero_left ℓ |>.1 (h ▸ hV))⟩
  rw [fdGalRepOfQuotient_obj, ← FDRep.forget₂_ρ A]
  set B := (forget₂ (FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))
    (Rep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))).obj A
  set X := (galRepOfQuotient ℓ F V).obj B
  have : ContinuousSMul (Field.absoluteGaloisGroup F) X.V :=
    (isSmoothDiscrete_galRepOfQuotient ℓ F V B).continuousSMul
  have : Finite B := Module.finite_of_finite (ZMod ℓ) (M := A)
  rw [← (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.toLinearEquiv
    (ZMod.map_smul _)).finrank_eq]
  -- The comparison's `[Module.Finite (ZMod p) A]` binder is elaborated after `[Fact p.Prime]`,
  -- along the field structure of `ZMod p`, which instance search does not identify with the
  -- module structure of `X.V`; the argument is therefore supplied by unification.
  exact @finrank_H1_eq_finrank_representationInvariants ℓ _ _ _ _ _ _ X.V _ _ _ _ _ _ _
    (fun g a ↦ galRepOfQuotient_ρ_eq_self ℓ F V B g.2 a) _ Module.Finite.of_finite _ V.isOpen hV
    B.ρ (fun g a ↦ ((TopRep.distribMulAction_smul X g a).trans
      (galRepOfQuotient_ρ_apply ℓ F V B g a)).symm)

variable (p : ℕ) [Fact p.Prime] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- **Tate's local Euler characteristic formula for an inflated representation, as an identity
of invariant dimensions.** Let `F/ℚ_p` be finite, `ℓ` a prime not dividing the index of `V`, and
`M` a representation of `G = G_F ⧸ V` inflating to `μ_ℓ`. For every finite-dimensional
representation `A` of `G` over `𝔽_ℓ`, the formula `χ_F(A) = φ_F(A)` for the inflation of `A` holds
exactly when `dim (H¹(V, 𝔽_ℓ) ⊗ A)^G = dim A^G + dim (M^∨ ⊗ A)^G + [F : ℚ_p] v_p(#A)`. -/
theorem localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_iff {ℓ : ℕ} [Fact ℓ.Prime]
    (hV : V.toSubgroup.index.Coprime ℓ)
    {M : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient ℓ F V).obj M ≅ muNRep ℓ F)
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ))
        ((fdGalRepOfQuotient ℓ F V).obj A) = localCardNorm p ((fdGalRepOfQuotient ℓ F V).obj A) ↔
      finrank (ZMod ℓ) (Representation.invariants
          ((h1ConjRepresentation (p := ℓ) (G := Field.absoluteGaloisGroup F)
            (N := V.toSubgroup)).tprod A.ρ)) =
        finrank (ZMod ℓ) (Representation.invariants A.ρ) +
          finrank (ZMod ℓ) (Representation.invariants
            (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) M) A)
            ((Representation.dual M.ρ).tprod A.ρ)) +
            finrank ℚ_[p] F * padicValNat p (Nat.card A) := by
  have hcard : Nat.card ((fdGalRepOfQuotient ℓ F V).obj A).V = Nat.card A := by
    rw [fdGalRepOfQuotient_obj, galRepOfQuotient_obj_V]
    -- `forget₂ (FDRep _ _) (Rep _ _)` keeps the carrier of `A`.
    rfl
  rw [localEulerCharacteristic_eq_localCardNorm_iff_finrank, hcard,
    finrank_continuousCohomology_zero_fdGalRepOfQuotient,
    finrank_continuousCohomology_one_fdGalRepOfQuotient hV,
    finrank_continuousCohomology_two_fdGalRepOfQuotient (Nat.cast_ne_zero.2 (NeZero.ne ℓ)).isUnit
      hV e]

end TauCeti.ClassFieldTheory
