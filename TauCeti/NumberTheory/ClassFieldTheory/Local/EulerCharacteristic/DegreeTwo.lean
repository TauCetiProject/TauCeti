/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.FiniteQuotient
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Cardinality
public import TauCeti.RepresentationTheory.Dual

import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo

/-!
# `H²` of an inflated representation by duality

Let `F` be a nonarchimedean local field, `V` an open normal subgroup of `G_F` with finite quotient
`G = G_F ⧸ V`, and `ℓ` a prime invertible in `F`. Suppose that `V` acts trivially on `μ_ℓ`, so that
`μ_ℓ` is the inflation of a representation `M` of `G`. For a finite-dimensional representation
`A` of `G` over `𝔽_ℓ`, inflated to `G_F` by `fdGalRepOfQuotient`, this file computes `H²(F, A)`
in terms of the representation theory of the finite group `G`:

```text
#H²(F, A) = #H⁰(F, Hom(A, μ_ℓ)) = #Hom_{G_F}(A, μ_ℓ) = #Hom_G(A, M),
dim H²(F, A) = dim Hom_G(A, M) = dim Hom_G(M, A) = dim (M^∨ ⊗ A)^G  (ℓ ∤ #G).
```

The first line is local Tate duality in degrees `(0, 2)` and the invariants of the Tate dual
(`natCard_continuousCohomology_two_eq_natCard_hom`), followed by the full faithfulness of
inflation. In the second line, `ℓ ∤ #G` makes `𝔽_ℓ[G]` semisimple, and the intertwiners in the
two directions are then equally many (`FDRep.finrank_hom_comm`); the intertwiners
`M → A` are the invariants of `M^∨ ⊗ A` (`FDRep.finrank_invariants_dual_tprod`).

Such an `M` exists as soon as `V` acts trivially on `μ_ℓ`
(`exists_fdGalRepOfQuotient_iso_muNRep`). In the dévissage proving Tate's local Euler
characteristic formula, once the modular Artin theorem has reduced to `ℓ ∤ #G` and `μ_ℓ` has been
adjoined to the fixed field of `V`, this expresses `dim H²` through the invariants of a tensor
product with `μ_ℓ^{-1}`, the form in which `dim H¹` is also computed.

## Main results

* `TauCeti.ClassFieldTheory.natCard_continuousCohomology_two_fdGalRepOfQuotient`:
  `#H²(F, A) = #Hom_G(A, M)`, for every `n` invertible in `F`.
* `TauCeti.ClassFieldTheory.finrank_continuousCohomology_two_fdGalRepOfQuotient`:
  `dim H²(F, A) = dim (M^∨ ⊗ A)^G` for a prime `ℓ` not dividing `#G`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory Module

variable {n : ℕ} {F : Type} [Field F] {V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)}

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **`#H²(F, A) = #Hom_G(A, μₙ)` for an inflated representation.** Let `n` be invertible in `F`
and `M` a representation of `G = G_F ⧸ V` inflating to `μₙ`. For every finite-dimensional
representation `A` of `G`, the order of `H²(F, A)` is the number of intertwiners `A → M`: local
duality in degrees `(0, 2)` (`natCard_continuousCohomology_two_eq_natCard_hom`) counts the
`G_F`-equivariant maps `A → μₙ`, and inflation, being fully faithful, identifies them with the
intertwiners `A → M`. -/
theorem natCard_continuousCohomology_two_fdGalRepOfQuotient (hn : IsUnit (n : F))
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F)
    (A : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    Nat.card (continuousCohomology 2 ((fdGalRepOfQuotient n F V).obj A)) = Nat.card (A ⟶ M) := by
  have : NeZero n := NeZero.of_neZero_natCast F (h := ⟨hn.ne_zero⟩)
  let forgetA := (forget₂ (FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))
    (Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))).obj A
  have : Finite forgetA.V := Module.finite_of_finite (ZMod n) (M := A)
  rw [fdGalRepOfQuotient_obj, natCard_continuousCohomology_two_eq_natCard_hom hn,
    ← Nat.card_congr (FDRep.forget₂HomLinearEquiv A M).toEquiv,
    Nat.card_congr ((Functor.FullyFaithful.ofFullyFaithful (galRepOfQuotient n F V)).homEquiv)]
  exact Nat.card_congr
    ((Iso.refl _).homCongr (eqToIso (fdGalRepOfQuotient_obj n F V M).symm ≪≫ e).symm)

/-- **`dim H²(F, A) = dim (μ_ℓ^{-1} ⊗ A)^G` for an inflated representation.** Let `ℓ` be a
prime invertible in `F`, `V` an open normal subgroup of `G_F` of index prime to `ℓ`, and `M` a
representation of `G = G_F ⧸ V` inflating to `μ_ℓ`. For every finite-dimensional representation
`A` of `G` over `𝔽_ℓ`, `dim H²(F, A) = dim Hom_G(A, M)`
(`natCard_continuousCohomology_two_fdGalRepOfQuotient`), which is `dim Hom_G(M, A)` because
`ℓ ∤ #G` (`FDRep.finrank_hom_comm`), that is `dim (M^∨ ⊗ A)^G`
(`FDRep.finrank_invariants_dual_tprod`). -/
theorem finrank_continuousCohomology_two_fdGalRepOfQuotient {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : F)) (hV : V.toSubgroup.index.Coprime ℓ)
    {M : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient ℓ F V).obj M ≅ muNRep ℓ F)
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    finrank (ZMod ℓ) (continuousCohomology 2 ((fdGalRepOfQuotient ℓ F V).obj A)) =
      finrank (ZMod ℓ) (Representation.invariants
        (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) M) A)
        (Representation.tprod (Representation.dual M.ρ) A.ρ)) := by
  have hℓp : ℓ.Prime := Fact.out
  have : V.toSubgroup.FiniteIndex :=
    ⟨fun h => hℓp.one_lt.ne' (Nat.coprime_zero_left ℓ |>.1 (h ▸ hV))⟩
  have : Invertible (Nat.card (Field.absoluteGaloisGroup F ⧸ V.toSubgroup) : ZMod ℓ) :=
    invertibleOfNonzero <| by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hℓp).1 hV.symm
  have : Module.Finite (ZMod ℓ) (A ⟶ M) :=
    Module.Finite.equiv (Representation.linHom.invariantsEquivFDRepHom A M)
  have : Finite (A ⟶ M) := Module.finite_of_finite (ZMod ℓ)
  have : Finite (continuousCohomology 2 ((fdGalRepOfQuotient ℓ F V).obj A)) :=
    finite_H hℓ.ne_zero _ Fact.out le_rfl
  rw [FDRep.finrank_invariants_dual_tprod M A, ← FDRep.finrank_hom_comm A M]
  apply Nat.pow_right_injective hℓp.two_le
  dsimp only
  rw [FiniteField.pow_finrank_eq_natCard, FiniteField.pow_finrank_eq_natCard,
    natCard_continuousCohomology_two_fdGalRepOfQuotient hℓ e A]

end TauCeti.ClassFieldTheory
