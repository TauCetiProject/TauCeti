/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Perfect

import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo

/-!
# The order of `H²` by local duality

Let `F` be a nonarchimedean local field, `n` invertible in `F`, and `A` a finite smooth discrete
`ZMod n`-representation of `G_F`, with Tate dual `A' = Hom(A, μₙ)`. The `(0, 2)` case of local
Tate duality (`TauCeti.ClassFieldTheory.tateDualityPairing_perfect`) identifies `H⁰(F, A')` with
the `ZMod n`-dual of `H²(F, A)`, and a finite group killed by `n` has as many characters with
values in `ZMod n` as elements. So `#H²(F, A) = #H⁰(F, A')`.

The invariants of `A'` are the `G_F`-equivariant homomorphisms `A → μₙ`
(`TauCeti.ClassFieldTheory.tateDualInvariantsEquivHom`), so `H⁰(F, A') = Hom_{G_F}(A, μₙ)`, and
`#H²(F, A) = #Hom_{G_F}(A, μₙ)`. This is how the Euler characteristic computes `H²` from
equivariant homomorphisms into the roots of unity.

## Main results

* `TauCeti.ClassFieldTheory.natCard_continuousCohomology_two_eq_zero_tateDual`:
  `#H²(F, A) = #H⁰(F, Hom(A, μₙ))`.
* `TauCeti.ClassFieldTheory.natCard_continuousCohomology_zero_tateDual`:
  `#H⁰(F, Hom(A, μₙ)) = #Hom_{G_F}(A, μₙ)`, for every discrete `A` and every field `F`.
* `TauCeti.ClassFieldTheory.natCard_continuousCohomology_two_eq_natCard_hom`:
  `#H²(F, A) = #Hom_{G_F}(A, μₙ)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory

universe u

variable {n : ℕ}

section DegreeZero

variable {F : Type u} [Field F]

/-- **`#H⁰(F, Hom(A, μₙ)) = #Hom_{G_F}(A, μₙ)`** for a discrete Galois module `A`: Mathlib's
`ContinuousCohomology.zeroIso` identifies `H⁰` with the invariants, and those are the equivariant
homomorphisms (`tateDualInvariantsEquivHom`). -/
theorem natCard_continuousCohomology_zero_tateDual (A : GalRep n F) [DiscreteTopology A.V] :
    Nat.card (_root_.continuousCohomology.{0, u, u} 0 (tateDual A)) =
      Nat.card (A ⟶ muNRep n F) :=
  Nat.card_congr <|
    (ContinuousCohomology.zeroIso (tateDual A)).toContinuousLinearEquiv.toEquiv.trans
      (tateDualInvariantsEquivHom A).toEquiv

end DegreeZero

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **The order of `H²` by duality**: for `n` invertible in the local field `F` and `A` finite
smooth discrete, `#H²(F, A) = #H⁰(F, Hom(A, μₙ))`. The `(0, 2)` case of
`tateDualityPairing_perfect` identifies `H⁰(F, Hom(A, μₙ))` with the characters
`H²(F, A) → ZMod n`, which are as many as the elements of the finite group `H²(F, A)`, killed by
`n` (`natCard_addMonoidHom_zmod`). -/
theorem natCard_continuousCohomology_two_eq_zero_tateDual (hn : IsUnit (n : F)) (A : GalRep n F)
    [DiscreteTopology A.V] [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    Nat.card (continuousCohomology 2 A) = Nat.card (continuousCohomology 0 (tateDual A)) := by
  have : NeZero n := NeZero.of_neZero_natCast F (h := ⟨hn.ne_zero⟩)
  have : Finite (continuousCohomology 2 A) := finite_H hn.ne_zero A Fact.out le_rfl
  let tr := h2MuEquivZMod F hn
  -- The pairing `H⁰(F, A') × H²(F, A) → ZMod n`, curried.
  let Φ : continuousCohomology 0 (tateDual A) →+ continuousCohomology 2 A →+ ZMod n :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (tateDualityPairing A tr 0 2 rfl x)
      (tateDualityPairing_add_right A tr 0 2 rfl x)) fun x x' =>
        AddMonoidHom.ext (tateDualityPairing_add_left A tr 0 2 rfl x x')
  obtain ⟨hsep, hrep⟩ := tateDualityPairing_perfect hn A tr 0 2 rfl
  have hΦ : Function.Bijective Φ := by
    refine ⟨(injective_iff_map_eq_zero Φ).2 fun x hx => hsep x fun y => ?_, fun ψ => ?_⟩
    · exact DFunLike.congr_fun hx y
    · obtain ⟨x, hx⟩ := hrep ψ
      exact ⟨x, AddMonoidHom.ext hx⟩
  rw [Nat.card_congr (Equiv.ofBijective Φ hΦ),
    natCard_addMonoidHom_zmod fun y => ZModModule.char_nsmul_eq_zero n y]

/-- **`#H²(F, A) = #Hom_{G_F}(A, μₙ)`** for `n` invertible in the local field `F` and `A` finite
smooth discrete: duality in degrees `(0, 2)` (`natCard_continuousCohomology_two_eq_zero_tateDual`)
and the invariants of the Tate dual (`natCard_continuousCohomology_zero_tateDual`). -/
theorem natCard_continuousCohomology_two_eq_natCard_hom (hn : IsUnit (n : F)) (A : GalRep n F)
    [DiscreteTopology A.V] [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    Nat.card (continuousCohomology 2 A) = Nat.card (A ⟶ muNRep n F) := by
  rw [natCard_continuousCohomology_two_eq_zero_tateDual hn A,
    natCard_continuousCohomology_zero_tateDual A]

end TauCeti.ClassFieldTheory
