/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Units
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo

/-!
# The local Euler characteristic

For a finite smooth discrete Galois representation `A` over a nonarchimedean local field, this
file defines the three-term local Euler characteristic

```text
χ_F(A) = |H⁰(F, A)| |H²(F, A)| / |H¹(F, A)|.
```

## Main results

* `TauCeti.ClassFieldTheory.localEulerCharacteristic`: the positive-rational-valued local Euler
  characteristic of a finite smooth discrete Galois representation.
* `TauCeti.ClassFieldTheory.localEulerCharacteristic_congr`: invariance under isomorphism.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {n : ℕ} {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **The three-term local Euler characteristic** of a finite smooth discrete Galois
representation, as a positive rational number:
`χ_F(A) = |H⁰(F, A)| |H²(F, A)| / |H¹(F, A)|`. -/
def localEulerCharacteristic (hn : (n : F) ≠ 0) (A : GalRep n F)
    [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    Units.posSubgroup ℚ := by
  have h₀ : Finite (continuousCohomology 0 A) :=
    finite_H (F := F) (n := n) hn A Fact.out (i := 0) (by omega)
  have h₁ : Finite (continuousCohomology 1 A) :=
    finite_H (F := F) (n := n) hn A Fact.out (i := 1) (by omega)
  have h₂ : Finite (continuousCohomology 2 A) :=
    finite_H (F := F) (n := n) hn A Fact.out (i := 2) (by omega)
  let q : ℚ :=
    (Nat.card (continuousCohomology 0 A) : ℚ) * Nat.card (continuousCohomology 2 A) /
      Nat.card (continuousCohomology 1 A)
  have hq : 0 < q := div_pos
    (mul_pos
      (by exact_mod_cast @Nat.card_pos (continuousCohomology 0 A) inferInstance h₀)
      (by exact_mod_cast @Nat.card_pos (continuousCohomology 2 A) inferInstance h₂))
    (by exact_mod_cast @Nat.card_pos (continuousCohomology 1 A) inferInstance h₁)
  exact ⟨Units.mk0 q hq.ne', hq⟩

/-- The value of `localEulerCharacteristic` in `ℚ`. -/
@[simp]
theorem localEulerCharacteristic_coe (hn : (n : F) ≠ 0) (A : GalRep n F)
    [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    ((localEulerCharacteristic hn A).1 : ℚ) =
      (Nat.card (continuousCohomology 0 A) : ℚ) * Nat.card (continuousCohomology 2 A) /
        Nat.card (continuousCohomology 1 A) := by
  rfl

/-- **Isomorphism invariance of the local Euler characteristic.** Isomorphic representations have
the same local Euler characteristic; finiteness and smoothness of `B` follow from those of `A`
along the isomorphism. -/
theorem localEulerCharacteristic_congr (hn : (n : F) ≠ 0) {A B : GalRep n F}
    [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] (e : A ≅ B) :
    haveI : Finite B.V := .of_surjective e.hom.hom fun y ↦ ⟨e.inv.hom y, by simp⟩
    haveI : Fact (IsSmoothDiscrete (ZMod n) B) :=
      ⟨.of_injective e.inv (fun x y h ↦ by simpa using congr(e.hom.hom $h)) Fact.out⟩
    localEulerCharacteristic hn A = localEulerCharacteristic hn B := by
  have hcard (i : ℕ) : Nat.card (continuousCohomology i A) = Nat.card (continuousCohomology i B) :=
    Nat.card_congr ((ContinuousCohomology.continuousCohomologyFunctor (ZMod n) _ i).mapIso
      e).toContinuousLinearEquiv.toEquiv
  apply Subtype.ext
  apply Units.ext
  simp only [localEulerCharacteristic_coe, hcard]

end TauCeti.ClassFieldTheory
