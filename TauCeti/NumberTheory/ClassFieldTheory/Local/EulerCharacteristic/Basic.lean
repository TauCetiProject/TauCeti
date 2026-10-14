/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Units
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex

/-!
# The local Euler characteristic

For a finite smooth discrete Galois representation `A` over a nonarchimedean local field, this
file defines the three-term local Euler characteristic

```text
χ_F(A) = |H⁰(F, A)| |H²(F, A)| / |H¹(F, A)|.
```

Over a finite compatible extension `F` of `ℚ_p` (`TauCeti.FinitePadicExtension`) it also defines
the normalized absolute value of the order of `A`,

```text
φ_F(A) = ‖#A‖_F = |#A|_p ^ [F : ℚ_p] = p ^ (-[F : ℚ_p] v_p(#A)),
```

so that Tate's local Euler characteristic formula reads `χ_F = φ_F`.

## Main results

* `TauCeti.ClassFieldTheory.localEulerCharacteristic`: the positive-rational-valued local Euler
  characteristic of a finite smooth discrete Galois representation.
* `TauCeti.ClassFieldTheory.localEulerCharacteristic_congr`: invariance under isomorphism.
* `TauCeti.ClassFieldTheory.localCardNorm`: the normalized absolute value `φ_F(A)` of the order.
* `TauCeti.ClassFieldTheory.localCardNorm_congr`: invariance under isomorphism.
* `TauCeti.ClassFieldTheory.localCardNorm_mul_of_exact`: multiplicativity in short exact sequences.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {n : ℕ}

section EulerCharacteristic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
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

end EulerCharacteristic

section CardNorm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [FinitePadicExtension F p]

/-- **The normalized absolute value of the order** of a finite Galois representation over a
finite compatible extension `F` of `ℚ_p`, as a positive rational number:
`φ_F(A) = ‖#A‖_F = |#A|_p ^ [F : ℚ_p] = p ^ (-[F : ℚ_p] v_p(#A))`, the right-hand side of Tate's
local Euler characteristic formula `χ_F(A) = φ_F(A)`. -/
def localCardNorm (A : GalRep n F) [Finite A.V] : Units.posSubgroup ℚ :=
  have hq : 0 < padicNorm p (Nat.card A.V) ^ Module.finrank ℚ_[p] F :=
    pow_pos ((padicNorm.nonneg _).lt_of_ne
      (padicNorm.nonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')).symm) _
  ⟨Units.mk0 _ hq.ne', hq⟩

/-- The value of `localCardNorm` in `ℚ`. -/
@[simp]
theorem localCardNorm_coe (A : GalRep n F) [Finite A.V] :
    ((localCardNorm p A).1 : ℚ) = padicNorm p (Nat.card A.V) ^ Module.finrank ℚ_[p] F := by
  rfl

/-- **Isomorphism invariance of `localCardNorm`.** Isomorphic representations have the same
order, hence the same normalized absolute value of the order. -/
theorem localCardNorm_congr {A B : GalRep n F} [Finite A.V] (e : A ≅ B) :
    haveI : Finite B.V := .of_surjective e.hom.hom fun y ↦ ⟨e.inv.hom y, by simp⟩
    localCardNorm p A = localCardNorm p B := by
  apply Subtype.ext
  apply Units.ext
  simp only [localCardNorm_coe,
    Nat.card_congr ((CategoryTheory.forget (GalRep n F)).mapIso e).toEquiv]

/-- **Multiplicativity of `localCardNorm`.** If `0 → A → B → C → 0` is an exact sequence of
representations with `B` finite, then `φ_F(B) = φ_F(A) φ_F(C)`: the order of `B` is the product
of the orders of `A` and `C`, and the `p`-adic norm is multiplicative. -/
theorem localCardNorm_mul_of_exact {A B C : GalRep n F} [Finite B.V]
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    haveI : Finite A.V := .of_injective _ hf
    haveI : Finite C.V := .of_surjective _ hg
    localCardNorm p B = localCardNorm p A * localCardNorm p C := by
  have : Finite A.V := .of_injective _ hf
  have : Finite C.V := .of_surjective _ hg
  have hcard : Nat.card B.V = Nat.card A.V * Nat.card C.V := by
    have hker : g.hom.toAddMonoidHom.ker = f.hom.toAddMonoidHom.range := by
      ext b
      exact (hfg b).trans Iff.rfl
    rw [← AddSubgroup.card_ker_mul_card_range g.hom.toAddMonoidHom, hker,
      (AddMonoidHom.range_eq_top (f := g.hom.toAddMonoidHom)).2 hg, AddSubgroup.card_top,
      mul_left_inj' Nat.card_pos.ne']
    exact (Nat.card_congr (Equiv.ofInjective _ hf)).symm
  apply Subtype.ext
  apply Units.ext
  simp only [localCardNorm_coe, Subgroup.coe_mul, Units.val_mul, hcard, Nat.cast_mul,
    padicNorm.mul, mul_pow]

end CardNorm

end TauCeti.ClassFieldTheory
