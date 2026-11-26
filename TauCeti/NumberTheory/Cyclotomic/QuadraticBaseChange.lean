/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import TauCeti.FieldTheory.IntermediateField.Quadratic
import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# Cyclotomic irreducibility over a quadratic extension

A cyclotomic polynomial irreducible over the base field stays irreducible after adjoining a
square root exactly when the square root does not already lie in the cyclotomic extension.
Comparing degrees in the two towers through the compositum detects this even when their degrees
are not coprime.
-/

public section

open IntermediateField Polynomial

/-- Let `ζ` be a primitive `n`-th root and `x` a square root of a nonsquare in `K`.
If `Φₙ` is irreducible over `K`, it stays irreducible over `K(x)` exactly when `x ∉ K(ζ)`. -/
theorem IsPrimitiveRoot.irreducible_cyclotomic_adjoin_sq_iff_notMem {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (cyclotomic n K)) {a : K} {x : L}
    (hx : x ^ 2 = algebraMap K L a) (ha : ¬ IsSquare a) :
    Irreducible (cyclotomic n K⟮x⟯) ↔ x ∉ K⟮ζ⟯ := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hirr
  let : NeZero n := ⟨hn⟩
  let := hζ.intermediateField_adjoin_isCyclotomicExtension K
  let := hζ.intermediateField_adjoin_isCyclotomicExtension K⟮x⟯
  have hquad : Module.finrank K K⟮x⟯ = 2 :=
    TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare hx ha
  have hcyclo : Module.finrank K K⟮ζ⟯ = n.totient :=
    IsCyclotomicExtension.finrank _ hirr
  have htower : Module.finrank K (K⟮x⟯ ⊔ K⟮ζ⟯ : IntermediateField K L) =
      2 * Module.finrank K⟮x⟯ K⟮x⟯⟮ζ⟯ := by
    calc
      _ = Module.finrank K ((K⟮x⟯⟮ζ⟯).restrictScalars K) := by
        rw [restrictScalars_adjoin_eq_sup]
      -- Restriction of scalars leaves the carrier and the inherited `K`-action unchanged.
      _ = Module.finrank K K⟮x⟯⟮ζ⟯ := rfl
      _ = _ := by rw [← Module.finrank_mul_finrank K K⟮x⟯, hquad]
  rw [IsCyclotomicExtension.irreducible_cyclotomic_iff_finrank_eq_totient K⟮x⟯ K⟮x⟯⟮ζ⟯]
  constructor
  · intro hdegree hmem
    have hle : K⟮x⟯ ≤ K⟮ζ⟯ := adjoin_simple_le_iff.mpr hmem
    rw [sup_eq_right.mpr hle, hcyclo, hdegree] at htower
    have hpos := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
    omega
  · intro hmem
    have hsq : x ^ 2 ∈ K⟮ζ⟯ := hx ▸ IntermediateField.algebraMap_mem _ _
    have hdegree := K⟮ζ⟯.finrank_sup_adjoin_simple_eq_mul_two hsq hmem
    rw [sup_comm, htower, hcyclo] at hdegree
    omega
