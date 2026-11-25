/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Degree

/-!
# An irreducible projective representation of `C₂ × C₂`

Checks for Schur's theorem on projective representations
(`TauCeti.IsProjectiveRep.finrank_dvd_card`).

Let `Q = C₂ × C₂`, written `Multiplicative (ZMod 2 × ZMod 2)`, with generators `a = (1, 0)` and
`b = (0, 1)`. On `k²` let `a` act by `A = diag(1, -1)` and `b` by the coordinate swap `B`, and
`(i, j)` by `A^i B^j`. Since `B A = -A B`, this is a projective representation with factor set
`α((i, j), (i', j')) = (-1)^(j i')`, which takes the value `-1` at `(b, a)`
(`TauCeti.Examples.KleinFour.isProjectiveRep_ρ`). In characteristic zero the only
subspaces stable under `A` and `B` are `0` and `k²`: a nonzero stable subspace contains a nonzero
multiple of a coordinate vector, and `B` gives the other one
(`TauCeti.Examples.KleinFour.eq_bot_or_eq_top`). So its dimension `2` divides `|Q| = 4`, as
Schur's theorem says, although every irreducible ordinary representation of the abelian group
`C₂ × C₂` over an algebraically closed field is one-dimensional.

Irreducibility is needed: three copies of the trivial representation of `C₂`, a projective
representation with the trivial factor set, have dimension `3`, which does not divide `|C₂| = 2`.
-/

public section

namespace TauCeti.Examples.KleinFour

open Matrix Module

/-- The group `C₂ × C₂`. -/
abbrev Q : Type := Multiplicative (ZMod 2 × ZMod 2)

/-- The generator `a = (1, 0)`. -/
abbrev a : Q := Multiplicative.ofAdd (1, 0)

/-- The generator `b = (0, 1)`. -/
abbrev b : Q := Multiplicative.ofAdd (0, 1)

/-- The sign `(-1)^(j i')` of the factor set, as a unit of `ℤ`. -/
def sign (g h : Q) : ℤˣ :=
  if (Multiplicative.toAdd g).2 = 1 ∧ (Multiplicative.toAdd h).1 = 1 then -1 else 1

/-- `sign` is a factor set: the cocycle identity and normalization are checked on all elements. -/
theorem sign_cocycle (g h j : Q) : sign (g * h) j * sign g h = sign h j * sign g (h * j) := by
  revert g h j
  decide

/-- `A = diag(1, -1)` over `ℤ`. -/
def Az : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- The coordinate swap `B` over `ℤ`. -/
def Bz : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The integer matrix `A^i B^j` of `(i, j)`. -/
def Mz (g : Q) : Matrix (Fin 2) (Fin 2) ℤ :=
  (if (Multiplicative.toAdd g).1 = 1 then Az else 1) *
    (if (Multiplicative.toAdd g).2 = 1 then Bz else 1)

/-- `A^i B^j A^{i'} B^{j'} = (-1)^(j i') A^{i + i'} B^{j + j'}`, checked on all elements. -/
theorem Mz_mul (g h : Q) : Mz g * Mz h = ((sign g h : ℤˣ) : ℤ) • Mz (g * h) := by
  revert g h
  decide +kernel

/-- `M g` is invertible, with inverse `(-1)^(j i) M g`. -/
theorem Mz_mul_smul_self (g : Q) : Mz g * (((sign g g : ℤˣ) : ℤ) • Mz g) = 1 := by
  revert g
  decide +kernel

/-- `M 1 = 1`. -/
theorem Mz_one : Mz 1 = 1 := by
  decide +kernel

variable (k : Type*) [Field k]

/-- The factor set `α((i, j), (i', j')) = (-1)^(j i')` with values in `kˣ`. -/
def α (g h : Q) : kˣ := Units.map (Int.castRingHom k).toMonoidHom (sign g h)

/-- The values of `α` are the integer signs. -/
theorem coe_α (g h : Q) : (α k g h : k) = ((sign g h : ℤˣ) : ℤ) := by
  simp [α]

instance isFactorSet_α : IsFactorSet (α k) where
  cocycle g h j := by
    simp only [α, ← map_mul, sign_cocycle]
  one_left g := by
    simp only [α]
    rw [show sign 1 g = 1 by revert g; decide, map_one]

/-- The matrix `A^i B^j` of `(i, j)` over `k`. -/
def M (g : Q) : Matrix (Fin 2) (Fin 2) k := (Int.castRingHom k).mapMatrix (Mz g)

/-- `A^i B^j A^{i'} B^{j'} = (-1)^(j i') A^{i + i'} B^{j + j'}`. -/
theorem M_mul (g h : Q) : M k g * M k h = (α k g h : k) • M k (g * h) := by
  rw [M, M, ← map_mul, Mz_mul, map_zsmul, coe_α, ← Int.cast_smul_eq_zsmul k, M]

/-- `M g * ((-1)^(j i) M g) = 1`. -/
theorem M_mul_smul_self (g : Q) : M k g * ((α k g g : k) • M k g) = 1 := by
  rw [M, coe_α, Int.cast_smul_eq_zsmul, ← map_zsmul, ← map_mul, Mz_mul_smul_self, map_one]

/-- The operator `A^i B^j` of `(i, j)` on `k²`. -/
noncomputable def ρ (g : Q) : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) :=
  LinearEquiv.ofLinearMap (toLin' (M k g)) (toLin' ((α k g g : k) • M k g))
    (by rw [← toLin'_mul, M_mul_smul_self, toLin'_one])
    (by rw [← toLin'_mul, Matrix.smul_mul, ← Matrix.mul_smul, M_mul_smul_self, toLin'_one])

/-- `ρ g` acts by the matrix `M g`. -/
theorem ρ_apply (g : Q) (x : Fin 2 → k) : ρ k g x = M k g *ᵥ x := by
  rw [ρ]
  rfl

/-- **`ρ` is a projective representation of `C₂ × C₂` with factor set `α`.** -/
theorem isProjectiveRep_ρ : IsProjectiveRep (ρ k) (α k) where
  isFactorSet := inferInstance
  map_one := by
    ext x : 1
    simp [ρ_apply, M, Mz_one]
  mul_apply g h x := by
    rw [ρ_apply, ρ_apply, ρ_apply, mulVec_mulVec, M_mul, smul_mulVec]

/-- The factor set takes the value `-1` at `(b, a)`: `B A = -A B`. -/
theorem α_b_a : (α k b a : k) = -1 := by
  rw [coe_α, show sign b a = -1 by decide]
  simp

variable {k} [CharZero k]

/-- **Irreducibility.** In characteristic zero, the only subspaces of `k²` stable under every
`ρ g` are `0` and `k²`. A nonzero stable `W` contains `v` and `A v`, hence `2 v₀ e₀` and
`2 v₁ e₁`, so a coordinate vector, and `B` swaps the coordinate vectors. -/
theorem eq_bot_or_eq_top (W : Submodule k (Fin 2 → k)) (hW : ∀ g, ∀ w ∈ W, ρ k g w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  refine or_iff_not_imp_left.2 fun hne => ?_
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hA : ∀ w ∈ W, ![w 0, -w 1] ∈ W := fun w hw => by
    convert hW a w hw using 1
    ext i
    fin_cases i <;> simp [ρ_apply, M, Mz, Az, mulVec, dotProduct, Fin.sum_univ_two]
  have hB : ∀ w ∈ W, ![w 1, w 0] ∈ W := fun w hw => by
    convert hW b w hw using 1
    ext i
    fin_cases i <;> simp [ρ_apply, M, Mz, Bz, mulVec, dotProduct, Fin.sum_univ_two]
  -- `e₀ ∈ W` or `e₁ ∈ W`, and then both are.
  have he : Pi.single 0 1 ∈ W ∧ Pi.single 1 1 ∈ W := by
    have hsum := W.add_mem hv (hA v hv)
    have hdiff := W.sub_mem hv (hA v hv)
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv0 (funext fun i => by fin_cases i <;> simp [h0, h1])
      have he1 : Pi.single 1 1 ∈ W := by
        convert W.smul_mem (2 * v 1)⁻¹ hdiff using 1
        ext i
        fin_cases i
        · simp [h0, Matrix.vecHead]
        · simp only [Fin.mk_one, Pi.single_eq_same, Pi.smul_apply, Pi.sub_apply,
            Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul, sub_neg_eq_add]
          field_simp
          ring
      refine ⟨?_, he1⟩
      convert hB _ he1 using 1
      ext i
      fin_cases i <;> simp
    · have he0 : Pi.single 0 1 ∈ W := by
        convert W.smul_mem (2 * v 0)⁻¹ hsum using 1
        ext i
        fin_cases i
        · simp only [Fin.zero_eta, Pi.single_eq_same, Pi.smul_apply, Pi.add_apply,
            Matrix.cons_val_zero, smul_eq_mul]
          field_simp
          ring
        · simp [Matrix.vecHead, Matrix.vecTail]
      refine ⟨he0, ?_⟩
      convert hB _ he0 using 1
      ext i
      fin_cases i <;> simp
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [hx]
  exact W.add_mem (W.smul_mem _ he.1) (W.smul_mem _ he.2)

/-- **Check of Schur's theorem.** Over an algebraically closed field of characteristic zero, the
dimension `2` of the irreducible projective representation `ρ` of `C₂ × C₂` divides `|Q| = 4`. -/
theorem finrank_dvd_card [IsAlgClosed k] : finrank k (Fin 2 → k) ∣ Nat.card Q :=
  (isProjectiveRep_ρ k).finrank_dvd_card eq_bot_or_eq_top

omit [CharZero k] in
/-- `ρ` has dimension `2` and `|Q| = 4`. -/
theorem finrank_eq_and_card_eq : finrank k (Fin 2 → k) = 2 ∧ Nat.card Q = 4 := by
  refine ⟨by simp, ?_⟩
  rw [Nat.card_eq_fintype_card]
  rfl

omit [CharZero k] in
/-- **Check: irreducibility is needed.** Three copies of the trivial representation of `C₂`
form a projective representation with the trivial factor set, of dimension `3`, which does not
divide `|C₂| = 2`. -/
theorem trivial_three_not_dvd :
    IsProjectiveRep (fun _ : Multiplicative (ZMod 2) => LinearEquiv.refl k (Fin 3 → k)) 1 ∧
      ¬ finrank k (Fin 3 → k) ∣ Nat.card (Multiplicative (ZMod 2)) := by
  refine ⟨⟨⟨fun _ _ _ => rfl, fun _ => rfl⟩, rfl, fun _ _ _ => by simp⟩, ?_⟩
  rw [Module.finrank_fin_fun, Nat.card_eq_fintype_card]
  decide

end TauCeti.Examples.KleinFour
