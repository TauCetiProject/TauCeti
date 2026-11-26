/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Glued
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Weights
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Weights

/-!
# Explicit shortest dual-lattice representatives of ADE glue labels and glue words

`TauCeti.DynkinType.glueAlphabetIsometry` identifies `t.glueAlphabet ht` of a valid simply-laced
Dynkin type `t` with the discriminant quadratic module of `t.rootLattice ht`, while
`TauCeti.DynkinType.isLeast_glueMinimum` shows existentially that every coset attains its shortest
norm `t.glueMinimum ht a`.

This file defines a canonical **computable** rational vector `t.glueRepresentativeVector ht a` in
simple-root coordinates `Fin t.rank → ℚ` for every glue label `a : t.glueAlphabet ht` (and
`t.glueLabelVector d` for digits `d : ℕ`): `typeACosetRepresentative n a.val` on `Aₙ`; `0`,
`typeDSpinorWeight n`, `typeDVectorWeight n`, `typeDCospinorWeight n` on `Dₙ`; `0`,
`±typeE₆MinusculeWeight` on `E₆`; `0`, `typeE₇MinusculeWeight` on `E₇`; and `0` on `E₈`. Bundled
in `(t.rootLattice ht).dualCarrier` as `t.glueRepresentative hv ht a`, it represents
`t.glueAlphabetIsometry hv ht a`, attains `t.glueMinimum ht a`, separates distinct labels modulo
the root lattice, and realizes the quadratic half-norm, polar pairing, and additive order of
`t.glueAlphabet`. Componentwise, `glueWordRepresentativeVector` gives choice-free generators and
coset-membership criteria for `TauCeti.DynkinType.gluedLattice`.

## Main declarations

* `TauCeti.DynkinType.glueLabelVector`, `TauCeti.DynkinType.glueRepresentativeVector`,
  `TauCeti.DynkinType.glueRepresentative`: computable simple-root coordinates and bundled
  dual-carrier representatives of glue digits and labels, with `mk_glueRepresentative`,
  `form_glueRepresentativeVector_self`, `glueRepresentativeVector_injective`, and
  `glueRepresentativeVector_sub_mem_carrier_iff`.
* `TauCeti.DynkinType.glueLabelVector_D_one_apply`, `TauCeti.DynkinType.glueLabelVector_E6_one`,
  `TauCeti.DynkinType.glueLabelVector_E6_two`, `TauCeti.DynkinType.glueLabelVector_E7_one`, and
  the other `Dₙ` coordinate formulas for the printed label vectors.
* `TauCeti.DynkinType.pairing_glueAlphabet_eq_form_glueRepresentative` and
  `TauCeti.DynkinType.zsmul_eq_zero_iff_zsmul_glueRepresentativeVector_mem_carrier`: bilinear
  pairings and torsion conditions in `glueAlphabet` read off `glueRepresentativeVector`.
* `TauCeti.DynkinType.glueWordRepresentativeVector`, `TauCeti.DynkinType.glueWordRepresentative`,
  `TauCeti.DynkinType.gluedLattice_carrier_eq_sup_span_glueWordRepresentativeVector`,
  `TauCeti.DynkinType.glueWordRepresentativeVector_mem_gluedLattice_carrier_iff`, and
  `TauCeti.DynkinType.mem_gluedLattice_carrier_iff_exists_int`: componentwise glue-word
  representatives and explicit generator and membership formulas for `gluedLattice`.
* `TauCeti.DynkinType.zsmul_glueWordRepresentativeVector_mem_carrier_iff`,
  `TauCeti.DynkinType.gluedLatticeIsometryOfEq_glueWordRepresentativeVector`, and
  `TauCeti.DynkinType.mem_gluedLattice_carrier_iff_exists_nsmul`: torsion, naturality under
  reindexing, and the cyclic coset decomposition of glued lattices.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I, IV, V, VI.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3, 6--8 and Chapter 16 §1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

-- Private zero-vector and equal-lattice transport helpers.

private theorem form_eq_zero_of_eq_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : IntegralLattice V) {x : V} (hx : x = 0) : L.form x x = 0 := by
  rw [hx, map_zero]

private theorem mk_eq_zero_of_val_eq_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    {L : IntegralLattice V} (u : L.dualCarrier) (hu : (u : V) = 0) :
    (Submodule.Quotient.mk u : L.DiscriminantGroup) = 0 :=
  (L.discriminantGroup_mk_eq_zero_iff u).mpr (hu.symm ▸ L.carrier.zero_mem)

private theorem mem_dualCarrier_of_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    {L₁ L₂ : IntegralLattice V} (h : L₁ = L₂) {x : V} (hx : x ∈ L₂.dualCarrier) :
    x ∈ L₁.dualCarrier :=
  h ▸ hx

private theorem form_of_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    {L₁ L₂ : IntegralLattice V} (h : L₁ = L₂) (x y : V) : L₁.form x y = L₂.form x y :=
  h ▸ rfl

/-! ## Computable representatives of Conway--Sloane glue digits -/

/-- **Computable dual-lattice vector of a glue digit** `d` of `t` in Bourbaki simple-root
coordinates `Fin t.rank → ℚ`.  When `t` is valid and simply laced and `d < t.glueLabelCount`, this
is the canonical shortest representative of the discriminant coset named by digit `d`
(`mk_glueLabelVector`, `form_glueLabelVector_self`).  Digits `d ≥ t.glueLabelCount` evaluate to `0`,
except on `Aₙ` where `typeACosetRepresentative n d` gives a dual-carrier representative of `d • ω₁`
for all `d : ℕ` (guaranteed shortest for `d ≤ n + 1`). -/
def glueLabelVector : (t : DynkinType) → ℕ → Fin t.rank → ℚ
  | A n, d => typeACosetRepresentative n d
  | D n, d =>
    if d = 1 then typeDSpinorWeight n
    else if d = 2 then typeDVectorWeight n
    else if d = 3 then typeDCospinorWeight n else 0
  | E6, d =>
    if d = 1 then typeE₆MinusculeWeight else if d = 2 then -typeE₆MinusculeWeight else 0
  | E7, d => if d = 1 then typeE₇MinusculeWeight else 0
  | _, _ => 0

/-- On `Aₙ`, `glueLabelVector` is `typeACosetRepresentative n d`. -/
@[simp] theorem glueLabelVector_A (n d : ℕ) :
    (A n).glueLabelVector d = typeACosetRepresentative n d := (rfl)

/-- On `Dₙ`, digits `1, 2, 3` map to spinor, vector, and cospinor weights, and others to `0`. -/
@[simp] theorem glueLabelVector_D (n d : ℕ) :
    (D n).glueLabelVector d =
      if d = 1 then typeDSpinorWeight n
      else if d = 2 then typeDVectorWeight n
      else if d = 3 then typeDCospinorWeight n else 0 := (rfl)

/-- On `E₆`, digits `1, 2` map to `ϖ₁` and `-ϖ₁`, and other digits to `0`. -/
@[simp] theorem glueLabelVector_E6 (d : ℕ) :
    E6.glueLabelVector d =
      if d = 1 then typeE₆MinusculeWeight else if d = 2 then -typeE₆MinusculeWeight else 0 := (rfl)

/-- On `E₇`, digit `1` maps to `ϖ₇`, and other digits to `0`. -/
@[simp] theorem glueLabelVector_E7 (d : ℕ) :
    E7.glueLabelVector d = if d = 1 then typeE₇MinusculeWeight else 0 := (rfl)

/-- On `E₈`, `glueLabelVector` is identically `0`. -/
@[simp] theorem glueLabelVector_E8 (d : ℕ) : E8.glueLabelVector d = 0 := (rfl)

/-- Digit `0` maps to the zero vector for every Dynkin type. -/
@[simp] theorem glueLabelVector_zero (t : DynkinType) : t.glueLabelVector 0 = 0 := by
  cases t with
  | A n => exact typeACosetRepresentative_zero n
  | D _ | E6 | E7 | E8 | B _ | C _ | F4 | G2 => rfl

/-- `rootLatticeIsometryOfEq` preserves `glueLabelVector`. -/
@[simp] theorem rootLatticeIsometryOfEq_glueLabelVector {t s : DynkinType} (h : t = s)
    (ht : t.IsSimplyLaced) (hs : s.IsSimplyLaced) (d : ℕ) :
    t.rootLatticeIsometryOfEq ht h hs (t.glueLabelVector d) = s.glueLabelVector d := by
  subst h; rw [rootLatticeIsometryOfEq_rfl, Isometry.refl_apply]

/-- The `j`-th simple-root coordinate of the spinor label `1` of `Dₙ`. -/
@[simp] theorem glueLabelVector_D_one_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 1 j =
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then ((n : ℚ) - 2) / 4 else (n : ℚ) / 4 := by
  have := j.isLt
  simp only [glueLabelVector_D, ↓reduceIte, typeDSpinorWeight_apply]
  split_ifs <;> first | omega | push_cast; ring

/-- The `j`-th simple-root coordinate of the vector label `2` of `Dₙ`. -/
@[simp] theorem glueLabelVector_D_two_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 2 j =
      if j.val + 2 = n then -(1 / 2) else if j.val + 1 = n then 1 / 2 else 0 := by
  have := j.isLt
  simp only [glueLabelVector_D, OfNat.ofNat_ne_one, ↓reduceIte, typeDVectorWeight_apply]
  split_ifs <;> first | omega | rfl

/-- The `j`-th simple-root coordinate of the cospinor label `3` of `Dₙ`. -/
@[simp] theorem glueLabelVector_D_three_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 3 j =
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then (n : ℚ) / 4 else ((n : ℚ) - 2) / 4 := by
  have := j.isLt
  simp only [glueLabelVector_D, OfNat.ofNat_ne_one, ↓reduceIte, typeDCospinorWeight_apply,
    Nat.reduceEqDiff]
  split_ifs <;> first | omega | push_cast; ring

/-- Label `1` of `E₆` is the minuscule weight `ϖ₁`. -/
theorem glueLabelVector_E6_one : E6.glueLabelVector 1 = typeE₆MinusculeWeight := (rfl)

/-- Label `2` of `E₆` is `-ϖ₁`. -/
theorem glueLabelVector_E6_two : E6.glueLabelVector 2 = -typeE₆MinusculeWeight := (rfl)

/-- Label `1` of `E₇` is the minuscule weight `ϖ₇`. -/
theorem glueLabelVector_E7_one : E7.glueLabelVector 1 = typeE₇MinusculeWeight := (rfl)

/-- Out-of-range labels `4 ≤ a` of `Dₙ` evaluate to `0`. -/
theorem glueLabelVector_D_of_ge (n : ℕ) {a : ℕ} (ha : 4 ≤ a) :
    (D n).glueLabelVector a = 0 := by
  match a with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl

/-- Out-of-range labels `3 ≤ a` of `E₆` evaluate to `0`. -/
theorem glueLabelVector_E6_of_ge {a : ℕ} (ha : 3 ≤ a) : E6.glueLabelVector a = 0 := by
  match a with | 0 | 1 | 2 => omega | _ + 3 => rfl

/-- Out-of-range labels `2 ≤ a` of `E₇` evaluate to `0`. -/
theorem glueLabelVector_E7_of_ge {a : ℕ} (ha : 2 ≤ a) : E7.glueLabelVector a = 0 := by
  match a with | 0 | 1 => omega | _ + 2 => rfl

/-- Every label of `Cₙ` evaluates to `0`. -/
@[simp] theorem glueLabelVector_C (n a : ℕ) : (C n).glueLabelVector a = 0 := (rfl)

/-- Every label of `F₄` evaluates to `0`. -/
@[simp] theorem glueLabelVector_F4 (a : ℕ) : F4.glueLabelVector a = 0 := (rfl)

/-- In type `Dₙ`, the cospinor representative is the spinor representative minus the vector
representative at every rank. -/
theorem glueLabelVector_D_three_eq_sub (n : ℕ) :
    (D n).glueLabelVector 3 = (D n).glueLabelVector 1 - (D n).glueLabelVector 2 := by
  funext j
  rw [Pi.sub_apply]
  dsimp only [rank] at j
  have hj : j.val < n := j.isLt
  rw [glueLabelVector_D_three_apply, glueLabelVector_D_one_apply, glueLabelVector_D_two_apply]
  split_ifs <;> first | omega | ring

/-- Every `glueLabelVector` of a valid simply-laced Dynkin type lies in the dual carrier of its
root lattice. -/
theorem glueLabelVector_mem_dualCarrier (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (d : ℕ) : t.glueLabelVector d ∈ (t.rootLattice ht).dualCarrier := by
  cases t with
  | A n =>
    exact mem_dualCarrier_of_eq (rootLattice_A n ht) (typeACosetRepresentative_mem_dualCarrier n d)
  | D n =>
    have hn := valid_D.mp hv
    rcases eq_or_ne d 1 with rfl | h1; · exact typeDSpinorWeight_mem_dualCarrier hn ht
    rcases eq_or_ne d 2 with rfl | h2; · exact typeDVectorWeight_mem_dualCarrier hn ht
    rcases eq_or_ne d 3 with rfl | h3; · exact typeDCospinorWeight_mem_dualCarrier hn ht
    have h0 : (D n).glueLabelVector d = 0 := funext fun (j : Fin n) ↦ by
      simp only [glueLabelVector_D, h1, h2, h3, ↓reduceIte]; rfl
    exact h0 ▸ ((D n).rootLattice ht).dualCarrier.zero_mem
  | E6 =>
    rcases eq_or_ne d 1 with rfl | h1
    · exact mem_dualCarrier_of_eq (rootLattice_E6 ht) typeE₆MinusculeWeight_mem_dualCarrier
    rcases eq_or_ne d 2 with rfl | h2
    · exact mem_dualCarrier_of_eq (rootLattice_E6 ht)
        (typeE₆RootLattice.dualCarrier.neg_mem typeE₆MinusculeWeight_mem_dualCarrier)
    have h0 : E6.glueLabelVector d = 0 := funext fun (j : Fin 6) ↦ by
      simp only [glueLabelVector_E6, h1, h2, ↓reduceIte]; rfl
    exact h0 ▸ (E6.rootLattice ht).dualCarrier.zero_mem
  | E7 =>
    rcases eq_or_ne d 1 with rfl | h1
    · exact mem_dualCarrier_of_eq (rootLattice_E7 ht) typeE₇MinusculeWeight_mem_dualCarrier
    have h0 : E7.glueLabelVector d = 0 := funext fun (j : Fin 7) ↦ by
      simp only [glueLabelVector_E7, h1, ↓reduceIte]; rfl
    exact h0 ▸ (E7.rootLattice ht).dualCarrier.zero_mem
  | E8 => exact (E8.rootLattice ht).dualCarrier.zero_mem
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

private theorem mk_glueLabelVector_A (n : ℕ) (hv : (A n).Valid) (ht : (A n).IsSimplyLaced)
    (d : Fin (A n).glueLabelCount) :
    (Submodule.Quotient.mk ⟨(A n).glueLabelVector d.val,
        (A n).glueLabelVector_mem_dualCarrier hv ht d.val⟩ :
        ((A n).rootLattice ht).DiscriminantGroup) =
      (A n).glueAlphabetIsometry hv ht ((A n).glueLabelEquiv ht d) := by
  have hd : ((d.val : ZMod (n + 1)).val) = d.val := ZMod.val_natCast_of_lt d.isLt
  rw [glueLabelEquiv_A, glueAlphabetIsometry_A_apply,
    ← mk_typeACosetRepresentativeDual_val (d.val : ZMod (n + 1))]
  exact ((Isometry.ofEq (rootLattice_A n ht).symm).discriminantGroupEquiv_mk_eq_mk_of_apply_eq <|
    (Isometry.ofEq_apply _ _).trans <|
      (coe_typeACosetRepresentativeDual n _).trans <|
        (congrArg (typeACosetRepresentative n) hd).trans
          (glueLabelVector_A n d.val).symm).symm

-- Explicit identifications of the bundled type-D glue-label representatives.

private theorem glueLabelVectorDual_D_one (n : ℕ) (hv : (D n).Valid) (ht : (D n).IsSimplyLaced) :
    (⟨(D n).glueLabelVector 1, (D n).glueLabelVector_mem_dualCarrier hv ht 1⟩ :
        ((D n).rootLattice ht).dualCarrier) =
      typeDSpinorWeightDual n (valid_D.mp hv) ht := by
  apply Subtype.ext
  rw [Submodule.coe_mk, coe_typeDSpinorWeightDual, glueLabelVector_D, ite_eq_left rfl]

private theorem glueLabelVectorDual_D_two (n : ℕ) (hv : (D n).Valid) (ht : (D n).IsSimplyLaced) :
    (⟨(D n).glueLabelVector 2, (D n).glueLabelVector_mem_dualCarrier hv ht 2⟩ :
        ((D n).rootLattice ht).dualCarrier) =
      typeDVectorWeightDual n (valid_D.mp hv) ht := by
  apply Subtype.ext
  rw [Submodule.coe_mk, coe_typeDVectorWeightDual, glueLabelVector_D,
    ite_eq_right (by omega), ite_eq_left rfl]

private theorem glueLabelVectorDual_D_three (n : ℕ) (hv : (D n).Valid)
    (ht : (D n).IsSimplyLaced) :
    (⟨(D n).glueLabelVector 3, (D n).glueLabelVector_mem_dualCarrier hv ht 3⟩ :
        ((D n).rootLattice ht).dualCarrier) =
      typeDCospinorWeightDual n (valid_D.mp hv) ht := by
  apply Subtype.ext
  rw [Submodule.coe_mk, coe_typeDCospinorWeightDual, glueLabelVector_D,
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

private theorem mk_glueLabelVector_D (n : ℕ) (hv : (D n).Valid) (ht : (D n).IsSimplyLaced)
    (d : Fin (D n).glueLabelCount) :
    (Submodule.Quotient.mk ⟨(D n).glueLabelVector d.val,
        (D n).glueLabelVector_mem_dualCarrier hv ht d.val⟩ :
        ((D n).rootLattice ht).DiscriminantGroup) =
      (D n).glueAlphabetIsometry hv ht ((D n).glueLabelEquiv ht d) := by
  have hn : 4 ≤ n := valid_D.mp hv
  have : NeZero n := ⟨by omega⟩
  rcases d with ⟨d, hd⟩; simp only [glueLabelCount] at hd; interval_cases d
  · have h0 : (D n).glueLabelEquiv ht ⟨0, hd⟩ = 0 :=
      ((D n).glueLabelEquiv ht).symm.injective
        ((Equiv.symm_apply_apply _ _).trans ((D n).glueLabelEquiv_symm_zero ht).symm)
    rw [h0, map_zero]; exact mk_eq_zero_of_val_eq_zero _ (glueLabelVector_zero (D n))
  · rw [glueLabelVectorDual_D_one n hv ht, mk_typeDSpinorWeightDual]
    rcases Nat.even_or_odd n with hpar | hpar
    · rw [glueAlphabetIsometry_D_apply_of_even n hv ht hpar, glueLabelEquiv_D_of_even n ht hpar]
      simp only [Nat.reduceDiv, Nat.cast_zero, Nat.reduceMod, Nat.cast_one,
        zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one]
    · rw [glueAlphabetIsometry_D_apply_of_odd n hv ht hpar, glueLabelEquiv_D_of_odd n ht hpar,
        Nat.cast_one, zmodFourAddEquivCheckerboardDiscriminantGroup_apply_one n hpar]
  · rw [glueLabelVectorDual_D_two n hv ht, mk_typeDVectorWeightDual]
    rcases Nat.even_or_odd n with hpar | hpar
    · rw [glueAlphabetIsometry_D_apply_of_even n hv ht hpar, glueLabelEquiv_D_of_even n ht hpar]
      simp only [Nat.div_self zero_lt_two, Nat.cast_one, Nat.mod_self, Nat.cast_zero,
        zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_zero]
    · rw [glueAlphabetIsometry_D_apply_of_odd n hv ht hpar, glueLabelEquiv_D_of_odd n ht hpar,
        Nat.cast_ofNat, zmodFourAddEquivCheckerboardDiscriminantGroup_apply_two n hpar]
  · rw [glueLabelVectorDual_D_three n hv ht, mk_typeDCospinorWeightDual]
    rcases Nat.even_or_odd n with hpar | hpar
    · rw [glueAlphabetIsometry_D_apply_of_even n hv ht hpar, glueLabelEquiv_D_of_even n ht hpar]
      simp only [Nat.reduceDiv, Nat.cast_one, Nat.reduceMod,
        zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one]
    · rw [glueAlphabetIsometry_D_apply_of_odd n hv ht hpar, glueLabelEquiv_D_of_odd n ht hpar,
        Nat.cast_ofNat, zmodFourAddEquivCheckerboardDiscriminantGroup_apply_three n hpar]

private theorem mk_glueLabelVector_E6 (hv : E6.Valid) (ht : E6.IsSimplyLaced)
    (d : Fin E6.glueLabelCount) :
    (Submodule.Quotient.mk ⟨E6.glueLabelVector d.val,
        E6.glueLabelVector_mem_dualCarrier hv ht d.val⟩ :
        (E6.rootLattice ht).DiscriminantGroup) =
      E6.glueAlphabetIsometry hv ht (E6.glueLabelEquiv ht d) := by
  rcases d with ⟨d, hd⟩; simp only [glueLabelCount] at hd
  rw [glueLabelEquiv_E6, glueAlphabetIsometry_E6_apply]
  interval_cases d
  · refine (mk_eq_zero_of_val_eq_zero _ (glueLabelVector_zero E6)).trans ?_
    rw [Nat.cast_zero, map_zero, map_zero]
    -- The two zero classes agree across `Fin E6.rank` and `Fin 6`.
    rfl
  · rw [Nat.cast_one, typeE₆DiscriminantGroupEquiv_apply_one, ← mk_typeE₆MinusculeWeightDual]
    exact ((Isometry.ofEq (rootLattice_E6 ht).symm).discriminantGroupEquiv_mk_eq_mk_of_apply_eq <|
      (Isometry.ofEq_apply _ _).trans coe_typeE₆MinusculeWeightDual).symm
  · have h2 : ((2 : ℕ) : ZMod 3) = -1 :=
      eq_neg_of_add_eq_zero_left
        (by rw [← Nat.cast_one, ← Nat.cast_add]; exact ZMod.natCast_self 3)
    have hmk2 : (Submodule.Quotient.mk (-typeE₆MinusculeWeightDual) :
          typeE₆RootLattice.DiscriminantGroup) =
        typeE₆DiscriminantGroupEquiv ((2 : ℕ) : ZMod 3) := by
      rw [Submodule.Quotient.mk_neg, mk_typeE₆MinusculeWeightDual, h2, map_neg,
        typeE₆DiscriminantGroupEquiv_apply_one]
    rw [← hmk2]
    exact ((Isometry.ofEq (rootLattice_E6 ht).symm).discriminantGroupEquiv_mk_eq_mk_of_apply_eq <|
      (Isometry.ofEq_apply _ _).trans
        ((Submodule.coe_neg _ typeE₆MinusculeWeightDual).trans
          (congrArg Neg.neg coe_typeE₆MinusculeWeightDual))).symm

private theorem mk_glueLabelVector_E7 (hv : E7.Valid) (ht : E7.IsSimplyLaced)
    (d : Fin E7.glueLabelCount) :
    (Submodule.Quotient.mk ⟨E7.glueLabelVector d.val,
        E7.glueLabelVector_mem_dualCarrier hv ht d.val⟩ :
        (E7.rootLattice ht).DiscriminantGroup) =
      E7.glueAlphabetIsometry hv ht (E7.glueLabelEquiv ht d) := by
  rcases d with ⟨d, hd⟩; simp only [glueLabelCount] at hd
  rw [glueLabelEquiv_E7, glueAlphabetIsometry_E7_apply]
  interval_cases d
  · refine (mk_eq_zero_of_val_eq_zero _ (glueLabelVector_zero E7)).trans ?_
    rw [Nat.cast_zero, map_zero, map_zero]
    -- The two zero classes agree across `Fin E7.rank` and `Fin 7`.
    rfl
  · rw [Nat.cast_one, typeE₇DiscriminantGroupEquiv_apply_one, ← mk_typeE₇MinusculeWeightDual]
    exact ((Isometry.ofEq (rootLattice_E7 ht).symm).discriminantGroupEquiv_mk_eq_mk_of_apply_eq <|
      (Isometry.ofEq_apply _ _).trans coe_typeE₇MinusculeWeightDual).symm

/-- For every valid digit `d : Fin t.glueLabelCount`, `t.glueLabelVector d.val` represents the
discriminant class of `t.glueLabelEquiv ht d`. -/
theorem mk_glueLabelVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (d : Fin t.glueLabelCount) :
    (Submodule.Quotient.mk ⟨t.glueLabelVector d.val,
        t.glueLabelVector_mem_dualCarrier hv ht d.val⟩ :
        (t.rootLattice ht).DiscriminantGroup) =
      t.glueAlphabetIsometry hv ht (t.glueLabelEquiv ht d) := by
  cases t with
  | A n => exact mk_glueLabelVector_A n hv ht d
  | D n => exact mk_glueLabelVector_D n hv ht d
  | E6 => exact mk_glueLabelVector_E6 hv ht d
  | E7 => exact mk_glueLabelVector_E7 hv ht d
  | E8 =>
    rw [glueLabelEquiv_E8, map_zero]
    exact mk_eq_zero_of_val_eq_zero _ (glueLabelVector_E8 d.val)
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **Squared norm of `glueLabelVector`.**  For every valid digit `d : Fin t.glueLabelCount`,
`t.glueLabelVector d.val` has squared norm `t.glueLabelMinimum d.val`. -/
@[simp] theorem form_glueLabelVector_self (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (d : Fin t.glueLabelCount) :
    (t.rootLattice ht).form (t.glueLabelVector d.val) (t.glueLabelVector d.val) =
      t.glueLabelMinimum d.val := by
  cases t with
  | A n =>
    exact (form_of_eq (rootLattice_A n ht) _ _).trans (form_typeACosetRepresentative_self d.isLt.le)
  | D n =>
    have hn4 : 4 ≤ n := valid_D.mp hv
    rcases d with ⟨d, hd⟩; simp only [glueLabelCount] at hd; interval_cases d
    · exact form_eq_zero_of_eq_zero _ (glueLabelVector_zero (D n))
    · exact form_typeDSpinorWeight_self hn4 ht
    · exact form_typeDVectorWeight_self hn4 ht
    · exact form_typeDCospinorWeight_self hn4 ht
  | E6 =>
    rcases d with ⟨d, hd⟩; simp only [glueLabelCount] at hd; interval_cases d
    · exact form_eq_zero_of_eq_zero _ (glueLabelVector_zero E6)
    · exact (form_of_eq (rootLattice_E6 ht) _ _).trans form_typeE₆MinusculeWeight_self
    · have hneg :
          typeE₆RootLattice.form (-typeE₆MinusculeWeight) (-typeE₆MinusculeWeight) = 4 / 3 := by
        rw [LinearMap.map_neg₂, map_neg, neg_neg, form_typeE₆MinusculeWeight_self]
      exact (form_of_eq (rootLattice_E6 ht) _ _).trans hneg
  | E7 =>
    rcases d with ⟨d, hd⟩; simp only [glueLabelCount] at hd; interval_cases d
    · exact form_eq_zero_of_eq_zero _ (glueLabelVector_zero E7)
    · exact (form_of_eq (rootLattice_E7 ht) _ _).trans form_typeE₇MinusculeWeight_self
  | E8 =>
    rcases d with ⟨d, hd⟩; simp only [glueLabelCount] at hd; interval_cases d
    exact form_eq_zero_of_eq_zero _ (glueLabelVector_E8 0)
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-! ## Shortest dual-lattice representatives of glue-alphabet labels -/

/-- **Computable shortest dual-lattice representative of a glue label** `a : t.glueAlphabet ht`, in
Bourbaki simple-root coordinates `Fin t.rank → ℚ`. -/
def glueRepresentativeVector (t : DynkinType) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) : Fin t.rank → ℚ :=
  t.glueLabelVector ((t.glueLabelEquiv ht).symm a).val

/-- `glueRepresentativeVector` applies `glueLabelVector` to the canonical digit of `a`. -/
theorem glueRepresentativeVector_def (t : DynkinType) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    t.glueRepresentativeVector ht a = t.glueLabelVector ((t.glueLabelEquiv ht).symm a).val :=
  (rfl)

/-- On a digit `d : Fin t.glueLabelCount`, `glueRepresentativeVector` agrees with
`glueLabelVector d.val`. -/
@[simp] theorem glueRepresentativeVector_glueLabelEquiv (t : DynkinType) (ht : t.IsSimplyLaced)
    (d : Fin t.glueLabelCount) :
    t.glueRepresentativeVector ht (t.glueLabelEquiv ht d) = t.glueLabelVector d.val := by
  rw [glueRepresentativeVector_def, Equiv.symm_apply_apply]

/-- The zero glue label is represented by the zero vector. -/
@[simp] theorem glueRepresentativeVector_zero (t : DynkinType) (ht : t.IsSimplyLaced) :
    t.glueRepresentativeVector ht 0 = 0 := by
  rw [glueRepresentativeVector_def, glueLabelEquiv_symm_zero, glueLabelVector_zero]

/-- On `Aₙ`, `glueRepresentativeVector` is `typeACosetRepresentative n a.val`. -/
@[simp] theorem glueRepresentativeVector_A (n : ℕ) (ht : (A n).IsSimplyLaced) (a : ZMod (n + 1)) :
    (A n).glueRepresentativeVector ht a = typeACosetRepresentative n a.val :=
  ((A n).glueRepresentativeVector_def ht a).trans
    (congrArg (A n).glueLabelVector (congrArg Fin.val (glueLabelEquiv_A_symm_apply n ht a)))

/-- For even `n`, `glueRepresentativeVector` on `Dₙ` sends `(0, 1)`, `(1, 0)`, `(1, 1)` in
`ℤ/2 × ℤ/2` to `typeDSpinorWeight n`, `typeDVectorWeight n`, `typeDCospinorWeight n`, and `0` to
`0`. -/
theorem glueRepresentativeVector_D_of_even (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Even n)
    (a : (D n).glueAlphabet ht) (b : ZMod 2 × ZMod 2)
    (hb : FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn) a = b) :
    (D n).glueRepresentativeVector ht a =
      if b = (0, 1) then typeDSpinorWeight n
      else if b = (1, 0) then typeDVectorWeight n
      else if b = (1, 1) then typeDCospinorWeight n else 0 := by
  subst hb
  obtain ⟨⟨d, hd⟩, rfl⟩ := ((D n).glueLabelEquiv ht).surjective a
  simp only [glueLabelCount] at hd
  rw [glueRepresentativeVector_glueLabelEquiv, glueLabelEquiv_D_of_even n ht hn]
  interval_cases d <;>
    simp only [glueLabelVector_zero, glueLabelVector_D, Nat.zero_div, Nat.zero_mod, Nat.reduceDiv,
      Nat.reduceMod, Nat.div_self zero_lt_two, Nat.mod_self, Nat.cast_zero, Nat.cast_one,
      Prod.mk.injEq, zero_ne_one, one_ne_zero, OfNat.ofNat_ne_one, Nat.reduceEqDiff,
      and_self, and_false, false_and, ↓reduceIte] <;>
    -- `(0 : Fin (D n).rank → ℚ)` and `(0 : Fin n → ℚ)` are definitionally equal (`d = 0`).
    rfl

/-- For odd `n`, `glueRepresentativeVector` on `Dₙ` sends `1, 2, 3 ∈ ℤ/4` to
`typeDSpinorWeight n`, `typeDVectorWeight n`, `typeDCospinorWeight n`, and `0` to `0`. -/
theorem glueRepresentativeVector_D_of_odd (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Odd n)
    (a : (D n).glueAlphabet ht) (b : ZMod 4)
    (hb : FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_odd n ht hn) a = b) :
    (D n).glueRepresentativeVector ht a =
      if b = 1 then typeDSpinorWeight n
      else if b = 2 then typeDVectorWeight n
      else if b = 3 then typeDCospinorWeight n else 0 := by
  subst hb
  obtain ⟨⟨d, hd⟩, rfl⟩ := ((D n).glueLabelEquiv ht).surjective a
  simp only [glueLabelCount] at hd
  rw [glueRepresentativeVector_glueLabelEquiv, glueLabelEquiv_D_of_odd n ht hn]
  interval_cases d <;>
    simp only [glueLabelVector_zero, glueLabelVector_D, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, ← (ZMod.val_injective 4).eq_iff, ZMod.val_zero, ZMod.val_one_eq_one_mod,
      ZMod.val_ofNat, Nat.reduceMod, Nat.reduceEqDiff, zero_ne_one, OfNat.ofNat_ne_one,
      ↓reduceIte] <;>
    -- `(0 : Fin (D n).rank → ℚ)` and `(0 : Fin n → ℚ)` are definitionally equal (`d = 0`).
    rfl

/-- On `E₆`, `glueRepresentativeVector` sends `0, 1, 2 ∈ ℤ/3` to `0`, `ϖ₁`, `-ϖ₁`. -/
@[simp] theorem glueRepresentativeVector_E6 (ht : E6.IsSimplyLaced) (a : ZMod 3) :
    E6.glueRepresentativeVector ht a =
      if a = 1 then typeE₆MinusculeWeight else if a = 2 then -typeE₆MinusculeWeight else 0 := by
  obtain ⟨⟨d, hd⟩, rfl⟩ := (E6.glueLabelEquiv ht).surjective a
  simp only [glueLabelCount] at hd
  rw [glueRepresentativeVector_glueLabelEquiv, glueLabelEquiv_E6 ht]
  interval_cases d <;>
    simp only [glueLabelVector_zero, glueLabelVector_E6, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, ← (ZMod.val_injective 3).eq_iff, ZMod.val_zero, ZMod.val_one_eq_one_mod,
      ZMod.val_ofNat, Nat.reduceMod, Nat.reduceEqDiff, zero_ne_one, OfNat.ofNat_ne_one,
      ↓reduceIte] <;>
    -- `(0 : Fin E6.rank → ℚ)` and `(0 : Fin 6 → ℚ)` are definitionally equal (`d = 0`).
    rfl

/-- On `E₇`, `glueRepresentativeVector` sends `0, 1 ∈ ℤ/2` to `0`, `ϖ₇`. -/
@[simp] theorem glueRepresentativeVector_E7 (ht : E7.IsSimplyLaced) (a : ZMod 2) :
    E7.glueRepresentativeVector ht a = if a = 1 then typeE₇MinusculeWeight else 0 := by
  obtain ⟨⟨d, hd⟩, rfl⟩ := (E7.glueLabelEquiv ht).surjective a
  simp only [glueLabelCount] at hd
  rw [glueRepresentativeVector_glueLabelEquiv, glueLabelEquiv_E7 ht]
  interval_cases d
  · simp only [glueLabelVector_zero E7, Nat.cast_zero, zero_ne_one, ↓reduceIte]
    -- `(0 : Fin E7.rank → ℚ)` and `(0 : Fin 7 → ℚ)` are definitionally equal.
    rfl
  · simp

/-- On `E₈`, `glueRepresentativeVector` is identically `0`. -/
@[simp] theorem glueRepresentativeVector_E8 (ht : E8.IsSimplyLaced) (a : E8.glueAlphabet ht) :
    E8.glueRepresentativeVector ht a = 0 := by
  rw [Subsingleton.elim a 0, glueRepresentativeVector_zero]

/-- **Naturality along equal Dynkin types**: `rootLatticeIsometryOfEq` intertwines
`glueRepresentativeVector` with `glueAlphabet_congr`. -/
theorem rootLatticeIsometryOfEq_glueRepresentativeVector {t s : DynkinType} (h : t = s)
    (ht : t.IsSimplyLaced) (hs : s.IsSimplyLaced) (a : t.glueAlphabet ht) :
    t.rootLatticeIsometryOfEq ht h hs (t.glueRepresentativeVector ht a) =
      s.glueRepresentativeVector hs
        (FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_congr h ht hs) a) := by
  rw [glueRepresentativeVector_def, glueRepresentativeVector_def,
    val_glueLabelEquiv_symm_ofEq h ht hs a, rootLatticeIsometryOfEq_glueLabelVector]

/-- `glueRepresentativeVector` lies in `(t.rootLattice ht).dualCarrier` when `t` is valid. -/
theorem glueRepresentativeVector_mem_dualCarrier (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    t.glueRepresentativeVector ht a ∈ (t.rootLattice ht).dualCarrier :=
  t.glueLabelVector_mem_dualCarrier hv ht _

/-- **Bundled shortest dual-lattice representative of a glue label** `a : t.glueAlphabet ht`. -/
noncomputable def glueRepresentative (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) : (t.rootLattice ht).dualCarrier :=
  ⟨t.glueRepresentativeVector ht a, t.glueRepresentativeVector_mem_dualCarrier hv ht a⟩

/-- The underlying vector of `glueRepresentative` is `glueRepresentativeVector`. -/
@[simp] theorem coe_glueRepresentative (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    (t.glueRepresentative hv ht a : Fin t.rank → ℚ) = t.glueRepresentativeVector ht a := (rfl)

/-- The zero glue label has bundled representative `0`. -/
@[simp] theorem glueRepresentative_zero (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    t.glueRepresentative hv ht 0 = 0 :=
  Subtype.ext (t.glueRepresentativeVector_zero ht)

/-- **`glueRepresentative` represents the discriminant coset `glueAlphabetIsometry`.** -/
@[simp] theorem mk_glueRepresentative (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    (Submodule.Quotient.mk (t.glueRepresentative hv ht a) :
        (t.rootLattice ht).DiscriminantGroup) =
      t.glueAlphabetIsometry hv ht a := by
  obtain ⟨d, rfl⟩ := (t.glueLabelEquiv ht).surjective a
  have heq : t.glueRepresentative hv ht (t.glueLabelEquiv ht d) =
      ⟨t.glueLabelVector d.val, t.glueLabelVector_mem_dualCarrier hv ht d.val⟩ :=
    Subtype.ext (t.glueRepresentativeVector_glueLabelEquiv ht d)
  rw [heq, mk_glueLabelVector]

/-- Distinct glue labels have distinct bundled dual-lattice representatives. -/
theorem glueRepresentative_injective (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    Function.Injective (t.glueRepresentative hv ht) := by
  intro a b hab
  have hmk := congrArg (Submodule.Quotient.mk : _ → (t.rootLattice ht).DiscriminantGroup) hab
  rw [mk_glueRepresentative, mk_glueRepresentative] at hmk
  exact (t.glueAlphabetIsometry hv ht).injective hmk

/-- Distinct glue labels have distinct rational representative vectors. -/
theorem glueRepresentativeVector_injective (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    Function.Injective (t.glueRepresentativeVector ht) := fun _ _ hab ↦
  t.glueRepresentative_injective hv ht <| Subtype.ext <| by
    rw [coe_glueRepresentative, coe_glueRepresentative, hab]

/-- `glueRepresentative` vanishes if and only if the glue label is `0`. -/
@[simp] theorem glueRepresentative_eq_zero_iff (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    t.glueRepresentative hv ht a = 0 ↔ a = 0 := by
  rw [← t.glueRepresentative_zero hv ht]; exact (t.glueRepresentative_injective hv ht).eq_iff

/-- `glueRepresentativeVector` vanishes if and only if the glue label is `0`. -/
@[simp] theorem glueRepresentativeVector_eq_zero_iff (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    t.glueRepresentativeVector ht a = 0 ↔ a = 0 := by
  rw [← t.glueRepresentativeVector_zero ht]
  exact (t.glueRepresentativeVector_injective hv ht).eq_iff

/-- Two glue-label representative vectors differ by a root-lattice vector iff the labels agree. -/
theorem glueRepresentativeVector_sub_mem_carrier_iff (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a b : t.glueAlphabet ht) :
    t.glueRepresentativeVector ht a - t.glueRepresentativeVector ht b ∈
        (t.rootLattice ht).carrier ↔ a = b := by
  rw [← coe_glueRepresentative t hv ht a, ← coe_glueRepresentative t hv ht b, ← Submodule.coe_sub,
    ← discriminantGroup_mk_eq_iff, mk_glueRepresentative, mk_glueRepresentative]
  exact (t.glueAlphabetIsometry hv ht).injective.eq_iff

/-- `glueRepresentativeVector` belongs to the root-lattice carrier iff the glue label is `0`. -/
theorem glueRepresentativeVector_mem_carrier_iff (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    t.glueRepresentativeVector ht a ∈ (t.rootLattice ht).carrier ↔ a = 0 := by
  simpa only [glueRepresentativeVector_zero, sub_zero] using
    t.glueRepresentativeVector_sub_mem_carrier_iff hv ht a 0

/-- A dual vector `y` lies in the discriminant coset named by `a` iff
`y - glueRepresentativeVector a` lies in the root lattice. -/
theorem sub_glueRepresentativeVector_mem_carrier_iff (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (y : (t.rootLattice ht).dualCarrier) (a : t.glueAlphabet ht) :
    (y : Fin t.rank → ℚ) - t.glueRepresentativeVector ht a ∈ (t.rootLattice ht).carrier ↔
      Submodule.Quotient.mk y = t.glueAlphabetIsometry hv ht a := by
  rw [← t.mk_glueRepresentative hv ht a, discriminantGroup_mk_eq_iff, Submodule.coe_sub,
    coe_glueRepresentative]

/-- Representatives are additive modulo the root lattice: `glueRepresentativeVector (a + b)`
differs from `glueRepresentativeVector a + glueRepresentativeVector b` by a root-lattice vector. -/
theorem glueRepresentativeVector_add_sub_mem_carrier (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a b : t.glueAlphabet ht) :
    t.glueRepresentativeVector ht (a + b) -
        (t.glueRepresentativeVector ht a + t.glueRepresentativeVector ht b) ∈
      (t.rootLattice ht).carrier := by
  have h : (Submodule.Quotient.mk (t.glueRepresentative hv ht (a + b)) :
      (t.rootLattice ht).DiscriminantGroup) =
      Submodule.Quotient.mk (t.glueRepresentative hv ht a + t.glueRepresentative hv ht b) := by
    rw [Submodule.Quotient.mk_add (R := ℤ), mk_glueRepresentative, mk_glueRepresentative,
      mk_glueRepresentative, map_add]
    rfl
  simpa only [discriminantGroup_mk_eq_iff, Submodule.coe_sub, Submodule.coe_add,
    coe_glueRepresentative] using h

/-- **`glueRepresentativeVector` attains the shortest norm `t.glueMinimum ht a`.** -/
@[simp] theorem form_glueRepresentativeVector_self (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    (t.rootLattice ht).form (t.glueRepresentativeVector ht a) (t.glueRepresentativeVector ht a) =
      t.glueMinimum ht a := by
  obtain ⟨d, rfl⟩ := (t.glueLabelEquiv ht).surjective a
  rw [glueRepresentativeVector_glueLabelEquiv, form_glueLabelVector_self t hv ht d,
    glueMinimum_glueLabelEquiv]

/-- **Minimality of `glueRepresentative`**: no dual vector in the coset `t.glueAlphabetIsometry hv
ht a` has strictly smaller squared norm than `t.glueRepresentative hv ht a`. -/
theorem form_glueRepresentative_self_le (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) (x : (t.rootLattice ht).dualCarrier)
    (hx : (Submodule.Quotient.mk x : (t.rootLattice ht).DiscriminantGroup) =
      t.glueAlphabetIsometry hv ht a) :
    (t.rootLattice ht).form (t.glueRepresentative hv ht a) (t.glueRepresentative hv ht a) ≤
      (t.rootLattice ht).form x x := by
  rw [coe_glueRepresentative, form_glueRepresentativeVector_self t hv ht a]
  exact (t.isLeast_glueMinimum hv ht a).2 ⟨x, hx, rfl⟩

/-- **Quadratic half-norm of a glue label**: `q(a) = ⟨v_a, v_a⟩ / 2 mod ℤ`. -/
theorem quadratic_glueAlphabet_eq_form_glueRepresentative_self_div_two (t : DynkinType)
    (hv : t.Valid) (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    (t.glueAlphabet ht).quadratic a =
      (((t.rootLattice ht).form (t.glueRepresentativeVector ht a)
          (t.glueRepresentativeVector ht a) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [form_glueRepresentativeVector_self t hv ht a]
  exact quadratic_glueAlphabet_eq_glueMinimum_div_two t ht a

/-- **Polar bilinear pairing of two glue labels**: `b(a, b) = ⟨v_a, v_b⟩ mod ℤ`. -/
theorem pairing_glueAlphabet_eq_form_glueRepresentative (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a b : t.glueAlphabet ht) :
    (t.glueAlphabet ht).toFiniteBilinearModule.pairing a b =
      (((t.rootLattice ht).form (t.glueRepresentativeVector ht a)
          (t.glueRepresentativeVector ht b) : ℚ) : AddCircle (1 : ℚ)) := by
  refine ((t.glueAlphabetIsometry hv ht).toHom.map_pairing a b).symm.trans ?_
  rw [FiniteQuadraticModule.Isometry.toHom_apply, FiniteQuadraticModule.Isometry.toHom_apply]
  refine ((t.rootLattice ht).discriminantBilinearModule_pairing _ _).trans ?_
  rw [← mk_glueRepresentative t hv ht a, ← mk_glueRepresentative t hv ht b,
    discriminantPairing_mk, coe_glueRepresentative, coe_glueRepresentative]

/-- **Torsion of a glue label**: `k • a = 0` in `t.glueAlphabet ht` iff `k • v_a` belongs to the
root-lattice carrier. -/
theorem zsmul_eq_zero_iff_zsmul_glueRepresentativeVector_mem_carrier (t : DynkinType)
    (hv : t.Valid) (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) (k : ℤ) :
    k • a = 0 ↔ k • t.glueRepresentativeVector ht a ∈ (t.rootLattice ht).carrier := by
  have hsmul : (t.glueAlphabetIsometry hv ht) (k • a) =
      (Submodule.Quotient.mk (k • t.glueRepresentative hv ht a) :
        (t.rootLattice ht).DiscriminantGroup) :=
    (map_zsmul (t.glueAlphabetIsometry hv ht) k a).trans
      ((congrArg (k • ·) (t.mk_glueRepresentative hv ht a).symm).trans
        (Submodule.Quotient.mk_smul _ k (t.glueRepresentative hv ht a)).symm)
  have h0 : ((Submodule.Quotient.mk (k • t.glueRepresentative hv ht a) :
        (t.rootLattice ht).DiscriminantGroup) = 0) ↔
      k • t.glueRepresentativeVector ht a ∈ (t.rootLattice ht).carrier := by
    rw [discriminantGroup_mk_eq_zero_iff, Submodule.coe_smul, coe_glueRepresentative]
  exact (map_eq_zero_iff (t.glueAlphabetIsometry hv ht)
    (t.glueAlphabetIsometry hv ht).injective).symm.trans
    ((Iff.of_eq (congrArg (· = 0) hsmul)).trans h0)

/-- **Additive order of a glue label**: the order of `a` in `t.glueAlphabet ht` equals the order of
the coset of `t.glueRepresentative hv ht a` in the discriminant group. -/
theorem addOrderOf_eq_addOrderOf_mk_glueRepresentative (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    addOrderOf a =
      addOrderOf (Submodule.Quotient.mk (t.glueRepresentative hv ht a) :
        (t.rootLattice ht).DiscriminantGroup) := by
  rw [mk_glueRepresentative]
  exact (addOrderOf_injective (t.glueAlphabetIsometry hv ht).toAddEquiv.toAddMonoidHom
    (t.glueAlphabetIsometry hv ht).injective a).symm

/-! ## Shortest representatives of glue words and glued-lattice generators -/

section GlueWord

universe v

/-- **Computable shortest dual-lattice representative of a glue word**
`w : ∀ i, (t i).glueAlphabet (ht i)` in `∀ i, Fin (t i).rank → ℚ`. -/
def glueWordRepresentativeVector {ι : Type v} (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)
    (w : ∀ i, (t i).glueAlphabet (ht i)) : ∀ i, Fin (t i).rank → ℚ :=
  fun i ↦ (t i).glueRepresentativeVector (ht i) (w i)

/-- `glueWordRepresentativeVector` acts componentwise by `glueRepresentativeVector`. -/
theorem glueWordRepresentativeVector_def {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht w = fun i ↦ (t i).glueRepresentativeVector (ht i) (w i) :=
  (rfl)

/-- Evaluating `glueWordRepresentativeVector` at `i` gives `(t i).glueRepresentativeVector`. -/
@[simp] theorem glueWordRepresentativeVector_apply {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (w : ∀ i, (t i).glueAlphabet (ht i)) (i : ι) :
    glueWordRepresentativeVector t ht w i = (t i).glueRepresentativeVector (ht i) (w i) := (rfl)

/-- The zero glue word is represented by the zero vector. -/
@[simp] theorem glueWordRepresentativeVector_zero {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) : glueWordRepresentativeVector t ht 0 = 0 := by
  ext i j; simp

/-- Distinct glue words have distinct rational representative vectors when all components are
valid. -/
theorem glueWordRepresentativeVector_injective {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (hv : ∀ i, (t i).Valid) :
    Function.Injective (glueWordRepresentativeVector t ht) := fun _ _ h ↦
  funext fun i ↦ (t i).glueRepresentativeVector_injective (hv i) (ht i) (congrFun h i)

/-- `glueWordRepresentativeVector` vanishes if and only if the glue word is `0`. -/
@[simp] theorem glueWordRepresentativeVector_eq_zero_iff {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht w = 0 ↔ w = 0 := by
  rw [← glueWordRepresentativeVector_zero t ht]
  exact (glueWordRepresentativeVector_injective t ht hv).eq_iff

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)

/-- `glueWordRepresentativeVector` belongs to the dual carrier of the orthogonal sum of root
lattices when all components are valid. -/
theorem glueWordRepresentativeVector_mem_dualCarrier (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  (mem_dualCarrier_pi_iff _ _).mpr fun i ↦
    (t i).glueRepresentativeVector_mem_dualCarrier (hv i) (ht i) (w i)

/-- **Bundled shortest dual-lattice representative of a glue word.** -/
noncomputable def glueWordRepresentative (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) : (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  ⟨glueWordRepresentativeVector t ht w, glueWordRepresentativeVector_mem_dualCarrier t ht hv w⟩

/-- The underlying vector of `glueWordRepresentative` is `glueWordRepresentativeVector`. -/
@[simp] theorem coe_glueWordRepresentative (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (glueWordRepresentative t ht hv w : ∀ i, Fin (t i).rank → ℚ) =
      glueWordRepresentativeVector t ht w := (rfl)

/-- The zero glue word has bundled representative `0`. -/
@[simp] theorem glueWordRepresentative_zero (hv : ∀ i, (t i).Valid) :
    glueWordRepresentative t ht hv 0 = 0 :=
  Subtype.ext (glueWordRepresentativeVector_zero t ht)

/-- **`glueWordRepresentative` represents the discriminant coset `glueWordIsometry`.** -/
@[simp] theorem mk_glueWordRepresentative (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (Submodule.Quotient.mk (glueWordRepresentative t ht hv w) :
        (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      glueWordIsometry t ht hv w := by
  apply (discriminantGroupPiEquiv _).injective
  ext i
  rw [discriminantGroupPiEquiv_mk, discriminantGroupPiEquiv_glueWordIsometry,
    ← mk_glueRepresentative (t i) (hv i) (ht i) (w i)]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (coe_piDualCarrierEquiv_apply _ _ i))

/-- Distinct glue words have distinct bundled dual-lattice representatives. -/
theorem glueWordRepresentative_injective (hv : ∀ i, (t i).Valid) :
    Function.Injective (glueWordRepresentative t ht hv) := fun w₁ w₂ h ↦
  glueWordRepresentativeVector_injective t ht hv <| by
    rw [← coe_glueWordRepresentative t ht hv w₁, ← coe_glueWordRepresentative t ht hv w₂, h]

/-- `glueWordRepresentative` vanishes if and only if the glue word is `0`. -/
@[simp] theorem glueWordRepresentative_eq_zero_iff (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentative t ht hv w = 0 ↔ w = 0 := by
  rw [← glueWordRepresentative_zero t ht hv]
  exact (glueWordRepresentative_injective t ht hv).eq_iff

/-- Two glue-word representative vectors differ by a root-lattice vector iff the words agree. -/
theorem glueWordRepresentativeVector_sub_mem_carrier_iff (hv : ∀ i, (t i).Valid)
    (w₁ w₂ : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht w₁ - glueWordRepresentativeVector t ht w₂ ∈
        (pi fun i ↦ (t i).rootLattice (ht i)).carrier ↔ w₁ = w₂ := by
  rw [← coe_glueWordRepresentative t ht hv w₁, ← coe_glueWordRepresentative t ht hv w₂,
    ← Submodule.coe_sub, ← discriminantGroup_mk_eq_iff, mk_glueWordRepresentative,
    mk_glueWordRepresentative]
  exact (glueWordIsometry t ht hv).injective.eq_iff

/-- `glueWordRepresentativeVector` belongs to the orthogonal sum of root lattices iff `w = 0`. -/
theorem glueWordRepresentativeVector_mem_carrier_iff (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).carrier ↔ w = 0 :=
  by simpa only [glueWordRepresentativeVector_zero, sub_zero] using
    glueWordRepresentativeVector_sub_mem_carrier_iff t ht hv w 0

/-- **`glueWordRepresentativeVector` attains the shortest norm
`∑ i, (t i).glueMinimum (ht i) (w i)`.** -/
theorem form_glueWordRepresentativeVector_self (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordRepresentativeVector t ht w)
        (glueWordRepresentativeVector t ht w) = ∑ i, (t i).glueMinimum (ht i) (w i) := by
  rw [pi_form, LinearMap.BilinForm.pi_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (t i).form_glueRepresentativeVector_self (hv i) (ht i) (w i)

/-- **Minimality of `glueWordRepresentative`**: no dual vector in the coset `glueWordIsometry t ht
hv w` has smaller squared norm. -/
theorem form_glueWordRepresentative_self_le (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) (x : (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier)
    (hx : (Submodule.Quotient.mk x : (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      glueWordIsometry t ht hv w) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordRepresentative t ht hv w)
        (glueWordRepresentative t ht hv w) ≤ (pi fun i ↦ (t i).rootLattice (ht i)).form x x := by
  rw [coe_glueWordRepresentative, form_glueWordRepresentativeVector_self t ht hv w]
  exact (isLeast_sum_glueMinimum t hv ht w).2 ⟨x, hx, rfl⟩

/-- **Polar bilinear pairing of two glue words from their explicit representatives.** -/
theorem pairing_pi_glueAlphabet_eq_form_glueWordRepresentative (hv : ∀ i, (t i).Valid)
    (w₁ w₂ : ∀ i, (t i).glueAlphabet (ht i)) :
    (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).toFiniteBilinearModule.pairing
        w₁ w₂ =
      (((pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordRepresentativeVector t ht w₁)
          (glueWordRepresentativeVector t ht w₂) : ℚ) : AddCircle (1 : ℚ)) := by
  refine ((glueWordIsometry t ht hv).toHom.map_pairing w₁ w₂).symm.trans ?_
  rw [FiniteQuadraticModule.Isometry.toHom_apply, FiniteQuadraticModule.Isometry.toHom_apply]
  refine ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantBilinearModule_pairing _ _).trans ?_
  rw [← mk_glueWordRepresentative t ht hv w₁, ← mk_glueWordRepresentative t ht hv w₂,
    discriminantPairing_mk, coe_glueWordRepresentative, coe_glueWordRepresentative]

/-- **Explicit generators of a glued lattice**: if `G` generates `H`, then `(gluedLattice t ht hv
H hH).carrier` is spanned over `ℤ` by the root-lattice carrier and
`glueWordRepresentativeVector t ht '' G`. -/
theorem gluedLattice_carrier_eq_sup_span_glueWordRepresentativeVector (hv : ∀ i, (t i).Valid)
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    {G : Set (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i))}
    (hG : AddSubgroup.closure G = H) :
    (gluedLattice t ht hv H hH).carrier =
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier ⊔
        Submodule.span ℤ (glueWordRepresentativeVector t ht '' G) := by
  simpa only [coe_glueWordRepresentative] using
    gluedLattice_carrier_eq_sup_span t ht hv H hH hG (glueWordRepresentative t ht hv)
      fun w _ ↦ mk_glueWordRepresentative t ht hv w

/-- **Coset decomposition of a glued lattice**: `x` lies in `gluedLattice` iff it differs from
`glueWordRepresentativeVector t ht w`, for some `w ∈ H`, by a root-lattice vector. -/
theorem mem_gluedLattice_carrier_iff_exists_sub_mem (hv : ∀ i, (t i).Valid)
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedLattice t ht hv H hH).carrier ↔
      ∃ w ∈ H, x - glueWordRepresentativeVector t ht w ∈
        (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  rw [mem_gluedLattice_carrier_iff]
  constructor
  · rintro ⟨hx, hw⟩
    refine ⟨_, hw, ?_⟩
    have hsub := (discriminantGroup_mk_eq_iff _ ⟨x, hx⟩
      (glueWordRepresentative t ht hv _)).mp <| by
        rw [mk_glueWordRepresentative]
        exact ((glueWordIsometry t ht hv).toAddEquiv.apply_symm_apply _).symm
    rwa [Submodule.coe_sub, coe_glueWordRepresentative] at hsub
  · rintro ⟨w, hw, hsub⟩
    have hx : x ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier := by
      simpa only [sub_add_cancel] using (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier.add_mem
        ((pi fun i ↦ (t i).rootLattice (ht i)).le_dualCarrier hsub)
        (glueWordRepresentativeVector_mem_dualCarrier t ht hv w)
    refine ⟨hx, ?_⟩
    have hmk : (Submodule.Quotient.mk ⟨x, hx⟩ :
          (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
        (glueWordIsometry t ht hv).toAddEquiv w :=
      ((discriminantGroup_mk_eq_iff _ ⟨x, hx⟩ (glueWordRepresentative t ht hv w)).mpr
        (by rwa [Submodule.coe_sub, coe_glueWordRepresentative])).trans
        (mk_glueWordRepresentative t ht hv w)
    rwa [hmk, AddEquiv.symm_apply_apply]

/-- `glueWordRepresentativeVector t ht w` belongs to `(gluedLattice t ht hv H hH).carrier` iff
`w ∈ H`. -/
@[simp] theorem glueWordRepresentativeVector_mem_gluedLattice_carrier_iff (hv : ∀ i, (t i).Valid)
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht w ∈ (gluedLattice t ht hv H hH).carrier ↔ w ∈ H := by
  rw [mem_gluedLattice_carrier_iff_exists_sub_mem]
  exact ⟨fun ⟨w', hw', hsub⟩ ↦
    (glueWordRepresentativeVector_sub_mem_carrier_iff t ht hv w w').mp hsub ▸ hw',
    fun hw ↦ ⟨w, hw, sub_self (glueWordRepresentativeVector t ht w) ▸
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier.zero_mem⟩⟩

/-- **Coordinatewise membership criterion for a glued lattice**: `x` belongs to `gluedLattice` iff
there is `w ∈ H` such that every coordinate `x i j` differs from
`(t i).glueRepresentativeVector (ht i) (w i) j` by an integer. -/
theorem mem_gluedLattice_carrier_iff_exists_int (hv : ∀ i, (t i).Valid)
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedLattice t ht hv H hH).carrier ↔
      ∃ w ∈ H, ∀ i j, ∃ z : ℤ,
        (z : ℚ) = x i j - (t i).glueRepresentativeVector (ht i) (w i) j := by
  rw [mem_gluedLattice_carrier_iff_exists_sub_mem]
  refine exists_congr fun w ↦ and_congr_right fun _ ↦ ?_
  rw [mem_pi_carrier_iff]; refine forall_congr' fun i ↦ ?_
  rw [mem_rootLattice_carrier_iff]; refine forall_congr' fun j ↦ exists_congr fun z ↦ ?_
  rw [Pi.sub_apply, Pi.sub_apply, glueWordRepresentativeVector_apply]

/-- **Naturality of `glueWordRepresentativeVector` along reindexing to an equal family of
components.** -/
theorem glueWordRepresentativeVector_piGlueAlphabetCongr {κ : Type*} [Fintype κ]
    {s : κ → DynkinType} (hs : ∀ k, (s k).IsSimplyLaced) (σ : κ ≃ ι) (h : ∀ k, t (σ k) = s k)
    (w : ∀ i, (t i).glueAlphabet (ht i)) (k : κ) :
    glueWordRepresentativeVector s hs (piGlueAlphabetCongr t ht σ h w) k =
      (t (σ k)).rootLatticeIsometryOfEq (ht (σ k)) (h k) (hs k)
        (glueWordRepresentativeVector t ht w (σ k)) := by
  rw [glueWordRepresentativeVector_apply, piGlueAlphabetCongr_apply,
    glueWordRepresentativeVector_apply, rootLatticeIsometryOfEq_glueRepresentativeVector]

/-- A dual vector `x` of the orthogonal sum of root lattices lies in the coset named by the glue
word `w` iff `x - glueWordRepresentativeVector t ht w` lies in the orthogonal sum of root
lattices. -/
theorem sub_glueWordRepresentativeVector_mem_carrier_iff (hv : ∀ i, (t i).Valid)
    (x : (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (x : ∀ i, Fin (t i).rank → ℚ) - glueWordRepresentativeVector t ht w ∈
        (pi fun i ↦ (t i).rootLattice (ht i)).carrier ↔
      Submodule.Quotient.mk x = glueWordIsometry t ht hv w := by
  rw [← mk_glueWordRepresentative t ht hv w, discriminantGroup_mk_eq_iff, Submodule.coe_sub,
    coe_glueWordRepresentative]

/-- Glue-word representatives are additive modulo the orthogonal sum of root lattices. -/
theorem glueWordRepresentativeVector_add_sub_mem_carrier (hv : ∀ i, (t i).Valid)
    (v w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht (v + w) -
        (glueWordRepresentativeVector t ht v + glueWordRepresentativeVector t ht w) ∈
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  rw [mem_pi_carrier_iff]
  intro i
  simp only [Pi.sub_apply, Pi.add_apply, glueWordRepresentativeVector_apply]
  exact (t i).glueRepresentativeVector_add_sub_mem_carrier (hv i) (ht i) (v i) (w i)

/-- An integer multiple `k • glueWordRepresentativeVector t ht w` lies in the orthogonal sum of
root lattices iff `k • w = 0`. -/
theorem zsmul_glueWordRepresentativeVector_mem_carrier_iff (hv : ∀ i, (t i).Valid)
    (k : ℤ) (w : ∀ i, (t i).glueAlphabet (ht i)) :
    k • glueWordRepresentativeVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).carrier ↔
      k • w = 0 := by
  have hmk :
      (Submodule.Quotient.mk (k • glueWordRepresentative t ht hv w) :
          (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
        glueWordIsometry t ht hv (k • w) := by
    rw [Submodule.Quotient.mk_smul, mk_glueWordRepresentative]
    exact (map_zsmul (glueWordIsometry t ht hv) k w).symm
  rw [← coe_glueWordRepresentative t ht hv w, ← Submodule.coe_smul,
    ← discriminantGroup_mk_eq_zero_iff, hmk]
  exact map_eq_zero_iff (glueWordIsometry t ht hv) (EquivLike.injective _)

/-- A natural multiple `k • glueWordRepresentativeVector t ht w` lies in the orthogonal sum of
root lattices iff `k • w = 0`. -/
theorem nsmul_glueWordRepresentativeVector_mem_carrier_iff (hv : ∀ i, (t i).Valid)
    (k : ℕ) (w : ∀ i, (t i).glueAlphabet (ht i)) :
    k • glueWordRepresentativeVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).carrier ↔
      k • w = 0 := by
  rw [← natCast_zsmul, zsmul_glueWordRepresentativeVector_mem_carrier_iff t ht hv, natCast_zsmul]

/-- **Naturality of `glueWordRepresentativeVector` under `gluedLatticeIsometryOfEq`**: the
coordinate-preserving isometry between glued lattices of equal families of components maps
`glueWordRepresentativeVector t ht w` to the representative of `piGlueAlphabetCongr t ht σ h w`. -/
@[simp] theorem gluedLatticeIsometryOfEq_glueWordRepresentativeVector (hv : ∀ i, (t i).Valid)
    {H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i))}
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    {κ : Type*} [Fintype κ] {s : κ → DynkinType} {hs : ∀ k, (s k).IsSimplyLaced}
    (hvs : ∀ k, (s k).Valid)
    {H' : AddSubgroup (FiniteQuadraticModule.pi fun k ↦ (s k).glueAlphabet (hs k))}
    (hH' : (FiniteQuadraticModule.pi fun k ↦ (s k).glueAlphabet (hs k)).IsIsotropic H')
    (σ : κ ≃ ι) (h : ∀ k, t (σ k) = s k)
    (hHH' : ∀ w, piGlueAlphabetCongr t ht σ h w ∈ H' ↔ w ∈ H)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    gluedLatticeIsometryOfEq t ht hv H hH hvs hH' σ h hHH' (glueWordRepresentativeVector t ht w) =
      glueWordRepresentativeVector s hs (piGlueAlphabetCongr t ht σ h w) := by
  funext k j
  rw [gluedLatticeIsometryOfEq_apply, glueWordRepresentativeVector_piGlueAlphabetCongr,
    rootLatticeIsometryOfEq_apply]

/-- **Coset decomposition of a cyclic glued lattice**: if the glue subgroup `H` is generated by a
single glue word `w` with `m • w = 0` (`0 < m`), then `x` lies in `gluedLattice` iff
`x - k • glueWordRepresentativeVector t ht w` lies in the orthogonal sum of root lattices for some
`k < m`. -/
theorem mem_gluedLattice_carrier_iff_exists_nsmul (hv : ∀ i, (t i).Valid)
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    {w : ∀ i, (t i).glueAlphabet (ht i)} (hHw : H = AddSubgroup.zmultiples w)
    {m : ℕ} (hm : 0 < m) (hmw : m • w = 0) (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedLattice t ht hv H hH).carrier ↔
      ∃ k < m, x - k • glueWordRepresentativeVector t ht w ∈
        (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  constructor
  · intro hx
    obtain ⟨hxDual, hw⟩ := (mem_gluedLattice_carrier_iff t ht hv H hH x).mp hx
    classical
    have hwFin : IsOfFinAddOrder w := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, hmw⟩
    rw [hHw, hwFin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hw
    obtain ⟨k, hk, hkw⟩ := hw
    refine ⟨k, (Finset.mem_range.mp hk).trans_le (addOrderOf_le_of_nsmul_eq_zero hm hmw), ?_⟩
    have hmk_smul :
        (Submodule.Quotient.mk ((k : ℤ) • glueWordRepresentative t ht hv w) :
            (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
          glueWordIsometry t ht hv ((k : ℤ) • w) := by
      rw [Submodule.Quotient.mk_smul, mk_glueWordRepresentative]
      exact (map_zsmul (glueWordIsometry t ht hv) (k : ℤ) w).symm
    have hmk :
        (Submodule.Quotient.mk ⟨x, hxDual⟩ :
            (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
          Submodule.Quotient.mk ((k : ℤ) • glueWordRepresentative t ht hv w) := by
      rw [hmk_smul, natCast_zsmul]
      exact (AddEquiv.symm_apply_eq _).mp hkw.symm
    have hdiff := (discriminantGroup_mk_eq_iff _ _ _).mp hmk
    rwa [Submodule.coe_sub, Submodule.coe_smul, coe_glueWordRepresentative, natCast_zsmul]
      at hdiff
  · rintro ⟨k, -, hmem⟩
    have hw : glueWordRepresentativeVector t ht w ∈ (gluedLattice t ht hv H hH).carrier :=
      (glueWordRepresentativeVector_mem_gluedLattice_carrier_iff t ht hv H hH w).mpr
        (hHw ▸ AddSubgroup.mem_zmultiples w)
    exact sub_add_cancel x (k • glueWordRepresentativeVector t ht w) ▸
      add_mem (carrier_le_gluedLattice_carrier t ht hv H hH hmem)
        ((gluedLattice t ht hv H hH).carrier.nsmul_mem hw k)

end GlueWord

end TauCeti.DynkinType
