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

`TauCeti.DynkinType.glueAlphabetIsometry` identifies the glue alphabet `t.glueAlphabet ht` of a
valid simply-laced Dynkin type `t` with the discriminant quadratic module of `t.rootLattice ht`,
and `TauCeti.DynkinType.isLeast_glueMinimum` shows existentially that every coset attains its
shortest norm `t.glueMinimum ht a`.

This file provides a canonical **computable** rational vector `t.glueRepresentativeVector ht a` in
simple-root coordinates `Fin t.rank → ℚ` for every glue label `a : t.glueAlphabet ht` (and, at the
printed digit level, `t.glueLabelVector d` for `d : ℕ`):

* for `Aₙ` and residue `a ∈ ℤ/(n+1)`, it is `typeACosetRepresentative n a.val` (the Bourbaki
  fundamental weight `ϖₖ` for `1 ≤ k ≤ n`, and `0` for `k = 0`);
* for `Dₙ` and printed digits `0, 1, 2, 3` (`0`, spinor, vector, cospinor), it is `0`,
  `typeDSpinorWeight n`, `typeDVectorWeight n`, `typeDCospinorWeight n`;
* for `E₆` and residues `0, 1, 2 ∈ ℤ/3`, it is `0`, `typeE₆MinusculeWeight`,
  `-typeE₆MinusculeWeight`;
* for `E₇` and residues `0, 1 ∈ ℤ/2`, it is `0`, `typeE₇MinusculeWeight`;
* for `E₈`, it is `0`.

Bundled in `(t.rootLattice ht).dualCarrier` as `t.glueRepresentative hv ht a`, this vector:

* represents `t.glueAlphabetIsometry hv ht a` (`mk_glueRepresentative`);
* attains the coset minimum `t.glueMinimum ht a` (`form_glueRepresentative_self` and
  `form_glueRepresentative_self_le`);
* realizes the quadratic half-norm, polar bilinear pairing, and additive order of `t.glueAlphabet`
  directly in the ambient rational form and root-lattice carrier
  (`quadratic_glueAlphabet_eq_form_glueRepresentative_self_div_two`,
  `pairing_glueAlphabet_eq_form_glueRepresentative`,
  `zsmul_eq_zero_iff_zsmul_glueRepresentativeVector_mem_carrier`,
  `addOrderOf_eq_addOrderOf_mk_glueRepresentative`).

Applied componentwise to a finite family `t : ι → DynkinType`, `glueWordRepresentativeVector` gives
computable shortest dual-lattice representatives for glue words, yielding choice-free generator and
coset-membership formulas for `TauCeti.DynkinType.gluedLattice`
(`gluedLattice_carrier_eq_sup_span_glueWordRepresentativeVector`,
`mem_gluedLattice_carrier_iff_exists_sub_mem`, `mem_gluedLattice_carrier_iff_exists_int`).

## Main declarations

* `TauCeti.DynkinType.glueLabelVector`: computable simple-root coordinates of a printed glue digit.
* `TauCeti.DynkinType.glueRepresentativeVector` and `TauCeti.DynkinType.glueRepresentative`:
  computable simple-root coordinates and bundled dual-carrier representative of a glue label.
* `TauCeti.DynkinType.mk_glueRepresentative` and `TauCeti.DynkinType.form_glueRepresentative_self`:
  `glueRepresentative` lies in the coset `glueAlphabetIsometry` and has squared norm `glueMinimum`.
* `TauCeti.DynkinType.pairing_glueAlphabet_eq_form_glueRepresentative` and
  `TauCeti.DynkinType.zsmul_eq_zero_iff_zsmul_glueRepresentativeVector_mem_carrier`: bilinear
  pairings and torsion conditions in `glueAlphabet` read off `glueRepresentativeVector`.
* `TauCeti.DynkinType.glueWordRepresentativeVector` and `TauCeti.DynkinType.glueWordRepresentative`:
  componentwise shortest representatives of glue words.
* `TauCeti.DynkinType.gluedLattice_carrier_eq_sup_span_glueWordRepresentativeVector` and
  `TauCeti.DynkinType.mem_gluedLattice_carrier_iff_exists_int`: explicit generators and coordinate
  coset membership for `gluedLattice`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I, IV, V, VI.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3, 6--8 and Chapter 16 §1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

private theorem isNondegenerate_rootLattice_A (n : ℕ) (ht : (A n).IsSimplyLaced) :
    @IsNondegenerate (Fin n → ℚ) _ (Pi.Function.module _ _ _) ((A n).rootLattice ht) :=
  inferInstanceAs ((A n).rootLattice ht).IsNondegenerate

private theorem isNondegenerate_rootLattice_E6 (ht : E6.IsSimplyLaced) :
    @IsNondegenerate (Fin 6 → ℚ) _ (Pi.Function.module _ _ _) (E6.rootLattice ht) :=
  inferInstanceAs (E6.rootLattice ht).IsNondegenerate

private theorem isNondegenerate_rootLattice_E7 (ht : E7.IsSimplyLaced) :
    @IsNondegenerate (Fin 7 → ℚ) _ (Pi.Function.module _ _ _) (E7.rootLattice ht) :=
  inferInstanceAs (E7.rootLattice ht).IsNondegenerate

private theorem isNondegenerate_rootLattice_E8 (ht : E8.IsSimplyLaced) :
    @IsNondegenerate (Fin 8 → ℚ) _ (Pi.Function.module _ _ _) (E8.rootLattice ht) :=
  inferInstanceAs (E8.rootLattice ht).IsNondegenerate

attribute [local instance] isNondegenerate_rootLattice_A isNondegenerate_rootLattice_E6
  isNondegenerate_rootLattice_E7 isNondegenerate_rootLattice_E8

/-! Term-mode transport helpers across equal lattices on the same ambient space. -/

private theorem form_eq_zero_of_eq_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : IntegralLattice V) {x : V} (hx : x = 0) :
    L.form x x = 0 := by
  rw [hx, map_zero]

private theorem mk_eq_zero_of_val_eq_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    {L : IntegralLattice V} (u : L.dualCarrier) (hu : (u : V) = 0) :
    (Submodule.Quotient.mk u : L.DiscriminantGroup) = 0 :=
  (L.discriminantGroup_mk_eq_zero_iff u).mpr (hu.symm ▸ L.carrier.zero_mem)

/-! ## Computable representatives of printed Conway--Sloane digits -/

/-- **Computable shortest dual-lattice vector of a printed Conway--Sloane glue digit** `d` of `t`
in Bourbaki simple-root coordinates `Fin t.rank → ℚ`.  Digits outside the valid range (other than
`Aₙ`, where `typeACosetRepresentative` is defined uniformly for all `d`) evaluate to `0`. -/
def glueLabelVector : (t : DynkinType) → ℕ → Fin t.rank → ℚ
  | A n, d => typeACosetRepresentative n d
  | D n, d =>
    if d = 1 then typeDSpinorWeight n
    else if d = 2 then typeDVectorWeight n
    else if d = 3 then typeDCospinorWeight n
    else 0
  | E6, d =>
    if d = 1 then typeE₆MinusculeWeight
    else if d = 2 then -typeE₆MinusculeWeight
    else 0
  | E7, d => if d = 1 then typeE₇MinusculeWeight else 0
  | _, _ => 0

@[simp]
theorem glueLabelVector_A (n d : ℕ) :
    (A n).glueLabelVector d = typeACosetRepresentative n d :=
  (rfl)

@[simp]
theorem glueLabelVector_D (n d : ℕ) :
    (D n).glueLabelVector d =
      if d = 1 then typeDSpinorWeight n
      else if d = 2 then typeDVectorWeight n
      else if d = 3 then typeDCospinorWeight n
      else 0 :=
  (rfl)

@[simp]
theorem glueLabelVector_E6 (d : ℕ) :
    E6.glueLabelVector d =
      if d = 1 then typeE₆MinusculeWeight
      else if d = 2 then -typeE₆MinusculeWeight
      else 0 :=
  (rfl)

@[simp]
theorem glueLabelVector_E7 (d : ℕ) :
    E7.glueLabelVector d = if d = 1 then typeE₇MinusculeWeight else 0 :=
  (rfl)

@[simp]
theorem glueLabelVector_E8 (d : ℕ) : E8.glueLabelVector d = 0 :=
  (rfl)

/-- Digit `0` maps to the zero vector for every Dynkin type. -/
@[simp]
theorem glueLabelVector_zero (t : DynkinType) : t.glueLabelVector 0 = 0 := by
  cases t with
  | A n => exact typeACosetRepresentative_zero n
  | D n =>
    funext (j : Fin n)
    simp only [glueLabelVector_D, OfNat.zero_ne_ofNat, zero_ne_one, ↓reduceIte]
    -- `(0 : Fin (D n).rank → ℚ) j` is definitionally `0`.
    rfl
  | E6 =>
    funext (j : Fin 6)
    simp only [glueLabelVector_E6, OfNat.zero_ne_ofNat, zero_ne_one, ↓reduceIte]
    -- `(0 : Fin E6.rank → ℚ) j` is definitionally `0`.
    rfl
  | E7 =>
    funext (j : Fin 7)
    simp only [glueLabelVector_E7, zero_ne_one, ↓reduceIte]
    -- `(0 : Fin E7.rank → ℚ) j` is definitionally `0`.
    rfl
  | E8 | B _ | C _ | F4 | G2 => rfl

/-- `rootLatticeIsometryOfEq` preserves `glueLabelVector`. -/
@[simp]
theorem rootLatticeIsometryOfEq_glueLabelVector {t s : DynkinType} (h : t = s)
    (ht : t.IsSimplyLaced) (hs : s.IsSimplyLaced) (d : ℕ) :
    t.rootLatticeIsometryOfEq ht h hs (t.glueLabelVector d) = s.glueLabelVector d := by
  subst h
  rw [rootLatticeIsometryOfEq_rfl, Isometry.refl_apply]

/-- Every `glueLabelVector` of a valid simply-laced Dynkin type lies in the dual carrier of its
root lattice. -/
theorem glueLabelVector_mem_dualCarrier (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (d : ℕ) : t.glueLabelVector d ∈ (t.rootLattice ht).dualCarrier := by
  cases t with
  | A n =>
    exact (SetLike.ext_iff.mp (congrArg IntegralLattice.dualCarrier (rootLattice_A n ht))
      (typeACosetRepresentative n d)).mpr (typeACosetRepresentative_mem_dualCarrier n d)
  | D n =>
    have hn : 4 ≤ n := valid_D.mp hv
    by_cases h1 : d = 1
    · subst h1; exact typeDSpinorWeight_mem_dualCarrier hn ht
    by_cases h2 : d = 2
    · subst h2; exact typeDVectorWeight_mem_dualCarrier hn ht
    by_cases h3 : d = 3
    · subst h3; exact typeDCospinorWeight_mem_dualCarrier hn ht
    have h0 : (D n).glueLabelVector d = 0 := by
      funext (j : Fin n)
      simp only [glueLabelVector_D, h1, h2, h3, ↓reduceIte]
      -- `(0 : Fin (D n).rank → ℚ) j` is definitionally `0`.
      rfl
    exact Eq.mp (congrArg (· ∈ ((D n).rootLattice ht).dualCarrier) h0.symm)
      ((D n).rootLattice ht).dualCarrier.zero_mem
  | E6 =>
    by_cases h1 : d = 1
    · subst h1
      exact (SetLike.ext_iff.mp (congrArg IntegralLattice.dualCarrier (rootLattice_E6 ht))
        typeE₆MinusculeWeight).mpr typeE₆MinusculeWeight_mem_dualCarrier
    by_cases h2 : d = 2
    · subst h2
      exact (SetLike.ext_iff.mp (congrArg IntegralLattice.dualCarrier (rootLattice_E6 ht))
        (-typeE₆MinusculeWeight)).mpr
        (typeE₆RootLattice.dualCarrier.neg_mem typeE₆MinusculeWeight_mem_dualCarrier)
    have h0 : E6.glueLabelVector d = 0 := by
      funext (j : Fin 6)
      simp only [glueLabelVector_E6, h1, h2, ↓reduceIte]
      -- `(0 : Fin E6.rank → ℚ) j` is definitionally `0`.
      rfl
    exact Eq.mp (congrArg (· ∈ (E6.rootLattice ht).dualCarrier) h0.symm)
      (E6.rootLattice ht).dualCarrier.zero_mem
  | E7 =>
    by_cases h1 : d = 1
    · subst h1
      exact (SetLike.ext_iff.mp (congrArg IntegralLattice.dualCarrier (rootLattice_E7 ht))
        typeE₇MinusculeWeight).mpr typeE₇MinusculeWeight_mem_dualCarrier
    have h0 : E7.glueLabelVector d = 0 := by
      funext (j : Fin 7)
      simp only [glueLabelVector_E7, h1, ↓reduceIte]
      -- `(0 : Fin E7.rank → ℚ) j` is definitionally `0`.
      rfl
    exact Eq.mp (congrArg (· ∈ (E7.rootLattice ht).dualCarrier) h0.symm)
      (E7.rootLattice ht).dualCarrier.zero_mem
  | E8 => exact (E8.rootLattice ht).dualCarrier.zero_mem
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- For every valid digit `d : Fin t.glueLabelCount`, `t.glueLabelVector d.val` represents the
discriminant class of `t.glueLabelEquiv ht d`. -/
theorem mk_glueLabelVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (d : Fin t.glueLabelCount) :
    (Submodule.Quotient.mk
        ⟨t.glueLabelVector d.val, t.glueLabelVector_mem_dualCarrier hv ht d.val⟩ :
        (t.rootLattice ht).DiscriminantGroup) =
      t.glueAlphabetIsometry hv ht (t.glueLabelEquiv ht d) := by
  cases t with
  | A n =>
    have hd : ((d.val : ZMod (n + 1)).val) = d.val := ZMod.val_natCast_of_lt d.isLt
    have heq : (⟨(A n).glueLabelVector d.val, (A n).glueLabelVector_mem_dualCarrier hv ht d.val⟩ :
          ((A n).rootLattice ht).dualCarrier) =
        (Isometry.ofEq (rootLattice_A n ht).symm).dualCarrierEquiv
          (typeACosetRepresentativeDual n (d.val : ZMod (n + 1)).val) :=
      Subtype.ext <| ((glueLabelVector_A n d.val).trans
        (congrArg (typeACosetRepresentative n) hd.symm)).trans
        ((Isometry.coe_dualCarrierEquiv_apply _ _).trans
          ((Isometry.ofEq_apply (rootLattice_A n ht).symm _).trans
            (coe_typeACosetRepresentativeDual n _))).symm
    refine (congrArg Submodule.Quotient.mk heq).trans ?_
    refine (Isometry.discriminantGroupEquiv_mk (Isometry.ofEq (rootLattice_A n ht).symm)
      (typeACosetRepresentativeDual n (d.val : ZMod (n + 1)).val)).symm.trans ?_
    rw [mk_typeACosetRepresentativeDual_val, glueLabelEquiv_A, glueAlphabetIsometry_A_apply]
  | D n =>
    have hn4 : 4 ≤ n := valid_D.mp hv
    have : NeZero n := ⟨by omega⟩
    obtain ⟨d, hd⟩ := d
    simp only [glueLabelCount] at hd
    rcases Nat.even_or_odd n with hpar | hpar
    · rw [glueAlphabetIsometry_D_apply_of_even n hv ht hpar, glueLabelEquiv_D_of_even n ht hpar]
      interval_cases d
      · refine (mk_eq_zero_of_val_eq_zero _ (glueLabelVector_zero (D n))).trans ?_
        rw [Nat.zero_div, Nat.zero_mod, Nat.cast_zero, Prod.mk_zero_zero, map_zero, map_zero]
      · have heq : (⟨(D n).glueLabelVector 1, (D n).glueLabelVector_mem_dualCarrier hv ht 1⟩ :
              ((D n).rootLattice ht).dualCarrier) = typeDSpinorWeightDual n hn4 ht :=
          Subtype.ext (by simp)
        rw [heq, mk_typeDSpinorWeightDual]
        simp only [Nat.reduceDiv, Nat.cast_zero, Nat.reduceMod, Nat.cast_one,
          zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one]
      · have heq : (⟨(D n).glueLabelVector 2, (D n).glueLabelVector_mem_dualCarrier hv ht 2⟩ :
              ((D n).rootLattice ht).dualCarrier) = typeDVectorWeightDual n hn4 ht :=
          Subtype.ext (by simp)
        rw [heq, mk_typeDVectorWeightDual]
        simp only [Nat.div_self zero_lt_two, Nat.cast_one, Nat.mod_self, Nat.cast_zero,
          zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_zero]
      · have heq : (⟨(D n).glueLabelVector 3, (D n).glueLabelVector_mem_dualCarrier hv ht 3⟩ :
              ((D n).rootLattice ht).dualCarrier) = typeDCospinorWeightDual n hn4 ht :=
          Subtype.ext (by simp)
        rw [heq, mk_typeDCospinorWeightDual]
        simp only [Nat.reduceDiv, Nat.cast_one, Nat.reduceMod,
          zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one]
    · rw [glueAlphabetIsometry_D_apply_of_odd n hv ht hpar, glueLabelEquiv_D_of_odd n ht hpar]
      interval_cases d
      · refine (mk_eq_zero_of_val_eq_zero _ (glueLabelVector_zero (D n))).trans ?_
        rw [Nat.cast_zero, map_zero, map_zero]
      · have heq : (⟨(D n).glueLabelVector 1, (D n).glueLabelVector_mem_dualCarrier hv ht 1⟩ :
              ((D n).rootLattice ht).dualCarrier) = typeDSpinorWeightDual n hn4 ht :=
          Subtype.ext (by simp)
        rw [heq, mk_typeDSpinorWeightDual, Nat.cast_one,
          zmodFourAddEquivCheckerboardDiscriminantGroup_apply_one n hpar]
      · have heq : (⟨(D n).glueLabelVector 2, (D n).glueLabelVector_mem_dualCarrier hv ht 2⟩ :
              ((D n).rootLattice ht).dualCarrier) = typeDVectorWeightDual n hn4 ht :=
          Subtype.ext (by simp)
        rw [heq, mk_typeDVectorWeightDual, Nat.cast_ofNat,
          zmodFourAddEquivCheckerboardDiscriminantGroup_apply_two n hpar]
      · have heq : (⟨(D n).glueLabelVector 3, (D n).glueLabelVector_mem_dualCarrier hv ht 3⟩ :
              ((D n).rootLattice ht).dualCarrier) = typeDCospinorWeightDual n hn4 ht :=
          Subtype.ext (by simp)
        rw [heq, mk_typeDCospinorWeightDual, Nat.cast_ofNat,
          zmodFourAddEquivCheckerboardDiscriminantGroup_apply_three n hpar]
  | E6 =>
    obtain ⟨d, hd⟩ := d
    simp only [glueLabelCount] at hd
    rw [glueLabelEquiv_E6, glueAlphabetIsometry_E6_apply]
    interval_cases d
    · refine (mk_eq_zero_of_val_eq_zero _ (glueLabelVector_zero E6)).trans ?_
      rw [Nat.cast_zero, map_zero, map_zero]
      -- The two zero classes agree across `Fin E6.rank` and `Fin 6`.
      rfl
    · have heq : (⟨E6.glueLabelVector 1, E6.glueLabelVector_mem_dualCarrier hv ht 1⟩ :
            (E6.rootLattice ht).dualCarrier) =
          (Isometry.ofEq (rootLattice_E6 ht).symm).dualCarrierEquiv typeE₆MinusculeWeightDual :=
        Subtype.ext <| ((Isometry.coe_dualCarrierEquiv_apply _ _).trans
          ((Isometry.ofEq_apply (rootLattice_E6 ht).symm _).trans
            coe_typeE₆MinusculeWeightDual)).symm
      refine (congrArg Submodule.Quotient.mk heq).trans ?_
      refine (Isometry.discriminantGroupEquiv_mk (Isometry.ofEq (rootLattice_E6 ht).symm)
        typeE₆MinusculeWeightDual).symm.trans ?_
      rw [mk_typeE₆MinusculeWeightDual, Nat.cast_one, typeE₆DiscriminantGroupEquiv_apply_one]
    · have heq : (⟨E6.glueLabelVector 2, E6.glueLabelVector_mem_dualCarrier hv ht 2⟩ :
            (E6.rootLattice ht).dualCarrier) =
          (Isometry.ofEq (rootLattice_E6 ht).symm).dualCarrierEquiv (-typeE₆MinusculeWeightDual) :=
        Subtype.ext <| ((Isometry.coe_dualCarrierEquiv_apply _ _).trans
          ((Isometry.ofEq_apply (rootLattice_E6 ht).symm _).trans
            ((Submodule.coe_neg _ typeE₆MinusculeWeightDual).trans
              (congrArg Neg.neg coe_typeE₆MinusculeWeightDual)))).symm
      have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
      refine (congrArg Submodule.Quotient.mk heq).trans ?_
      refine (Isometry.discriminantGroupEquiv_mk (Isometry.ofEq (rootLattice_E6 ht).symm)
        (-typeE₆MinusculeWeightDual)).symm.trans ?_
      refine congrArg (Isometry.ofEq (rootLattice_E6 ht).symm).discriminantGroupEquiv ?_
      rw [Submodule.Quotient.mk_neg, mk_typeE₆MinusculeWeightDual, h2, map_neg,
        typeE₆DiscriminantGroupEquiv_apply_one]
  | E7 =>
    obtain ⟨d, hd⟩ := d
    simp only [glueLabelCount] at hd
    rw [glueLabelEquiv_E7, glueAlphabetIsometry_E7_apply]
    interval_cases d
    · refine (mk_eq_zero_of_val_eq_zero _ (glueLabelVector_zero E7)).trans ?_
      rw [Nat.cast_zero, map_zero, map_zero]
      -- The two zero classes agree across `Fin E7.rank` and `Fin 7`.
      rfl
    · have heq : (⟨E7.glueLabelVector 1, E7.glueLabelVector_mem_dualCarrier hv ht 1⟩ :
            (E7.rootLattice ht).dualCarrier) =
          (Isometry.ofEq (rootLattice_E7 ht).symm).dualCarrierEquiv typeE₇MinusculeWeightDual :=
        Subtype.ext <| ((Isometry.coe_dualCarrierEquiv_apply _ _).trans
          ((Isometry.ofEq_apply (rootLattice_E7 ht).symm _).trans
            coe_typeE₇MinusculeWeightDual)).symm
      refine (congrArg Submodule.Quotient.mk heq).trans ?_
      refine (Isometry.discriminantGroupEquiv_mk (Isometry.ofEq (rootLattice_E7 ht).symm)
        typeE₇MinusculeWeightDual).symm.trans ?_
      rw [mk_typeE₇MinusculeWeightDual, Nat.cast_one, typeE₇DiscriminantGroupEquiv_apply_one]
  | E8 =>
    rw [glueLabelEquiv_E8, map_zero]
    exact mk_eq_zero_of_val_eq_zero
      ⟨E8.glueLabelVector d.val, E8.glueLabelVector_mem_dualCarrier hv ht d.val⟩
      (glueLabelVector_E8 d.val)
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **Squared norm of `glueLabelVector`.**  For every valid digit `d : Fin t.glueLabelCount`,
`t.glueLabelVector d.val` has squared norm `t.glueLabelMinimum d.val`. -/
@[simp]
theorem form_glueLabelVector_self (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (d : Fin t.glueLabelCount) :
    (t.rootLattice ht).form (t.glueLabelVector d.val) (t.glueLabelVector d.val) =
      t.glueLabelMinimum d.val := by
  cases t with
  | A n =>
    exact (LinearMap.congr_fun (LinearMap.congr_fun
      (congrArg IntegralLattice.form (rootLattice_A n ht)) _) _).trans
      (form_typeACosetRepresentative_self d.isLt.le)
  | D n =>
    have hn4 : 4 ≤ n := valid_D.mp hv
    obtain ⟨d, hd⟩ := d
    simp only [glueLabelCount] at hd
    interval_cases d
    · exact form_eq_zero_of_eq_zero _ (glueLabelVector_zero (D n))
    · exact form_typeDSpinorWeight_self hn4 ht
    · exact form_typeDVectorWeight_self hn4 ht
    · exact form_typeDCospinorWeight_self hn4 ht
  | E6 =>
    obtain ⟨d, hd⟩ := d
    simp only [glueLabelCount] at hd
    interval_cases d
    · exact form_eq_zero_of_eq_zero _ (glueLabelVector_zero E6)
    · exact (LinearMap.congr_fun (LinearMap.congr_fun
        (congrArg IntegralLattice.form (rootLattice_E6 ht)) _) _).trans
        form_typeE₆MinusculeWeight_self
    · have hneg :
          typeE₆RootLattice.form (-typeE₆MinusculeWeight) (-typeE₆MinusculeWeight) = 4 / 3 := by
        rw [LinearMap.map_neg₂, map_neg, neg_neg, form_typeE₆MinusculeWeight_self]
      exact (LinearMap.congr_fun (LinearMap.congr_fun
        (congrArg IntegralLattice.form (rootLattice_E6 ht)) _) _).trans hneg
  | E7 =>
    obtain ⟨d, hd⟩ := d
    simp only [glueLabelCount] at hd
    interval_cases d
    · exact form_eq_zero_of_eq_zero _ (glueLabelVector_zero E7)
    · exact (LinearMap.congr_fun (LinearMap.congr_fun
        (congrArg IntegralLattice.form (rootLattice_E7 ht)) _) _).trans
        form_typeE₇MinusculeWeight_self
  | E8 =>
    obtain ⟨d, hd⟩ := d
    simp only [glueLabelCount] at hd
    interval_cases d
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

theorem glueRepresentativeVector_def (t : DynkinType) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    t.glueRepresentativeVector ht a = t.glueLabelVector ((t.glueLabelEquiv ht).symm a).val :=
  (rfl)

/-- On a printed digit `d : Fin t.glueLabelCount`, `glueRepresentativeVector` agrees with
`glueLabelVector d.val`. -/
@[simp]
theorem glueRepresentativeVector_glueLabelEquiv (t : DynkinType) (ht : t.IsSimplyLaced)
    (d : Fin t.glueLabelCount) :
    t.glueRepresentativeVector ht (t.glueLabelEquiv ht d) = t.glueLabelVector d.val := by
  rw [glueRepresentativeVector_def, Equiv.symm_apply_apply]

/-- The zero glue label is represented by the zero vector. -/
@[simp]
theorem glueRepresentativeVector_zero (t : DynkinType) (ht : t.IsSimplyLaced) :
    t.glueRepresentativeVector ht 0 = 0 := by
  rw [glueRepresentativeVector_def, glueLabelEquiv_symm_zero, glueLabelVector_zero]

/-- On `Aₙ`, `glueRepresentativeVector` is `typeACosetRepresentative n a.val`. -/
@[simp]
theorem glueRepresentativeVector_A (n : ℕ) (ht : (A n).IsSimplyLaced) (a : ZMod (n + 1)) :
    (A n).glueRepresentativeVector ht a = typeACosetRepresentative n a.val := by
  refine ((A n).glueRepresentativeVector_def ht a).trans ?_
  exact congrArg (A n).glueLabelVector (congrArg Fin.val (glueLabelEquiv_A_symm_apply n ht a))

/-- On `E₆`, `glueRepresentativeVector` sends `0, 1, 2 ∈ ℤ/3` to `0`, `ϖ₁`, `-ϖ₁`. -/
@[simp]
theorem glueRepresentativeVector_E6 (ht : E6.IsSimplyLaced) (a : ZMod 3) :
    E6.glueRepresentativeVector ht a =
      if a = 1 then typeE₆MinusculeWeight
      else if a = 2 then -typeE₆MinusculeWeight
      else 0 := by
  rcases (by decide : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2) a with rfl | rfl | rfl
  · have h01 : (0 : ZMod 3) ≠ 1 := by decide
    have h02 : (0 : ZMod 3) ≠ 2 := by decide
    simp only [h01, h02, ↓reduceIte]
    exact E6.glueRepresentativeVector_zero ht
  · simp only [↓reduceIte]
    exact (congrArg (E6.glueRepresentativeVector ht)
      (glueLabelEquiv_E6 ht ⟨1, by decide⟩).symm).trans
      ((E6.glueRepresentativeVector_glueLabelEquiv ht ⟨1, by decide⟩).trans (by simp))
  · have h21 : (2 : ZMod 3) ≠ 1 := by decide
    simp only [h21, ↓reduceIte]
    exact (congrArg (E6.glueRepresentativeVector ht)
      (glueLabelEquiv_E6 ht ⟨2, by decide⟩).symm).trans
      ((E6.glueRepresentativeVector_glueLabelEquiv ht ⟨2, by decide⟩).trans (by simp))

/-- On `E₇`, `glueRepresentativeVector` sends `0, 1 ∈ ℤ/2` to `0`, `ϖ₇`. -/
@[simp]
theorem glueRepresentativeVector_E7 (ht : E7.IsSimplyLaced) (a : ZMod 2) :
    E7.glueRepresentativeVector ht a = if a = 1 then typeE₇MinusculeWeight else 0 := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a with rfl | rfl
  · simp only [zero_ne_one, ↓reduceIte]
    exact E7.glueRepresentativeVector_zero ht
  · simp only [↓reduceIte]
    exact (congrArg (E7.glueRepresentativeVector ht)
      (glueLabelEquiv_E7 ht ⟨1, by decide⟩).symm).trans
      ((E7.glueRepresentativeVector_glueLabelEquiv ht ⟨1, by decide⟩).trans (by simp))

/-- On `E₈`, `glueRepresentativeVector` is identically `0`. -/
@[simp]
theorem glueRepresentativeVector_E8 (ht : E8.IsSimplyLaced) (a : E8.glueAlphabet ht) :
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

@[simp]
theorem coe_glueRepresentative (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    (t.glueRepresentative hv ht a : Fin t.rank → ℚ) = t.glueRepresentativeVector ht a :=
  (rfl)

@[simp]
theorem glueRepresentative_zero (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    t.glueRepresentative hv ht 0 = 0 :=
  Subtype.ext (t.glueRepresentativeVector_zero ht)

/-- **`glueRepresentative` represents the discriminant coset `glueAlphabetIsometry`.** -/
@[simp]
theorem mk_glueRepresentative (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    (Submodule.Quotient.mk (t.glueRepresentative hv ht a) :
        (t.rootLattice ht).DiscriminantGroup) =
      t.glueAlphabetIsometry hv ht a := by
  obtain ⟨d, rfl⟩ := (t.glueLabelEquiv ht).surjective a
  have heq : t.glueRepresentative hv ht (t.glueLabelEquiv ht d) =
      ⟨t.glueLabelVector d.val, t.glueLabelVector_mem_dualCarrier hv ht d.val⟩ :=
    Subtype.ext (t.glueRepresentativeVector_glueLabelEquiv ht d)
  rw [heq, mk_glueLabelVector]

/-- **`glueRepresentativeVector` attains the shortest norm `t.glueMinimum ht a`.** -/
@[simp]
theorem form_glueRepresentativeVector_self (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    (t.rootLattice ht).form (t.glueRepresentativeVector ht a) (t.glueRepresentativeVector ht a) =
      t.glueMinimum ht a := by
  obtain ⟨d, rfl⟩ := (t.glueLabelEquiv ht).surjective a
  rw [glueRepresentativeVector_glueLabelEquiv,
    form_glueLabelVector_self t hv ht d, glueMinimum_glueLabelEquiv]

/-- **`glueRepresentative` attains the shortest norm `t.glueMinimum ht a`.** -/
theorem form_glueRepresentative_self (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    (t.rootLattice ht).form (t.glueRepresentative hv ht a) (t.glueRepresentative hv ht a) =
      t.glueMinimum ht a :=
  t.form_glueRepresentativeVector_self hv ht a

/-- **Minimality of `glueRepresentative`**: no dual vector in the coset `t.glueAlphabetIsometry hv
ht a` has strictly smaller squared norm than `t.glueRepresentative hv ht a`. -/
theorem form_glueRepresentative_self_le (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) (x : (t.rootLattice ht).dualCarrier)
    (hx : (Submodule.Quotient.mk x : (t.rootLattice ht).DiscriminantGroup) =
      t.glueAlphabetIsometry hv ht a) :
    (t.rootLattice ht).form (t.glueRepresentative hv ht a) (t.glueRepresentative hv ht a) ≤
      (t.rootLattice ht).form x x := by
  rw [form_glueRepresentative_self]
  exact (t.isLeast_glueMinimum hv ht a).2 ⟨x, hx, rfl⟩

/-- **Quadratic half-norm of a glue label from its explicit representative**:
`q(a) = ⟨v_a, v_a⟩ / 2 mod ℤ`. -/
theorem quadratic_glueAlphabet_eq_form_glueRepresentative_self_div_two (t : DynkinType)
    (hv : t.Valid) (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    (t.glueAlphabet ht).quadratic a =
      (((t.rootLattice ht).form (t.glueRepresentativeVector ht a)
          (t.glueRepresentativeVector ht a) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [form_glueRepresentativeVector_self t hv ht a]
  exact quadratic_glueAlphabet_eq_glueMinimum_div_two t ht a

/-- **Polar bilinear pairing of two glue labels from their explicit representatives**:
`b(a, b) = ⟨v_a, v_b⟩ mod ℤ`. -/
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

/-- **Torsion of a glue label in terms of its explicit representative**: an integer multiple
`k • a` vanishes in `t.glueAlphabet ht` if and only if `k • v_a` belongs to the root-lattice
carrier. -/
theorem zsmul_eq_zero_iff_zsmul_glueRepresentativeVector_mem_carrier (t : DynkinType)
    (hv : t.Valid) (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) (k : ℤ) :
    k • a = 0 ↔ k • t.glueRepresentativeVector ht a ∈ (t.rootLattice ht).carrier := by
  have hsmul : (t.glueAlphabetIsometry hv ht) (k • a) =
      (Submodule.Quotient.mk (k • t.glueRepresentative hv ht a) :
        (t.rootLattice ht).DiscriminantGroup) :=
    (map_zsmul (t.glueAlphabetIsometry hv ht) k a).trans
      ((congrArg (k • ·) (t.mk_glueRepresentative hv ht a).symm).trans
        (Submodule.Quotient.mk_smul _ k (t.glueRepresentative hv ht a)).symm)
  exact (map_eq_zero_iff (t.glueAlphabetIsometry hv ht)
    (t.glueAlphabetIsometry hv ht).injective).symm.trans
    ((Iff.of_eq (congrArg (· = 0) hsmul)).trans (discriminantGroup_mk_eq_zero_iff _ _))

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
`w : ∀ i, (t i).glueAlphabet (ht i)` in the ambient space `∀ i, Fin (t i).rank → ℚ` of the
orthogonal sum of root lattices. -/
def glueWordRepresentativeVector {ι : Type v} (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    ∀ i, Fin (t i).rank → ℚ :=
  fun i ↦ (t i).glueRepresentativeVector (ht i) (w i)

theorem glueWordRepresentativeVector_def {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordRepresentativeVector t ht w = fun i ↦ (t i).glueRepresentativeVector (ht i) (w i) :=
  (rfl)

@[simp]
theorem glueWordRepresentativeVector_apply {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (w : ∀ i, (t i).glueAlphabet (ht i)) (i : ι) :
    glueWordRepresentativeVector t ht w i = (t i).glueRepresentativeVector (ht i) (w i) :=
  (rfl)

@[simp]
theorem glueWordRepresentativeVector_zero {ι : Type v} (t : ι → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) :
    glueWordRepresentativeVector t ht 0 = 0 := by
  ext i j
  simp

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
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  ⟨glueWordRepresentativeVector t ht w, glueWordRepresentativeVector_mem_dualCarrier t ht hv w⟩

@[simp]
theorem coe_glueWordRepresentative (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (glueWordRepresentative t ht hv w : ∀ i, Fin (t i).rank → ℚ) =
      glueWordRepresentativeVector t ht w :=
  (rfl)

@[simp]
theorem glueWordRepresentative_zero (hv : ∀ i, (t i).Valid) :
    glueWordRepresentative t ht hv 0 = 0 :=
  Subtype.ext (glueWordRepresentativeVector_zero t ht)

/-- **`glueWordRepresentative` represents the discriminant coset `glueWordIsometry`.** -/
@[simp]
theorem mk_glueWordRepresentative (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (Submodule.Quotient.mk (glueWordRepresentative t ht hv w) :
        (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      glueWordIsometry t ht hv w := by
  apply (discriminantGroupPiEquiv _).injective
  ext i
  rw [discriminantGroupPiEquiv_mk, discriminantGroupPiEquiv_glueWordIsometry,
    ← mk_glueRepresentative (t i) (hv i) (ht i) (w i)]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (coe_piDualCarrierEquiv_apply _ _ i))

/-- **`glueWordRepresentative` attains the shortest norm `∑ i, (t i).glueMinimum (ht i) (w i)`.** -/
theorem form_glueWordRepresentative_self (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordRepresentative t ht hv w)
        (glueWordRepresentative t ht hv w) =
      ∑ i, (t i).glueMinimum (ht i) (w i) := by
  rw [coe_glueWordRepresentative, pi_form, piForm_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (t i).form_glueRepresentativeVector_self (hv i) (ht i) (w i)

/-- Same as `form_glueWordRepresentative_self`, written directly on
`glueWordRepresentativeVector`. -/
theorem form_glueWordRepresentativeVector_self (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordRepresentativeVector t ht w)
        (glueWordRepresentativeVector t ht w) =
      ∑ i, (t i).glueMinimum (ht i) (w i) :=
  form_glueWordRepresentative_self t ht hv w

/-- **Minimality of `glueWordRepresentative`**: no dual vector in the coset `glueWordIsometry t ht
hv w` has smaller squared norm. -/
theorem form_glueWordRepresentative_self_le (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i))
    (x : (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier)
    (hx : (Submodule.Quotient.mk x : (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      glueWordIsometry t ht hv w) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordRepresentative t ht hv w)
        (glueWordRepresentative t ht hv w) ≤
      (pi fun i ↦ (t i).rootLattice (ht i)).form x x := by
  rw [form_glueWordRepresentative_self]
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
H hH).carrier` is spanned over `ℤ` by the root-lattice carrier and the computable vectors
`glueWordRepresentativeVector t ht w` for `w ∈ G`. -/
theorem gluedLattice_carrier_eq_sup_span_glueWordRepresentativeVector (hv : ∀ i, (t i).Valid)
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    {G : Set (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i))}
    (hG : AddSubgroup.closure G = H) :
    (gluedLattice t ht hv H hH).carrier =
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier ⊔
        Submodule.span ℤ (glueWordRepresentativeVector t ht '' G) :=
  gluedLattice_carrier_eq_sup_span t ht hv H hH hG (glueWordRepresentative t ht hv)
    fun w _ ↦ mk_glueWordRepresentative t ht hv w

/-- **Coset decomposition of a glued lattice**: a rational vector `x` lies in `gluedLattice` if and
only if it differs from `glueWordRepresentativeVector t ht w`, for some glue word `w ∈ H`, by a
vector of the orthogonal sum of root lattices. -/
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
    set w := (glueWordIsometry t ht hv).toAddEquiv.symm (Submodule.Quotient.mk ⟨x, hx⟩)
    refine ⟨w, hw, ?_⟩
    have hmk : (Submodule.Quotient.mk ⟨x, hx⟩ :
          (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
        Submodule.Quotient.mk (glueWordRepresentative t ht hv w) := by
      rw [mk_glueWordRepresentative]
      exact ((glueWordIsometry t ht hv).toAddEquiv.apply_symm_apply _).symm
    exact (discriminantGroup_mk_eq_iff _ ⟨x, hx⟩ (glueWordRepresentative t ht hv w)).mp hmk
  · rintro ⟨w, hw, hsub⟩
    have hx : x ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier := by
      have hsub' := (pi fun i ↦ (t i).rootLattice (ht i)).le_dualCarrier hsub
      have hrep := glueWordRepresentativeVector_mem_dualCarrier t ht hv w
      simpa only [sub_add_cancel] using
        (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier.add_mem hsub' hrep
    refine ⟨hx, ?_⟩
    have hmk : (Submodule.Quotient.mk ⟨x, hx⟩ :
          (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
        (glueWordIsometry t ht hv).toAddEquiv w := by
      exact ((discriminantGroup_mk_eq_iff _ ⟨x, hx⟩
        (glueWordRepresentative t ht hv w)).mpr hsub).trans
        (mk_glueWordRepresentative t ht hv w)
    rw [hmk, AddEquiv.symm_apply_apply]
    exact hw

/-- **Coordinatewise membership criterion for a glued lattice**: `x` belongs to `gluedLattice` if
and only if there is a glue word `w ∈ H` such that every simple-root coordinate `x i j` differs from
`(t i).glueRepresentativeVector (ht i) (w i) j` by an integer. -/
theorem mem_gluedLattice_carrier_iff_exists_int (hv : ∀ i, (t i).Valid)
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedLattice t ht hv H hH).carrier ↔
      ∃ w ∈ H, ∀ i j, ∃ z : ℤ, (z : ℚ) = x i j - (t i).glueRepresentativeVector (ht i) (w i) j := by
  rw [mem_gluedLattice_carrier_iff_exists_sub_mem]
  refine exists_congr fun w ↦ and_congr_right fun _ ↦ ?_
  rw [mem_pi_carrier_iff]
  refine forall_congr' fun i ↦ ?_
  rw [mem_rootLattice_carrier_iff]
  rfl

end GlueWord

end TauCeti.DynkinType
