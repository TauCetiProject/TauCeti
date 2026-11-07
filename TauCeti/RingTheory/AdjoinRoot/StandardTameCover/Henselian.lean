/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
public import TauCeti.FieldTheory.IsSepClosed
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Henselian.Integral
import TauCeti.RingTheory.Henselian.Radical
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# Strictly henselian root covers

If `A` is local, `f` belongs to its maximal ideal and `e > 0`, the root cover
`A[x]/(x^e - f)` is local and has the same residue field as `A`. If `A` is henselian,
so is the cover. In particular, extracting a root of a local equation of a divisor over a
strictly henselian base again gives a strictly henselian ring. Finite étale algebras over
that ring therefore split into products of copies of it.

No invertibility of `e`, regularity or Noetherianity is needed here. To use the residue-field
statements, install `standardTameCover_isLocalRing` as a local instance first.

## References

* The Stacks Project, Lemma 58.31.5, https://stacks.math.columbia.edu/tag/0EYG.
* The Stacks Project, Lemma 10.153.4, https://stacks.math.columbia.edu/tag/04GH.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {f : A} {e : ℕ}

section ResidueField

variable [IsLocalRing A] [IsLocalRing (standardTameCover A f e)]

/-- The root of a positive-degree cover along an element of the maximal ideal vanishes in
its residue field. -/
@[simp]
theorem standardTameCover_residue_root (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    residue (standardTameCover A f e) (AdjoinRoot.root (X ^ e - C f)) = 0 := by
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  have hcomap : (maximalIdeal (standardTameCover A f e)).under A = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal inferInstance
  rw [residue_eq_zero_iff]
  apply Ideal.IsPrime.mem_of_pow_mem inferInstance e
  rw [AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]
  rwa [← Ideal.mem_comap, ← Ideal.under_def, hcomap]

/-- The residue field of a positive-degree root cover along the maximal ideal is canonically
isomorphic to that of the base. The root reduces to zero, and constants reduce as in `A`. -/
noncomputable def standardTameCoverResidueFieldEquiv (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    ResidueField (standardTameCover A f e) ≃+* ResidueField A := by
  let φ : standardTameCover A f e →+* ResidueField A :=
    AdjoinRoot.lift (residue A) 0 (by simp [he, (residue_eq_zero_iff f).mpr hf])
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨a, rfl⟩ := residue_surjective z
    exact ⟨AdjoinRoot.of _ a, by simp [φ]⟩
  have hker : RingHom.ker φ = maximalIdeal (standardTameCover A f e) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)

/-- The residue-field identification of a root cover preserves the residues of constants. -/
@[simp]
theorem standardTameCoverResidueFieldEquiv_residue_of (hf : f ∈ maximalIdeal A) (he : e ≠ 0)
    (a : A) :
    standardTameCoverResidueFieldEquiv hf he
      (residue (standardTameCover A f e) (AdjoinRoot.of _ a)) = residue A a := by
  unfold standardTameCoverResidueFieldEquiv
  -- `erw` identifies the residue-field wrapper with the quotient used by the two comparisons.
  erw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, AdjoinRoot.lift_of]

/-- In the inverse residue-field identification, a constant is sent to the same constant. -/
@[simp]
theorem standardTameCoverResidueFieldEquiv_symm_residue (hf : f ∈ maximalIdeal A) (he : e ≠ 0)
    (a : A) :
    (standardTameCoverResidueFieldEquiv hf he).symm (residue A a) =
      residue (standardTameCover A f e) (AdjoinRoot.of _ a) := by
  apply (standardTameCoverResidueFieldEquiv hf he).injective
  simp

/-- A root cover along the maximal ideal has separably closed residue field whenever the
base does. This does not require the exponent to be invertible. -/
theorem standardTameCover_isSepClosed_residueField [IsSepClosed (ResidueField A)]
    (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    IsSepClosed (ResidueField (standardTameCover A f e)) :=
  IsSepClosed.of_ringEquiv (standardTameCoverResidueFieldEquiv hf he).symm

end ResidueField

/-- A positive-degree root cover along the maximal ideal of a henselian local ring is
henselian local. Combined with `standardTameCover_isSepClosed_residueField`, this shows that
root extraction preserves strict henselianity. -/
theorem standardTameCover_henselianLocalRing [HenselianLocalRing A]
    (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    HenselianLocalRing (standardTameCover A f e) := by
  have := standardTameCover_isLocalRing hf he
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  let B := standardTameCover A f e
  have : IsLocalHom (algebraMap A B) :=
    AdjoinRoot.isLocalHom_of_monic_of_degree_pos (monic_X_pow_sub_C f he)
      (by rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero he)]; exact_mod_cast Nat.pos_of_ne_zero he)
  let I := (maximalIdeal A).map (algebraMap A B)
  have hrad : I.radical = maximalIdeal B := by
    obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_map (R := A) (S := B)
    apply le_antisymm
    · exact (Ideal.IsPrime.radical_le_iff inferInstance).mpr
        (IsLocalRing.map_maximalIdeal_le _)
    · intro b hb
      exact ⟨n, hn (Ideal.pow_mem_pow hb n)⟩
  have : HenselianRing B I := inferInstance
  have : HenselianRing B I.radical := inferInstance
  rw [hrad] at this
  exact HenselianRing.henselianLocalRing B

end TauCeti
