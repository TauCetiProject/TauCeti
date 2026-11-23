/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient

import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber

/-!
# Root signs at the orbit weights of a dominant weight

Let `λ` be a dominant weight for a base of a finite crystallographic reduced root system, with
stabilizer the standard parabolic subgroup `W_λ` of its walls
(`RootPairing.parabolic_wallIndices_eq_stabilizer`). Each orbit weight is `w λ` for a unique
minimal representative `w` of its coset in `W / W_λ`
(`TauCeti.existsUnique_isMinimalCosetRep_smul_eq`). This file counts the positive roots by the sign
of their pairing with `w λ`:

* exactly `ℓ(w)` positive roots pair negatively with `w λ`;
* exactly `N_λ - ℓ(w)` pair positively, where `N_λ` is the number of positive roots not orthogonal
  to `λ`, that is, the positive roots outside the root subsystem of the stabilizer.

The first count holds because the negatively pairing positive roots are exactly the inversions of
`w⁻¹` (`TauCeti.setOf_isPos_and_coroot'_smul_neg_eq_inversions_inv`). Every inversion `β` of `w⁻¹`
pairs nonpositively with `w λ`; if it paired to zero, `s_β` would fix `w λ`, so `s_β w` would be a
shorter element of the coset `w W_λ`. This characterizes minimality
(`TauCeti.isMinimalCosetRep_iff_forall_mem_inversions_inv_coroot'_smul_ne_zero`). The second count
uses that the number of positive roots not orthogonal to a weight is invariant under the Weyl group
(`TauCeti.ncard_setOf_isPos_and_coroot'_smul_ne_zero`), since root negation exchanges the positive
roots pairing positively with the negative roots pairing negatively. The roots orthogonal to `λ`,
which on a chamber wall form a nonempty subsystem, are excluded from both counts.

In the Morse theory of a height function `f_X = ⟨·, X⟩` on a coadjoint orbit, the critical point
at `w λ` has index twice the number of positive roots `β` with `⟨X, β^∨⟩ ⟨w λ, β^∨⟩ > 0`. For `X`
in the open dominant chamber that number is `N_λ - ℓ(w)`, and for `X` in the open antidominant
chamber it is `ℓ(w)`
(`TauCeti.ncard_setOf_isPos_and_mul_coroot'_smul_pos_add_length_of_mem_openDominantChamber`,
`TauCeti.ncard_setOf_isPos_and_mul_coroot'_smul_pos_of_neg_mem_openDominantChamber`). The
statements here are about root pairings only; for a compact Lie group they are applied to the root
system of a maximal torus.

## Main results

* `TauCeti.isMinimalCosetRep_iff_forall_mem_inversions_inv_coroot'_smul_ne_zero`: `w` is minimal in
  `w W_λ` exactly when no inversion of `w⁻¹` is orthogonal to `w λ`.
* `TauCeti.setOf_isPos_and_coroot'_smul_neg_eq_inversions_inv`: for minimal `w`, the positive
  roots pairing negatively with `w λ` are the inversions of `w⁻¹`.
* `TauCeti.ncard_setOf_isPos_and_coroot'_smul_neg`: there are `ℓ(w)` of them.
* `TauCeti.ncard_setOf_isPos_and_coroot'_smul_pos_add_length`: for minimal `w`, the number of
  positive roots pairing positively with `w λ`, plus `ℓ(w)`, is `N_λ`.
* `TauCeti.ncard_setOf_isPos_and_mul_coroot'_smul_pos_add_length_of_mem_openDominantChamber` and
  `TauCeti.ncard_setOf_isPos_and_mul_coroot'_smul_pos_of_neg_mem_openDominantChamber`: the index
  counts for `X` in the open dominant and antidominant chambers.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.4.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Sections 1.7 and 1.10.
-/

public section

namespace TauCeti

open RootPairing Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : _root_.RootPairing ι R M N} {b : P.Base}
  [LinearOrder R] [IsStrictOrderedRing R] [Finite ι]

/-! ### Minimal coset representatives -/

variable [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced] {lam : M}

/-- **Minimal coset representatives are detected by their inversions.** For a dominant weight `λ`,
a Weyl-group element `w` is the minimal representative of its coset `w W_λ` exactly when no
inversion of `w⁻¹` is orthogonal to `w λ`. If an inversion `β` were orthogonal to `w λ`, then
`s_β w` would be a shorter element of the same coset. -/
theorem isMinimalCosetRep_iff_forall_mem_inversions_inv_coroot'_smul_ne_zero
    (hlam : lam ∈ dominantChamber P b) {w : P.weylGroup} :
    (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w ↔
      ∀ i ∈ inversions P b w⁻¹, P.coroot' i (w • lam) ≠ 0 := by
  refine ⟨fun hw i hi hzero ↦ ?_, fun h ↦ ?_⟩
  · -- The reflection `s_β` fixes `w λ`, so `s_β w` lies in the coset of `w`, but it is shorter.
    have hmem : w⁻¹ * (RootPairing.weylGroup.ofIdx P i * w) ∈
        (weylCoxeterSystem P b).parabolic (P.wallIndices b lam) := by
      rw [inv_mul_mem_parabolic_wallIndices_iff hlam, mul_smul,
        ofIdx_smul_eq_self_of_coroot'_eq_zero hzero]
    have hle := (weylCoxeterSystem P b).length_mul_of_isMinimalCosetRep hw hmem
    have hlt := (ncard_inversions_ofIdx_mul_lt_iff P b w ((mem_inversions P b _ i).mp hi).1).mpr hi
    rw [mul_inv_cancel_left, length_weylCoxeterSystem_eq, length_weylCoxeterSystem_eq] at hle
    omega
  · -- A wall reflection `s_j` fixes `λ`, so every inversion of `w⁻¹` pairs negatively with
    -- `(w s_j) λ = w λ` and is an inversion of `(w s_j)⁻¹`; hence `s_j` does not shorten `w`.
    rw [CoxeterSystem.isMinimalCosetRep_iff]
    intro j hj hdesc
    rw [CoxeterSystem.IsRightDescent, length_weylCoxeterSystem_eq, length_weylCoxeterSystem_eq,
      ← ncard_inversions_inv P b (w * _), ← ncard_inversions_inv P b w] at hdesc
    refine hdesc.not_ge (ncard_le_ncard fun i hi ↦
      mem_inversions_inv_of_coroot'_smul_neg P b hlam ((mem_inversions P b _ i).mp hi).1 ?_)
    rw [mul_smul, MulAction.mem_stabilizer_iff.mp ((P.parabolic_wallIndices_eq_stabilizer b
      hlam).le ((weylCoxeterSystem P b).simple_mem_parabolic hj))]
    exact (coroot'_smul_nonpos_of_mem_inversions_inv P b hlam hi).lt_of_ne (h i hi)

/-- **The positive roots pairing negatively with an orbit weight are the inversions of the inverse
of its minimal coset representative.** -/
theorem setOf_isPos_and_coroot'_smul_neg_eq_inversions_inv (hlam : lam ∈ dominantChamber P b)
    {w : P.weylGroup} (hw : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w) :
    {i | b.IsPos i ∧ P.coroot' i (w • lam) < 0} = inversions P b w⁻¹ := by
  have h := (isMinimalCosetRep_iff_forall_mem_inversions_inv_coroot'_smul_ne_zero hlam).mp hw
  ext i
  refine ⟨fun hi ↦ mem_inversions_inv_of_coroot'_smul_neg P b hlam hi.1 hi.2, fun hi ↦
    ⟨((mem_inversions P b _ i).mp hi).1,
      (coroot'_smul_nonpos_of_mem_inversions_inv P b hlam hi).lt_of_ne (h i hi)⟩⟩

/-- **Length formula on `W / W_λ`, negative side.** For a dominant weight `λ` and the minimal
representative `w` of a coset of its stabilizer, exactly `ℓ(w)` positive roots pair negatively with
`w λ`. -/
theorem ncard_setOf_isPos_and_coroot'_smul_neg (hlam : lam ∈ dominantChamber P b)
    {w : P.weylGroup} (hw : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w) :
    {i | b.IsPos i ∧ P.coroot' i (w • lam) < 0}.ncard = (weylCoxeterSystem P b).length w := by
  rw [setOf_isPos_and_coroot'_smul_neg_eq_inversions_inv hlam hw, ncard_inversions_inv,
    length_weylCoxeterSystem_eq]

/-- **Length formula on `W / W_λ`, positive side.** For a dominant weight `λ` and the minimal
representative `w` of a coset of its stabilizer, the number of positive roots pairing positively
with `w λ`, plus `ℓ(w)`, is the number of positive roots not orthogonal to `λ`. The roots of the
stabilizer, orthogonal to `λ`, are not counted. -/
theorem ncard_setOf_isPos_and_coroot'_smul_pos_add_length (hlam : lam ∈ dominantChamber P b)
    {w : P.weylGroup} (hw : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w) :
    {i | b.IsPos i ∧ 0 < P.coroot' i (w • lam)}.ncard + (weylCoxeterSystem P b).length w =
      {i | b.IsPos i ∧ P.coroot' i lam ≠ 0}.ncard := by
  rw [← ncard_setOf_isPos_and_coroot'_smul_ne_zero P b w,
    ncard_setOf_isPos_and_coroot'_ne_zero_eq_add, ncard_setOf_isPos_and_coroot'_smul_neg hlam hw,
    add_comm]

/-- **Index count for a height in the open dominant chamber.** For `X` in the open dominant chamber,
a dominant weight `λ` and the minimal representative `w` of a coset of its stabilizer, the number of
positive roots `β` with `⟨X, β^∨⟩ ⟨w λ, β^∨⟩ > 0`, plus `ℓ(w)`, is the number of positive roots not
orthogonal to `λ`. -/
theorem ncard_setOf_isPos_and_mul_coroot'_smul_pos_add_length_of_mem_openDominantChamber
    (hlam : lam ∈ dominantChamber P b)
    {w : P.weylGroup} (hw : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w)
    {X : M} (hX : X ∈ openDominantChamber P b) :
    {i | b.IsPos i ∧ 0 < P.coroot' i X * P.coroot' i (w • lam)}.ncard +
        (weylCoxeterSystem P b).length w =
      {i | b.IsPos i ∧ P.coroot' i lam ≠ 0}.ncard := by
  rw [← ncard_setOf_isPos_and_coroot'_smul_pos_add_length hlam hw]
  congr 2
  ext i
  refine and_congr_right fun hi ↦ mul_pos_iff_of_pos_left ?_
  exact coroot'_pos_of_mem_posRoots P b hX ((mem_posRoots P b i).mpr hi)

/-- **Index count for a height in the open antidominant chamber.** For `-X` in the open dominant
chamber, a dominant weight `λ` and the minimal representative `w` of a coset of its stabilizer,
exactly `ℓ(w)` positive roots `β` have `⟨X, β^∨⟩ ⟨w λ, β^∨⟩ > 0`. -/
theorem ncard_setOf_isPos_and_mul_coroot'_smul_pos_of_neg_mem_openDominantChamber
    (hlam : lam ∈ dominantChamber P b)
    {w : P.weylGroup} (hw : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w)
    {X : M} (hX : -X ∈ openDominantChamber P b) :
    {i | b.IsPos i ∧ 0 < P.coroot' i X * P.coroot' i (w • lam)}.ncard =
      (weylCoxeterSystem P b).length w := by
  rw [← ncard_setOf_isPos_and_coroot'_smul_neg hlam hw]
  congr 1
  ext i
  refine and_congr_right fun hi ↦ ?_
  have h := mul_pos_iff_of_pos_left (b := -P.coroot' i (w • lam))
    (coroot'_pos_of_mem_posRoots P b hX ((mem_posRoots P b i).mpr hi))
  rwa [map_neg, neg_mul_neg, neg_pos] at h

end TauCeti
