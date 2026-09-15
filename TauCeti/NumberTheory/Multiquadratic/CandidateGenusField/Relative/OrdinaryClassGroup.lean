/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.GenusCharacter
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.OrdinaryTwoRank
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The ordinary class-group quotient in genus-field sign coordinates

Let `d > 0` be squarefree and nonsquare, and let `K = ℚ(√d)` be the embedded quadratic base of
the candidate genus field. The genus characters identify `Cl⁺(K) / Cl⁺(K)²` with the sign vectors
of even parity on the prime discriminants dividing `disc K`. Passing from the narrow class group
to the ordinary class group kills the narrow class of `(√d)`. In sign coordinates that class is
the vector which is `1` precisely at the negative prime discriminants.

This file therefore identifies

`Cl(K) / Cl(K)²`

with the quotient of the relative sign space by the line spanned by the negative-coordinate
vector. This is the class-group half of the real genus-field isomorphism, formulated for comparison
with the quotient induced by restriction from the full candidate genus field to its maximal totally
real subfield.

The description is the real-quadratic counterpart of
`autCandidateGenusFieldEquivElementaryTwoQuotient`, which handles the imaginary case directly
because narrow and ordinary class groups then agree. See F. Lemmermeyer, *Reciprocity Laws: From
Euler to Eisenstein*, §2.2, and D. A. Cox, *Primes of the Form x² + ny²*, §6.A.

## Main definitions and results

* `candidateGenusFieldNegativeSign`: the sign vector supported at the negative prime
  discriminants.
* `candidateGenusFieldOrdinaryClassGroupSignMap`: the surjection from relative sign vectors to
  the ordinary elementary-`2` class-group quotient.
* `ker_candidateGenusFieldOrdinaryClassGroupSignMap`: its kernel is the line spanned by the
  negative-coordinate vector.
* `ordinaryElementaryTwoQuotientEquivRelativeSignQuotient`: the resulting linear equivalence
  from `Cl(K) / Cl(K)²` to that sign-space quotient.
-/

public section

open NumberField

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- The sign vector which records the negative prime discriminants dividing `disc ℚ(√d)`.

The value is `1 : ZMod 2` at a negative prime discriminant and `0` at a positive one. For
positive `d`, the number of negative factors is even, so this vector belongs to
`candidateGenusFieldRelativeSignSubmodule`. -/
noncomputable def candidateGenusFieldNegativeSign (hd : Squarefree d) :
    {P // P ∈ genusPrimeDiscriminants hd} → ZMod 2 :=
  fun P => if P.1 < 0 then 1 else 0

@[simp] theorem candidateGenusFieldNegativeSign_apply (hd : Squarefree d)
    (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    candidateGenusFieldNegativeSign hd P = if P.1 < 0 then 1 else 0 := (rfl)

/-- The narrow class of the chosen square root, viewed modulo squares. It generates the possible
defect between the narrow and ordinary elementary-`2` class-group quotients. -/
noncomputable def candidateGenusFieldBaseNarrowDefect (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    NarrowClassGroup.ElementaryTwoQuotient (candidateGenusFieldBase hd) :=
  TauCeti.elementaryTwoQuotientMk
    (NarrowClassGroup.mkPrincipal
      (Units.mk0 (candidateGenusFieldBaseGen hd : candidateGenusFieldBase hd)
        (coe_gen_ne_zero (minpoly_candidateGenusFieldBaseGen hd
          hnsq))))

/-- In genus-character coordinates, the narrow-to-ordinary defect is the vector supported at the
negative prime discriminants. -/
theorem candidateGenusFieldBaseGenusCharLinearMap_narrowDefect (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d) :
    candidateGenusFieldBaseGenusCharLinearMap hd hnsq
        (candidateGenusFieldBaseNarrowDefect hd hnsq) =
      candidateGenusFieldNegativeSign hd := by
  funext P
  rw [candidateGenusFieldBaseGenusCharLinearMap_apply]
  rw [candidateGenusFieldBaseNarrowDefect,
    genusCharFunElementaryTwoQuotientFamilyLinearMap_apply,
    genusCharFunElementaryTwoQuotientLinearMap_mk,
    TauCeti.additiveIntUnitsLinearEquiv_apply, candidateGenusFieldNegativeSign_apply,
    toMul_ofMul]
  simp only [Units.ext_iff, Units.val_one,
    genusCharFunNarrowClassGroupHom_mkPrincipal_gen
      (genusPrimeDiscriminants_spec hd).1 (genusPrimeDiscriminants_spec hd).2.1
      (genusPrimeDiscriminants_spec hd).2.2
      (minpoly_candidateGenusFieldBaseGen hd hnsq)
      (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd hpos P.2]
  by_cases hP : P.1 < 0
  · rw [Int.sign_eq_neg_one_of_neg hP]
    simp [hP]
  · have hP0 : 0 < P.1 := lt_of_le_of_ne (le_of_not_gt hP)
      ((genusPrimeDiscriminants_spec hd).1 P P.2).isFundamentalDiscriminant.ne_zero.symm
    rw [Int.sign_eq_one_of_pos hP0]
    simp [hP]

/-- For positive `d`, the negative-coordinate vector has even parity and hence belongs to the
relative sign space. -/
theorem candidateGenusFieldNegativeSign_mem (hd : Squarefree d) (hpos : 0 < d) :
    candidateGenusFieldNegativeSign hd ∈ candidateGenusFieldRelativeSignSubmodule hd := by
  -- The case `d = 1` has no prime discriminants; otherwise use the genus-character realization.
  rcases eq_or_ne d 1 with rfl | hne
  · have hempty : genusPrimeDiscriminants hd = ∅ :=
      genusPrimeDiscriminants_eq hd (by simp)
        (by rw [Finset.prod_empty, fundamentalDiscriminant_of_mod_four_eq_one (by decide)])
    rw [mem_candidateGenusFieldRelativeSignSubmodule_iff]
    exact Finset.sum_eq_zero fun P _ => (Finset.notMem_empty P.1 (hempty ▸ P.2)).elim
  · have hnsq : ¬ IsSquare ((d : ℤ) : ℚ) :=
      not_isSquare_intCast_of_squarefree_of_ne_one hd hne
    rw [← candidateGenusFieldBaseGenusCharLinearMap_narrowDefect hd hnsq hpos,
      ← range_candidateGenusFieldBaseGenusCharLinearMap hd hnsq]
    exact ⟨candidateGenusFieldBaseNarrowDefect hd hnsq, rfl⟩

/-- Forgetting positivity, transported through genus-character sign coordinates. This is the
canonical surjection from the relative sign space onto `Cl(K) / Cl(K)²`. -/
noncomputable def candidateGenusFieldOrdinaryClassGroupSignMap (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    candidateGenusFieldRelativeSignSubmodule hd →ₗ[ZMod 2]
      TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 (candidateGenusFieldBase hd)) :=
  (NarrowClassGroup.toClassGroupElementaryTwoQuotient (candidateGenusFieldBase hd)).comp
    (narrowElementaryTwoQuotientEquivRelativeSign hd
      hnsq).symm.toLinearMap

/-- The ordinary class-group sign map evaluates by first recovering the narrow square class and
then forgetting positivity. -/
theorem candidateGenusFieldOrdinaryClassGroupSignMap_apply (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ))
    (v : candidateGenusFieldRelativeSignSubmodule hd) :
    candidateGenusFieldOrdinaryClassGroupSignMap hd hnsq v =
      NarrowClassGroup.toClassGroupElementaryTwoQuotient (candidateGenusFieldBase hd)
        ((narrowElementaryTwoQuotientEquivRelativeSign hd hnsq).symm v) := (rfl)

/-- The ordinary class-group sign map is surjective. -/
theorem candidateGenusFieldOrdinaryClassGroupSignMap_surjective (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    Function.Surjective (candidateGenusFieldOrdinaryClassGroupSignMap hd hnsq) :=
  NarrowClassGroup.toClassGroupElementaryTwoQuotient_surjective
    (candidateGenusFieldBase hd) |>.comp
      (narrowElementaryTwoQuotientEquivRelativeSign hd
        hnsq).symm.surjective

private theorem ker_toClassGroupElementaryTwoQuotient_eq_span_narrowDefect
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    LinearMap.ker
        (NarrowClassGroup.toClassGroupElementaryTwoQuotient (candidateGenusFieldBase hd)) =
      ZMod 2 ∙ candidateGenusFieldBaseNarrowDefect hd hnsq := by
  apply le_antisymm
  · intro x hx
    obtain ⟨C, rfl⟩ := TauCeti.elementaryTwoQuotientMk_surjective x
    rw [LinearMap.mem_ker,
      NarrowClassGroup.toClassGroupElementaryTwoQuotient_mk] at hx
    have hxmap : TauCeti.elementaryTwoQuotientMap
        (NarrowClassGroup.toClassGroup (K := candidateGenusFieldBase hd))
        (TauCeti.elementaryTwoQuotientMk C) = 0 := by
      rw [TauCeti.elementaryTwoQuotientMap_mk]
      exact hx
    obtain ⟨C', hC', hC'C⟩ := MonoidHom.exists_mem_ker_elementaryTwoQuotientMk_eq
      (NarrowClassGroup.toClassGroup (K := candidateGenusFieldBase hd))
      NarrowClassGroup.toClassGroup_surjective hxmap
    rw [← hC'C]
    rw [NarrowClassGroup.toClassGroup_ker] at hC'
    obtain ⟨u, rfl⟩ := hC'
    rcases mkPrincipal_eq_one_or_eq_mkPrincipal_gen
        (minpoly_candidateGenusFieldBaseGen hd hnsq)
        (adjoin_candidateGenusFieldBaseGen_eq_top hd) u with hu | hu
    · rw [hu, TauCeti.elementaryTwoQuotientMk_one]
      exact Submodule.zero_mem _
    · rw [hu]
      exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      candidateGenusFieldBaseNarrowDefect,
      NarrowClassGroup.toClassGroupElementaryTwoQuotient_mk,
      NarrowClassGroup.toClassGroup_mkPrincipal]
    exact TauCeti.elementaryTwoQuotientMk_one

/-- The kernel of the ordinary class-group sign map is exactly the line generated by the vector
supported at the negative prime discriminants. If every prime discriminant is positive, this
vector is zero and the map is an equivalence; otherwise it removes one sign dimension. -/
theorem ker_candidateGenusFieldOrdinaryClassGroupSignMap (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d) :
    LinearMap.ker (candidateGenusFieldOrdinaryClassGroupSignMap hd hnsq) =
      ZMod 2 ∙
        (⟨candidateGenusFieldNegativeSign hd,
          candidateGenusFieldNegativeSign_mem hd hpos⟩ :
            candidateGenusFieldRelativeSignSubmodule hd) := by
  set z : candidateGenusFieldRelativeSignSubmodule hd :=
    ⟨candidateGenusFieldNegativeSign hd, candidateGenusFieldNegativeSign_mem hd hpos⟩ with hzdef
  have hez : narrowElementaryTwoQuotientEquivRelativeSign hd hnsq
      (candidateGenusFieldBaseNarrowDefect hd hnsq) = z := by
    apply Subtype.ext
    rw [narrowElementaryTwoQuotientEquivRelativeSign_apply_coe, hzdef]
    exact candidateGenusFieldBaseGenusCharLinearMap_narrowDefect hd hnsq hpos
  have hz : candidateGenusFieldOrdinaryClassGroupSignMap hd hnsq z = 0 := by
    rw [candidateGenusFieldOrdinaryClassGroupSignMap_apply, ← hez,
      LinearEquiv.symm_apply_apply, ← LinearMap.mem_ker,
      ker_toClassGroupElementaryTwoQuotient_eq_span_narrowDefect hd hnsq]
    exact Submodule.mem_span_singleton_self _
  ext v
  constructor
  · intro hv
    have hv' : (narrowElementaryTwoQuotientEquivRelativeSign hd hnsq).symm v ∈
        ZMod 2 ∙ candidateGenusFieldBaseNarrowDefect hd hnsq := by
      rw [← ker_toClassGroupElementaryTwoQuotient_eq_span_narrowDefect hd hnsq,
        LinearMap.mem_ker, ← candidateGenusFieldOrdinaryClassGroupSignMap_apply]
      exact LinearMap.mem_ker.mp hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv'
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    rw [← hez, ← map_smul, ha, LinearEquiv.apply_symm_apply]
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [LinearMap.mem_ker, map_smul, hz, smul_zero]

/-- **The ordinary elementary-`2` class-group quotient in sign coordinates.** For positive
squarefree `d`, `Cl(ℚ(√d)) / Cl(ℚ(√d))²` is the even-parity sign space modulo the line generated
by the negative-coordinate vector. -/
noncomputable def ordinaryElementaryTwoQuotientEquivRelativeSignQuotient
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d) :
    TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 (candidateGenusFieldBase hd)) ≃ₗ[ZMod 2]
      (candidateGenusFieldRelativeSignSubmodule hd ⧸
        ZMod 2 ∙
          (⟨candidateGenusFieldNegativeSign hd,
            candidateGenusFieldNegativeSign_mem hd hpos⟩ :
              candidateGenusFieldRelativeSignSubmodule hd)) :=
  ((Submodule.quotEquivOfEq _ _
      (ker_candidateGenusFieldOrdinaryClassGroupSignMap hd hnsq hpos).symm).trans
    ((candidateGenusFieldOrdinaryClassGroupSignMap hd hnsq).quotKerEquivOfSurjective
      (candidateGenusFieldOrdinaryClassGroupSignMap_surjective hd hnsq))).symm

/-- The sign-space quotient equivalence sends the class of a relative sign vector to its ordinary
class-group image. -/
@[simp] theorem ordinaryElementaryTwoQuotientEquivRelativeSignQuotient_symm_mk
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d)
    (v : candidateGenusFieldRelativeSignSubmodule hd) :
    (ordinaryElementaryTwoQuotientEquivRelativeSignQuotient hd hnsq hpos).symm
        (Submodule.Quotient.mk v) =
      candidateGenusFieldOrdinaryClassGroupSignMap hd hnsq v := by
  rw [ordinaryElementaryTwoQuotientEquivRelativeSignQuotient,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end TauCeti.Multiquadratic
