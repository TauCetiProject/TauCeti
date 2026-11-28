/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PrincipalLevel
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.LinearAlgebra.Matrix.Action
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Row congruence levels of finite adelic unitary groups

In the finite adelic unitary group, impose a principal congruence modulo one ideal and a
congruence on a single row modulo a second ideal. The latter condition is a stabilizer,
not a kernel of reduction. The resulting subgroup contains the principal level of the
product ideal and is open when both ideals are nonzero.

This is the source level of the definite theta lifts in `New.Data.levelX` and
`New.Data.principalLevel_le_levelX`, `grh/src/New/UpperBound/Objects/Columns.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) (revision `72fead1`).
-/

public noncomputable section

open IsDedekindDomain Matrix NumberField

namespace TauCeti

variable {E ι : Type*} [Field E] [NumberField E] [IsCMField E] [Fintype ι] [DecidableEq ι]

variable (E) in
/-- The subgroup of the principal level of `M` in which row `i` agrees with row `i` of the
identity modulo `N`. Transpose carries the row condition to a column stabilizer in the
opposite group. -/
def rowUnitaryLevel (M N : Ideal (𝓞 E)) (i : ι) : Subgroup (finiteAdelicUnitaryGroup E ι) :=
  let J := FiniteAdeleRing.completedIdeal E N
  let Q := FiniteAdeleRing.integralAdeles (𝓞 E) E ⧸ J
  let red := (GeneralLinearGroup.transposeMulEquiv (R := Q) ι).toMonoidHom.comp
    (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk J))
  let principal := (GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (FiniteAdeleRing.completedIdeal E M))).ker
  ((principal ⊓ (MulAction.stabilizer (GL ι Q) (Pi.single i 1 : ι → Q)).op.comap red).map
    (FiniteAdeleRing.integralGL E ι)).subgroupOf (finiteAdelicUnitaryGroup E ι)

/-- Membership in the row level is the simultaneous entrywise principal congruence and the
marked row congruence, on the same integral representative. -/
theorem mem_rowUnitaryLevel_iff {M N : Ideal (𝓞 E)} {i : ι}
    {g : finiteAdelicUnitaryGroup E ι} : g ∈ rowUnitaryLevel E M N i ↔
    ∃ h : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E),
      FiniteAdeleRing.integralGL E ι h = g ∧
      (∀ j k, (h : Matrix ι ι _) j k - (1 : Matrix ι ι _) j k ∈
        FiniteAdeleRing.completedIdeal E M) ∧
      (∀ k, (h : Matrix ι ι _) i k - (1 : Matrix ι ι _) i k ∈
        FiniteAdeleRing.completedIdeal E N) := by
  simp only [rowUnitaryLevel, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_inf,
    GeneralLinearGroup.mem_ker_map_quotientMk_iff, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, Subgroup.mem_op, MulAction.mem_stabilizer_iff, Units.smul_def,
    Matrix.smul_eq_mulVec, GeneralLinearGroup.coe_unop_transposeMulEquiv, Matrix.mulVec_transpose,
    Matrix.single_vecMul, one_smul]
  let J := FiniteAdeleRing.completedIdeal E N
  have hdiag (k : ι) :
      (Pi.single i 1 : ι → FiniteAdeleRing.integralAdeles (𝓞 E) E ⧸ J) k =
        Ideal.Quotient.mk J ((1 : Matrix ι ι _) i k) := by
    by_cases hki : k = i
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hki, Matrix.one_apply_ne (Ne.symm hki)]
  have hrow (h : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) :
      (GeneralLinearGroup.map (Ideal.Quotient.mk J) h : Matrix ι ι
        (FiniteAdeleRing.integralAdeles (𝓞 E) E ⧸ J)).row i = Pi.single i 1 ↔
      ∀ k, (h : Matrix ι ι _) i k - (1 : Matrix ι ι _) i k ∈ J := by
    rw [funext_iff]
    simp only [Matrix.row_apply, GeneralLinearGroup.map_apply, hdiag, Ideal.Quotient.eq]
  constructor
  · rintro ⟨h, ⟨hM, hN⟩, hg⟩
    exact ⟨h, hg, hM, (hrow h).mp hN⟩
  · rintro ⟨h, hg, hM, hN⟩
    exact ⟨h, ⟨hM, (hrow h).mpr hN⟩, hg⟩

/-- The row level is contained in its defining principal level. -/
theorem rowUnitaryLevel_le_principalUnitaryLevel (M N : Ideal (𝓞 E)) (i : ι) :
    rowUnitaryLevel E M N i ≤ principalUnitaryLevel E ι M := by
  rw [rowUnitaryLevel, principalUnitaryLevel_def]
  exact Subgroup.subgroupOf_mono _ (Subgroup.map_mono inf_le_left)

/-- Any principal level whose modulus is contained in both ideals lies in the row level. -/
theorem principalUnitaryLevel_le_rowUnitaryLevel {L M N : Ideal (𝓞 E)} (i : ι)
    (hLM : L ≤ M) (hLN : L ≤ N) : principalUnitaryLevel E ι L ≤ rowUnitaryLevel E M N i := by
  intro g hg
  obtain ⟨h, he, hL⟩ := mem_principalUnitaryLevel_iff.mp hg
  exact mem_rowUnitaryLevel_iff.mpr ⟨h, he,
    fun j k ↦ FiniteAdeleRing.completedIdeal_mono E hLM (hL j k),
    fun k ↦ FiniteAdeleRing.completedIdeal_mono E hLN (hL i k)⟩

/-- In particular, the row level contains the principal level of the product ideal. -/
theorem principalUnitaryLevel_mul_le_rowUnitaryLevel (M N : Ideal (𝓞 E)) (i : ι) :
    principalUnitaryLevel E ι (M * N) ≤ rowUnitaryLevel E M N i :=
  principalUnitaryLevel_le_rowUnitaryLevel i Ideal.mul_le_left Ideal.mul_le_right

/-- With no row condition, the row level is just the principal level. -/
@[simp] theorem rowUnitaryLevel_top (M : Ideal (𝓞 E)) (i : ι) :
    rowUnitaryLevel E M ⊤ i = principalUnitaryLevel E ι M :=
  le_antisymm (rowUnitaryLevel_le_principalUnitaryLevel M ⊤ i)
    (principalUnitaryLevel_le_rowUnitaryLevel i le_rfl le_top)

/-- When the two ideals are nonzero, the row level is an open subgroup contained in the
integral finite adelic unitary group. -/
theorem isUnitaryLevel_rowUnitaryLevel {M N : Ideal (𝓞 E)} (i : ι)
    (hM : M ≠ ⊥) (hN : N ≠ ⊥) : IsUnitaryLevel (rowUnitaryLevel E M N i) :=
  (isUnitaryLevel_principalUnitaryLevel (ι := ι) (mul_ne_zero hM hN)).mono
    (principalUnitaryLevel_mul_le_rowUnitaryLevel M N i)
    ((rowUnitaryLevel_le_principalUnitaryLevel M N i).trans
      (principalUnitaryLevel_le_integralAdelicUnitaryGroup E ι M))

end TauCeti
