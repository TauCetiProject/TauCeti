/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality

import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The `A₅⁴ D₄` block-triality symmetry

In Conway--Sloane's Table 16.1, the row `A₅⁴ D₄` (`TauCeti.RootfulNiemeierType.a5FourthD4`) has
four `A₅` components followed by one `D₄` component, glued additively along the cyclic pattern
`[2(024)0]` and the three literal words `[33001]`, `[30302]`, `[30033]`.  Unlike every other
pattern in the table, the coordinate rotation `TauCeti.RootfulNiemeierType.a5FourthD4BlockPerm`
(`1 ↦ 2 ↦ 3 ↦ 1`, fixing `0` and `4`) indicated by `[2(024)0]` does not preserve the glue subgroup
by permuting components alone: it sends `[33001]` to `[30301]`, while the glue subgroup has
`[30302]`.

Pairing that block rotation of the three marked `A₅` components with the triality isometry
`TauCeti.DynkinType.typeD4Triality` on the `D₄` component restores invariance of the glue subgroup:
`typeD4Triality` cycles the nonzero `D₄` glue labels `1 ↦ 2 ↦ 3 ↦ 1` (`s ↦ v ↦ c ↦ s`), so the
combined action sends `[33001] ↦ [30302] ↦ [30033] ↦ [33001]` while permuting the three expanded
words of `[2(024)0]` among themselves.  Naturality of gluing under combined reindexing and
componentwise root-lattice isometries (`TauCeti.DynkinType.gluedLatticePiCongrIsometry`) then lifts
this action to an order-`3` self-isometry
`TauCeti.RootfulNiemeierType.a5FourthD4BlockTrialityIsometry` of `a5FourthD4.lattice`
(`TauCeti.niemeierA5FourthD4`), giving the group homomorphism
`TauCeti.RootfulNiemeierType.a5FourthD4PatternIsometryHom` for every pattern of the row.

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4BlockPerm`: the order-`3` permutation of the five
  component positions indicated by `[2(024)0]`, fixing `0` and `4` and cycling `1 ↦ 2 ↦ 3 ↦ 1`.
* `TauCeti.RootfulNiemeierType.a5FourthD4BlockTrialityGlueEquiv`: the induced self-isometry of
  `a5FourthD4.glueModule`, permuting `a5FourthD4.glueGenerators` and preserving
  `a5FourthD4.glueSubgroup` (`a5FourthD4BlockTrialityGlueEquiv_mem_glueSubgroup_iff`).
* `TauCeti.RootfulNiemeierType.a5FourthD4BlockTrialityIsometry`: the order-`3` self-isometry of
  `a5FourthD4.lattice` rotating the three marked `A₅` components and acting by `typeD4Triality` on
  the `D₄` component, with componentwise evaluation lemmas and
  `orderOf_a5FourthD4BlockTrialityIsometry`.
* `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`,
  `TauCeti.RootfulNiemeierType.a5FourthD4PatternIsometryHom`: the resulting faithful action of
  `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries` and action of `p.symmetries` for every
  `p ∈ a5FourthD4.gluePatterns` on `a5FourthD4.lattice`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §3 and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### Component types and the `[2(024)0]` block permutation -/

/-- The `A₅⁴ D₄` row has five components, so numerals index `Fin a5FourthD4.components.length`. -/
instance instNeZeroLengthComponentsA5FourthD4 : NeZero a5FourthD4.components.length :=
  inferInstanceAs (NeZero 5)

/-- The first four components of `A₅⁴ D₄` have type `A₅`. -/
theorem componentType_a5FourthD4_of_lt {i : Fin a5FourthD4.components.length} (hi : i.val < 4) :
    a5FourthD4.componentType i = A 5 := by
  fin_cases i <;> first | rfl | simp at hi

/-- The fifth component of `A₅⁴ D₄` has type `D₄`. -/
@[simp]
theorem componentType_a5FourthD4_four : a5FourthD4.componentType 4 = D 4 :=
  (rfl)

/-- **The block rotation of `A₅⁴ D₄`**: the coordinate permutation of the five component positions
indicated by `[2(024)0]`, fixing position `0` and the `D₄` position `4` while cycling the three
marked `A₅` positions `1 ↦ 2 ↦ 3 ↦ 1`. -/
@[expose] def a5FourthD4BlockPerm : Equiv.Perm (Fin a5FourthD4.components.length) :=
  Equiv.swap 1 3 * Equiv.swap 1 2

/-- `a5FourthD4BlockPerm` agrees with the block-rotation generator of
`(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`. -/
theorem a5FourthD4BlockPerm_eq_finSumPerm :
    (a5FourthD4BlockPerm : Equiv.Perm (Fin 5)) =
      Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm (1 : Equiv.Perm (Fin 1)) (finRotate 3))
        (1 : Equiv.Perm (Fin 1)) := by
  let g := Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm (1 : Equiv.Perm (Fin 1)) (finRotate 3))
    (1 : Equiv.Perm (Fin 1))
  have h0 : g (Fin.castAdd 1 (Fin.castAdd 3 0)) = 0 := by
    rw [Equiv.Perm.finSumPerm_apply_castAdd, Equiv.Perm.finSumPerm_apply_castAdd]; decide
  have h1 : g (Fin.castAdd 1 (Fin.natAdd 1 0)) = 2 := by
    rw [Equiv.Perm.finSumPerm_apply_castAdd, Equiv.Perm.finSumPerm_apply_natAdd]; decide
  have h2 : g (Fin.castAdd 1 (Fin.natAdd 1 1)) = 3 := by
    rw [Equiv.Perm.finSumPerm_apply_castAdd, Equiv.Perm.finSumPerm_apply_natAdd]; decide
  have h3 : g (Fin.castAdd 1 (Fin.natAdd 1 2)) = 1 := by
    rw [Equiv.Perm.finSumPerm_apply_castAdd, Equiv.Perm.finSumPerm_apply_natAdd]; decide
  have h4 : g (Fin.natAdd 4 0) = 4 := by
    rw [Equiv.Perm.finSumPerm_apply_natAdd]; decide
  let s : Equiv.Perm (Fin 5) := Equiv.swap 1 3 * Equiv.swap 1 2
  have heq : s = g := by
    refine Equiv.ext fun i ↦ ?_
    fin_cases i
    · exact (by decide : s 0 = 0).trans h0.symm
    · exact (by decide : s 1 = 2).trans h1.symm
    · exact (by decide : s 2 = 3).trans h2.symm
    · exact (by decide : s 3 = 1).trans h3.symm
    · exact (by decide : s 4 = 4).trans h4.symm
  exact heq

/-- `a5FourthD4BlockPerm` fixes position `0`. -/
@[simp] theorem a5FourthD4BlockPerm_apply_zero : a5FourthD4BlockPerm 0 = 0 := by decide
/-- `a5FourthD4BlockPerm` sends position `1` to position `2`. -/
@[simp] theorem a5FourthD4BlockPerm_apply_one : a5FourthD4BlockPerm 1 = 2 := by decide
/-- `a5FourthD4BlockPerm` sends position `2` to position `3`. -/
@[simp] theorem a5FourthD4BlockPerm_apply_two : a5FourthD4BlockPerm 2 = 3 := by decide
/-- `a5FourthD4BlockPerm` sends position `3` to position `1`. -/
@[simp] theorem a5FourthD4BlockPerm_apply_three : a5FourthD4BlockPerm 3 = 1 := by decide
/-- `a5FourthD4BlockPerm` fixes the `D₄` position `4`. -/
@[simp] theorem a5FourthD4BlockPerm_apply_four : a5FourthD4BlockPerm 4 = 4 := by decide

/-- `a5FourthD4BlockPerm⁻¹` fixes position `0`. -/
@[simp] theorem a5FourthD4BlockPerm_inv_apply_zero : a5FourthD4BlockPerm⁻¹ 0 = 0 := by decide
/-- `a5FourthD4BlockPerm⁻¹` sends position `1` to position `3`. -/
@[simp] theorem a5FourthD4BlockPerm_inv_apply_one : a5FourthD4BlockPerm⁻¹ 1 = 3 := by decide
/-- `a5FourthD4BlockPerm⁻¹` sends position `2` to position `1`. -/
@[simp] theorem a5FourthD4BlockPerm_inv_apply_two : a5FourthD4BlockPerm⁻¹ 2 = 1 := by decide
/-- `a5FourthD4BlockPerm⁻¹` sends position `3` to position `2`. -/
@[simp] theorem a5FourthD4BlockPerm_inv_apply_three : a5FourthD4BlockPerm⁻¹ 3 = 2 := by decide
/-- `a5FourthD4BlockPerm⁻¹` fixes the `D₄` position `4`. -/
@[simp] theorem a5FourthD4BlockPerm_inv_apply_four : a5FourthD4BlockPerm⁻¹ 4 = 4 := by decide

/-- `a5FourthD4BlockPerm` has exponent three. -/
@[simp]
theorem a5FourthD4BlockPerm_pow_three : a5FourthD4BlockPerm ^ 3 = 1 := by decide

/-- `a5FourthD4BlockPerm` has order three. -/
@[simp]
theorem orderOf_a5FourthD4BlockPerm : orderOf a5FourthD4BlockPerm = 3 :=
  orderOf_eq_prime a5FourthD4BlockPerm_pow_three (by decide)

/-- `a5FourthD4BlockPerm` preserves the component Dynkin types of `A₅⁴ D₄`. -/
theorem componentType_a5FourthD4_a5FourthD4BlockPerm (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType (a5FourthD4BlockPerm k) = a5FourthD4.componentType k := by
  fin_cases k
  · change a5FourthD4.componentType (a5FourthD4BlockPerm 0) = a5FourthD4.componentType 0
    rw [a5FourthD4BlockPerm_apply_zero]
  · change a5FourthD4.componentType (a5FourthD4BlockPerm 1) = a5FourthD4.componentType 1
    rw [a5FourthD4BlockPerm_apply_one]; rfl
  · change a5FourthD4.componentType (a5FourthD4BlockPerm 2) = a5FourthD4.componentType 2
    rw [a5FourthD4BlockPerm_apply_two]; rfl
  · change a5FourthD4.componentType (a5FourthD4BlockPerm 3) = a5FourthD4.componentType 3
    rw [a5FourthD4BlockPerm_apply_three]; rfl
  · change a5FourthD4.componentType (a5FourthD4BlockPerm 4) = a5FourthD4.componentType 4
    rw [a5FourthD4BlockPerm_apply_four]

/-- `a5FourthD4BlockPerm⁻¹` preserves the component Dynkin types of `A₅⁴ D₄`. -/
theorem componentType_a5FourthD4_a5FourthD4BlockPerm_inv (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k) = a5FourthD4.componentType k := by
  fin_cases k
  · change a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ 0) = a5FourthD4.componentType 0
    rw [a5FourthD4BlockPerm_inv_apply_zero]
  · change a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ 1) = a5FourthD4.componentType 1
    rw [a5FourthD4BlockPerm_inv_apply_one]; rfl
  · change a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ 2) = a5FourthD4.componentType 2
    rw [a5FourthD4BlockPerm_inv_apply_two]; rfl
  · change a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ 3) = a5FourthD4.componentType 3
    rw [a5FourthD4BlockPerm_inv_apply_three]; rfl
  · change a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ 4) = a5FourthD4.componentType 4
    rw [a5FourthD4BlockPerm_inv_apply_four]

/-! ### Action of block rotation plus `D₄` triality on glue words -/

/-- The componentwise root-lattice self-isometry applying `typeD4Triality` on the `D₄` component at
position `4` and the identity on the four `A₅` components. -/
private noncomputable def a5FourthD4TrialityRootComponent
    (k : Fin a5FourthD4.components.length) :
    IntegralLattice.Isometry
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k))
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k)) :=
  if hk : k = 4 then
    hk ▸ typeD4Triality (a5FourthD4.isSimplyLaced_componentType 4)
  else
    1

/-- The componentwise glue-alphabet self-isometry applying `typeD4GlueAlphabetTriality` on the `D₄`
component at position `4` and the identity on the four `A₅` components. -/
private noncomputable def a5FourthD4TrialityGlueComponent
    (k : Fin a5FourthD4.components.length) :
    FiniteQuadraticModule.Isometry
      ((a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k))
      ((a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)) :=
  if hk : k = 4 then
    hk ▸ typeD4GlueAlphabetTriality (a5FourthD4.isSimplyLaced_componentType 4)
  else
    QuadraticMap.IsometryEquiv.refl _

private theorem glueAlphabetIsometry_a5FourthD4TrialityGlueComponent
    (k : Fin a5FourthD4.components.length)
    (x : (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)) :
    (a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
        (a5FourthD4.isSimplyLaced_componentType k) (a5FourthD4TrialityGlueComponent k x) =
      (a5FourthD4TrialityRootComponent k).discriminantQuadraticIsometry
        ((a5FourthD4.componentType k).isEven_rootLattice
          (a5FourthD4.isSimplyLaced_componentType k))
        ((a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
          (a5FourthD4.isSimplyLaced_componentType k) x) := by
  by_cases hk : k = 4
  · subst hk
    simp only [a5FourthD4TrialityGlueComponent, a5FourthD4TrialityRootComponent, ↓reduceDIte]
    exact glueAlphabetIsometry_typeD4GlueAlphabetTriality
      (a5FourthD4.isSimplyLaced_componentType 4) (a5FourthD4.valid_componentType 4) x
  · have hg : a5FourthD4TrialityGlueComponent k x = x := by
      simp only [a5FourthD4TrialityGlueComponent, hk, ↓reduceDIte]
      rfl
    have hr : a5FourthD4TrialityRootComponent k = 1 := by
      simp only [a5FourthD4TrialityRootComponent, hk, ↓reduceDIte]
    rw [hg, hr]
    refine ((Isometry.discriminantQuadraticIsometry_apply _ _ _).trans ?_).symm
    rw [Isometry.one_def, Isometry.discriminantGroupEquiv_refl]
    rfl

/-- **The block-triality isometry on the glue module of `A₅⁴ D₄`**: it reads component `k` from
`a5FourthD4BlockPerm⁻¹ k` and applies `typeD4GlueAlphabetTriality` on the `D₄` component at
position `4`. -/
noncomputable def a5FourthD4BlockTrialityGlueEquiv :
    FiniteQuadraticModule.Isometry a5FourthD4.glueModule a5FourthD4.glueModule :=
  (piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
      a5FourthD4BlockPerm⁻¹ componentType_a5FourthD4_a5FourthD4BlockPerm_inv
      (hs := a5FourthD4.isSimplyLaced_componentType)).trans
    (QuadraticMap.IsometryEquiv.pi a5FourthD4TrialityGlueComponent)

private theorem a5FourthD4BlockTrialityGlueEquiv_apply_aux (w : a5FourthD4.glueModule)
    (k : Fin a5FourthD4.components.length) :
    a5FourthD4BlockTrialityGlueEquiv w k =
      a5FourthD4TrialityGlueComponent k
        (FiniteQuadraticModule.Isometry.ofEq
          (glueAlphabet_congr (componentType_a5FourthD4_a5FourthD4BlockPerm_inv k)
            (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k))
            (a5FourthD4.isSimplyLaced_componentType k))
          (w (a5FourthD4BlockPerm⁻¹ k))) := by
  change a5FourthD4TrialityGlueComponent k
      (piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        a5FourthD4BlockPerm⁻¹ componentType_a5FourthD4_a5FourthD4BlockPerm_inv
        (hs := a5FourthD4.isSimplyLaced_componentType) w k) = _
  rw [piGlueAlphabetCongr_apply]

private theorem ofEq_glueAlphabet_apply_eq (w : a5FourthD4.glueModule)
    {a b : Fin a5FourthD4.components.length} (hab : a = b)
    {t : DynkinType} {ht : t.IsSimplyLaced} (ha : a5FourthD4.componentType a = t)
    (hb : a5FourthD4.componentType b = t) :
    FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_congr ha (a5FourthD4.isSimplyLaced_componentType a) ht) (w a) =
      FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_congr hb (a5FourthD4.isSimplyLaced_componentType b) ht) (w b) := by
  subst hab
  rfl

/-- `a5FourthD4BlockTrialityGlueEquiv` fixes the `A₅` glue label in position `0`. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueEquiv_apply_zero (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueEquiv w 0 = w 0 := by
  rw [a5FourthD4BlockTrialityGlueEquiv_apply_aux, a5FourthD4TrialityGlueComponent,
    dite_eq_right (by decide)]
  exact (ofEq_glueAlphabet_apply_eq w a5FourthD4BlockPerm_inv_apply_zero
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 0) rfl).trans
    ((FiniteQuadraticModule.Isometry.ofEq_apply _ (w 0)).trans (cast_eq _ (w 0)))

/-- `a5FourthD4BlockTrialityGlueEquiv` reads the `A₅` glue label in position `1` from
position `3`. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueEquiv_apply_one (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueEquiv w 1 = w 3 := by
  rw [a5FourthD4BlockTrialityGlueEquiv_apply_aux, a5FourthD4TrialityGlueComponent,
    dite_eq_right (by decide)]
  exact (ofEq_glueAlphabet_apply_eq w a5FourthD4BlockPerm_inv_apply_one
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 1) rfl).trans
    ((FiniteQuadraticModule.Isometry.ofEq_apply _ (w 3)).trans (cast_eq _ (w 3)))

/-- `a5FourthD4BlockTrialityGlueEquiv` reads the `A₅` glue label in position `2` from
position `1`. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueEquiv_apply_two (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueEquiv w 2 = w 1 := by
  rw [a5FourthD4BlockTrialityGlueEquiv_apply_aux, a5FourthD4TrialityGlueComponent,
    dite_eq_right (by decide)]
  exact (ofEq_glueAlphabet_apply_eq w a5FourthD4BlockPerm_inv_apply_two
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 2) rfl).trans
    ((FiniteQuadraticModule.Isometry.ofEq_apply _ (w 1)).trans (cast_eq _ (w 1)))

/-- `a5FourthD4BlockTrialityGlueEquiv` reads the `A₅` glue label in position `3` from
position `2`. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueEquiv_apply_three (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueEquiv w 3 = w 2 := by
  rw [a5FourthD4BlockTrialityGlueEquiv_apply_aux, a5FourthD4TrialityGlueComponent,
    dite_eq_right (by decide)]
  exact (ofEq_glueAlphabet_apply_eq w a5FourthD4BlockPerm_inv_apply_three
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 3) rfl).trans
    ((FiniteQuadraticModule.Isometry.ofEq_apply _ (w 2)).trans (cast_eq _ (w 2)))

/-- On the `D₄` glue label in position `4`, `a5FourthD4BlockTrialityGlueEquiv` acts by
`typeD4GlueAlphabetTriality`. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueEquiv_apply_four (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueEquiv w 4 =
      typeD4GlueAlphabetTriality (a5FourthD4.isSimplyLaced_componentType 4) (w 4) := by
  rw [a5FourthD4BlockTrialityGlueEquiv_apply_aux, a5FourthD4TrialityGlueComponent,
    dite_eq_left rfl]
  exact congrArg (typeD4GlueAlphabetTriality (a5FourthD4.isSimplyLaced_componentType 4))
    ((ofEq_glueAlphabet_apply_eq w a5FourthD4BlockPerm_inv_apply_four
      (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 4) rfl).trans
      ((FiniteQuadraticModule.Isometry.ofEq_apply _ (w 4)).trans (cast_eq _ (w 4))))

/-- Applying `a5FourthD4BlockTrialityGlueEquiv` three times fixes every glue word. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueEquiv_apply_apply_apply (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueEquiv
        (a5FourthD4BlockTrialityGlueEquiv (a5FourthD4BlockTrialityGlueEquiv w)) = w := by
  funext k
  fin_cases k
  · exact (a5FourthD4BlockTrialityGlueEquiv_apply_zero _).trans
      ((a5FourthD4BlockTrialityGlueEquiv_apply_zero _).trans
        (a5FourthD4BlockTrialityGlueEquiv_apply_zero w))
  · exact (a5FourthD4BlockTrialityGlueEquiv_apply_one _).trans
      ((a5FourthD4BlockTrialityGlueEquiv_apply_three _).trans
        (a5FourthD4BlockTrialityGlueEquiv_apply_two w))
  · exact (a5FourthD4BlockTrialityGlueEquiv_apply_two _).trans
      ((a5FourthD4BlockTrialityGlueEquiv_apply_one _).trans
        (a5FourthD4BlockTrialityGlueEquiv_apply_three w))
  · exact (a5FourthD4BlockTrialityGlueEquiv_apply_three _).trans
      ((a5FourthD4BlockTrialityGlueEquiv_apply_two _).trans
        (a5FourthD4BlockTrialityGlueEquiv_apply_one w))
  · exact (a5FourthD4BlockTrialityGlueEquiv_apply_four _).trans <|
      (congrArg (typeD4GlueAlphabetTriality (a5FourthD4.isSimplyLaced_componentType 4))
        ((a5FourthD4BlockTrialityGlueEquiv_apply_four _).trans
          (congrArg (typeD4GlueAlphabetTriality (a5FourthD4.isSimplyLaced_componentType 4))
            (a5FourthD4BlockTrialityGlueEquiv_apply_four w)))).trans
      (typeD4GlueAlphabetTriality_apply_apply_apply
        (a5FourthD4.isSimplyLaced_componentType 4) (w 4))

/-- The digit-word transformation corresponding to `a5FourthD4BlockTrialityGlueEquiv`: it cycles
the three marked `A₅` digits `(d₁, d₂, d₃) ↦ (d₃, d₁, d₂)` and cycles the nonzero `D₄` digits
`1 ↦ 2 ↦ 3 ↦ 1`. -/
private def a5FourthD4BlockTrialityDigits (l : List ℕ) : List ℕ :=
  [l.getD 0 0, l.getD 3 0, l.getD 1 0, l.getD 2 0,
    match l.getD 4 0 with
    | 1 => 2
    | 2 => 3
    | 3 => 1
    | d => d]

private theorem encodeGlueWord_a5FourthD4BlockTrialityGlueEquiv (w : a5FourthD4.glueModule) :
    encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        (a5FourthD4BlockTrialityGlueEquiv w) =
      a5FourthD4BlockTrialityDigits
        (encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w) := by
  set l := encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w
  have hl (i : Fin a5FourthD4.components.length) :
      l.getD i 0 =
        (((a5FourthD4.componentType i).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType i)).symm (w i)).val := by
    rw [List.getD_eq_getElem _ _ (by simp [l]), getElem_encodeGlueWord]
  let f : Fin a5FourthD4.components.length → ℕ := fun i ↦
    (((a5FourthD4.componentType i).glueLabelEquiv
      (a5FourthD4.isSimplyLaced_componentType i)).symm
      (a5FourthD4BlockTrialityGlueEquiv w i)).val
  have hofFn : List.ofFn f = [f 0, f 1, f 2, f 3, f 4] := rfl
  rw [encodeGlueWord_def]
  change List.ofFn f = a5FourthD4BlockTrialityDigits l
  rw [hofFn, a5FourthD4BlockTrialityDigits]
  have hf0 : f 0 = l.getD 0 0 :=
    (congrArg
      (fun x ↦ (((A 5).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType 0)).symm x).val)
      (a5FourthD4BlockTrialityGlueEquiv_apply_zero w)).trans (hl 0).symm
  have hf1 : f 1 = l.getD 3 0 :=
    (congrArg
      (fun x ↦ (((A 5).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType 1)).symm x).val)
      (a5FourthD4BlockTrialityGlueEquiv_apply_one w)).trans (hl 3).symm
  have hf2 : f 2 = l.getD 1 0 :=
    (congrArg
      (fun x ↦ (((A 5).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType 2)).symm x).val)
      (a5FourthD4BlockTrialityGlueEquiv_apply_two w)).trans (hl 1).symm
  have hf3 : f 3 = l.getD 2 0 :=
    (congrArg
      (fun x ↦ (((A 5).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType 3)).symm x).val)
      (a5FourthD4BlockTrialityGlueEquiv_apply_three w)).trans (hl 2).symm
  have hf4 : f 4 = (match l.getD 4 0 with | 1 => 2 | 2 => 3 | 3 => 1 | d => d) := by
    obtain ⟨j, hj⟩ :
        ∃ j : Fin 4,
          ((D 4).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType 4)).symm (w 4) = j :=
      ⟨_, rfl⟩
    have hj1 : f 4 = (trialityGlueLabelPerm j).val :=
      congrArg Fin.val <|
        (congrArg (((a5FourthD4.componentType 4).glueLabelEquiv
            (a5FourthD4.isSimplyLaced_componentType 4)).symm)
          (a5FourthD4BlockTrialityGlueEquiv_apply_four w)).trans <|
        (glueLabelEquiv_symm_typeD4GlueAlphabetTriality
          (a5FourthD4.isSimplyLaced_componentType 4) (w 4)).trans
          (congrArg trialityGlueLabelPerm hj)
    have hj2 : l.getD 4 0 = j.val := (hl 4).trans (congrArg Fin.val hj)
    rw [hj1, hj2]
    fin_cases j <;> simp
  rw [hf0, hf1, hf2, hf3, hf4]

private theorem a5FourthD4BlockTrialityDigits_mem_glueWords :
    ∀ l ∈ a5FourthD4.glueWords, a5FourthD4BlockTrialityDigits l ∈ a5FourthD4.glueWords := by
  decide

/-- `a5FourthD4BlockTrialityGlueEquiv` maps `a5FourthD4.glueGenerators` into itself. -/
theorem a5FourthD4BlockTrialityGlueEquiv_mem_glueGenerators {w : a5FourthD4.glueModule}
    (hw : w ∈ a5FourthD4.glueGenerators) :
    a5FourthD4BlockTrialityGlueEquiv w ∈ a5FourthD4.glueGenerators := by
  rw [mem_glueGenerators_iff, encodeGlueWord_a5FourthD4BlockTrialityGlueEquiv]
  exact a5FourthD4BlockTrialityDigits_mem_glueWords _ (mem_glueGenerators_iff.mp hw)

/-- **`a5FourthD4BlockTrialityGlueEquiv` preserves the glue subgroup of `A₅⁴ D₄`.** -/
@[simp]
theorem a5FourthD4BlockTrialityGlueEquiv_mem_glueSubgroup_iff (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueEquiv w ∈ a5FourthD4.glueSubgroup ↔ w ∈ a5FourthD4.glueSubgroup := by
  have hpre : a5FourthD4BlockTrialityGlueEquiv ⁻¹' a5FourthD4.glueGenerators =
      a5FourthD4.glueGenerators := by
    ext v
    refine ⟨fun hv ↦ ?_, fun hv ↦ a5FourthD4BlockTrialityGlueEquiv_mem_glueGenerators hv⟩
    have hv3 := a5FourthD4BlockTrialityGlueEquiv_mem_glueGenerators
      (a5FourthD4BlockTrialityGlueEquiv_mem_glueGenerators hv)
    rwa [a5FourthD4BlockTrialityGlueEquiv_apply_apply_apply] at hv3
  have hmap : a5FourthD4.glueSubgroup.map
      (a5FourthD4BlockTrialityGlueEquiv : a5FourthD4.glueModule →+ a5FourthD4.glueModule) =
        a5FourthD4.glueSubgroup := by
    rw [glueSubgroup_def, AddMonoidHom.map_closure, AddMonoidHom.coe_ofClass]
    exact congrArg AddSubgroup.closure ((congrArg _ hpre.symm).trans
      (Set.image_preimage_eq _ (EquivLike.surjective a5FourthD4BlockTrialityGlueEquiv)))
  have h := AddSubgroup.mem_map_iff_mem
    (f := (a5FourthD4BlockTrialityGlueEquiv : a5FourthD4.glueModule →+ a5FourthD4.glueModule))
    (by rw [AddMonoidHom.coe_ofClass]; exact EquivLike.injective a5FourthD4BlockTrialityGlueEquiv)
    (K := a5FourthD4.glueSubgroup) (x := w)
  rwa [hmap, AddMonoidHom.coe_ofClass] at h

/-! ### The lifted self-isometry of `a5FourthD4.lattice` -/

private noncomputable def a5FourthD4BlockTrialityRootComponent
    (k : Fin a5FourthD4.components.length) :
    IntegralLattice.Isometry
      ((a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k)).rootLattice
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k)))
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k)) :=
  ((a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k)).rootLatticeIsometryOfEq
    (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k))
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv k)
    (a5FourthD4.isSimplyLaced_componentType k)).trans (a5FourthD4TrialityRootComponent k)

private theorem glueAlphabetIsometry_a5FourthD4BlockTrialityRootComponent
    (k : Fin a5FourthD4.components.length)
    (x : (a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k)).glueAlphabet
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k))) :
    (a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
        (a5FourthD4.isSimplyLaced_componentType k)
        (a5FourthD4TrialityGlueComponent k
          (FiniteQuadraticModule.Isometry.ofEq
            (glueAlphabet_congr (componentType_a5FourthD4_a5FourthD4BlockPerm_inv k)
              (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k))
              (a5FourthD4.isSimplyLaced_componentType k)) x)) =
      (a5FourthD4BlockTrialityRootComponent k).discriminantQuadraticIsometry
        ((a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k)).isEven_rootLattice
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k)))
        ((a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k)).glueAlphabetIsometry
          (a5FourthD4.valid_componentType (a5FourthD4BlockPerm⁻¹ k))
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k)) x) := by
  let e₁ := (a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k)).rootLatticeIsometryOfEq
    (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k))
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv k)
    (a5FourthD4.isSimplyLaced_componentType k)
  let e₂ := a5FourthD4TrialityRootComponent k
  have h1 : (a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
      (a5FourthD4.isSimplyLaced_componentType k)
      (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_congr (componentType_a5FourthD4_a5FourthD4BlockPerm_inv k)
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k))
          (a5FourthD4.isSimplyLaced_componentType k)) x) =
      e₁.discriminantGroupEquiv
        ((a5FourthD4.componentType (a5FourthD4BlockPerm⁻¹ k)).glueAlphabetIsometry
          (a5FourthD4.valid_componentType (a5FourthD4BlockPerm⁻¹ k))
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k)) x) :=
    (glueAlphabetIsometry_ofEq (componentType_a5FourthD4_a5FourthD4BlockPerm_inv k) _ _ _ _ x).trans
      (Isometry.discriminantQuadraticIsometry_apply e₁ _ _)
  exact (glueAlphabetIsometry_a5FourthD4TrialityGlueComponent k _).trans <|
    (Isometry.discriminantQuadraticIsometry_apply e₂ _ _).trans <|
    (congrArg e₂.discriminantGroupEquiv h1).trans <|
    ((LinearEquiv.congr_fun (Isometry.discriminantGroupEquiv_trans e₁ e₂) _).trans
      (LinearEquiv.trans_apply _)).symm.trans
    (Isometry.discriminantQuadraticIsometry_apply
      (a5FourthD4BlockTrialityRootComponent k) _ _).symm

/-- **The block-triality self-isometry of `N_(A₅⁴ D₄)`**: it fixes the first `A₅` component,
rotates the next three `A₅` components `1 ↦ 2 ↦ 3 ↦ 1`, and applies `typeD4Triality` on the `D₄`
component at position `4`. -/
noncomputable def a5FourthD4BlockTrialityIsometry :
    IntegralLattice.Isometry a5FourthD4.lattice a5FourthD4.lattice :=
  (Isometry.ofEq (lattice_def a5FourthD4)).trans <|
    (gluedLatticePiCongrIsometry a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
      a5FourthD4.valid_componentType a5FourthD4.glueSubgroup a5FourthD4.isIsotropic_glueSubgroup
      a5FourthD4.valid_componentType a5FourthD4.isIsotropic_glueSubgroup a5FourthD4BlockPerm⁻¹
      a5FourthD4BlockTrialityRootComponent
      (fun k x ↦ a5FourthD4TrialityGlueComponent k
        (FiniteQuadraticModule.Isometry.ofEq
          (glueAlphabet_congr (componentType_a5FourthD4_a5FourthD4BlockPerm_inv k)
            (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm⁻¹ k))
            (a5FourthD4.isSimplyLaced_componentType k)) x))
      glueAlphabetIsometry_a5FourthD4BlockTrialityRootComponent
      fun w ↦
        (congrArg (· ∈ a5FourthD4.glueSubgroup)
          (funext (a5FourthD4BlockTrialityGlueEquiv_apply_aux w)).symm).to_iff.trans
          (a5FourthD4BlockTrialityGlueEquiv_mem_glueSubgroup_iff w)).trans
    (Isometry.ofEq (lattice_def a5FourthD4).symm)

private theorem a5FourthD4BlockTrialityIsometry_apply_aux
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) (k : Fin a5FourthD4.components.length) :
    a5FourthD4BlockTrialityIsometry x k =
      a5FourthD4BlockTrialityRootComponent k (x (a5FourthD4BlockPerm⁻¹ k)) := by
  rw [a5FourthD4BlockTrialityIsometry, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticePiCongrIsometry_apply]

private theorem rootLatticeIsometryOfEq_eq_of_eq
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ)
    {a b k : Fin a5FourthD4.components.length} (hab : a = b)
    (ha : a5FourthD4.componentType a = a5FourthD4.componentType k)
    (hbk : a5FourthD4.componentType b = a5FourthD4.componentType k)
    (y : Fin (a5FourthD4.componentType k).rank → ℚ)
    (hy : ∀ j, x b (Fin.cast (congrArg rank hbk).symm j) = y j) :
    (a5FourthD4.componentType a).rootLatticeIsometryOfEq
        (a5FourthD4.isSimplyLaced_componentType a) ha
        (a5FourthD4.isSimplyLaced_componentType k) (x a) = y := by
  subst hab
  ext j
  rw [rootLatticeIsometryOfEq_apply]
  exact hy j

/-- `a5FourthD4BlockTrialityIsometry` fixes the `A₅` component in position `0`. -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockTrialityIsometry x 0 = x 0 := by
  rw [a5FourthD4BlockTrialityIsometry_apply_aux, a5FourthD4BlockTrialityRootComponent,
    Isometry.trans_apply, a5FourthD4TrialityRootComponent, dite_eq_right (by decide),
    Isometry.one_apply]
  exact rootLatticeIsometryOfEq_eq_of_eq x a5FourthD4BlockPerm_inv_apply_zero
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 0) rfl (x 0)
    fun j ↦ congrArg (x 0) (Fin.cast_eq_self j)

/-- `a5FourthD4BlockTrialityIsometry` reads position `1` from position `3`. -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockTrialityIsometry x 1 = x 3 := by
  rw [a5FourthD4BlockTrialityIsometry_apply_aux, a5FourthD4BlockTrialityRootComponent,
    Isometry.trans_apply, a5FourthD4TrialityRootComponent, dite_eq_right (by decide),
    Isometry.one_apply]
  exact rootLatticeIsometryOfEq_eq_of_eq x a5FourthD4BlockPerm_inv_apply_one
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 1) rfl (x 3)
    fun j ↦ congrArg (x 3) (Fin.cast_eq_self j)

/-- `a5FourthD4BlockTrialityIsometry` reads position `2` from position `1`. -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockTrialityIsometry x 2 = x 1 := by
  rw [a5FourthD4BlockTrialityIsometry_apply_aux, a5FourthD4BlockTrialityRootComponent,
    Isometry.trans_apply, a5FourthD4TrialityRootComponent, dite_eq_right (by decide),
    Isometry.one_apply]
  exact rootLatticeIsometryOfEq_eq_of_eq x a5FourthD4BlockPerm_inv_apply_two
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 2) rfl (x 1)
    fun j ↦ congrArg (x 1) (Fin.cast_eq_self j)

/-- `a5FourthD4BlockTrialityIsometry` reads position `3` from position `2`. -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockTrialityIsometry x 3 = x 2 := by
  rw [a5FourthD4BlockTrialityIsometry_apply_aux, a5FourthD4BlockTrialityRootComponent,
    Isometry.trans_apply, a5FourthD4TrialityRootComponent, dite_eq_right (by decide),
    Isometry.one_apply]
  exact rootLatticeIsometryOfEq_eq_of_eq x a5FourthD4BlockPerm_inv_apply_three
    (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 3) rfl (x 2)
    fun j ↦ congrArg (x 2) (Fin.cast_eq_self j)

/-- On the `D₄` component in position `4`, `a5FourthD4BlockTrialityIsometry` acts by
`typeD4Triality`. -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_apply_four
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockTrialityIsometry x 4 =
      typeD4Triality (a5FourthD4.isSimplyLaced_componentType 4) (x 4) := by
  rw [a5FourthD4BlockTrialityIsometry_apply_aux, a5FourthD4BlockTrialityRootComponent,
    Isometry.trans_apply, a5FourthD4TrialityRootComponent, dite_eq_left rfl]
  exact congrArg (typeD4Triality (a5FourthD4.isSimplyLaced_componentType 4))
    (rootLatticeIsometryOfEq_eq_of_eq x a5FourthD4BlockPerm_inv_apply_four
      (componentType_a5FourthD4_a5FourthD4BlockPerm_inv 4) rfl (x 4)
      fun j ↦ congrArg (x 4) (Fin.cast_eq_self j))

/-- **`a5FourthD4BlockTrialityIsometry` has exponent three.** -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_pow_three :
    a5FourthD4BlockTrialityIsometry ^ 3 = 1 := by
  refine Isometry.ext fun x ↦ funext fun k ↦ ?_
  simp only [pow_three, Isometry.mul_apply, Isometry.one_apply]
  fin_cases k
  · change a5FourthD4BlockTrialityIsometry _ 0 = x 0
    simp
  · change a5FourthD4BlockTrialityIsometry _ 1 = x 1
    simp
  · change a5FourthD4BlockTrialityIsometry _ 2 = x 2
    simp
  · change a5FourthD4BlockTrialityIsometry _ 3 = x 3
    simp
  · change a5FourthD4BlockTrialityIsometry _ 4 = x 4
    simp only [a5FourthD4BlockTrialityIsometry_apply_four]
    have htri (ht : (D 4).IsSimplyLaced) (y : Fin (D 4).rank → ℚ) :
        typeD4Triality ht (typeD4Triality ht (typeD4Triality ht y)) = y := by
      have h := congrArg (fun f ↦ f y) (typeD4Triality_pow_three ht)
      simpa only [pow_three, Isometry.mul_apply, Isometry.one_apply] using h
    exact htri (a5FourthD4.isSimplyLaced_componentType 4) (x 4)

/-- `a5FourthD4BlockTrialityIsometry` moves the second `A₅` component, so it is not the identity. -/
theorem a5FourthD4BlockTrialityIsometry_ne_one :
    a5FourthD4BlockTrialityIsometry ≠ 1 := fun h ↦ by
  let v : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ :=
    Pi.single (1 : Fin a5FourthD4.components.length) (fun _ ↦ 1)
  let j₀ : Fin (a5FourthD4.componentType 2).rank := ⟨0, by decide⟩
  have hv := congrArg (fun f : Isometry a5FourthD4.lattice a5FourthD4.lattice ↦ f v 2 j₀) h
  rw [a5FourthD4BlockTrialityIsometry_apply_two, Isometry.one_apply] at hv
  have h1 : v 1 j₀ = 1 := by simp [v]
  have h2 : v 2 j₀ = 0 := by simp [v]
  linarith

/-- **`a5FourthD4BlockTrialityIsometry` has order exactly three.** -/
@[simp]
theorem orderOf_a5FourthD4BlockTrialityIsometry :
    orderOf a5FourthD4BlockTrialityIsometry = 3 :=
  orderOf_eq_prime a5FourthD4BlockTrialityIsometry_pow_three
    a5FourthD4BlockTrialityIsometry_ne_one

/-! ### Action of the pattern symmetries of `A₅⁴ D₄` on `a5FourthD4.lattice` -/

private theorem symmetries_a5FourthD4Cyclic :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries =
      Subgroup.zpowers
        (a5FourthD4BlockPerm :
          Equiv.Perm (Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length)) := by
  rw [GluePattern.symmetries_cyclic]
  exact congrArg Subgroup.zpowers a5FourthD4BlockPerm_eq_finSumPerm.symm

/-- The canonical block-rotation generator of
`(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`. -/
def a5FourthD4CyclicSymmetryGen : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries :=
  ⟨a5FourthD4BlockPerm,
    symmetries_a5FourthD4Cyclic.ge (Subgroup.mem_zpowers _)⟩

/-- Coercing `a5FourthD4CyclicSymmetryGen` to a permutation recovers `a5FourthD4BlockPerm`. -/
@[simp]
theorem val_a5FourthD4CyclicSymmetryGen :
    (a5FourthD4CyclicSymmetryGen.val : Equiv.Perm (Fin a5FourthD4.components.length)) =
      a5FourthD4BlockPerm :=
  (rfl)

/-- **The block rotations of `[2(024)0]` act on `a5FourthD4.lattice`** by mapping the canonical
generator to `a5FourthD4BlockTrialityIsometry`. -/
noncomputable def a5FourthD4CyclicSymmetryHom :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries →*
      IntegralLattice.Isometry a5FourthD4.lattice a5FourthD4.lattice :=
  monoidHomOfForallMemZpowers (g := a5FourthD4CyclicSymmetryGen)
    (fun x ↦ by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (symmetries_a5FourthD4Cyclic.le x.2)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩)
    (by
      rw [orderOf_a5FourthD4BlockTrialityIsometry, ← Subgroup.orderOf_coe]
      exact (orderOf_a5FourthD4BlockPerm : orderOf a5FourthD4CyclicSymmetryGen.val = 3).symm.dvd)

/-- `a5FourthD4CyclicSymmetryHom` maps the canonical block-rotation generator to
`a5FourthD4BlockTrialityIsometry`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_gen :
    a5FourthD4CyclicSymmetryHom a5FourthD4CyclicSymmetryGen =
      a5FourthD4BlockTrialityIsometry :=
  monoidHomOfForallMemZpowers_apply_gen _ _

/-- `a5FourthD4CyclicSymmetryHom` is injective: the three rotations of `[2(024)0]` act faithfully
on `a5FourthD4.lattice`. -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, a5FourthD4CyclicSymmetryGen ^ n = x := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (symmetries_a5FourthD4Cyclic.le x.2)
    exact ⟨n, Subtype.ext hn⟩
  rw [MonoidHom.mem_ker, map_zpow, a5FourthD4CyclicSymmetryHom_gen,
    ← orderOf_dvd_iff_zpow_eq_one, orderOf_a5FourthD4BlockTrialityIsometry] at hx
  rw [← orderOf_dvd_iff_zpow_eq_one, ← Subgroup.orderOf_coe]
  have hord : orderOf a5FourthD4CyclicSymmetryGen.val = 3 := orderOf_a5FourthD4BlockPerm
  rwa [hord]

/-- **Every pattern of `A₅⁴ D₄` acts on `a5FourthD4.lattice`**: `[2(024)0]` acts through
`a5FourthD4CyclicSymmetryHom` (block rotation paired with `D₄` triality), and the three literal
patterns have trivial symmetry group and act trivially. -/
noncomputable def a5FourthD4PatternIsometryHom :
    {p : GluePattern} → p ∈ a5FourthD4.gluePatterns →
      p.symmetries →* IntegralLattice.Isometry a5FourthD4.lattice a5FourthD4.lattice
  | .literal _, _ => 1
  | .cyclic pre block post, hp =>
    have heq : GluePattern.cyclic pre block post = .cyclic [2] [0, 2, 4] [0] := by
      simp only [gluePatterns, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hp
      exact hp
    heq ▸ a5FourthD4CyclicSymmetryHom
  | .evenPermutations _, hp => by
    simp [gluePatterns] at hp

/-- On the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`, `a5FourthD4PatternIsometryHom` is
`a5FourthD4CyclicSymmetryHom`. -/
@[simp]
theorem a5FourthD4PatternIsometryHom_cyclic
    (hp : .cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns) :
    a5FourthD4PatternIsometryHom hp = a5FourthD4CyclicSymmetryHom :=
  (rfl)

/-- On any literal pattern of `A₅⁴ D₄`, `a5FourthD4PatternIsometryHom` is trivial. -/
@[simp]
theorem a5FourthD4PatternIsometryHom_literal {w : List ℕ}
    (hp : .literal w ∈ a5FourthD4.gluePatterns) :
    a5FourthD4PatternIsometryHom hp = 1 :=
  (rfl)

/-- **Every pattern of `A₅⁴ D₄` acts faithfully on `a5FourthD4.lattice`.** -/
theorem a5FourthD4PatternIsometryHom_injective {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) :
    Function.Injective (a5FourthD4PatternIsometryHom hp) := by
  have hp' := hp
  simp only [gluePatterns, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl
  · exact a5FourthD4CyclicSymmetryHom_injective
  all_goals
    intro g h _
    exact Subtype.ext
      ((Subgroup.mem_bot.mp ((GluePattern.symmetries_literal _).le g.2)).trans
        (Subgroup.mem_bot.mp ((GluePattern.symmetries_literal _).le h.2)).symm)

end RootfulNiemeierType

end TauCeti
