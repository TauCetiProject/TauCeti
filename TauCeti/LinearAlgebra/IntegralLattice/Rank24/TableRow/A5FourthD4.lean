/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality

/-!
# Coupled block-rotation and `D₄`-triality symmetry of the table row `A₅⁴ D₄`

The row `A₅⁴ D₄` (`TauCeti.RootfulNiemeierType.a5FourthD4`) of Conway--Sloane Table 16.1 has five
ordered components `(A₅, A₅, A₅, A₅, D₄)` and glue columns

`[2(024)0], [33001], [30302], [30033]`.

As characterized across all 23 rows by
`TauCeti.RootfulNiemeierType.forall_permCongr_mem_glueSymmetries_iff` (proved from
`TauCeti.RootfulNiemeierType.permCongr_finRotate_not_mem_glueSymmetries_a5FourthD4` in
`TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.Symmetry`), `A₅⁴ D₄` is the unique row of
the rootful rank-24 table whose indicated pattern symmetries are not pure position glue symmetries:
rotating the three `A₅` positions `1 ↦ 2 ↦ 3 ↦ 1` marked in `[2(024)0]` while fixing the `D₄` label
in position `4` carries `[33001]` out of the glue subgroup.

To preserve the full glue subgroup of `A₅⁴ D₄`, the 3-cycle `1 ↦ 2 ↦ 3 ↦ 1` on the three marked
`A₅` components (`TauCeti.RootfulNiemeierType.a5FourthD4BlockRot`) must be coupled with the
order-three triality automorphism `TauCeti.DynkinType.typeD4Triality` on the `D₄` component in
position `4`, which fixes the `D₄` glue label `0` and cycles `1 ↦ 2 ↦ 3 ↦ 1` (`s ↦ v ↦ c ↦ s`) via
`TauCeti.DynkinType.typeD4GlueAlphabetTriality`.  That coupled transformation fixes the `0` suffix
of `[2(024)0]` while rotating `(024)`, and cycles `[33001] ↦ [30302] ↦ [30033] ↦ [33001]`.

Using `QuadraticMap.IsometryEquiv.piCongr'` and
`TauCeti.DynkinType.gluedLatticePiCongrIsometry'`, this file constructs:

* `TauCeti.RootfulNiemeierType.a5FourthD4BlockTrialityGlueIsometry`: the coupled quadratic
  self-isometry of `a5FourthD4.glueModule`, which permutes `a5FourthD4.glueGenerators` and
  preserves `a5FourthD4.glueSubgroup`.
* `TauCeti.niemeierA5FourthD4BlockTriality`: the induced proper self-isometry of
  `TauCeti.niemeierA5FourthD4` of order `3`, acting by cyclic shift on `A₅` positions `1, 2, 3`,
  fixing `A₅` position `0`, and acting by `typeD4Triality` on `D₄` position `4`.
* `TauCeti.RootfulNiemeierType.a5FourthD4PatternIsometryHom`: the faithful action of `p.symmetries`
  on `niemeierA5FourthD4` for every pattern `p ∈ a5FourthD4.gluePatterns` (combined with the other
  22 rows into `TauCeti.RootfulNiemeierType.patternTrialityIsometryHom` in
  `TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.Symmetry`).

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4BlockRot`: the 3-cycle `1 ↦ 2 ↦ 3 ↦ 1` on the five
  component positions of `A₅⁴ D₄`, identified with the rotated block of `[2(024)0]` by
  `permCongr_finRotate_eq_a5FourthD4BlockRot`.
* `TauCeti.RootfulNiemeierType.a5FourthD4BlockTrialityGlueIsometry`,
  `a5FourthD4BlockTrialityGlueIsometry_mem_glueGenerators_iff`,
  `a5FourthD4BlockTrialityGlueIsometry_mem_glueSubgroup_iff`: the coupled glue-word isometry and
  its invariance of the glue generators and glue subgroup.
* `TauCeti.niemeierA5FourthD4BlockTriality`, `niemeierA5FourthD4BlockTriality_pow_three`,
  `orderOf_niemeierA5FourthD4BlockTriality`, `det_niemeierA5FourthD4BlockTriality`: the order-`3`
  proper self-isometry of `niemeierA5FourthD4`.
* `TauCeti.RootfulNiemeierType.a5FourthD4PatternIsometryHom`,
  `a5FourthD4PatternIsometryHom_literal`, `a5FourthD4PatternIsometryHom_mk_finRotate`,
  `exists_a5FourthD4PatternIsometryHom_eq_pow`, `det_a5FourthD4PatternIsometryHom`,
  `a5FourthD4PatternIsometryHom_injective`: the faithful pattern-symmetry action on `A₅⁴ D₄`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7.1, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### Component structure and block rotation of `A₅⁴ D₄` -/

/-- The row `A₅⁴ D₄` has five ordered components. -/
theorem length_components_a5FourthD4 : a5FourthD4.components.length = 5 :=
  (rfl)

/-- Position `0` of `A₅⁴ D₄` has type `A₅`. -/
theorem componentType_a5FourthD4_zero : a5FourthD4.componentType 0 = .A 5 :=
  (rfl)

/-- Position `1` of `A₅⁴ D₄` has type `A₅`. -/
theorem componentType_a5FourthD4_one : a5FourthD4.componentType 1 = .A 5 :=
  (rfl)

/-- Position `2` of `A₅⁴ D₄` has type `A₅`. -/
theorem componentType_a5FourthD4_two : a5FourthD4.componentType 2 = .A 5 :=
  (rfl)

/-- Position `3` of `A₅⁴ D₄` has type `A₅`. -/
theorem componentType_a5FourthD4_three : a5FourthD4.componentType 3 = .A 5 :=
  (rfl)

/-- Position `4` of `A₅⁴ D₄` has type `D₄`. -/
theorem componentType_a5FourthD4_four : a5FourthD4.componentType 4 = .D 4 :=
  (rfl)

/-- The expanded Conway--Sloane digit words of `A₅⁴ D₄` are the three rotations of `[2(024)0]`
together with `[33001]`, `[30302]`, and `[30033]`. -/
theorem glueWords_a5FourthD4 :
    a5FourthD4.glueWords =
      {[2, 0, 2, 4, 0], [2, 2, 4, 0, 0], [2, 4, 0, 2, 0],
       [3, 3, 0, 0, 1], [3, 0, 3, 0, 2], [3, 0, 0, 3, 3]} := by
  decide

/-- **The block rotation of `A₅⁴ D₄`**: the 3-cycle `1 ↦ 2 ↦ 3 ↦ 1` on the three `A₅` positions
marked in `[2(024)0]`, fixing position `0` and the `D₄` position `4`. -/
def a5FourthD4BlockRot : Equiv.Perm (Fin a5FourthD4.components.length) :=
  Equiv.swap 1 3 * Equiv.swap 1 2

@[simp]
theorem a5FourthD4BlockRot_zero : a5FourthD4BlockRot 0 = 0 := by decide

@[simp]
theorem a5FourthD4BlockRot_one : a5FourthD4BlockRot 1 = 2 := by decide

@[simp]
theorem a5FourthD4BlockRot_two : a5FourthD4BlockRot 2 = 3 := by decide

@[simp]
theorem a5FourthD4BlockRot_three : a5FourthD4BlockRot 3 = 1 := by decide

@[simp]
theorem a5FourthD4BlockRot_four : a5FourthD4BlockRot 4 = 4 := by decide

@[simp]
theorem a5FourthD4BlockRot_symm_zero : a5FourthD4BlockRot.symm 0 = 0 := by decide

@[simp]
theorem a5FourthD4BlockRot_symm_one : a5FourthD4BlockRot.symm 1 = 3 := by decide

@[simp]
theorem a5FourthD4BlockRot_symm_two : a5FourthD4BlockRot.symm 2 = 1 := by decide

@[simp]
theorem a5FourthD4BlockRot_symm_three : a5FourthD4BlockRot.symm 3 = 2 := by decide

@[simp]
theorem a5FourthD4BlockRot_symm_four : a5FourthD4BlockRot.symm 4 = 4 := by decide

@[simp]
theorem a5FourthD4BlockRot_pow_three : a5FourthD4BlockRot ^ 3 = 1 := by
  decide

theorem a5FourthD4BlockRot_ne_one : a5FourthD4BlockRot ≠ 1 := by
  decide

/-- `a5FourthD4BlockRot` has exact order `3`. -/
@[simp]
theorem orderOf_a5FourthD4BlockRot : orderOf a5FourthD4BlockRot = 3 :=
  orderOf_eq_prime a5FourthD4BlockRot_pow_three a5FourthD4BlockRot_ne_one

/-- `a5FourthD4BlockRot` preserves the Dynkin type at every component position. -/
theorem componentType_a5FourthD4BlockRot (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType (a5FourthD4BlockRot k) = a5FourthD4.componentType k := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide +revert
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp <;> rfl

/-- `a5FourthD4BlockRot.symm` preserves the Dynkin type at every component position. -/
theorem componentType_a5FourthD4BlockRot_symm (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType (a5FourthD4BlockRot.symm k) = a5FourthD4.componentType k := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide +revert
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp <;> rfl

/-- The generator of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`, transported to the
component positions of `A₅⁴ D₄`, is `a5FourthD4BlockRot`. -/
theorem permCongr_finRotate_eq_a5FourthD4BlockRot
    (hlen : (GluePattern.cyclic [2] [0, 2, 4] [0]).length = a5FourthD4.components.length :=
      by decide) :
    (finCongr hlen).permCongr
        (Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate 3)) 1) =
      a5FourthD4BlockRot := by
  -- Evaluate both permutations on the identity digit word `[0, 1, 2, 3, 4]`.
  have hseed : (fun j : Fin (GluePattern.cyclic [0] [1, 2, 3] [4]).length ↦ (j : ℕ)) =
      (GluePattern.cyclic [0] [1, 2, 3] [4]).seed := by
    have h0 := GluePattern.ofFn_seed_cyclic_comp_pow [0] [1, 2, 3] [4] 0
    rw [pow_zero, Equiv.Perm.coe_one] at h0
    exact List.ofFn_injective ((by decide : _ = [0, 1, 2, 3, 4]).trans h0.symm)
  have hrot : List.ofFn (fun j : Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length ↦
        (Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate 3)) 1 j : ℕ)) =
      [0, 2, 3, 1, 4] := by
    have h1 := GluePattern.ofFn_seed_cyclic_comp_pow [0] [1, 2, 3] [4] 1
    rw [pow_one, ← hseed] at h1
    exact h1
  have hlist : List.ofFn (fun k : Fin a5FourthD4.components.length ↦
        (((finCongr hlen).permCongr
          (Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate 3)) 1) k) : ℕ)) =
      List.ofFn (fun k : Fin a5FourthD4.components.length ↦ (a5FourthD4BlockRot k : ℕ)) :=
    (congrArg List.ofFn (funext fun _ ↦ rfl)).trans
      ((List.ofFn_congr hlen _).symm.trans (hrot.trans (by decide)))
  ext k
  exact congrFun (List.ofFn_injective hlist) k

/-! ### Coupled glue-word isometry and preservation of the glue subgroup -/

private theorem componentType_a5FourthD4BlockRot_symm_eq_D4
    {k : Fin a5FourthD4.components.length} (hk : k = 4) :
    a5FourthD4.componentType (a5FourthD4BlockRot.symm k) = .D 4 := by
  rw [hk, a5FourthD4BlockRot_symm_four]
  rfl

private theorem D4_eq_componentType_a5FourthD4
    {k : Fin a5FourthD4.components.length} (hk : k = 4) :
    .D 4 = a5FourthD4.componentType k := by
  rw [hk]
  rfl

/-- Componentwise glue-alphabet isometries for the coupled symmetry of `A₅⁴ D₄`: `D₄` triality on
position `4`, and the canonical type identification on `A₅` positions `0, 1, 2, 3`. -/
private noncomputable def a5FourthD4BlockTrialityGlueComponent
    (k : Fin a5FourthD4.components.length) :
    FiniteQuadraticModule.Isometry
      ((a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).glueAlphabet
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k)))
      ((a5FourthD4.componentType k).glueAlphabet
        (a5FourthD4.isSimplyLaced_componentType k)) :=
  if hk : k = 4 then
    (FiniteQuadraticModule.Isometry.ofEq
      (glueAlphabet_congr (componentType_a5FourthD4BlockRot_symm_eq_D4 hk)
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k))
        (isSimplyLaced_D 4))).trans <|
      (typeD4GlueAlphabetTriality (isSimplyLaced_D 4)).trans
        (FiniteQuadraticModule.Isometry.ofEq
          (glueAlphabet_congr (D4_eq_componentType_a5FourthD4 hk) (isSimplyLaced_D 4)
            (a5FourthD4.isSimplyLaced_componentType k)))
  else
    FiniteQuadraticModule.Isometry.ofEq
      (glueAlphabet_congr (componentType_a5FourthD4BlockRot_symm k)
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k))
        (a5FourthD4.isSimplyLaced_componentType k))

/-- **The coupled glue-word isometry of `A₅⁴ D₄`**: rotates the three marked `A₅` glue labels by
`1 ↦ 2 ↦ 3 ↦ 1`, fixes the leading `A₅` glue label at `0`, and applies `typeD4GlueAlphabetTriality`
(`1 ↦ 2 ↦ 3 ↦ 1`) to the `D₄` glue label at `4`. -/
noncomputable def a5FourthD4BlockTrialityGlueIsometry :
    FiniteQuadraticModule.Isometry a5FourthD4.glueModule a5FourthD4.glueModule :=
  QuadraticMap.IsometryEquiv.piCongr' a5FourthD4BlockRot a5FourthD4BlockTrialityGlueComponent

private theorem a5FourthD4BlockTrialityGlueIsometry_apply (w : a5FourthD4.glueModule)
    (k : Fin a5FourthD4.components.length) :
    a5FourthD4BlockTrialityGlueIsometry w k =
      a5FourthD4BlockTrialityGlueComponent k (w (a5FourthD4BlockRot.symm k)) := by
  rw [a5FourthD4BlockTrialityGlueIsometry, QuadraticMap.IsometryEquiv.piCongr'_apply]

/-- Identifying glue alphabets at equal component indices transports `w a` to `w b`. -/
private theorem glueAlphabet_ofEq_eq_apply (w : a5FourthD4.glueModule)
    {a b : Fin a5FourthD4.components.length} (hab : a = b)
    (ha : (a5FourthD4.componentType a).glueAlphabet
        (a5FourthD4.isSimplyLaced_componentType a) =
      (a5FourthD4.componentType b).glueAlphabet
        (a5FourthD4.isSimplyLaced_componentType b)) :
    FiniteQuadraticModule.Isometry.ofEq ha (w a) = w b := by
  subst hab
  exact (FiniteQuadraticModule.Isometry.ofEq_apply ha (w a)).trans (cast_eq _ _)

/-- Identifying the glue alphabet at index `a = 4` with `(D 4).glueAlphabet` transports `w a` to
`w 4`. -/
private theorem glueAlphabet_ofEq_D4_apply (w : a5FourthD4.glueModule)
    {a : Fin a5FourthD4.components.length} (ha4 : a = 4)
    (ha : (a5FourthD4.componentType a).glueAlphabet
        (a5FourthD4.isSimplyLaced_componentType a) =
      (D 4).glueAlphabet (isSimplyLaced_D 4)) :
    FiniteQuadraticModule.Isometry.ofEq ha (w a) = w 4 := by
  subst ha4
  exact (FiniteQuadraticModule.Isometry.ofEq_apply ha (w 4)).trans (cast_eq _ _)

@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_apply_zero (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry w 0 = w 0 := by
  rw [a5FourthD4BlockTrialityGlueIsometry_apply,
    a5FourthD4BlockTrialityGlueComponent, dite_eq_right (by decide)]
  exact glueAlphabet_ofEq_eq_apply w a5FourthD4BlockRot_symm_zero _

@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_apply_one (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry w 1 = w 3 := by
  rw [a5FourthD4BlockTrialityGlueIsometry_apply,
    a5FourthD4BlockTrialityGlueComponent, dite_eq_right (by decide)]
  exact glueAlphabet_ofEq_eq_apply w a5FourthD4BlockRot_symm_one _

@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_apply_two (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry w 2 = w 1 := by
  rw [a5FourthD4BlockTrialityGlueIsometry_apply,
    a5FourthD4BlockTrialityGlueComponent, dite_eq_right (by decide)]
  exact glueAlphabet_ofEq_eq_apply w a5FourthD4BlockRot_symm_two _

@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_apply_three (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry w 3 = w 2 := by
  rw [a5FourthD4BlockTrialityGlueIsometry_apply,
    a5FourthD4BlockTrialityGlueComponent, dite_eq_right (by decide)]
  exact glueAlphabet_ofEq_eq_apply w a5FourthD4BlockRot_symm_three _

/-- On the `D₄` position `4`, `a5FourthD4BlockTrialityGlueIsometry` acts by
`typeD4GlueAlphabetTriality`. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_apply_four (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry w 4 =
      typeD4GlueAlphabetTriality (isSimplyLaced_D 4) (w 4) := by
  refine (a5FourthD4BlockTrialityGlueIsometry_apply w 4).trans ?_
  have hcomp : a5FourthD4BlockTrialityGlueComponent 4 =
      (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_congr (componentType_a5FourthD4BlockRot_symm_eq_D4 rfl)
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm 4))
          (isSimplyLaced_D 4))).trans
        ((typeD4GlueAlphabetTriality (isSimplyLaced_D 4)).trans
          (FiniteQuadraticModule.Isometry.ofEq
            (glueAlphabet_congr (D4_eq_componentType_a5FourthD4 rfl) (isSimplyLaced_D 4)
              (a5FourthD4.isSimplyLaced_componentType 4)))) :=
    dite_eq_left rfl
  refine (DFunLike.congr_fun hcomp _).trans ?_
  refine (QuadraticMap.IsometryEquiv.trans_apply _ _ _).trans ?_
  refine (QuadraticMap.IsometryEquiv.trans_apply _ _ _).trans ?_
  refine (FiniteQuadraticModule.Isometry.ofEq_apply _ _).trans ?_
  refine (cast_eq _ _).trans ?_
  exact congrArg (typeD4GlueAlphabetTriality (isSimplyLaced_D 4))
    (glueAlphabet_ofEq_D4_apply w a5FourthD4BlockRot_symm_four _)

/-- Applying `a5FourthD4BlockTrialityGlueIsometry` three times returns the original glue word. -/
@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_apply_apply_apply (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry
        (a5FourthD4BlockTrialityGlueIsometry (a5FourthD4BlockTrialityGlueIsometry w)) = w := by
  funext k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide +revert
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · rw [a5FourthD4BlockTrialityGlueIsometry_apply_zero,
      a5FourthD4BlockTrialityGlueIsometry_apply_zero,
      a5FourthD4BlockTrialityGlueIsometry_apply_zero]
  · rw [a5FourthD4BlockTrialityGlueIsometry_apply_one,
      a5FourthD4BlockTrialityGlueIsometry_apply_three,
      a5FourthD4BlockTrialityGlueIsometry_apply_two]
  · rw [a5FourthD4BlockTrialityGlueIsometry_apply_two,
      a5FourthD4BlockTrialityGlueIsometry_apply_one,
      a5FourthD4BlockTrialityGlueIsometry_apply_three]
  · rw [a5FourthD4BlockTrialityGlueIsometry_apply_three,
      a5FourthD4BlockTrialityGlueIsometry_apply_two,
      a5FourthD4BlockTrialityGlueIsometry_apply_one]
  · rw [a5FourthD4BlockTrialityGlueIsometry_apply_four,
      a5FourthD4BlockTrialityGlueIsometry_apply_four,
      a5FourthD4BlockTrialityGlueIsometry_apply_four]
    exact typeD4GlueAlphabetTriality_apply_apply_apply (isSimplyLaced_D 4) (w 4)

/-- **Digits of `a5FourthD4BlockTrialityGlueIsometry`**: positions `0, 1, 2, 3` read the Conway--
Sloane digits of `w` from `0, 3, 1, 2`, while position `4` applies `typeD4TrialityLabelPerm` to the
`D₄` digit of `w 4`. -/
theorem encodeGlueWord_a5FourthD4BlockTrialityGlueIsometry (w : a5FourthD4.glueModule) :
    encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        (a5FourthD4BlockTrialityGlueIsometry w) =
      [(((a5FourthD4.componentType 0).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType 0)).symm (w 0)).val,
       (((a5FourthD4.componentType 3).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType 3)).symm (w 3)).val,
       (((a5FourthD4.componentType 1).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType 1)).symm (w 1)).val,
       (((a5FourthD4.componentType 2).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType 2)).symm (w 2)).val,
       (typeD4TrialityLabelPerm
          (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm (w 4))).val] := by
  let f (k : Fin a5FourthD4.components.length) : ℕ :=
    (((a5FourthD4.componentType k).glueLabelEquiv
      (a5FourthD4.isSimplyLaced_componentType k)).symm
      (a5FourthD4BlockTrialityGlueIsometry w k)).val
  refine (encodeGlueWord_def _ _ _).trans
    ((List.ofFn_congr length_components_a5FourthD4 f).trans ?_)
  simp only [List.ofFn_succ, List.ofFn_zero]
  refine List.ext_getElem (by simp) fun n hn _ ↦ ?_
  match n with
  | 0 =>
    exact congrArg (fun v ↦ (((a5FourthD4.componentType 0).glueLabelEquiv _).symm v).val)
      (a5FourthD4BlockTrialityGlueIsometry_apply_zero w)
  | 1 =>
    exact congrArg (fun v ↦ (((a5FourthD4.componentType 1).glueLabelEquiv _).symm v).val)
      (a5FourthD4BlockTrialityGlueIsometry_apply_one w)
  | 2 =>
    exact congrArg (fun v ↦ (((a5FourthD4.componentType 2).glueLabelEquiv _).symm v).val)
      (a5FourthD4BlockTrialityGlueIsometry_apply_two w)
  | 3 =>
    exact congrArg (fun v ↦ (((a5FourthD4.componentType 3).glueLabelEquiv _).symm v).val)
      (a5FourthD4BlockTrialityGlueIsometry_apply_three w)
  | 4 =>
    exact (congrArg (fun v ↦ (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm v).val)
      (a5FourthD4BlockTrialityGlueIsometry_apply_four w)).trans
      (congrArg Fin.val (glueLabelEquiv_symm_typeD4GlueAlphabetTriality
        (isSimplyLaced_D 4) (w 4)))
  | n + 5 => simp at hn

/-- `a5FourthD4BlockTrialityGlueIsometry` maps every glue generator of `A₅⁴ D₄` to a glue
generator. -/
private theorem a5FourthD4BlockTrialityGlueIsometry_mem_glueGenerators_of_mem
    {w : a5FourthD4.glueModule} (hw : w ∈ a5FourthD4.glueGenerators) :
    a5FourthD4BlockTrialityGlueIsometry w ∈ a5FourthD4.glueGenerators := by
  rw [mem_glueGenerators_iff] at hw ⊢
  have hd4 : (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm (w 4)).val =
      (encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w).getD
        4 0 :=
    (getD_encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w 4).symm
  rw [encodeGlueWord_a5FourthD4BlockTrialityGlueIsometry, ← getD_encodeGlueWord,
    ← getD_encodeGlueWord, ← getD_encodeGlueWord, ← getD_encodeGlueWord]
  generalize ((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm (w 4) = i4 at hd4 ⊢
  have hall : ∀ j : Fin (D 4).glueLabelCount, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  have hi4 := hall i4
  rw [glueWords_a5FourthD4] at hw ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hi4 with rfl | rfl | rfl | rfl <;>
    simp only [typeD4TrialityLabelPerm_zero, typeD4TrialityLabelPerm_one,
      typeD4TrialityLabelPerm_two, typeD4TrialityLabelPerm_three] <;>
    (rcases hw with henc | henc | henc | henc | henc | henc <;>
      (rw [henc] at hd4 ⊢; first | decide | exact absurd hd4 (by decide)))

/-- **The coupled glue-word isometry permutes the glue generators of `A₅⁴ D₄`.** -/
@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_mem_glueGenerators_iff (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry w ∈ a5FourthD4.glueGenerators ↔
      w ∈ a5FourthD4.glueGenerators := by
  refine ⟨fun hw ↦ ?_, a5FourthD4BlockTrialityGlueIsometry_mem_glueGenerators_of_mem⟩
  have hw3 := a5FourthD4BlockTrialityGlueIsometry_mem_glueGenerators_of_mem
    (a5FourthD4BlockTrialityGlueIsometry_mem_glueGenerators_of_mem hw)
  rwa [a5FourthD4BlockTrialityGlueIsometry_apply_apply_apply] at hw3

/-- **The coupled glue-word isometry preserves the glue subgroup of `A₅⁴ D₄`.** -/
@[simp]
theorem a5FourthD4BlockTrialityGlueIsometry_mem_glueSubgroup_iff (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTrialityGlueIsometry w ∈ a5FourthD4.glueSubgroup ↔
      w ∈ a5FourthD4.glueSubgroup :=
  apply_mem_glueSubgroup_iff_of_mem_glueGenerators_iff a5FourthD4BlockTrialityGlueIsometry
    a5FourthD4BlockTrialityGlueIsometry_mem_glueGenerators_iff w

/-! ### The coupled block-rotation and triality isometry of `niemeierA5FourthD4` -/

/-- Componentwise root-lattice isometries for the coupled symmetry of `A₅⁴ D₄`: `typeD4Triality` on
position `4`, and `rootLatticeIsometryOfEq` on `A₅` positions `0, 1, 2, 3`. -/
private noncomputable def a5FourthD4BlockTrialityRootComponent
    (k : Fin a5FourthD4.components.length) :
    IntegralLattice.Isometry
      ((a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).rootLattice
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k)))
      ((a5FourthD4.componentType k).rootLattice
        (a5FourthD4.isSimplyLaced_componentType k)) :=
  if hk : k = 4 then
    ((a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).rootLatticeIsometryOfEq
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k))
      (componentType_a5FourthD4BlockRot_symm_eq_D4 hk) (isSimplyLaced_D 4)).trans <|
      (typeD4Triality (isSimplyLaced_D 4)).trans
        ((D 4).rootLatticeIsometryOfEq (isSimplyLaced_D 4) (D4_eq_componentType_a5FourthD4 hk)
          (a5FourthD4.isSimplyLaced_componentType k))
  else
    (a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).rootLatticeIsometryOfEq
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k))
      (componentType_a5FourthD4BlockRot_symm k)
      (a5FourthD4.isSimplyLaced_componentType k)

private theorem glueAlphabetIsometry_a5FourthD4BlockTrialityComponent
    (k : Fin a5FourthD4.components.length)
    (x : (a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).glueAlphabet
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k))) :
    (a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
        (a5FourthD4.isSimplyLaced_componentType k)
        (a5FourthD4BlockTrialityGlueComponent k x) =
      (a5FourthD4BlockTrialityRootComponent k).discriminantQuadraticIsometry
        ((a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).isEven_rootLattice
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k)))
        ((a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).glueAlphabetIsometry
          (a5FourthD4.valid_componentType (a5FourthD4BlockRot.symm k))
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k)) x) := by
  by_cases hk : k = 4
  · rw [a5FourthD4BlockTrialityGlueComponent, a5FourthD4BlockTrialityRootComponent,
      dite_eq_left hk, dite_eq_left hk, QuadraticMap.IsometryEquiv.trans_apply,
      QuadraticMap.IsometryEquiv.trans_apply]
    refine (glueAlphabetIsometry_ofEq (D4_eq_componentType_a5FourthD4 hk) (valid_D.mpr le_rfl)
      (a5FourthD4.valid_componentType k) (isSimplyLaced_D 4)
      (a5FourthD4.isSimplyLaced_componentType k) _).trans ?_
    rw [glueAlphabetIsometry_typeD4GlueAlphabetTriality (isSimplyLaced_D 4) (valid_D.mpr le_rfl),
      glueAlphabetIsometry_ofEq (componentType_a5FourthD4BlockRot_symm_eq_D4 hk)
        (a5FourthD4.valid_componentType (a5FourthD4BlockRot.symm k)) (valid_D.mpr le_rfl)
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k)) (isSimplyLaced_D 4)]
    let e₁ := (a5FourthD4.componentType (a5FourthD4BlockRot.symm k)).rootLatticeIsometryOfEq
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k))
      (componentType_a5FourthD4BlockRot_symm_eq_D4 hk) (isSimplyLaced_D 4)
    let e₂ := typeD4Triality (isSimplyLaced_D 4)
    let e₃ := (D 4).rootLatticeIsometryOfEq (isSimplyLaced_D 4)
      (D4_eq_componentType_a5FourthD4 hk) (a5FourthD4.isSimplyLaced_componentType k)
    have htr : e₁.discriminantGroupEquiv.trans
        (e₂.discriminantGroupEquiv.trans e₃.discriminantGroupEquiv) =
        (e₁.trans (e₂.trans e₃)).discriminantGroupEquiv := by
      rw [Isometry.discriminantGroupEquiv_trans, Isometry.discriminantGroupEquiv_trans]
    refine (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans ?_
    refine (congrArg _ ((Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
      (congrArg _ (Isometry.discriminantQuadraticIsometry_apply _ _ _)))).trans ?_
    exact (DFunLike.congr_fun htr _).trans
      (Isometry.discriminantQuadraticIsometry_apply _ _ _).symm
  · rw [a5FourthD4BlockTrialityGlueComponent, a5FourthD4BlockTrialityRootComponent,
      dite_eq_right hk, dite_eq_right hk]
    exact glueAlphabetIsometry_ofEq (componentType_a5FourthD4BlockRot_symm k)
      (a5FourthD4.valid_componentType (a5FourthD4BlockRot.symm k))
      (a5FourthD4.valid_componentType k)
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm k))
      (a5FourthD4.isSimplyLaced_componentType k) x

end RootfulNiemeierType

section NiemeierA5FourthD4BlockTriality

open RootfulNiemeierType DynkinType IntegralLattice

/-- **The coupled block-rotation and `D₄`-triality self-isometry of `niemeierA5FourthD4`**: fixes
the leading `A₅` component at position `0`, cyclically shifts the three `A₅` components at
positions `1 ↦ 2 ↦ 3 ↦ 1`, and applies `typeD4Triality` to the `D₄` component at position `4`. -/
noncomputable def niemeierA5FourthD4BlockTriality :
    IntegralLattice.Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  (Isometry.ofEq (lattice_def a5FourthD4)).trans <|
    (gluedLatticePiCongrIsometry' a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
      a5FourthD4.valid_componentType a5FourthD4.glueSubgroup a5FourthD4.isIsotropic_glueSubgroup
      a5FourthD4.valid_componentType a5FourthD4.isIsotropic_glueSubgroup
      a5FourthD4BlockRot a5FourthD4BlockTrialityRootComponent
      (fun k ↦ a5FourthD4BlockTrialityGlueComponent k)
      glueAlphabetIsometry_a5FourthD4BlockTrialityComponent
      (fun w ↦ by
        have hw : (fun k ↦ a5FourthD4BlockTrialityGlueComponent k (w (a5FourthD4BlockRot.symm k))) =
            a5FourthD4BlockTrialityGlueIsometry w :=
          funext fun k ↦ (a5FourthD4BlockTrialityGlueIsometry_apply w k).symm
        exact hw ▸ a5FourthD4BlockTrialityGlueIsometry_mem_glueSubgroup_iff w)).trans
    (Isometry.ofEq (lattice_def a5FourthD4).symm)

/-- Identifying root-lattice coordinates at equal component indices transports `x a` to `x b`. -/
private theorem rootLatticeIsometryOfEq_eq_apply
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ)
    {a b : Fin a5FourthD4.components.length} (hab : a = b) {T : DynkinType}
    {hT : T.IsSimplyLaced} (ha : a5FourthD4.componentType a = T)
    (hb : (a5FourthD4.componentType b).rank = T.rank) (j : Fin T.rank) :
    (a5FourthD4.componentType a).rootLatticeIsometryOfEq
        (a5FourthD4.isSimplyLaced_componentType a) ha hT (x a) j =
      x b (Fin.cast hb.symm j) := by
  subst hab
  exact (a5FourthD4.componentType a).rootLatticeIsometryOfEq_apply
    (a5FourthD4.isSimplyLaced_componentType a) ha hT (x a) j

@[simp]
theorem niemeierA5FourthD4BlockTriality_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    niemeierA5FourthD4BlockTriality x 0 = x 0 := by
  funext j
  rw [niemeierA5FourthD4BlockTriality, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticePiCongrIsometry'_apply,
    a5FourthD4BlockTrialityRootComponent, dite_eq_right (by decide)]
  exact (rootLatticeIsometryOfEq_eq_apply x a5FourthD4BlockRot_symm_zero _ rfl j).trans
    (congrArg (x 0) (Fin.cast_eq_self j))

@[simp]
theorem niemeierA5FourthD4BlockTriality_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    niemeierA5FourthD4BlockTriality x 1 = x 3 := by
  funext j
  rw [niemeierA5FourthD4BlockTriality, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticePiCongrIsometry'_apply,
    a5FourthD4BlockTrialityRootComponent, dite_eq_right (by decide)]
  exact (rootLatticeIsometryOfEq_eq_apply x a5FourthD4BlockRot_symm_one _ rfl j).trans
    (congrArg (x 3) (Fin.cast_eq_self j))

@[simp]
theorem niemeierA5FourthD4BlockTriality_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    niemeierA5FourthD4BlockTriality x 2 = x 1 := by
  funext j
  rw [niemeierA5FourthD4BlockTriality, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticePiCongrIsometry'_apply,
    a5FourthD4BlockTrialityRootComponent, dite_eq_right (by decide)]
  exact (rootLatticeIsometryOfEq_eq_apply x a5FourthD4BlockRot_symm_two _ rfl j).trans
    (congrArg (x 1) (Fin.cast_eq_self j))

@[simp]
theorem niemeierA5FourthD4BlockTriality_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    niemeierA5FourthD4BlockTriality x 3 = x 2 := by
  funext j
  rw [niemeierA5FourthD4BlockTriality, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticePiCongrIsometry'_apply,
    a5FourthD4BlockTrialityRootComponent, dite_eq_right (by decide)]
  exact (rootLatticeIsometryOfEq_eq_apply x a5FourthD4BlockRot_symm_three _ rfl j).trans
    (congrArg (x 2) (Fin.cast_eq_self j))

/-- On the `D₄` component at position `4`, `niemeierA5FourthD4BlockTriality` acts by
`typeD4Triality`. -/
@[simp]
theorem niemeierA5FourthD4BlockTriality_apply_four
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    niemeierA5FourthD4BlockTriality x 4 =
      typeD4Triality (isSimplyLaced_D 4) (x 4) := by
  funext j
  rw [niemeierA5FourthD4BlockTriality, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticePiCongrIsometry'_apply,
    a5FourthD4BlockTrialityRootComponent, dite_eq_left rfl,
    Isometry.trans_apply, Isometry.trans_apply]
  refine (rootLatticeIsometryOfEq_apply (D 4) (isSimplyLaced_D 4)
    (D4_eq_componentType_a5FourthD4 rfl) (a5FourthD4.isSimplyLaced_componentType 4) _ j).trans ?_
  have hin : (a5FourthD4.componentType (a5FourthD4BlockRot.symm 4)).rootLatticeIsometryOfEq
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockRot.symm 4))
      (componentType_a5FourthD4BlockRot_symm_eq_D4 rfl) (isSimplyLaced_D 4)
      (x (a5FourthD4BlockRot.symm 4)) = x 4 := by
    funext m
    exact (rootLatticeIsometryOfEq_eq_apply x a5FourthD4BlockRot_symm_four _ rfl m).trans
      (congrArg (x 4) (Fin.cast_eq_self m))
  rw [hin]
  rfl

/-- The cube of `niemeierA5FourthD4BlockTriality` is the identity isometry. -/
@[simp]
theorem niemeierA5FourthD4BlockTriality_pow_three :
    niemeierA5FourthD4BlockTriality ^ 3 = 1 := by
  ext x k j
  rw [pow_succ, pow_two, Isometry.mul_apply, Isometry.mul_apply, Isometry.one_apply]
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide +revert
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · rw [niemeierA5FourthD4BlockTriality_apply_four, niemeierA5FourthD4BlockTriality_apply_four,
      niemeierA5FourthD4BlockTriality_apply_four]
    let y : Fin (D 4).rank → ℚ := x 4
    have h3 := DFunLike.congr_fun (typeD4Triality_pow_three (isSimplyLaced_D 4)) y
    rw [pow_succ, pow_two, Isometry.mul_apply, Isometry.mul_apply, Isometry.one_apply] at h3
    exact congrFun h3 j

/-- `niemeierA5FourthD4BlockTriality` is nontrivial. -/
theorem niemeierA5FourthD4BlockTriality_ne_one :
    niemeierA5FourthD4BlockTriality ≠ 1 := by
  intro h
  let x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ :=
    Pi.single (1 : Fin a5FourthD4.components.length) fun _ ↦ 1
  let j₀ : Fin (a5FourthD4.componentType 2).rank :=
    ⟨0, DynkinType.rank_pos (a5FourthD4.valid_componentType 2)⟩
  have hx := congrFun (congrFun (DFunLike.congr_fun h x) 2) j₀
  rw [niemeierA5FourthD4BlockTriality_apply_two, Isometry.one_apply] at hx
  have hx1 : x 1 j₀ = 1 := by simp [x]
  have hx2 : x 2 j₀ = 0 := by simp [x]
  rw [hx1, hx2] at hx
  exact one_ne_zero hx

/-- **`niemeierA5FourthD4BlockTriality` has exact order `3`.** -/
@[simp]
theorem orderOf_niemeierA5FourthD4BlockTriality :
    orderOf niemeierA5FourthD4BlockTriality = 3 :=
  orderOf_eq_prime niemeierA5FourthD4BlockTriality_pow_three
    niemeierA5FourthD4BlockTriality_ne_one

/-- **`niemeierA5FourthD4BlockTriality` is a proper isometry (`det = 1`).** -/
@[simp]
theorem det_niemeierA5FourthD4BlockTriality :
    Isometry.det niemeierA5FourthD4 niemeierA5FourthD4BlockTriality = 1 :=
  Isometry.det_eq_one_of_pow_eq_one (by decide : Odd 3) niemeierA5FourthD4BlockTriality_pow_three

/-- `niemeierA5FourthD4BlockTriality` belongs to the special orthogonal group of
`niemeierA5FourthD4`. -/
theorem niemeierA5FourthD4BlockTriality_mem_specialOrthogonalGroup :
    niemeierA5FourthD4BlockTriality ∈ specialOrthogonalGroup niemeierA5FourthD4 :=
  mem_specialOrthogonalGroup_iff.mpr det_niemeierA5FourthD4BlockTriality

end NiemeierA5FourthD4BlockTriality

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### Pattern symmetry action on `A₅⁴ D₄` -/

private theorem niemeierA5FourthD4BlockTriality_pow_of_blockRot_pow (k : ℕ) :
    niemeierA5FourthD4BlockTriality ^
        (![0, 0, 1, 2, 0] (((a5FourthD4BlockRot ^ k) 1).cast length_components_a5FourthD4)) =
      niemeierA5FourthD4BlockTriality ^ k := by
  rw [pow_eq_pow_mod k a5FourthD4BlockRot_pow_three,
    pow_eq_pow_mod k niemeierA5FourthD4BlockTriality_pow_three]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h0 | h1 | h2
  · rw [h0]
    have hexp : ![0, 0, 1, 2, 0] (((a5FourthD4BlockRot ^ 0) 1).cast length_components_a5FourthD4) =
        0 := by decide
    exact congrArg (niemeierA5FourthD4BlockTriality ^ ·) hexp
  · rw [h1]
    have hexp : ![0, 0, 1, 2, 0] (((a5FourthD4BlockRot ^ 1) 1).cast length_components_a5FourthD4) =
        1 := by decide
    exact congrArg (niemeierA5FourthD4BlockTriality ^ ·) hexp
  · rw [h2]
    have hexp : ![0, 0, 1, 2, 0] (((a5FourthD4BlockRot ^ 2) 1).cast length_components_a5FourthD4) =
        2 := by decide
    exact congrArg (niemeierA5FourthD4BlockTriality ^ ·) hexp

private theorem exp_permCongr_one {p : GluePattern} (hp : p ∈ a5FourthD4.gluePatterns) :
    ![0, 0, 1, 2, 0]
      ((((finCongr (length_eq_of_mem_gluePatterns hp)).permCongr
          (1 : Equiv.Perm (Fin p.length))) 1).cast length_components_a5FourthD4) = 0 := by
  rw [Equiv.Perm.one_def, Equiv.permCongr_refl, Equiv.refl_apply]
  decide

private theorem permCongr_finRotate_pow_eq_a5FourthD4BlockRot_pow
    (hlen : (GluePattern.cyclic [2] [0, 2, 4] [0]).length = a5FourthD4.components.length)
    (k : ℕ) :
    (finCongr hlen).permCongr
        (Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate 3)) 1 ^ k) =
      a5FourthD4BlockRot ^ k :=
  (map_pow (finCongr hlen).permCongrHom _ k).trans
    (congrArg (· ^ k) (permCongr_finRotate_eq_a5FourthD4BlockRot hlen))

private theorem exists_permCongr_eq_a5FourthD4BlockRot_pow {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) :
    ∃ k : ℕ, (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g.1 =
      a5FourthD4BlockRot ^ k := by
  rcases g with ⟨g1, hg2⟩
  have hp' := hp
  simp only [gluePatterns, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl
  · rw [GluePattern.symmetries_cyclic] at hg2
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg2)
    exact ⟨k, permCongr_finRotate_pow_eq_a5FourthD4BlockRot_pow _ k⟩
  all_goals
    rw [GluePattern.symmetries_literal, Subgroup.mem_bot] at hg2
    subst hg2
    exact ⟨0, by rw [pow_zero]; rfl⟩

/-- **The indicated symmetries of every pattern of `A₅⁴ D₄` act on `niemeierA5FourthD4`**:
trivially on the three literal patterns `[33001]`, `[30302]`, `[30033]`, and via powers of
`niemeierA5FourthD4BlockTriality` on the cyclic pattern `[2(024)0]`. -/
noncomputable def a5FourthD4PatternIsometryHom {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) :
    p.symmetries →* IntegralLattice.Isometry niemeierA5FourthD4 niemeierA5FourthD4 where
  toFun g :=
    niemeierA5FourthD4BlockTriality ^
      (![0, 0, 1, 2, 0]
        ((((finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g.1) 1).cast
          length_components_a5FourthD4))
  map_one' := by
    rw [Subgroup.coe_one, exp_permCongr_one hp, pow_zero]
  map_mul' g h := by
    rw [Subgroup.coe_mul]
    obtain ⟨k, hgk⟩ := exists_permCongr_eq_a5FourthD4BlockRot_pow hp g
    obtain ⟨m, hhm⟩ := exists_permCongr_eq_a5FourthD4BlockRot_pow hp h
    have hgh : (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr (g.1 * h.1) =
        a5FourthD4BlockRot ^ (k + m) :=
      (map_mul (finCongr (length_eq_of_mem_gluePatterns hp)).permCongrHom g.1 h.1).trans
        ((congrArg₂ (· * ·) hgk hhm).trans (pow_add _ _ _).symm)
    rw [hgh, hgk, hhm, niemeierA5FourthD4BlockTriality_pow_of_blockRot_pow,
      niemeierA5FourthD4BlockTriality_pow_of_blockRot_pow,
      niemeierA5FourthD4BlockTriality_pow_of_blockRot_pow, pow_add]

/-- Explicit formula for `a5FourthD4PatternIsometryHom hp g` in terms of the image of position `1`
under `g`. -/
-- Not `@[simp]`: kept out of the default simp set so specific `@[simp]` lemmas on literal
-- patterns, the cyclic generator, and `Isometry.det` fire without unfolding the internal exponent.
theorem a5FourthD4PatternIsometryHom_apply {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) :
    a5FourthD4PatternIsometryHom hp g =
      niemeierA5FourthD4BlockTriality ^
        (![0, 0, 1, 2, 0]
          ((((finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g.1) 1).cast
            length_components_a5FourthD4)) :=
  (rfl)

/-- Whenever `g` acts on the five component positions of `A₅⁴ D₄` as `a5FourthD4BlockRot ^ k`,
`a5FourthD4PatternIsometryHom hp g` is `niemeierA5FourthD4BlockTriality ^ k`. -/
theorem a5FourthD4PatternIsometryHom_eq_pow_of_permCongr_eq_pow {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) {k : ℕ}
    (hk : (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g.1 =
      a5FourthD4BlockRot ^ k) :
    a5FourthD4PatternIsometryHom hp g = niemeierA5FourthD4BlockTriality ^ k := by
  rw [a5FourthD4PatternIsometryHom_apply, hk,
    niemeierA5FourthD4BlockTriality_pow_of_blockRot_pow]

/-- Every indicated pattern symmetry of `A₅⁴ D₄` acts on the component positions as a power
`a5FourthD4BlockRot ^ k` (`k < 3`) and on `niemeierA5FourthD4` as the matching power
`niemeierA5FourthD4BlockTriality ^ k`. -/
theorem exists_a5FourthD4PatternIsometryHom_eq_pow {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) :
    ∃ k < 3,
      (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g.1 = a5FourthD4BlockRot ^ k ∧
        a5FourthD4PatternIsometryHom hp g = niemeierA5FourthD4BlockTriality ^ k := by
  obtain ⟨k, hk⟩ := exists_permCongr_eq_a5FourthD4BlockRot_pow hp g
  refine ⟨k % 3, Nat.mod_lt k (by decide), ?_, ?_⟩
  · exact hk.trans (pow_eq_pow_mod k a5FourthD4BlockRot_pow_three)
  · exact (a5FourthD4PatternIsometryHom_eq_pow_of_permCongr_eq_pow hp g hk).trans
      (pow_eq_pow_mod k niemeierA5FourthD4BlockTriality_pow_three)

/-- On any literal pattern of `A₅⁴ D₄`, `a5FourthD4PatternIsometryHom` is trivial. -/
@[simp]
theorem a5FourthD4PatternIsometryHom_literal {word : List ℕ}
    (hp : GluePattern.literal word ∈ a5FourthD4.gluePatterns)
    (g : (GluePattern.literal word).symmetries) :
    a5FourthD4PatternIsometryHom hp g = 1 := by
  have hg : g = 1 := by
    rcases g with ⟨g1, hg2⟩
    rw [GluePattern.symmetries_literal, Subgroup.mem_bot] at hg2
    exact Subtype.ext hg2
  rw [hg, map_one]

/-- On the generator of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`,
`a5FourthD4PatternIsometryHom` acts as `niemeierA5FourthD4BlockTriality`. -/
@[simp]
theorem a5FourthD4PatternIsometryHom_mk_finRotate
    (hp : GluePattern.cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns := List.Mem.head _) :
    a5FourthD4PatternIsometryHom hp
        ⟨Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate 3)) 1,
          by rw [GluePattern.symmetries_cyclic]; exact Subgroup.mem_zpowers _⟩ =
      niemeierA5FourthD4BlockTriality := by
  refine (a5FourthD4PatternIsometryHom_eq_pow_of_permCongr_eq_pow hp _ (k := 1) ?_).trans
    (pow_one _)
  rw [pow_one]
  exact permCongr_finRotate_eq_a5FourthD4BlockRot _

/-- Every pattern symmetry of `A₅⁴ D₄` acts on `niemeierA5FourthD4` with determinant `1`. -/
@[simp]
theorem det_a5FourthD4PatternIsometryHom {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) :
    Isometry.det niemeierA5FourthD4 (a5FourthD4PatternIsometryHom hp g) = 1 := by
  obtain ⟨k, -, -, hg⟩ := exists_a5FourthD4PatternIsometryHom_eq_pow hp g
  rw [hg, map_pow, det_niemeierA5FourthD4BlockTriality, one_pow]

/-- Every pattern symmetry of `A₅⁴ D₄` acts inside `specialOrthogonalGroup niemeierA5FourthD4`. -/
theorem a5FourthD4PatternIsometryHom_mem_specialOrthogonalGroup {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) :
    a5FourthD4PatternIsometryHom hp g ∈ specialOrthogonalGroup niemeierA5FourthD4 :=
  mem_specialOrthogonalGroup_iff.mpr (det_a5FourthD4PatternIsometryHom hp g)

/-- **The pattern-symmetry action `a5FourthD4PatternIsometryHom` on `niemeierA5FourthD4` is
faithful.** -/
theorem a5FourthD4PatternIsometryHom_injective {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) :
    Function.Injective (a5FourthD4PatternIsometryHom hp) := by
  refine (injective_iff_map_eq_one (a5FourthD4PatternIsometryHom hp)).mpr fun g hg ↦ ?_
  obtain ⟨k, -, hperm, hpow⟩ := exists_a5FourthD4PatternIsometryHom_eq_pow hp g
  rw [hpow] at hg
  have hdvd : 3 ∣ k := by
    rw [← orderOf_niemeierA5FourthD4BlockTriality]
    exact orderOf_dvd_iff_pow_eq_one.mpr hg
  have hrot1 : a5FourthD4BlockRot ^ k = 1 := by
    rw [← orderOf_a5FourthD4BlockRot] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  apply Subtype.ext
  exact (finCongr (length_eq_of_mem_gluePatterns hp)).permCongrHom.injective
    (hperm.trans (hrot1.trans
      (map_one (finCongr (length_eq_of_mem_gluePatterns hp)).permCongrHom).symm))

end RootfulNiemeierType

end TauCeti
