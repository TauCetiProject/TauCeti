/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.Symmetry
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality

/-!
# The marked rotation of the table row `A₅⁴ D₄` is a symmetry only together with triality

The row `A₅⁴ D₄` of the rootful rank-24 table, `TauCeti.RootfulNiemeierType.a5FourthD4`, has the
glue columns `[2(024)0]`, `[33001]`, `[30302]` and `[30033]`.  Its first pattern marks the block of
the `A₅` components in positions `1, 2, 3` for cyclic rotation.  Unlike the marked rotations of
every other row (`TauCeti.RootfulNiemeierType.mem_glueSymmetries_of_mem_symmetries`), this rotation
alone does not preserve the glue subgroup `H`: it permutes the `A₅` parts `3300`, `3030`, `3003`
of the last three words but keeps their `D₄` labels `1, 2, 3` in place.  For instance it carries
`[33001]` to `[30031]`, whose sum with `[30033]` is the nonzero word `[00002]` of shortest norm
`1`, while every nonzero word of `H` has shortest norm at least `4`.

The rotation becomes a symmetry when it is combined with the triality isometry of the `D₄`
component (`TauCeti.DynkinType.typeD4Triality`), which permutes the nonzero `D₄` labels by
`1 ↦ 2 ↦ 3 ↦ 1` (`TauCeti.DynkinType.discriminantGroupEquiv_typeD4Triality_glueLabelEquiv`): the
combined transformation permutes the six digit words of the row, so it preserves `H`, and the
induced isometry of the orthogonal sum of the component root lattices restricts to a
self-isometry of order three of the glued lattice `N = a5FourthD4.lattice`.

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4BlockRotation`: the rotation of the marked block on the
  component positions; its powers are the indicated symmetries of `[2(024)0]`
  (`map_symmetries_cyclic_eq_zpowers_a5FourthD4BlockRotation`).
* `TauCeti.RootfulNiemeierType.zpowers_a5FourthD4BlockRotation_inf_glueSymmetries_eq_bot`: no
  nontrivial power of the rotation is a glue symmetry of the row.
* `TauCeti.RootfulNiemeierType.a5FourthD4BlockTriality`: the rotation of the block composed with
  triality on the `D₄` label, on glue words; it preserves the glue subgroup
  (`a5FourthD4BlockTriality_mem_glueSubgroup_iff`).
* `TauCeti.RootfulNiemeierType.a5FourthD4BlockTrialityIsometry`: the corresponding self-isometry
  of `N`, which moves the `A₅` components in positions `1, 2, 3` to positions `2, 3, 1` and
  applies triality to the `D₄` component; it has order three
  (`orderOf_a5FourthD4BlockTrialityIsometry`).

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §§3 and 7.1, and Chapter 16, §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice GlueSpanMode

/-! ### The marked rotation -/

/-- **The rotation of the marked block of `[2(024)0]`** on the component positions of the row
`A₅⁴ D₄`: it moves the `A₅` components in positions `1, 2, 3` to positions `2, 3, 1` and fixes the
first `A₅` component and the `D₄` component in position `4`. -/
def a5FourthD4BlockRotation : Equiv.Perm (Fin a5FourthD4.components.length) :=
  (c[1, 2, 3] : Equiv.Perm (Fin 5))

/-- The rotation of the marked block is the cycle `1 ↦ 2 ↦ 3 ↦ 1`. -/
theorem a5FourthD4BlockRotation_def :
    a5FourthD4BlockRotation = (c[1, 2, 3] : Equiv.Perm (Fin 5)) :=
  (rfl)

/-- The inverse of the rotation of the marked block is the cycle `1 ↦ 3 ↦ 2 ↦ 1`. -/
@[simp]
theorem a5FourthD4BlockRotation_symm_eq :
    a5FourthD4BlockRotation.symm = (c[1, 3, 2] : Equiv.Perm (Fin 5)) :=
  Equiv.ext <| by decide

/-- The generator of the indicated symmetries of a marked block of three positions between one
leading and one trailing position is the cycle `1 ↦ 2 ↦ 3 ↦ 1`. -/
private theorem finSumPerm_finSumPerm_finRotate_three :
    Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate 3)) (1 : Equiv.Perm (Fin 1)) =
      c[(1 : Fin (1 + 3 + 1)), 2, 3] := by
  ext i
  obtain ⟨x | c, rfl⟩ := (finSumFinEquiv (m := 1 + 3) (n := 1)).surjective i
  · obtain ⟨a | b, rfl⟩ := (finSumFinEquiv (m := 1) (n := 3)).surjective x
    · simp only [finSumFinEquiv_apply_left, Equiv.Perm.finSumPerm_apply_castAdd,
        Equiv.Perm.one_apply]
      fin_cases a
      decide
    · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Equiv.Perm.finSumPerm_apply_castAdd, Equiv.Perm.finSumPerm_apply_natAdd, finRotate_apply]
      fin_cases b <;> decide
  · simp only [finSumFinEquiv_apply_right, Equiv.Perm.finSumPerm_apply_natAdd,
      Equiv.Perm.one_apply]
    fin_cases c
    decide

/-- The indicated symmetries of the pattern `[2(024)0]`, read on the component positions of the
row `A₅⁴ D₄`, are the powers of `a5FourthD4BlockRotation`. -/
theorem map_symmetries_cyclic_eq_zpowers_a5FourthD4BlockRotation
    (h : (GluePattern.cyclic [2] [0, 2, 4] [0]).length = a5FourthD4.components.length) :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries.map (finCongr h).permCongrHom.toMonoidHom =
      Subgroup.zpowers a5FourthD4BlockRotation := by
  rw [GluePattern.symmetries_cyclic]
  refine (MonoidHom.map_zpowers _ _).trans (congrArg _ ?_)
  refine (congrArg (finCongr h).permCongrHom.toMonoidHom
    finSumPerm_finSumPerm_finRotate_three).trans ?_
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Equiv.permCongrHom_coe]
  refine congrArg Fin.val ((Equiv.permCongr_apply _ _ _).trans ?_)
  simp only [finCongr_symm, finCongr_apply]
  decide +revert

/-- The rotation of the marked block has order three. -/
theorem orderOf_a5FourthD4BlockRotation : orderOf a5FourthD4BlockRotation = 3 :=
  orderOf_eq_prime (by decide) (by decide)

/-- The components of `A₅⁴ D₄` are `A₅` in the positions `0, 1, 2, 3` and `D₄` in position `4`. -/
private theorem componentType_a5FourthD4 (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType k = if (k : ℕ) < 4 then A 5 else D 4 := by
  fin_cases k <;> rfl

/-- The rotation of the marked block preserves the component types. -/
theorem componentType_a5FourthD4BlockRotation_symm (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType (a5FourthD4BlockRotation.symm k) = a5FourthD4.componentType k := by
  have h : ∀ k : Fin a5FourthD4.components.length,
      ((a5FourthD4BlockRotation.symm k : ℕ) < 4 ↔ (k : ℕ) < 4) := by
    decide
  rw [componentType_a5FourthD4, componentType_a5FourthD4]
  exact if_congr (h k) rfl rfl

/-- **The marked rotation of `A₅⁴ D₄` is not a glue symmetry.**  If it were, the rotation
`[30031]` of the glue word `[33001]` would lie in the glue subgroup, and so would its sum `[00002]`
with `[30033]`; but that word is nonzero of shortest norm `1 < 4`. -/
theorem a5FourthD4BlockRotation_notMem_glueSymmetries :
    a5FourthD4BlockRotation ∉ a5FourthD4.glueSymmetries := by
  intro hρ
  obtain ⟨w, hw, hw'⟩ := exists_decodeGlueWord_mem_glueGenerators (r := a5FourthD4)
    (l := [3, 3, 0, 0, 1]) (by decide)
  obtain ⟨u, hu, hu'⟩ := exists_decodeGlueWord_mem_glueGenerators (r := a5FourthD4)
    (l := [3, 0, 0, 3, 3]) (by decide)
  rw [decodeGlueWord_eq_some_iff] at hw' hu'
  set v := piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
    a5FourthD4BlockRotation (componentType_apply_of_mem_glueSymmetries _ hρ) w + u
  have hv : v ∈ a5FourthD4.glueSubgroup :=
    add_mem ((piGlueAlphabetCongr_mem_glueSubgroup_iff _ hρ w).mpr
      (a5FourthD4.glueSubgroup_def ▸ AddSubgroup.subset_closure hw))
      (a5FourthD4.glueSubgroup_def ▸ AddSubgroup.subset_closure hu)
  have he : encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType v =
      [0, 0, 0, 0, 2] := by
    rw [encodeGlueWord_add, encodeGlueWord_piGlueAlphabetCongr_eq_ofFn_getD, ← hw', ← hu']
    decide
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, encodeGlueWord_zero] at he
    exact absurd he (by decide)
  have h4 := four_le_sum_glueMinimum_of_mem_glueSubgroup _ hv hv0
  rw [← glueWordMinimum_encodeGlueWord, he] at h4
  revert h4
  decide +kernel

/-- **No nontrivial power of the marked rotation of `A₅⁴ D₄` is a glue symmetry.** -/
theorem zpowers_a5FourthD4BlockRotation_inf_glueSymmetries_eq_bot :
    Subgroup.zpowers a5FourthD4BlockRotation ⊓ a5FourthD4.glueSymmetries = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx ↦ ?_
  obtain ⟨hxρ, hxS⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxρ
  rw [← zpow_mod_orderOf, orderOf_a5FourthD4BlockRotation] at hxS ⊢
  obtain h | h | h : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
    omega
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hxS
    exact absurd hxS a5FourthD4BlockRotation_notMem_glueSymmetries
  · -- The square generates the same cyclic group as the rotation.
    rw [h] at hxS
    refine absurd ?_ a5FourthD4BlockRotation_notMem_glueSymmetries
    have hsq : a5FourthD4BlockRotation = (a5FourthD4BlockRotation ^ (2 : ℤ)) ^ (2 : ℤ) := by
      decide
    rw [hsq]
    exact zpow_mem hxS 2

/-! ### Triality on the `D₄` component -/

/-- The position `4` of the `D₄` component of `A₅⁴ D₄`. -/
private def d4Position : Fin a5FourthD4.components.length :=
  Fin.last 4

/-- Triality on the root lattice of the `D₄` component of `A₅⁴ D₄`. -/
private noncomputable def d4PositionTriality :
    Isometry ((a5FourthD4.componentType d4Position).rootLattice
        (a5FourthD4.isSimplyLaced_componentType d4Position))
      ((a5FourthD4.componentType d4Position).rootLattice
        (a5FourthD4.isSimplyLaced_componentType d4Position)) :=
  -- The component in position `4` is `D₄` by evaluation of the component list.
  typeD4Triality (isSimplyLaced_D 4)

/-- Triality on the `D₄` component and the identity on the `A₅` components. -/
private noncomputable def componentTriality (k : Fin a5FourthD4.components.length) :
    Isometry ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k))
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k)) :=
  Pi.mulSingle (M := fun k ↦ Isometry
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k))
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k)))
    d4Position d4PositionTriality k

private theorem d4PositionTriality_pow_three : d4PositionTriality ^ 3 = 1 :=
  typeD4Triality_pow_three _

/-- The action of `componentTriality` on the glue alphabet of each component. -/
private noncomputable def labelTriality (k : Fin a5FourthD4.components.length) :
    FiniteQuadraticModule.Isometry
      ((a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k))
      ((a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)) :=
  (((a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
      (a5FourthD4.isSimplyLaced_componentType k)).trans
    ((componentTriality k).discriminantQuadraticIsometry
      ((a5FourthD4.componentType k).isEven_rootLattice _))).trans
    ((a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
      (a5FourthD4.isSimplyLaced_componentType k)).symm

private theorem glueAlphabetIsometry_labelTriality (k : Fin a5FourthD4.components.length)
    (x : (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)) :
    (a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
        (a5FourthD4.isSimplyLaced_componentType k) (labelTriality k x) =
      (componentTriality k).discriminantQuadraticIsometry
        ((a5FourthD4.componentType k).isEven_rootLattice _)
        ((a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
          (a5FourthD4.isSimplyLaced_componentType k) x) := by
  rw [labelTriality, FiniteQuadraticModule.Isometry.trans_apply,
    FiniteQuadraticModule.Isometry.trans_apply, QuadraticMap.IsometryEquiv.apply_symm_apply]

/-- On digits, `labelTriality` applies `1 ↦ 2 ↦ 3 ↦ 1`, multiplication by `ω²`, to the label of
the `D₄` component and fixes the labels of the `A₅` components. -/
private theorem val_glueLabelEquiv_symm_labelTriality (k : Fin a5FourthD4.components.length)
    (x : (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)) :
    (((a5FourthD4.componentType k).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType k)).symm
        (labelTriality k x)).val =
      if (k : ℕ) = 4 then
        f4OmegaLabel (f4OmegaLabel (((a5FourthD4.componentType k).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType k)).symm x).val)
      else (((a5FourthD4.componentType k).glueLabelEquiv
        (a5FourthD4.isSimplyLaced_componentType k)).symm x).val := by
  split_ifs with hk
  · obtain rfl : k = d4Position := Fin.ext hk
    obtain ⟨i, rfl⟩ := ((a5FourthD4.componentType d4Position).glueLabelEquiv
      (a5FourthD4.isSimplyLaced_componentType d4Position)).surjective x
    rw [Equiv.symm_apply_apply]
    have hj : f4OmegaLabel (f4OmegaLabel i) <
        (a5FourthD4.componentType d4Position).glueLabelCount := by
      revert i
      decide
    have hi : labelTriality d4Position ((a5FourthD4.componentType d4Position).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType d4Position) i) =
        (a5FourthD4.componentType d4Position).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType d4Position) ⟨_, hj⟩ := by
      rw [labelTriality, FiniteQuadraticModule.Isometry.trans_apply,
        FiniteQuadraticModule.Isometry.trans_apply, QuadraticMap.IsometryEquiv.symm_apply_eq,
        componentTriality, Pi.mulSingle_eq_same]
      -- The component in position `4` is `D₄` by evaluation, so the label lemma for triality
      -- applies.
      refine (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
        ((discriminantGroupEquiv_typeD4Triality_glueLabelEquiv (isSimplyLaced_D 4)
          (valid_D.mpr le_rfl) i).trans (congrArg _ (congrArg _ (Fin.ext ?_))))
      have h : ∀ i : Fin 4, ((![0, 2, 3, 1] i : Fin 4) : ℕ) = f4OmegaLabel (f4OmegaLabel i) := by
        decide
      exact h i
    rw [hi, Equiv.symm_apply_apply]
  · have h1 : componentTriality k = 1 :=
      Pi.mulSingle_eq_of_ne (fun h ↦ hk (congrArg Fin.val h)) _
    have h2 : labelTriality k x = x := by
      rw [labelTriality, FiniteQuadraticModule.Isometry.trans_apply,
        FiniteQuadraticModule.Isometry.trans_apply, QuadraticMap.IsometryEquiv.symm_apply_eq, h1,
        Isometry.one_def]
      exact (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
        (DFunLike.congr_fun (Isometry.discriminantGroupEquiv_refl _) _)
    rw [h2]

/-! ### The rotation combined with triality, on glue words -/

/-- Reindexing glue words along the rotation of the marked block. -/
private noncomputable def blockRotationGlue :
    FiniteQuadraticModule.Isometry a5FourthD4.glueModule a5FourthD4.glueModule :=
  piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
    a5FourthD4BlockRotation.symm componentType_a5FourthD4BlockRotation_symm

/-- **The rotation of the marked block of `A₅⁴ D₄` combined with triality, on glue words**: it
moves the labels in positions `1, 2, 3` to positions `2, 3, 1` and applies `1 ↦ 2 ↦ 3 ↦ 1` to the
label of the `D₄` component (`encodeGlueWord_a5FourthD4BlockTriality`). -/
noncomputable def a5FourthD4BlockTriality :
    FiniteQuadraticModule.Isometry a5FourthD4.glueModule a5FourthD4.glueModule :=
  blockRotationGlue.trans (QuadraticMap.IsometryEquiv.pi labelTriality)

private theorem a5FourthD4BlockTriality_apply (w : a5FourthD4.glueModule)
    (k : Fin a5FourthD4.components.length) :
    a5FourthD4BlockTriality w k = labelTriality k (blockRotationGlue w k) :=
  -- `QuadraticMap.IsometryEquiv.pi` acts coordinatewise by definition.
  (rfl)

/-- The digits of the image of a glue word under `a5FourthD4BlockTriality`: the digit in position
`k` of the block is the digit of the word in the preceding position of the block, and the `D₄`
digit `d` becomes `ω² d`, that is, `1 ↦ 2 ↦ 3 ↦ 1`. -/
theorem encodeGlueWord_a5FourthD4BlockTriality (w : a5FourthD4.glueModule) :
    encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        (a5FourthD4BlockTriality w) =
      List.ofFn fun k ↦
        if (k : ℕ) = 4 then
          f4OmegaLabel (f4OmegaLabel ((encodeGlueWord a5FourthD4.componentType
            a5FourthD4.isSimplyLaced_componentType w).getD (a5FourthD4BlockRotation.symm k) 0))
        else (encodeGlueWord a5FourthD4.componentType
          a5FourthD4.isSimplyLaced_componentType w).getD (a5FourthD4BlockRotation.symm k) 0 := by
  rw [encodeGlueWord_def]
  congr 1
  funext k
  rw [a5FourthD4BlockTriality_apply, val_glueLabelEquiv_symm_labelTriality, blockRotationGlue,
    piGlueAlphabetCongr_apply,
    val_glueLabelEquiv_symm_ofEq (componentType_a5FourthD4BlockRotation_symm k),
    List.getD_eq_getElem _ _ (by simp), getElem_encodeGlueWord]

/-- **The rotation of the marked block combined with triality preserves the glue subgroup** of
`A₅⁴ D₄`: on digits it permutes the six glue words `[20240]`, `[22400]`, `[24020]`, `[33001]`,
`[30302]` and `[30033]` of the row. -/
theorem map_glueSubgroup_a5FourthD4BlockTriality :
    a5FourthD4.glueSubgroup.map a5FourthD4BlockTriality.toAddEquiv = a5FourthD4.glueSubgroup := by
  have hle : a5FourthD4.glueSubgroup.map a5FourthD4BlockTriality.toAddEquiv ≤
      a5FourthD4.glueSubgroup := by
    rw [AddSubgroup.map_le_iff_le_comap, glueSubgroup_def, AddSubgroup.closure_le]
    intro w hw
    refine AddSubgroup.subset_closure (mem_glueGenerators_iff.mpr ?_)
    rw [AddMonoidHom.coe_ofClass]
    -- The six digit words of the row are permuted.
    have hd : ∀ l ∈ a5FourthD4.glueWords, (List.ofFn fun k : Fin a5FourthD4.components.length ↦
        if (k : ℕ) = 4 then f4OmegaLabel (f4OmegaLabel (l.getD (a5FourthD4BlockRotation.symm k) 0))
        else l.getD (a5FourthD4BlockRotation.symm k) 0) ∈ a5FourthD4.glueWords := by
      decide
    exact (encodeGlueWord_a5FourthD4BlockTriality w).symm ▸ hd _ (mem_glueGenerators_iff.mp hw)
  exact AddSubgroup.eq_of_le_of_card_ge hle
    (AddSubgroup.card_map_of_injective (EquivLike.injective _)).ge

/-- A glue word lies in the glue subgroup of `A₅⁴ D₄` exactly when its image under the rotation
of the marked block combined with triality does. -/
theorem a5FourthD4BlockTriality_mem_glueSubgroup_iff (w : a5FourthD4.glueModule) :
    a5FourthD4BlockTriality w ∈ a5FourthD4.glueSubgroup ↔ w ∈ a5FourthD4.glueSubgroup := by
  have h := AddSubgroup.mem_map_iff_mem
    (f := (a5FourthD4BlockTriality.toAddEquiv : a5FourthD4.glueModule →+ a5FourthD4.glueModule))
    (by rw [AddMonoidHom.coe_ofClass]; exact EquivLike.injective _) (K := a5FourthD4.glueSubgroup)
    (x := w)
  rwa [map_glueSubgroup_a5FourthD4BlockTriality, AddMonoidHom.coe_ofClass] at h

/-! ### The induced isometry of the glued lattice -/

/-- The glue subgroup reindexed along the rotation of the marked block. -/
private noncomputable def rotatedGlueSubgroup : AddSubgroup a5FourthD4.glueModule :=
  a5FourthD4.glueSubgroup.map blockRotationGlue.toAddEquiv

private theorem isIsotropic_rotatedGlueSubgroup :
    a5FourthD4.glueModule.IsIsotropic rotatedGlueSubgroup :=
  (FiniteQuadraticModule.Isometry.isIsotropic_map_iff _ blockRotationGlue _).mpr
    a5FourthD4.isIsotropic_glueSubgroup

private theorem blockRotationGlue_mem_rotatedGlueSubgroup_iff (w : a5FourthD4.glueModule) :
    blockRotationGlue w ∈ rotatedGlueSubgroup ↔ w ∈ a5FourthD4.glueSubgroup :=
  AddSubgroup.mem_map_iff_mem
    (f := (blockRotationGlue.toAddEquiv : a5FourthD4.glueModule →+ a5FourthD4.glueModule))
    (by rw [AddMonoidHom.coe_ofClass]; exact EquivLike.injective _)

/-- **The rotation of the marked block of `A₅⁴ D₄` combined with triality is a symmetry of the
glued lattice**: the self-isometry of `N = a5FourthD4.lattice` which moves the `A₅` components in
positions `1, 2, 3` to positions `2, 3, 1`, fixes the first `A₅` component and applies
`typeD4Triality` to the `D₄` component (`a5FourthD4BlockTrialityIsometry_apply_of_ne`,
`a5FourthD4BlockTrialityIsometry_apply_last`). -/
noncomputable def a5FourthD4BlockTrialityIsometry :
    Isometry a5FourthD4.lattice a5FourthD4.lattice :=
  (Isometry.ofEq (lattice_def a5FourthD4)).trans <|
    ((gluedLatticeIsometryOfEq a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
      a5FourthD4.valid_componentType a5FourthD4.glueSubgroup a5FourthD4.isIsotropic_glueSubgroup
      a5FourthD4.valid_componentType isIsotropic_rotatedGlueSubgroup a5FourthD4BlockRotation.symm
      componentType_a5FourthD4BlockRotation_symm
      blockRotationGlue_mem_rotatedGlueSubgroup_iff).trans
      (gluedLatticePiIsometry a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        a5FourthD4.valid_componentType rotatedGlueSubgroup isIsotropic_rotatedGlueSubgroup
        a5FourthD4.valid_componentType a5FourthD4.isIsotropic_glueSubgroup componentTriality
        (fun k ↦ labelTriality k) glueAlphabetIsometry_labelTriality fun w ↦ by
          obtain ⟨v, rfl⟩ := blockRotationGlue.surjective w
          exact (a5FourthD4BlockTriality_mem_glueSubgroup_iff v).trans
            (blockRotationGlue_mem_rotatedGlueSubgroup_iff v).symm)).trans
    (Isometry.ofEq (lattice_def a5FourthD4).symm)

private theorem a5FourthD4BlockTrialityIsometry_apply
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) (k : Fin a5FourthD4.components.length) :
    a5FourthD4BlockTrialityIsometry x k = componentTriality k fun j ↦
      x (a5FourthD4BlockRotation.symm k)
        (Fin.cast (congrArg rank (componentType_a5FourthD4BlockRotation_symm k)).symm j) := by
  rw [a5FourthD4BlockTrialityIsometry, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.trans_apply, Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticePiIsometry_apply]
  congr 1
  funext j
  exact gluedLatticeIsometryOfEq_apply _ _ _ _ _ _ _ _ _ _ x k j

/-- Away from the `D₄` component, `a5FourthD4BlockTrialityIsometry` reads the component in
position `k` from position `a5FourthD4BlockRotation.symm k`. -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_apply_of_ne
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) {k : Fin a5FourthD4.components.length}
    (hk : (k : ℕ) ≠ 4) (j : Fin (a5FourthD4.componentType k).rank) :
    a5FourthD4BlockTrialityIsometry x k j =
      x (a5FourthD4BlockRotation.symm k)
        (Fin.cast (congrArg rank (componentType_a5FourthD4BlockRotation_symm k)).symm j) := by
  rw [a5FourthD4BlockTrialityIsometry_apply, componentTriality,
    Pi.mulSingle_eq_of_ne (fun h ↦ hk (congrArg Fin.val h)), Isometry.one_apply]

private theorem a5FourthD4BlockTrialityIsometry_apply_d4Position
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockTrialityIsometry x d4Position = d4PositionTriality (x d4Position) := by
  rw [a5FourthD4BlockTrialityIsometry_apply, componentTriality, Pi.mulSingle_eq_same]
  exact congrArg _ (funext fun j ↦ (a5FourthD4.apply_cast_eq_apply_cast x (by decide) _ rfl j).trans
    (congrArg (x d4Position) (Fin.cast_eq_self j)))

/-- On the `D₄` component, `a5FourthD4BlockTrialityIsometry` is triality. -/
@[simp]
theorem a5FourthD4BlockTrialityIsometry_apply_last
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockTrialityIsometry x (Fin.last 4) =
      typeD4Triality (isSimplyLaced_D 4) (x (Fin.last 4)) :=
  -- `d4Position` unfolds to `Fin.last 4`, and `d4PositionTriality` to
  -- `typeD4Triality (isSimplyLaced_D 4)` at the component type `D 4` evaluated there.
  a5FourthD4BlockTrialityIsometry_apply_d4Position x

/-- **The rotation of the marked block combined with triality has order three.** -/
theorem orderOf_a5FourthD4BlockTrialityIsometry : orderOf a5FourthD4BlockTrialityIsometry = 3 := by
  refine orderOf_eq_prime (Isometry.ext fun x ↦ funext fun k ↦ ?_) fun h ↦ ?_
  · rw [pow_three, Isometry.mul_apply, Isometry.mul_apply, Isometry.one_apply]
    by_cases hk : (k : ℕ) = 4
    · obtain rfl : k = d4Position := Fin.ext hk
      rw [a5FourthD4BlockTrialityIsometry_apply_d4Position,
        a5FourthD4BlockTrialityIsometry_apply_d4Position,
        a5FourthD4BlockTrialityIsometry_apply_d4Position, ← Isometry.mul_apply,
        ← Isometry.mul_apply, ← pow_three', d4PositionTriality_pow_three, Isometry.one_apply]
    · funext j
      have hk' : ∀ k : Fin a5FourthD4.components.length, (k : ℕ) ≠ 4 →
          (a5FourthD4BlockRotation.symm k : ℕ) ≠ 4 := by
        decide
      rw [a5FourthD4BlockTrialityIsometry_apply_of_ne _ hk,
        a5FourthD4BlockTrialityIsometry_apply_of_ne _ (hk' _ hk),
        a5FourthD4BlockTrialityIsometry_apply_of_ne _ (hk' _ (hk' _ hk))]
      have h3 : a5FourthD4BlockRotation.symm (a5FourthD4BlockRotation.symm
          (a5FourthD4BlockRotation.symm k)) = k := by
        revert k
        decide
      rw [Fin.cast_cast, Fin.cast_cast]
      exact (a5FourthD4.apply_cast_eq_apply_cast x h3 _ rfl j).trans
        (congrArg (x k) (Fin.cast_eq_self j))
  · -- The vector which is `1` on the second `A₅` component and `0` elsewhere is moved.
    have hx := congrFun (congrFun (DFunLike.congr_fun h
      fun (k : Fin a5FourthD4.components.length) (_ : Fin (a5FourthD4.componentType k).rank) ↦
        if (k : ℕ) = 1 then (1 : ℚ) else 0) ⟨2, by decide⟩) ⟨0, by decide⟩
    rw [a5FourthD4BlockTrialityIsometry_apply_of_ne _ (by decide), Isometry.one_apply] at hx
    revert hx
    decide

end RootfulNiemeierType

end TauCeti
