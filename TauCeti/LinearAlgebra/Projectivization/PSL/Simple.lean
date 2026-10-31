/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Perfect

/-!
# Simplicity of the projective special linear groups

Let `F` be a field and `ι` a finite type with at least two elements. The projective special linear
group `PSL ι F = SL ι F ⧸ Z(SL ι F)` acts faithfully and primitively on the projective space
`ℙ F (ι → F)`. For a line `p`, the subgroup `lineStab p` of `SL ι F` of matrices `A` with
`A v - v ∈ p` for every vector `v` is commutative, and these subgroups are permuted by conjugation
exactly as the lines are permuted by `SL ι F`. Every elementary transvection `xᵢⱼ(c)` lies in the
subgroup of the coordinate line through `eᵢ`, and transvections generate `SL ι F`, so their images
form an Iwasawa structure on the action of `PSL ι F`. Iwasawa's criterion
`MulAction.IwasawaStructure.isSimpleGroup` then shows that `PSL ι F` is simple as soon as it is
perfect, which holds when `SL ι F` is.

`SL ι F` is perfect on at least three coordinates over every field, and on two coordinates when
`F` has a nonzero element whose square is not one, in particular when `F` has at least four
elements. This gives the simplicity of `PSL_n(F)` in all the classical cases: every `n ≥ 3`, and
`n = 2` outside `F = 𝔽₂, 𝔽₃`.

Mathlib proves the case of `Fin 2` coordinates
(`Matrix.ProjectiveSpecialLinearGroup.rank_two_simple`, with the Iwasawa structure `PSL2.Iwasawa`).
Its commutativity and conjugation arguments apply verbatim to every coordinate type and are reused
here, while the generation step is the general generation of `SL ι F` by transvections.

## Main definitions

* `Matrix.ProjectiveSpecialLinearGroup.iwasawaStructure`: the Iwasawa structure of the action of
  `PSL ι F` on `ℙ F (ι → F)`.

## Main results

* `Matrix.SpecialLinearGroup.iSup_lineStab_eq_top`: the subgroups `lineStab p` generate
  `SL ι F`.
* `Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_commutator_eq_top`: `PSL ι F` is simple
  when `SL ι F` is perfect.
* `Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_three_le_card`: `PSL ι F` is simple on at
  least three coordinates.
* `Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_sq_ne_one` and
  `Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_four_le_natCard`: `PSL ι F` is simple on at
  least two coordinates over a field with a nonzero element whose square is not one, for example a
  field with at least four elements.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57–59.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, Theorem 4.10.
-/

public section

open MulAction

open scoped LinearAlgebra.Projectivization

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

namespace Matrix.SpecialLinearGroup

/-- **The subgroups `lineStab p` generate the special linear group.** Each transvection `xᵢⱼ(c)`
lies in the subgroup of the coordinate line through `eᵢ`, and transvections generate `SL ι F`. This
extends Mathlib's `PSL.iSup_lineStab_eq_top` from `Fin 2` to every finite coordinate type. -/
theorem iSup_lineStab_eq_top :
    ⨆ p : ℙ F (ι → F), lineStab p.submodule = (⊤ : Subgroup (SpecialLinearGroup ι F)) := by
  apply le_antisymm le_top
  rw [← closure_range_toSpecialLinearGroup_eq_top_of_field (ι := ι) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  have hv : (Pi.single i (1 : F) : ι → F) ≠ 0 := Pi.single_ne_zero_iff.2 one_ne_zero
  refine Subgroup.mem_iSup_of_mem (Projectivization.mk F _ hv) ?_
  rw [Projectivization.submodule_mk, TransvectionStruct.toSpecialLinearGroup_mk]
  exact SL2Gen.transvection_mem_lineStab hij c

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The images in `PSL ι F` of the subgroups `lineStab p` generate `PSL ι F`. -/
theorem iSup_iwasawaT_eq_top : iSup (PSL.iwasawaT (F := F) (ι := ι)) = ⊤ := by
  rw [← Subgroup.map_iSup, SpecialLinearGroup.iSup_lineStab_eq_top]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- **The Iwasawa structure of `PSL ι F` acting on `ℙ F (ι → F)`.** The subgroup attached to a line
`p` is the image of `lineStab p`; these subgroups are commutative, permuted by conjugation as the
lines are permuted, and generate `PSL ι F`. This extends Mathlib's `PSL2.Iwasawa` from `Fin 2` to
every finite coordinate type. -/
noncomputable def iwasawaStructure :
    IwasawaStructure (ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (SpecialLinearGroup.lineStab (F := F) (ι := ι) p.submodule) := by
      rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
      exact SpecialLinearGroup.lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    simp only [PSL.iwasawaT]
    rw [smul_proj_mk, PSL.smul_submodule, SpecialLinearGroup.lineStab_smul,
      PSL.iwasawaT_map_conj]
  is_generator := iSup_iwasawaT_eq_top

/-- The subgroup that `iwasawaStructure` attaches to a line `p` is the image of `lineStab p`. -/
@[simp]
theorem iwasawaStructure_T (p : ℙ F (ι → F)) : iwasawaStructure.T p = PSL.iwasawaT p :=
  (rfl)

/-- **Iwasawa's theorem for `PSL`.** On at least two coordinates, the projective special linear
group is simple as soon as the special linear group is perfect. -/
theorem isSimpleGroup_of_commutator_eq_top [Nontrivial ι]
    (h : commutator (SpecialLinearGroup ι F) = ⊤) :
    IsSimpleGroup (ProjectiveSpecialLinearGroup ι F) :=
  have : Group.IsPerfect (SpecialLinearGroup ι F) := ⟨h⟩
  IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top iwasawaStructure
    inferInstance

/-- **`PSL_n(F)` is simple for `n ≥ 3`**, over every field. -/
theorem isSimpleGroup_of_three_le_card (h : 3 ≤ Fintype.card ι) :
    IsSimpleGroup (ProjectiveSpecialLinearGroup ι F) :=
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  isSimpleGroup_of_commutator_eq_top (SpecialLinearGroup.commutator_eq_top_of_three_le_card h)

/-- **`PSL_n(F)` is simple for `n ≥ 2`** over a field with a nonzero element whose square is not
one. This extends Mathlib's `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'` from `Fin 2` to
every finite coordinate type with at least two elements. -/
theorem isSimpleGroup_of_sq_ne_one [Nontrivial ι] {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    IsSimpleGroup (ProjectiveSpecialLinearGroup ι F) :=
  isSimpleGroup_of_commutator_eq_top (SpecialLinearGroup.commutator_eq_top ha hasq)

/-- **`PSL_n(F)` is simple for `n ≥ 2`** over a field with at least four elements. This extends
Mathlib's `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple` from `Fin 2` to every finite
coordinate type with at least two elements. -/
theorem isSimpleGroup_of_four_le_natCard [Nontrivial ι] (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup (ProjectiveSpecialLinearGroup ι F) :=
  isSimpleGroup_of_commutator_eq_top (SpecialLinearGroup.commutator_eq_top_of_four_le_natCard hF)

end Matrix.ProjectiveSpecialLinearGroup
