/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.D4Six.Glue
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Glue.Decode
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Glue.Table

/-!
# The additive span of the printed `D₄⁶` glue words

Conway and Sloane print the glue code of `D₄⁶` as `[111111]` and `[0(02332)]`, to be read
`𝔽₄`-linearly. This file shows that the `𝔽₄`-linear reading is forced: the ordinary additive
closure of the six printed words is a subgroup of order `32`, of index two in the glue subgroup
`TauCeti.d4SixGlueSubgroup` of order `64`, and so it is not the glue code of the row.

The missing direction is detected by the first coordinate. The `D₄` glue alphabet is the Klein
four-group with labels `0`, `1 = s`, `2 = v`, `3 = c`, and the labels `0` and `1` form a
subgroup of index two. Every printed word has first label `0` or `1`, while `[222222]`, the
`ω²`-multiple of `[111111]`, has first label `2`.

* `TauCeti.mem_closure_d4SixPrintedDigits_iff`: the additive closure of the printed words
  consists of the words of the glue subgroup whose first label is `0` or `1`.
* `TauCeti.natCard_closure_d4SixPrintedDigits`: it has order `32`.
* `TauCeti.closure_d4SixPrintedDigits_lt_d4SixGlueSubgroup`: it is a proper subgroup of the
  glue subgroup.
* `TauCeti.RootfulNiemeierType.closure_decodedWords_lt_glueSubgroup_d4Sixth`: in the table
  `TauCeti.RootfulNiemeierType`, the additive closure of the decoded expanded patterns of the
  row `D₄⁶` is a proper subgroup of its glue subgroup, which is generated with the `𝔽₄`-linear
  span mode `TauCeti.GlueSpanMode.f4Linear`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §7, and Chapter 16, §1, Table 16.1.
-/

public section

namespace TauCeti

open DynkinType

/-! ### The vector bit of a `D₄` glue label -/

/-- The vector bit of a `D₄` glue class: `0` on the labels `0, 1` and `1` on the labels `2, 3`. -/
private noncomputable def d4VectorBit : (D 4).glueAlphabet (isSimplyLaced_D 4) →+ ZMod 2 :=
  (AddMonoidHom.fst (ZMod 2) (ZMod 2)).comp
    (FiniteQuadraticModule.Isometry.ofEq
      (glueAlphabet_D_of_even 4 (isSimplyLaced_D 4) (by decide))).toAddEquiv.toAddMonoidHom

private theorem d4VectorBit_glueLabelEquiv (i : Fin 4) :
    d4VectorBit ((D 4).glueLabelEquiv (isSimplyLaced_D 4) i) = ((i.val / 2 : ℕ) : ZMod 2) :=
  congrArg Prod.fst (glueLabelEquiv_D_of_even 4 _ (by decide) i)

private theorem d4VectorBit_eq_zero_iff (x : (D 4).glueAlphabet (isSimplyLaced_D 4)) :
    d4VectorBit x = 0 ↔ (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm x).val < 2 := by
  obtain ⟨i, rfl⟩ := ((D 4).glueLabelEquiv (isSimplyLaced_D 4)).surjective x
  rw [d4VectorBit_glueLabelEquiv, Equiv.symm_apply_apply]
  fin_cases i <;> decide

/-! ### The additive span of the printed words -/

/-- The decoding of a digit word of `D₄⁶`. -/
private abbrev d4SixDecode (d : Fin 6 → Fin 4) : d4SixGlueModule :=
  fun j ↦ (D 4).glueLabelEquiv (isSimplyLaced_D 4) (d j)

/-- The vector bit of the first coordinate of a glue word of `D₄⁶`. -/
private noncomputable def d4SixFirstVectorBit : d4SixGlueModule →+ ZMod 2 :=
  d4VectorBit.comp (Pi.evalAddMonoidHom _ 0)

private theorem d4SixFirstVectorBit_apply (w : d4SixGlueModule) :
    d4SixFirstVectorBit w = d4VectorBit (w 0) :=
  (rfl)

private theorem d4SixFirstVectorBit_decode (d : Fin 6 → Fin 4) :
    d4SixFirstVectorBit (d4SixDecode d) = (((d 0).val / 2 : ℕ) : ZMod 2) :=
  d4VectorBit_glueLabelEquiv (d 0)

/-- The word `[222222]`. -/
private abbrev d4SixAllVector : d4SixGlueModule := d4SixDecode ![2, 2, 2, 2, 2, 2]

private theorem d4SixAllVector_add_self : d4SixAllVector + d4SixAllVector = 0 := by
  funext j
  have hj : (![2, 2, 2, 2, 2, 2] : Fin 6 → Fin 4) j = 2 := by fin_cases j <;> rfl
  have h := (D 4).glueLabelEquiv_glueLabelAdd (isSimplyLaced_D 4) 2 2
  have h0 : (D 4).glueLabelAdd ((2 : Fin 4) : ℕ) ((2 : Fin 4) : ℕ) = 0 := by decide
  simp only [h0] at h
  simp only [Pi.add_apply, d4SixAllVector, d4SixDecode, hj]
  exact h.symm.trans (glueLabelEquiv_zero _ _)

private theorem closure_d4SixPrintedDigits_le_ker :
    AddSubgroup.closure (d4SixDecode '' d4SixPrintedDigits) ≤ d4SixFirstVectorBit.ker := by
  rw [AddSubgroup.closure_le]
  rintro _ ⟨d, hd, rfl⟩
  simp only [d4SixPrintedDigits_def, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, d4SixFirstVectorBit_decode]
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem d4SixGlueSubgroup_eq_sup :
    d4SixGlueSubgroup =
      AddSubgroup.zmultiples d4SixAllVector ⊔
        AddSubgroup.closure (d4SixDecode '' d4SixPrintedDigits) := by
  rw [d4SixGlueSubgroup_def, Set.image_insert_eq, Set.insert_eq, AddSubgroup.closure_union,
    ← AddSubgroup.zmultiples_eq_closure]

/-- **The additive span of the printed `D₄⁶` glue words**: a glue word lies in the additive closure
of `[111111]` and the five rotations of `[0(02332)]` exactly when it lies in the glue subgroup and
its first label is `0` or `1`. -/
theorem mem_closure_d4SixPrintedDigits_iff {w : d4SixGlueModule} :
    w ∈ AddSubgroup.closure
        ((fun d j ↦ (D 4).glueLabelEquiv (isSimplyLaced_D 4) (d j)) '' d4SixPrintedDigits) ↔
      w ∈ d4SixGlueSubgroup ∧ (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm (w 0)).val < 2 := by
  rw [← d4VectorBit_eq_zero_iff, ← d4SixFirstVectorBit_apply]
  refine ⟨fun hw ↦ ⟨?_, closure_d4SixPrintedDigits_le_ker hw⟩, fun ⟨hw, h0⟩ ↦ ?_⟩
  · rw [d4SixGlueSubgroup_def]
    exact AddSubgroup.closure_mono (Set.image_mono (Set.subset_insert _ _)) hw
  · rw [d4SixGlueSubgroup_eq_sup, AddSubgroup.mem_sup] at hw
    obtain ⟨_, ⟨k, rfl⟩, p, hp, rfl⟩ := hw
    -- The coefficient `k` of `[222222]` is even, as the first vector bit of `w` vanishes.
    have hk : (k : ZMod 2) = 0 := by
      rw [map_add, map_zsmul, closure_d4SixPrintedDigits_le_ker hp, d4SixFirstVectorBit_decode,
        add_zero] at h0
      simpa using h0
    obtain ⟨m, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k 2).mp hk
    beta_reduce
    rwa [Nat.cast_ofNat, mul_zsmul', two_zsmul, d4SixAllVector_add_self, zsmul_zero, zero_add]

/-- **The additive span of the printed `D₄⁶` glue words has order `32`.** It has index two in the
glue subgroup of order `64`, so the printed words must be read `𝔽₄`-linearly. -/
theorem natCard_closure_d4SixPrintedDigits :
    Nat.card (AddSubgroup.closure
      ((fun d j ↦ (D 4).glueLabelEquiv (isSimplyLaced_D 4) (d j)) '' d4SixPrintedDigits)) = 32 := by
  set P := AddSubgroup.closure (d4SixDecode '' d4SixPrintedDigits)
  have hle : P ≤ d4SixGlueSubgroup := fun _ hw ↦ (mem_closure_d4SixPrintedDigits_iff.mp hw).1
  -- `P` is the kernel of the first vector bit on the glue subgroup, which is onto `ZMod 2`.
  let f := d4SixFirstVectorBit.comp d4SixGlueSubgroup.subtype
  have hker : f.ker = P.addSubgroupOf d4SixGlueSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_closure_d4SixPrintedDigits_iff,
      ← d4VectorBit_eq_zero_iff, ← d4SixFirstVectorBit_apply]
    exact (and_iff_right x.2).symm
  have hall : d4SixAllVector ∈ d4SixGlueSubgroup := by
    rw [d4SixGlueSubgroup_def]
    exact AddSubgroup.subset_closure ⟨_, Set.mem_insert _ _, rfl⟩
  have h1 : f ⟨d4SixAllVector, hall⟩ = 1 :=
    (d4SixFirstVectorBit_decode ![2, 2, 2, 2, 2, 2]).trans (by decide)
  have hrange : f.range = ⊤ := eq_top_iff.mpr fun x _ ↦
    ⟨x.val • ⟨d4SixAllVector, hall⟩, by rw [map_nsmul, h1, nsmul_one, ZMod.natCast_zmod_val]⟩
  have hcard := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, hrange, natCard_d4SixGlueSubgroup, hker,
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv, AddSubgroup.card_top,
    Nat.card_zmod] at hcard
  exact Nat.eq_of_mul_eq_mul_right two_pos hcard

/-- **The additive span of the printed `D₄⁶` glue words is a proper subgroup of the glue
subgroup.** -/
theorem closure_d4SixPrintedDigits_lt_d4SixGlueSubgroup :
    AddSubgroup.closure
        ((fun d j ↦ (D 4).glueLabelEquiv (isSimplyLaced_D 4) (d j)) '' d4SixPrintedDigits) <
      d4SixGlueSubgroup := by
  refine lt_of_le_of_ne (fun _ hw ↦ (mem_closure_d4SixPrintedDigits_iff.mp hw).1) fun h ↦ ?_
  have := natCard_closure_d4SixPrintedDigits
  rw [h, natCard_d4SixGlueSubgroup] at this
  omega

/-! ### The span mode of the table row `D₄⁶` -/

namespace RootfulNiemeierType

/-- The first component of the row `D₄⁶`. -/
private abbrev d4SixthFirst : Fin d4Sixth.components.length := ⟨0, by decide⟩

/-- The vector bit of the first coordinate of a glue word of the table row `D₄⁶`. -/
-- The first component type of the row computes to `D 4` from the exposed table data, so the
-- `D₄` vector bit applies to the first coordinate.
private noncomputable def d4SixthFirstVectorBit : d4Sixth.glueModule →+ ZMod 2 :=
  d4VectorBit.comp (Pi.evalAddMonoidHom (fun i ↦
    (d4Sixth.componentType i).glueAlphabet (d4Sixth.isSimplyLaced_componentType i)) d4SixthFirst)

private theorem d4SixthFirstVectorBit_apply (w : d4Sixth.glueModule) :
    d4SixthFirstVectorBit w = d4VectorBit (w d4SixthFirst) :=
  (rfl)

/-- The first label of a glue word of the row `D₄⁶` is the first digit of its encoding. -/
private theorem val_glueLabelEquiv_symm_first (w : d4Sixth.glueModule) :
    (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm (w d4SixthFirst)).val =
      (encodeGlueWord d4Sixth.componentType d4Sixth.isSimplyLaced_componentType w)[0]'
        (by rw [length_encodeGlueWord]; decide) :=
  (getElem_encodeGlueWord d4Sixth.componentType d4Sixth.isSimplyLaced_componentType w
    d4SixthFirst).symm

/-- **The row `D₄⁶` needs its `𝔽₄`-linear span mode**: the additive closure of the decoded
expanded patterns `[111111]` and `[0(02332)]` is a proper subgroup of the glue subgroup of the
row. -/
theorem closure_decodedWords_lt_glueSubgroup_d4Sixth :
    AddSubgroup.closure (⋃ p ∈ d4Sixth.gluePatterns,
        p.decodedWords d4Sixth.componentType d4Sixth.isSimplyLaced_componentType) <
      d4Sixth.glueSubgroup := by
  set S : Set d4Sixth.glueModule := ⋃ p ∈ d4Sixth.gluePatterns,
    p.decodedWords d4Sixth.componentType d4Sixth.isSimplyLaced_componentType
  have hS : ∀ w ∈ S, encodeGlueWord d4Sixth.componentType d4Sixth.isSimplyLaced_componentType w ∈
      d4Sixth.glueWords ∧ d4SixthFirstVectorBit w = 0 := by
    intro w hw
    simp only [S, Set.mem_iUnion, GluePattern.mem_decodedWords_iff] at hw
    obtain ⟨p, hp, hw⟩ := hw
    refine ⟨mem_glueWords_of_mem_expand hp hw, ?_⟩
    -- Every expanded word has first digit `0` or `1`.
    have hfirst : ∀ p ∈ d4Sixth.gluePatterns, ∀ l ∈ p.expand, ∀ h : 0 < l.length,
        l[0] = 0 ∨ l[0] = 1 := by
      decide
    rw [d4SixthFirstVectorBit_apply]
    refine (d4VectorBit_eq_zero_iff (w d4SixthFirst)).mpr ?_
    rw [val_glueLabelEquiv_symm_first]
    rcases hfirst p hp _ hw (by rw [length_encodeGlueWord]; decide) with h | h <;> omega
  have hle : AddSubgroup.closure S ≤ d4Sixth.glueSubgroup := by
    rw [glueSubgroup_def]
    exact AddSubgroup.closure_mono fun w hw ↦ mem_glueGenerators_iff.mpr (hS w hw).1
  -- The word `[222222]` lies in the glue subgroup but has first vector bit `1`.
  obtain ⟨g, hg, hdec⟩ :=
    exists_decodeGlueWord_mem_glueGenerators replicate_two_mem_glueWords_d4Sixth
  have hg1 : d4SixthFirstVectorBit g = 1 := by
    have hrep := (decodeGlueWord_eq_some_iff _ _ _ _).mp hdec
    have h2 : (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm (g d4SixthFirst)).val = 2 := by
      rw [val_glueLabelEquiv_symm_first, List.getElem_of_eq hrep.symm, List.getElem_replicate]
    rw [d4SixthFirstVectorBit_apply, ← Equiv.apply_symm_apply
      ((D 4).glueLabelEquiv (isSimplyLaced_D 4)) (g d4SixthFirst), d4VectorBit_glueLabelEquiv,
      h2]
    decide
  refine lt_of_le_of_ne hle fun h ↦ ?_
  have hgS : g ∈ AddSubgroup.closure S := by
    rw [h, glueSubgroup_def]
    exact AddSubgroup.subset_closure hg
  have := (AddSubgroup.closure_le _).mpr (fun w hw ↦ AddMonoidHom.mem_ker.mpr (hS w hw).2) hgS
  rw [AddMonoidHom.mem_ker, hg1] at this
  exact one_ne_zero this

end RootfulNiemeierType

end TauCeti
