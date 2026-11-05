/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Stabilizer.Chain
public import TauCeti.InformationTheory.Coding.Additive.Equivalence
public import TauCeti.InformationTheory.Coding.Binary.Golay.Basic

/-!
# Permutation automorphisms and octad rigidity of the extended binary Golay code

Because the extended binary Golay code `TauCeti.BinaryGolay.code` has minimum weight eight, two
distinct octads (codewords of weight eight) can share at most four nonzero coordinates: over
`ZMod 2`, any five shared nonzero coordinates cancel in their difference, leaving a nonzero
codeword of weight at most `3 + 3 = 6 < 8`. Consequently, any coordinate permutation automorphism
of `code` that fixes at least five points of an octad fixes that octad as a codeword and stabilizes
its eight-point support setwise.

Combining octad rigidity with systematic encoding (`encodingEquiv`) and Euclidean self-duality
(`euclideanDual_code`) gives a concrete seven-point base `![0, 1, 2, 3, 4, 17, 5]` for the full
permutation automorphism group `AdditiveCode.permutationAut code.toAddSubgroup`:

* The unique octad containing `{0, 1, 2, 3, 4}` has support `{0, 1, 2, 3, 4, 17, 21, 23}`. Every
  automorphism fixing `0, 1, 2, 3, 4` maps `17` into `{17, 21, 23}`, and every automorphism fixing
  `0, 1, 2, 3, 4, 17` maps `5` into the sixteen-point complement of `{0, 1, 2, 3, 4, 17, 21, 23}`.
* Six pairs of octads, each meeting `{0, 1, 2, 3, 4, 17, 5}` in five coordinates, isolate the
  remaining information coordinates `6, 7, 8, 9, 10, 11` outside `{0, 1, 2, 3, 4, 17, 5}`. Thus
  any automorphism fixing `{0, 1, 2, 3, 4, 17, 5}` fixes all twelve information coordinates, hence
  fixes every codeword, and therefore equals `1`.

This bounds the basic-orbit lengths of `AdditiveCode.permutationAut code.toAddSubgroup` by
`24, 23, 22, 21, 20, 3, 16` and its order by `244823040`.

## Main declarations

* `TauCeti.BinaryGolay.mem_permutationAut_code_iff`: Gram-matrix criterion for coordinate
  permutation automorphisms of `code`.
* `TauCeti.BinaryGolay.eq_of_mem_code_of_hammingNorm_eq_eight`: at most one octad is nonzero on any
  five given coordinates.
* `TauCeti.BinaryGolay.comp_symm_eq_of_mem_permutationAut_of_hammingNorm_eq_eight`: an automorphism
  fixing five coordinates of an octad fixes that octad.
* `TauCeti.BinaryGolay.base`: the seven-point base `0, 1, 2, 3, 4, 17, 5` of the permutation
  automorphism group.
* `TauCeti.BinaryGolay.stabilizerChain_permutationAut_seven`: the pointwise stabilizer of
  `0, 1, 2, 3, 4, 17, 5` in `AdditiveCode.permutationAut code.toAddSubgroup` is trivial.
* `TauCeti.BinaryGolay.natCard_permutationAut_code_toAddSubgroup_le`,
  `TauCeti.BinaryGolay.natCard_permutationAut_code_le`: the permutation automorphism group of `code`
  has order at most `244823040`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer,
  1999, Chapter 10, §2.
* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University Press,
  2003, §9.2 and §10.2.
-/

public section

namespace TauCeti.BinaryGolay

open Matrix MulAction

/-! ### Gram criterion, decidability, and coordinate separation -/

/-- Entry formula for `block` using `Bool` arithmetic for fast kernel evaluation. -/
private def blockFun (i j : Fin 12) : ZMod 2 :=
  if i = 0 then (if j = 0 then 0 else 1) else if j = 0 then 1 else
    let r := (i.val + j.val - 2) % 11
    if r == 0 || r == 1 || r == 3 || r == 4 || r == 5 || r == 9 then 1 else 0

private theorem block_eq_blockFun : block = blockFun := by
  ext i j
  rw [block_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- A coordinate permutation preserves the extended binary Golay code if and only if permuting the
columns of `generator` remains orthogonal to `generator`. -/
theorem mem_permutationAut_code_iff {e : Equiv.Perm (Fin 24)} :
    e ∈ AdditiveCode.permutationAut code.toAddSubgroup ↔
      generator * (generator.submatrix id e.symm).transpose = 0 := by
  rw [AdditiveCode.mem_permutationAut_toAddSubgroup_iff, TauCeti.mem_permutationAut]
  simp only [TauCeti.funCongrLeft_mem_permutationGroup, true_and]
  have hfin : Module.finrank (ZMod 2)
      (code.map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm).toLinearMap) =
        Module.finrank (ZMod 2) code :=
    LinearEquiv.finrank_map_eq _ _
  have hmap : code.map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm).toLinearMap =
      (generator.submatrix id e.symm).generatedBy := by
    rw [code_def, Matrix.generatedBy_submatrix_equiv]
  constructor
  · intro h
    rw [← Matrix.generatedBy_le_checkedBy_iff, checkedBy_generator, ← hmap, h]
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq ?_ hfin
    rw [hmap, ← checkedBy_generator, Matrix.generatedBy_le_checkedBy_iff]
    exact h

/-- Membership in the coordinate permutation automorphism group of `BinaryGolay.code` is decidable
via the Gram criterion. -/
instance instDecidableMemPermutationAutCode (e : Equiv.Perm (Fin 24)) :
    Decidable (e ∈ AdditiveCode.permutationAut code.toAddSubgroup) :=
  let b : Matrix (Fin 12) (Fin 12) (ZMod 2) := fun i j ↦
    if i = 0 then (if j = 0 then 0 else 1) else if j = 0 then 1 else
      let r := (i.val + j.val - 2) % 11
      if r == 0 || r == 1 || r == 3 || r == 4 || r == 5 || r == 9 then 1 else 0
  let g : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
    fun i ↦ Fin.append ((1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) i) (b i)
  decidable_of_iff (g * (g.submatrix id e.symm).transpose = 0)
    (by
      have hg : generator = g := by
        rw [generator_def, block_eq_blockFun]
        rfl
      rw [mem_permutationAut_code_iff, hg])

/-- Two codewords of the extended binary Golay code agreeing on the twelve information coordinates
are equal. -/
theorem eq_of_mem_code_of_forall_castAdd_eq {x y : Fin 24 → ZMod 2} (hx : x ∈ code) (hy : y ∈ code)
    (h : ∀ i : Fin 12, x (i.castAdd 12) = y (i.castAdd 12)) : x = y := by
  have hsub : (⟨x, hx⟩ : code) = ⟨y, hy⟩ :=
    encodingEquiv.symm.injective <| funext fun i ↦ by
      rw [encodingEquiv_symm_apply, encodingEquiv_symm_apply]
      exact h i
  exact congrArg Subtype.val hsub

/-- Distinct coordinates of `Fin 24` are separated by some codeword of `code`. -/
theorem eq_of_forall_mem_code_apply_eq {i j : Fin 24} (h : ∀ c ∈ code, c i = c j) : i = j := by
  by_contra hij
  let v : Fin 24 → ZMod 2 := Pi.single i 1 - Pi.single j 1
  have hv_mem : v ∈ code := by
    rw [← euclideanDual_code, Submodule.mem_euclideanDual]
    intro c hc
    simp [v, dotProduct_sub, h c hc]
  have hv_ne : v ≠ 0 := by
    intro hv0
    have hi := congrFun hv0 i
    simp [v, hij] at hi
  have h8 : 8 ≤ hammingNorm v := eight_le_hammingNorm hv_mem hv_ne
  have hle2 : hammingNorm v ≤ 2 := by
    have hsub : Finset.univ.filter (fun k ↦ v k ≠ 0) ⊆ ({i, j} : Finset (Fin 24)) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      by_contra hnij
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnij
      exact hk (by simp [v, Pi.single_eq_of_ne hnij.1, Pi.single_eq_of_ne hnij.2])
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le i {j})
  omega

/-! ### Octad uniqueness and rigidity -/

/-- Two octads of the extended binary Golay code that are both nonzero on at least five coordinates
are equal. -/
theorem eq_of_mem_code_of_hammingNorm_eq_eight {x y : Fin 24 → ZMod 2} (hx : x ∈ code)
    (hy : y ∈ code) (hxw : hammingNorm x = 8) (hyw : hammingNorm y = 8) {s : Finset (Fin 24)}
    (hs5 : 5 ≤ s.card) (hs : ∀ i ∈ s, x i ≠ 0 ∧ y i ≠ 0) : x = y := by
  by_contra hxy
  have h8 : 8 ≤ hammingNorm (x - y) :=
    eight_le_hammingNorm (code.sub_mem hx hy) (sub_ne_zero.mpr hxy)
  let sx := Finset.univ.filter fun i ↦ x i ≠ 0
  let sy := Finset.univ.filter fun i ↦ y i ≠ 0
  let sd := Finset.univ.filter fun i ↦ (x - y) i ≠ 0
  have hsx : sx.card = 8 := hxw
  have hsy : sy.card = 8 := hyw
  have hsd : sd.card = hammingNorm (x - y) := rfl
  have hinter : 5 ≤ (sx ∩ sy).card := by
    refine hs5.trans (Finset.card_le_card fun i hi ↦ ?_)
    simp [sx, sy, (hs i hi).1, (hs i hi).2]
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hsd_sub : sd ⊆ (sx \ sy) ∪ (sy \ sx) := by
    intro i hi
    simp only [sd, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero] at hi
    rcases h01 (x i) with hxi | hxi <;> rcases h01 (y i) with hyi | hyi
    · exact absurd (hxi.trans hyi.symm) hi
    · exact Finset.mem_union_right _ (by simp [sx, sy, hxi, hyi])
    · exact Finset.mem_union_left _ (by simp [sx, sy, hxi, hyi])
    · exact absurd (hxi.trans hyi.symm) hi
  have hcard_le : sd.card ≤ (sx \ sy).card + (sy \ sx).card :=
    (Finset.card_le_card hsd_sub).trans (Finset.card_union_le _ _)
  have hsx_split := Finset.card_sdiff_add_card_inter sx sy
  have hsy_split := Finset.card_sdiff_add_card_inter sy sx
  rw [Finset.inter_comm sy sx] at hsy_split
  omega

/-- A coordinate permutation automorphism of `code` fixing at least five coordinates of the support
of an octad fixes that octad as a codeword. -/
theorem comp_symm_eq_of_mem_permutationAut_of_hammingNorm_eq_eight {σ : Equiv.Perm (Fin 24)}
    (hσ : σ ∈ AdditiveCode.permutationAut code.toAddSubgroup) {x : Fin 24 → ZMod 2}
    (hx : x ∈ code) (hxw : hammingNorm x = 8) {s : Finset (Fin 24)} (hs5 : 5 ≤ s.card)
    (hs : ∀ i ∈ s, x i ≠ 0 ∧ σ i = i) : x ∘ σ.symm = x :=
  eq_of_mem_code_of_hammingNorm_eq_eight
    (AdditiveCode.comp_symm_mem_of_mem_permutationAut hσ hx) hx
    ((Equiv.hammingNorm_comp σ.symm x).trans hxw) hxw hs5 fun i hi ↦ by
      have hsymm : σ.symm i = i := σ.symm_apply_eq.mpr (hs i hi).2.symm
      exact ⟨by simpa [Function.comp_apply, hsymm] using (hs i hi).1, (hs i hi).1⟩

/-- If an automorphism `σ` fixes at least five coordinates of an octad `x`, then `x` is constant on
every `σ`-orbit. -/
theorem apply_perm_eq_of_mem_permutationAut_of_hammingNorm_eq_eight {σ : Equiv.Perm (Fin 24)}
    (hσ : σ ∈ AdditiveCode.permutationAut code.toAddSubgroup) {x : Fin 24 → ZMod 2}
    (hx : x ∈ code) (hxw : hammingNorm x = 8) {s : Finset (Fin 24)} (hs5 : 5 ≤ s.card)
    (hs : ∀ i ∈ s, x i ≠ 0 ∧ σ i = i) (i : Fin 24) : x (σ i) = x i := by
  have h := congrFun (comp_symm_eq_of_mem_permutationAut_of_hammingNorm_eq_eight hσ hx hxw hs5 hs)
    (σ i)
  simpa using h.symm

/-! ### The seven-point base `0, 1, 2, 3, 4, 17, 5` -/

/-- The canonical seven-point base `0, 1, 2, 3, 4, 17, 5` for the permutation automorphism group of
`BinaryGolay.code`. Its body is exposed so importing modules can evaluate basic orbits in the
kernel. -/
@[expose] def base : ℕ → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 17
  | 6 => 5
  | _ => 0

@[simp] theorem base_zero : base 0 = 0 := (rfl)
@[simp] theorem base_one : base 1 = 1 := (rfl)
@[simp] theorem base_two : base 2 = 2 := (rfl)
@[simp] theorem base_three : base 3 = 3 := (rfl)
@[simp] theorem base_four : base 4 = 4 := (rfl)
@[simp] theorem base_five : base 5 = 17 := (rfl)
@[simp] theorem base_six : base 6 = 5 := (rfl)

@[simp]
theorem base_of_seven_le {n : ℕ} (hn : 7 ≤ n) : base n = 0 := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
  | _ + 7 => rfl

/-- The first seven points of `base` are pairwise distinct. -/
theorem injOn_base_Iio_seven : Set.InjOn base (Set.Iio 7) := by
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  interval_cases i <;> interval_cases j <;> simp_all

/-- At each of the seven base levels, the basic orbit avoids all previously fixed base points. -/
theorem orbit_stabilizerChain_subset_compl_of_lt_seven {i : ℕ} (hi : i < 7) :
    orbit ((AdditiveCode.permutationAut code.toAddSubgroup).stabilizerChain base i) (base i) ⊆
      (base '' Set.Iio i)ᶜ :=
  Subgroup.orbit_stabilizerChain_subset_compl fun ⟨_, hj, hji⟩ ↦
    (Set.mem_Iio.mp hj).ne (injOn_base_Iio_seven ((Set.mem_Iio.mp hj).trans hi) hi hji)

/-- For `i < 7`, the complement of the first `i` base points has cardinality `24 - i`. -/
theorem ncard_compl_image_base_Iio {i : ℕ} (hi : i < 7) :
    ((base '' Set.Iio i)ᶜ : Set (Fin 24)).ncard = 24 - i := by
  rw [Set.ncard_compl _ (Set.toFinite _),
    (injOn_base_Iio_seven.mono fun _ hx ↦ lt_trans hx hi).ncard_image,
    Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio, Nat.card_fin]

/-- Message vector of the unique octad containing `{0, 1, 2, 3, 4}`. -/
private def primaryOctadMessage : Fin 12 → ZMod 2 :=
  ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]

/-- The unique octad `{0, 1, 2, 3, 4, 17, 21, 23}` containing `{0, 1, 2, 3, 4}`. -/
private def primaryOctad : Fin 24 → ZMod 2 :=
  Fin.append primaryOctadMessage (primaryOctadMessage ᵥ* blockFun)

private theorem primaryOctad_mem_code : primaryOctad ∈ code :=
  mem_code_iff.mpr ⟨primaryOctadMessage, by rw [block_eq_blockFun]; rfl⟩

private theorem hammingNorm_primaryOctad : hammingNorm primaryOctad = 8 := by
  decide +kernel

private theorem primaryOctad_ne_zero_iff :
    ∀ i : Fin 24, primaryOctad i ≠ 0 ↔ i ∈ ({0, 1, 2, 3, 4, 17, 21, 23} : Finset (Fin 24)) := by
  decide +kernel

/-- The basic orbit at level `5` (`base 5 = 17`) lies in `{17, 21, 23}`. -/
theorem orbit_stabilizerChain_five_subset :
    orbit ((AdditiveCode.permutationAut code.toAddSubgroup).stabilizerChain base 5) (base 5) ⊆
      (({17, 21, 23} : Finset (Fin 24)) : Set (Fin 24)) := by
  intro _ hy
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := mem_orbit_iff.mp hy
  rw [Subgroup.mem_stabilizerChain_iff] at hσ
  rcases hσ with ⟨hσ_aut, hσ_fix⟩
  have hpres := apply_perm_eq_of_mem_permutationAut_of_hammingNorm_eq_eight hσ_aut
    primaryOctad_mem_code hammingNorm_primaryOctad (s := {0, 1, 2, 3, 4}) (by decide)
    (fun i hi ↦ by
      fin_cases i <;> simp at hi
      · exact ⟨by decide +kernel, hσ_fix 0 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 1 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 2 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 3 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 4 (by omega)⟩)
  have h17 : primaryOctad (σ 17) ≠ 0 := by
    rw [hpres 17]
    decide +kernel
  have hin := (primaryOctad_ne_zero_iff (σ 17)).mp h17
  have hne : ∀ k < 5, σ 17 ≠ base k := by
    intro k hk heq
    have hfix := hσ_fix k hk
    have : (17 : Fin 24) = base k := σ.injective (heq.trans hfix.symm)
    interval_cases k <;> simp at this
  have h0 := hne 0 (by omega)
  have h1 := hne 1 (by omega)
  have h2 := hne 2 (by omega)
  have h3 := hne 3 (by omega)
  have h4 := hne 4 (by omega)
  rw [Subgroup.smul_def, Equiv.Perm.smul_def, base_five, Finset.mem_coe]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hin ⊢
  rcases hin with h | h | h | h | h | h | h | h
  · exact absurd h h0
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact absurd h h4
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The basic orbit at level `6` (`base 6 = 5`) lies in the sixteen-point complement of the octad
`{0, 1, 2, 3, 4, 17, 21, 23}`. -/
theorem orbit_stabilizerChain_six_subset :
    orbit ((AdditiveCode.permutationAut code.toAddSubgroup).stabilizerChain base 6) (base 6) ⊆
      ((({0, 1, 2, 3, 4, 17, 21, 23} : Finset (Fin 24))ᶜ : Finset (Fin 24)) : Set (Fin 24)) := by
  intro _ hy
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := mem_orbit_iff.mp hy
  rw [Subgroup.mem_stabilizerChain_iff] at hσ
  rcases hσ with ⟨hσ_aut, hσ_fix⟩
  have hpres := apply_perm_eq_of_mem_permutationAut_of_hammingNorm_eq_eight hσ_aut
    primaryOctad_mem_code hammingNorm_primaryOctad (s := {0, 1, 2, 3, 4}) (by decide)
    (fun i hi ↦ by
      fin_cases i <;> simp at hi
      · exact ⟨by decide +kernel, hσ_fix 0 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 1 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 2 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 3 (by omega)⟩
      · exact ⟨by decide +kernel, hσ_fix 4 (by omega)⟩)
  rw [Subgroup.smul_def, Equiv.Perm.smul_def, base_six, Finset.mem_coe, Finset.mem_compl,
    ← primaryOctad_ne_zero_iff (σ 5), not_not]
  have h5 : primaryOctad 5 = 0 := by decide +kernel
  exact (hpres 5).trans h5

/-- Twelve messages whose encoded octads each contain five points of `{0, 1, 2, 3, 4, 17, 5}` and
pairwise isolate `6, 7, 8, 9, 10, 11` outside `{0, 1, 2, 3, 4, 17, 5}`. -/
private def isolatingOctadMessages : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0;
     1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0;
     1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0;
     1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0;
     0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0;
     1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0;
     1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0;
     1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1;
     1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1]

private def isolatingOctad (r : Fin 12) : Fin 24 → ZMod 2 :=
  Fin.append (isolatingOctadMessages r) (isolatingOctadMessages r ᵥ* blockFun)

private theorem isolatingOctad_mem_code (r : Fin 12) : isolatingOctad r ∈ code :=
  mem_code_iff.mpr ⟨isolatingOctadMessages r, by rw [block_eq_blockFun]; rfl⟩

private def baseSet : Finset (Fin 24) := {0, 1, 2, 3, 4, 17, 5}

private theorem exists_base_eq_of_mem_baseSet :
    ∀ i ∈ baseSet, ∃ k ∈ Finset.range 7, base k = i := by
  decide

private theorem isolatingOctad_spec :
    (∀ r : Fin 12, hammingNorm (isolatingOctad r) = 8 ∧
      5 ≤ (baseSet.filter fun i ↦ isolatingOctad r i ≠ 0).card) ∧
    (∀ t : Fin 6, ∀ j : Fin 24,
      (j ∉ baseSet ∧ isolatingOctad ⟨2 * t.val, by omega⟩ j ≠ 0 ∧
        isolatingOctad ⟨2 * t.val + 1, by omega⟩ j ≠ 0) ↔
        j = ⟨t.val + 6, by omega⟩) := by
  decide +kernel

/-- **The seven points `0, 1, 2, 3, 4, 17, 5` form a base** of the permutation automorphism group of
the extended binary Golay code. -/
theorem stabilizerChain_permutationAut_seven :
    (AdditiveCode.permutationAut code.toAddSubgroup).stabilizerChain base 7 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  rw [Subgroup.mem_stabilizerChain_iff] at hσ
  rcases hσ with ⟨hσ_aut, hσ_fix⟩
  have hfix_baseSet : ∀ i ∈ baseSet, σ i = i := fun i hi ↦ by
    obtain ⟨k, hk, rfl⟩ := exists_base_eq_of_mem_baseSet i hi
    exact hσ_fix k (Finset.mem_range.mp hk)
  obtain ⟨hspec_oct, hspec_iso⟩ := isolatingOctad_spec
  have hpres_iso : ∀ r : Fin 12, ∀ j : Fin 24, isolatingOctad r (σ j) = isolatingOctad r j :=
    fun r ↦ apply_perm_eq_of_mem_permutationAut_of_hammingNorm_eq_eight hσ_aut
      (isolatingOctad_mem_code r) (hspec_oct r).1 (hspec_oct r).2 fun i hi ↦ by
        simp only [Finset.mem_filter] at hi
        exact ⟨hi.2, hfix_baseSet i hi.1⟩
  have hlt6_mem : ∀ i : Fin 12, i.val < 6 → i.castAdd 12 ∈ baseSet := by decide
  have hfix_info : ∀ i : Fin 12, σ (i.castAdd 12) = i.castAdd 12 := by
    intro i
    by_cases hi6 : i.val < 6
    · exact hfix_baseSet _ (hlt6_mem i hi6)
    · let t : Fin 6 := ⟨i.val - 6, by omega⟩
      have hit : (⟨t.val + 6, by omega⟩ : Fin 24) = i.castAdd 12 := by
        ext
        simp [t]
        omega
      have hk_prop := (hspec_iso t (i.castAdd 12)).mpr hit.symm
      have hσ_not_mem : σ (i.castAdd 12) ∉ baseSet := by
        intro hmem
        have := σ.injective ((hfix_baseSet _ hmem).symm.trans rfl)
        exact hk_prop.1 (this ▸ hmem)
      have hσ_prop : σ (i.castAdd 12) ∉ baseSet ∧
          isolatingOctad ⟨2 * t.val, by omega⟩ (σ (i.castAdd 12)) ≠ 0 ∧
          isolatingOctad ⟨2 * t.val + 1, by omega⟩ (σ (i.castAdd 12)) ≠ 0 := by
        rw [hpres_iso, hpres_iso]
        exact ⟨hσ_not_mem, hk_prop.2⟩
      exact ((hspec_iso t (σ (i.castAdd 12))).mp hσ_prop).trans hit
  have hfix_codewords : ∀ c ∈ code, c ∘ σ.symm = c := fun c hc ↦
    eq_of_mem_code_of_forall_castAdd_eq
      (AdditiveCode.comp_symm_mem_of_mem_permutationAut hσ_aut hc) hc fun i ↦ by
        rw [Function.comp_apply, σ.symm_apply_eq.mpr (hfix_info i).symm]
  apply Equiv.Perm.ext
  intro j
  rw [Equiv.Perm.one_apply]
  refine (eq_of_forall_mem_code_apply_eq fun c hc ↦ ?_).symm
  have := congrFun (hfix_codewords c hc) (σ j)
  simpa using this

/-- The coordinate permutation automorphism group of `BinaryGolay.code` has order at most
`244823040`. -/
theorem natCard_permutationAut_code_toAddSubgroup_le :
    Nat.card (AdditiveCode.permutationAut code.toAddSubgroup) ≤ 244823040 := by
  let A := AdditiveCode.permutationAut code.toAddSubgroup
  rw [← A.prod_ncard_orbit_stabilizerChain_eq_card base stabilizerChain_permutationAut_seven]
  have hle : ∀ i : Fin 7, (orbit (A.stabilizerChain base i.val) (base i.val)).ncard ≤
      ![24, 23, 22, 21, 20, 3, 16] i := by
    intro i
    by_cases hi5 : i.val < 5
    · refine (Set.ncard_le_ncard (orbit_stabilizerChain_subset_compl_of_lt_seven i.isLt)).trans ?_
      rw [ncard_compl_image_base_Iio i.isLt]
      fin_cases i <;> simp at hi5 ⊢
    · fin_cases i <;> simp at hi5
      · refine (Set.ncard_le_ncard orbit_stabilizerChain_five_subset).trans ?_
        rw [Set.ncard_coe_finset]
        decide
      · refine (Set.ncard_le_ncard orbit_stabilizerChain_six_subset).trans ?_
        rw [Set.ncard_coe_finset]
        decide
  calc
    ∏ i ∈ Finset.range 7, (orbit (A.stabilizerChain base i) (base i)).ncard =
        ∏ i : Fin 7, (orbit (A.stabilizerChain base i.val) (base i.val)).ncard :=
      (Fin.prod_univ_eq_prod_range
        (fun i ↦ (orbit (A.stabilizerChain base i) (base i)).ncard) 7).symm
    _ ≤ ∏ i : Fin 7, ![24, 23, 22, 21, 20, 3, 16] i :=
      Finset.prod_le_prod fun i _ ↦ hle i
    _ = 244823040 := by decide

/-- The linear permutation automorphism group of `BinaryGolay.code` has order at most
`244823040`. -/
theorem natCard_permutationAut_code_le :
    Nat.card (TauCeti.permutationAut code) ≤ 244823040 := by
  rw [← AdditiveCode.natCard_permutationAut_toAddSubgroup]
  exact natCard_permutationAut_code_toAddSubgroup_le

end TauCeti.BinaryGolay
