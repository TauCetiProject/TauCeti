/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Primitive
public import TauCeti.GroupTheory.Perm.WreathProduct.Basic

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finset.NoncommProd

/-!
# Primitivity of the two actions of a wreath product

The permutation wreath product `D ≀ Sym(ι)` has two natural actions, with opposite behaviour.

The imprimitive action on `ι × Λ` is never primitive once `ι` and `Λ` each have at least two
points: every fibre `{i} × Λ` is a block, and such a fibre is neither a single point nor the whole
space.  This is the block structure that gives the action its name.

For the product action on `ι → Λ`, let the group `D` act faithfully and primitively, but not
regularly, on a nontrivial type `Λ`.  When `ι` is finite, `D ≀ Sym(ι)` acts primitively on the
function space `ι → Λ`.  The nonregularity hypothesis is essential.  It provides a nontrivial
stabilizer of a base point; primitivity and faithfulness then say that this stabilizer moves every
other point.  Applied in a single coordinate, such an element turns any nonsingleton block
containing a constant function into a block containing a pair that differs in only one coordinate.
Primitivity of the `D`-action then fills that coordinate, symmetry fills every coordinate, and the
base group fills the whole function space.

## Main results

* `TauCeti.WreathProduct.isBlock_fst_preimage_singleton`: each fibre `{i} × Λ` is a block for the
  imprimitive action.
* `TauCeti.WreathProduct.not_isPreprimitive_imprimitive`: the imprimitive action of `D ≀ Sym(ι)`
  on `ι × Λ` is not primitive when `ι` and `Λ` are nontrivial.
* `TauCeti.WreathProduct.isPreprimitive_product`: the product action of `D ≀ Sym(ι)` is
  primitive when the action of `D` is faithful, primitive, and nonregular.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, Theorem 2.7A.
-/

public section

namespace TauCeti.WreathProduct

open scoped Pointwise

open _root_.MulAction _root_.TauCeti.MulAction

universe u v w

variable {D : Type u} {ι : Type v} {Λ : Type w} [Group D] [MulAction D Λ]

/-! ### The imprimitive action -/

/-- The first projection `ι × Λ → ι`, equivariant from the imprimitive action of `D ≀ Sym(ι)` to
the action of the top group `Sym(ι)` along the projection `SemidirectProduct.rightHom`. -/
private def fstMulActionHom :
    ι × Λ →ₑ[(SemidirectProduct.rightHom : WreathProduct D ι →* Equiv.Perm ι)] ι where
  toFun := Prod.fst
  map_smul' _ _ := rfl

/-- Each fibre `{i} × Λ` is a block for the imprimitive action of `D ≀ Sym(ι)` on `ι × Λ`. -/
theorem isBlock_fst_preimage_singleton (i : ι) :
    IsBlock (WreathProduct D ι) (Prod.fst ⁻¹' {i} : Set (ι × Λ)) :=
  (IsTrivialBlock.isBlock (G := Equiv.Perm ι) (Or.inl Set.subsingleton_singleton)).preimage
    (fstMulActionHom (D := D) (Λ := Λ))

/-- **The imprimitive action is not primitive.** When there are at least two fibres with at least
two points each, a fibre `{i} × Λ` is a block that is neither a subsingleton nor the whole
space. -/
theorem not_isPreprimitive_imprimitive [Nontrivial ι] [Nontrivial Λ] :
    ¬ IsPreprimitive (WreathProduct D ι) (ι × Λ) := by
  intro h
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨a, b, hab⟩ := exists_pair_ne Λ
  rcases (isBlock_fst_preimage_singleton (D := D) (Λ := Λ) i).subsingleton_or_eq_univ with
    hs | hu
  · have ha : (i, a) ∈ (Prod.fst ⁻¹' {i} : Set (ι × Λ)) :=
      Set.mem_preimage.mpr (Set.mem_singleton i)
    have hb : (i, b) ∈ (Prod.fst ⁻¹' {i} : Set (ι × Λ)) :=
      Set.mem_preimage.mpr (Set.mem_singleton i)
    exact hab (congrArg Prod.snd (hs ha hb))
  · have hmem : (j, a) ∈ (Prod.fst ⁻¹' {i} : Set (ι × Λ)) := hu ▸ Set.mem_univ _
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact hij hmem.symm

/-! ### The product action -/

/-- The product action of a full permutation wreath product is primitive when its base action is
faithful and primitive but not regular.

Here nonregularity is expressed as failure of `IsCancelSMul`: for a pretransitive action,
`IsCancelSMul D Λ` says exactly that every point stabilizer is trivial.  The hypotheses imply the
usual lower bound of three on the size of a finite `Λ`; stating the theorem this way also covers
infinite primitive actions. -/
theorem isPreprimitive_product [Finite ι] [Nontrivial Λ] [FaithfulSMul D Λ]
    [IsPreprimitive D Λ] (hnotRegular : ¬ IsCancelSMul D Λ) :
    IsPreprimitive (WreathProduct D ι) (ι → Λ) := by
  classical
  let _ := Fintype.ofFinite ι
  -- We use these coordinate inclusions both to perturb a block in one place and, at the end,
  -- to generate every element of the finite base group.
  let baseSingle (i : ι) : D →* WreathProduct D ι :=
    SemidirectProduct.inl.comp (MonoidHom.mulSingle (fun _ : ι ↦ D) i)
  obtain ⟨a, ha⟩ : ∃ a : Λ, stabilizer D a ≠ ⊥ := by
    contrapose! hnotRegular
    exact isCancelSMul_iff_stabilizer_eq_bot.mpr hnotRegular
  let c : ι → Λ := fun _ ↦ a
  let _ : IsPretransitive (WreathProduct D ι) (ι → Λ) :=
    { exists_smul_eq := fun x y ↦ by
        choose d hd using fun i ↦ exists_smul_eq D (x i) (y i)
        refine ⟨⟨d, 1⟩, funext fun i ↦ ?_⟩
        simpa using hd i }
  -- It suffices to show that a nonsingleton block through the constant function is universal.
  apply IsPreprimitive.of_isTrivialBlock_base c
  intro B hc hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  have hnontrivial : B.Nontrivial := Set.not_subsingleton_iff.mp hsub
  obtain ⟨x, hx, y, hy, hxy⟩ := hnontrivial
  obtain ⟨y, hy, hyc⟩ : ∃ y ∈ B, y ≠ c := by
    by_cases hxc : x = c
    · exact ⟨y, hy, fun hyc ↦ hxy (hxc.trans hyc.symm)⟩
    · exact ⟨x, hx, hxc⟩
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ a := by
    by_contra h
    push Not at h
    exact hyc (funext h)
  -- A stabilizer element moves the exceptional coordinate without moving the constant tuple.
  obtain ⟨d, hda, hdy⟩ := exists_mem_stabilizer_smul_ne a ha hi
  let s : WreathProduct D ι := baseSingle i d
  have hsc : s • c = c := by
    funext j
    by_cases hji : j = i
    · subst j
      simpa [s, baseSingle, c] using mem_stabilizer_iff.mp hda
    · simp [s, baseSingle, c, hji]
  have hsy_ne : s • y ≠ y := by
    intro h
    exact hdy (by simpa [s, baseSingle] using congrFun h i)
  have hsB : s • B = B := hB.smul_eq_of_mem hc (hsc.symm ▸ hc)
  have hsy : s • y ∈ B := hsB ▸ Set.smul_mem_smul_set hy
  choose t ht using fun j ↦ exists_smul_eq D (y j) a
  let w : WreathProduct D ι := ⟨t, 1⟩
  have hwy : w • y = c := by
    funext j
    simpa [w, c] using ht j
  have hwB : w • B = B := hB.smul_eq_of_mem hy (hwy.symm ▸ hc)
  let b : Λ := (w • (s • y)) i
  have hba : b ≠ a := by
    have hb : b = t i • (d • y i) := by
      simp [b, w, s, baseSingle]
    rw [hb, ← ht i]
    exact fun h ↦ hdy (smul_left_cancel (t i) h)
  have hwsy : w • (s • y) ∈ B := hwB ▸ Set.smul_mem_smul_set hsy
  let vary : Λ → ι → Λ := fun z ↦ Function.update c i z
  have hwsy_eq : w • (s • y) = vary b := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [vary, b]
    · calc
        (w • (s • y)) j = (w • y) j := by
          simp [w, s, baseSingle, hji]
        _ = c j := congrFun hwy j
        _ = vary b j := by simp [vary, hji]
  -- Pulling the block back along the equivariant one-coordinate map lets base primitivity fill
  -- that coordinate completely.
  let varyEquiv : Λ →ₑ[baseSingle i] (ι → Λ) :=
    { toFun := vary
      map_smul' := fun g z ↦ by
        funext j
        by_cases hji : j = i
        · subst j
          have hone : (1 : Equiv.Perm ι).symm i = i := rfl
          simp [vary, baseSingle, hone]
        · have hone : (1 : Equiv.Perm ι).symm j = j := rfl
          simp [vary, baseSingle, hone, hji] }
  have hC : IsBlock D (varyEquiv ⁻¹' B) := hB.preimage varyEquiv
  have haC : a ∈ varyEquiv ⁻¹' B := by
    -- Expose membership in the preimage of the bundled equivariant map.
    change vary a ∈ B
    have : vary a = c := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [vary, c]
      · simp [vary, c, hji]
    rwa [this]
  have hbC : b ∈ varyEquiv ⁻¹' B := by
    -- Expose membership in the same preimage at the second point.
    change vary b ∈ B
    rwa [← hwsy_eq]
  have hC_univ : varyEquiv ⁻¹' B = Set.univ :=
    (IsPreprimitive.isTrivialBlock_of_isBlock hC).resolve_left fun h ↦ hba (h hbC haC)
  have hvary (z : Λ) : vary z ∈ B := by
    have : z ∈ varyEquiv ⁻¹' B := hC_univ.symm ▸ Set.mem_univ z
    exact this
  -- The top symmetric group transports the filled coordinate to any other coordinate.
  have hvaryAt (j : ι) (z : Λ) : Function.update c j z ∈ B := by
    let q : Equiv.Perm ι := Equiv.swap i j
    let r : WreathProduct D ι := ⟨1, q⟩
    have hrc : r • c = c := by
      funext k
      simp [r, c]
    have hrB : r • B = B := hB.smul_eq_of_mem hc (hrc.symm ▸ hc)
    have hr : r • vary z = Function.update c j z := by
      funext k
      by_cases hij : i = j
      · subst j
        simp [r, vary, q, c]
      · by_cases hki : k = i
        · subst k
          simpa [r, vary, q, c, hij] using
            (Function.update_of_ne (Ne.symm hij) z c)
        · by_cases hkj : k = j
          · subst k
            simp [r, vary, q, c]
          · simp [r, vary, q, c, Equiv.swap_apply_def, hki, hkj]
    rw [← hr, ← hrB]
    exact Set.smul_mem_smul_set (hvary z)
  have hsingle (j : ι) (g : D) : baseSingle j g ∈ stabilizer (WreathProduct D ι) B := by
    rw [mem_stabilizer_iff]
    apply hB.smul_eq_of_mem hc
    have hvalue : baseSingle j g • c = Function.update c j (g • a) := by
      funext k
      by_cases hkj : k = j
      · subst k
        simp [baseSingle, c]
      · simp [baseSingle, c, hkj]
    rw [hvalue]
    exact hvaryAt j (g • a)
  -- Finiteness of `ι` now lets the single-coordinate elements generate an arbitrary base
  -- element, which sends the constant tuple to any prescribed tuple.
  apply Set.eq_univ_of_forall
  intro z
  choose f hf using fun j ↦ exists_smul_eq D a (z j)
  let u : WreathProduct D ι := ⟨f, 1⟩
  have huB : u ∈ stabilizer (WreathProduct D ι) B := by
    let K := (stabilizer (WreathProduct D ι) B).comap SemidirectProduct.inl
    have hfK : f ∈ K := by
      rw [← Finset.noncommProd_mulSingle f]
      apply K.noncommProd_mem
        (fun i _ j _ _ ↦ Pi.mulSingle_apply_commute f i j)
      intro j _
      exact hsingle j (f j)
    exact hfK
  have huc : u • c = z := by
    funext j
    simpa [u, c] using hf j
  rw [← huc, ← mem_stabilizer_iff.mp huB]
  exact Set.smul_mem_smul_set hc

end TauCeti.WreathProduct
