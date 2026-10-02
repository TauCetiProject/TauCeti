/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic
public import TauCeti.InformationTheory.Coding.Puncture

/-!
# Puncturing and shortening additive codes

For an additive code over an abelian alphabet, puncturing restricts words to a set of
retained coordinates. Shortening retains the words whose extension by zero lies in the
original code. These operations need no scalar structure on the alphabet.

Puncturing reduces minimum distance by at most the number of deleted coordinates, even
when its image is zero. Shortening cannot reduce minimum distance provided the shortened
code is nonzero. The latter hypothesis is necessary because the zero code has minimum
distance zero. Forgetting scalar closure in a linear code commutes with both operations,
so their distance bounds are instances of the additive results.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.5 and 1.6.
-/

public section

namespace TauCeti

namespace AdditiveCode

variable {A ι : Type*} [AddCommGroup A]

/-- Puncturing an additive code retains precisely the coordinates in `s`. -/
def puncture (C : AdditiveCode A ι) (s : Set ι) : AdditiveCode A s :=
  C.map (AddMonoidHom.pi fun i : s ↦ Pi.evalAddMonoidHom (fun _ : ι ↦ A) i)

/-- Puncturing is the image under the coordinate restriction homomorphism. -/
theorem puncture_def (C : AdditiveCode A ι) (s : Set ι) :
    puncture C s =
      C.map (AddMonoidHom.pi fun i : s ↦ Pi.evalAddMonoidHom (fun _ : ι ↦ A) i) := (rfl)

/-- Shortening retains the words whose extension by zero is a codeword. -/
noncomputable def shorten (C : AdditiveCode A ι) (s : Set ι) : AdditiveCode A s :=
  C.comap (Function.ExtendByZero.hom A (Subtype.val : s → ι))

/-- Shortening is the inverse image under extension by zero. -/
theorem shorten_def (C : AdditiveCode A ι) (s : Set ι) :
    shorten C s = C.comap (Function.ExtendByZero.hom A (Subtype.val : s → ι)) := (rfl)

/-- A word belongs to the punctured code exactly when it restricts a codeword. -/
@[simp]
theorem mem_puncture_iff {C : AdditiveCode A ι} {s : Set ι} {y : s → A} :
    y ∈ puncture C s ↔ ∃ x ∈ C, ∀ i : s, x i = y i := by
  simp [puncture_def, AddSubgroup.mem_map, funext_iff]

/-- A word belongs to the shortened code exactly when its extension by zero belongs to
the original code. -/
@[simp]
theorem mem_shorten_iff {C : AdditiveCode A ι} {s : Set ι} {y : s → A} :
    y ∈ shorten C s ↔ Subtype.val.extend y 0 ∈ C := Iff.rfl

/-- Equivalently, shortening restricts the codewords that vanish outside the retained set. -/
theorem mem_shorten_iff_exists {C : AdditiveCode A ι} {s : Set ι} {y : s → A} :
    y ∈ shorten C s ↔
      ∃ x ∈ C, (∀ i ∉ s, x i = 0) ∧ ∀ j : s, x j = y j := by
  rw [mem_shorten_iff]
  constructor
  · intro h
    refine ⟨_, h, fun i hi ↦ ?_, fun j ↦ Subtype.val_injective.extend_apply y 0 j⟩
    rw [Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hi (hj ▸ j.2), Pi.zero_apply]
  · rintro ⟨x, hx, hx0, hxy⟩
    convert hx using 1
    funext i
    by_cases hi : i ∈ s
    · exact (Subtype.val_injective.extend_apply y 0 ⟨i, hi⟩).trans (hxy ⟨i, hi⟩).symm
    · rw [hx0 i hi, Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hi (hj ▸ j.2),
        Pi.zero_apply]

/-- Every shortened word is a punctured word. -/
theorem shorten_le_puncture (C : AdditiveCode A ι) (s : Set ι) :
    shorten C s ≤ puncture C s := by
  intro y hy
  obtain ⟨x, hx, _, hxy⟩ := mem_shorten_iff_exists.mp hy
  exact mem_puncture_iff.mpr ⟨x, hx, hxy⟩

/-- Puncturing preserves inclusion of additive codes. -/
@[gcongr]
theorem puncture_mono {C D : AdditiveCode A ι} (h : C ≤ D) (s : Set ι) :
    puncture C s ≤ puncture D s := AddSubgroup.map_mono h

/-- Shortening preserves inclusion of additive codes. -/
@[gcongr]
theorem shorten_mono {C D : AdditiveCode A ι} (h : C ≤ D) (s : Set ι) :
    shorten C s ≤ shorten D s := AddSubgroup.comap_mono h

/-- Puncturing the zero code gives the zero code. -/
@[simp]
theorem puncture_bot (s : Set ι) : puncture (⊥ : AdditiveCode A ι) s = ⊥ :=
  AddSubgroup.map_bot _

/-- Shortening the zero code gives the zero code. -/
@[simp]
theorem shorten_bot (s : Set ι) : shorten (⊥ : AdditiveCode A ι) s = ⊥ := by
  rw [shorten_def, AddMonoidHom.comap_bot, AddMonoidHom.ker_eq_bot_iff]
  exact Function.extend_injective Subtype.val_injective _

/-- Puncturing the whole word space gives the whole retained word space. -/
@[simp]
theorem puncture_top (s : Set ι) : puncture (⊤ : AdditiveCode A ι) s = ⊤ := by
  apply top_unique
  intro y _
  exact mem_puncture_iff.mpr ⟨Subtype.val.extend y 0, AddSubgroup.mem_top _,
    Subtype.val_injective.extend_apply y 0⟩

/-- Shortening the whole word space gives the whole retained word space. -/
@[simp]
theorem shorten_top (s : Set ι) : shorten (⊤ : AdditiveCode A ι) s = ⊤ :=
  AddSubgroup.comap_top _

section MinimumDistance

open Set

variable [DecidableEq A] [Fintype ι] (C : AdditiveCode A ι) (s : Set ι)
  [DecidablePred (· ∈ s)]

/-- Puncturing reduces minimum distance by at most the number of deleted coordinates,
including when the punctured code collapses to zero. The set `s` is retained. -/
theorem hammingMinDist_le_hammingMinDist_puncture_add_card_compl :
    hammingMinDist (C : Set (ι → A)) ≤
      hammingMinDist (puncture C s : Set (s → A)) + Fintype.card ↥sᶜ := by
  by_cases hC : C = ⊥
  · simp [hC]
  by_cases hP : puncture C s = ⊥
  · obtain ⟨x, hx, _, hxd⟩ := exists_hammingNorm_eq_hammingMinDist hC
    have hxs : s.domRestrict x = 0 := by
      have hm : s.domRestrict x ∈ puncture C s := mem_puncture_iff.mpr ⟨x, hx, fun _ ↦ rfl⟩
      simpa [hP] using hm
    rw [← hxd, hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs, hammingNorm_zero]
    simpa [hP] using (hammingNorm_le_card_fintype (x := sᶜ.domRestrict x))
  · obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hP
    obtain ⟨x, hx, hxy⟩ := mem_puncture_iff.mp hy
    have hxs : s.domRestrict x = y := funext hxy
    have hx0 : x ≠ 0 := by
      intro h
      apply hy0
      exact funext fun i ↦ (hxy i).symm.trans (congrFun h i)
    calc
      hammingMinDist (C : Set (ι → A)) ≤ hammingNorm x :=
        hammingMinDist_le_hammingNorm hx hx0
      _ = hammingNorm y + hammingNorm (sᶜ.domRestrict x) := by
        rw [hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs]
      _ ≤ hammingMinDist (puncture C s : Set (s → A)) + Fintype.card ↥sᶜ := by
        rw [hyd]
        exact Nat.add_le_add_left hammingNorm_le_card_fintype _

/-- Shortening cannot decrease minimum distance when the shortened additive code is nonzero. -/
theorem hammingMinDist_le_hammingMinDist_shorten (hS : shorten C s ≠ ⊥) :
    hammingMinDist (C : Set (ι → A)) ≤
      hammingMinDist (shorten C s : Set (s → A)) := by
  obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hS
  obtain ⟨x, hx, hxoff, hxy⟩ := mem_shorten_iff_exists.mp hy
  have hxs : s.domRestrict x = y := funext hxy
  have hxsc : sᶜ.domRestrict x = 0 := funext fun i ↦ hxoff i i.2
  have hx0 : x ≠ 0 := by
    intro h
    apply hy0
    exact funext fun i ↦ (hxy i).symm.trans (congrFun h i)
  calc
    hammingMinDist (C : Set (ι → A)) ≤ hammingNorm x := hammingMinDist_le_hammingNorm hx hx0
    _ = hammingMinDist (shorten C s : Set (s → A)) := by
      rw [hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs, hxsc, hammingNorm_zero,
        add_zero, hyd]

end MinimumDistance

end AdditiveCode

variable {F ι : Type*} [Field F]

/-- Forgetting scalar closure commutes with puncturing a linear code. -/
@[simp]
theorem LinearCode.toAddSubgroup_puncture (C : LinearCode F ι) (s : Set ι) :
    (puncture C s).toAddSubgroup = AdditiveCode.puncture C.toAddSubgroup s := by
  ext y
  rw [Submodule.mem_toAddSubgroup, mem_puncture, AdditiveCode.mem_puncture_iff]
  rfl

/-- Forgetting scalar closure commutes with shortening a linear code. -/
@[simp]
theorem LinearCode.toAddSubgroup_shorten (C : LinearCode F ι) (s : Set ι) :
    (shorten C s).toAddSubgroup = AdditiveCode.shorten C.toAddSubgroup s := by
  ext y
  rw [Submodule.mem_toAddSubgroup, mem_shorten_iff_extend_mem, AdditiveCode.mem_shorten_iff]
  rfl

end TauCeti
