/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.InformationTheory.Coding.Basic

/-!
# Puncturing and shortening additive and linear codes

An additive code is an additive subgroup of the word space; its puncture is the image under
restriction, and its shortening is the inverse image under extension by zero. These operations
require only an abelian alphabet. Forgetting scalar closure commutes with both operations.

A linear code on coordinates `ι` is a submodule of the word space `ι → F`, as defined in
`TauCeti/InformationTheory/Coding/Basic.lean`. Given a set `s` of coordinates to retain,
puncturing restricts every codeword to `s`. Shortening first restricts to the codewords which
vanish outside `s`, and then forgets those zero coordinates.

Neither the field nor the coordinate type is assumed finite; finiteness enters only in the
dimension bounds. The API records membership, order preservation, the zero and whole-space cases,
the comparison between shortening and puncturing, and dimension control. Restriction to the deleted
coordinates has the shortened code as its kernel, so `dim shorten C s + dim puncture C sᶜ = dim C`.
For a single deleted coordinate `i` this gives the exact dimensions: shortening at `i` drops the
dimension by one precisely when some codeword is nonzero at `i`, and puncturing at `i` drops it by
one precisely when the unit word at `i` is a codeword.

## Main declarations

* `puncture`: restriction of a code to a retained coordinate set.
* `shorten`: restriction after imposing zero outside the retained coordinate set.
* `punctureAt` and `shortenAt`: the corresponding operations deleting one coordinate.
* `mem_puncture` and `mem_shorten`: membership characterizations.
* `finrank_puncture_le`, `finrank_puncture_eq`, and `finrank_shorten_eq`: dimension control.
* `finrank_shorten_add_finrank_puncture_compl`: rank–nullity for shortening and puncturing.
* `finrank_shortenAt_add_one_of_exists_ne_zero` and `finrank_punctureAt_add_one_of_single_mem`:
  the exact dimension drop when deleting one coordinate.

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
theorem mem_puncture {C : AdditiveCode A ι} {s : Set ι} {y : s → A} :
    y ∈ puncture C s ↔ ∃ x ∈ C, ∀ i : s, x i = y i := by
  simp [puncture_def, AddSubgroup.mem_map, funext_iff]

/-- A word belongs to the shortened code exactly when its extension by zero belongs to
the original code. -/
@[simp]
theorem mem_shorten_iff_extend_mem {C : AdditiveCode A ι} {s : Set ι} {y : s → A} :
    y ∈ shorten C s ↔ Subtype.val.extend y 0 ∈ C := by
  rw [shorten_def, AddSubgroup.mem_comap]
  -- The extension hom coerces definitionally to `fun y ↦ Subtype.val.extend y 0`.
  rfl

/-- Equivalently, shortening restricts the codewords that vanish outside the retained set. -/
theorem mem_shorten {C : AdditiveCode A ι} {s : Set ι} {y : s → A} :
    y ∈ shorten C s ↔
      ∃ x ∈ C, (∀ i ∉ s, x i = 0) ∧ ∀ j : s, x j = y j := by
  rw [mem_shorten_iff_extend_mem]
  constructor
  · intro h
    refine ⟨_, h, fun i hi ↦ ?_, fun j ↦ Subtype.val_injective.extend_apply y 0 j⟩
    rw [Function.extend_val_apply' hi, Pi.zero_apply]
  · rintro ⟨x, hx, hx0, hxy⟩
    convert hx using 1
    funext i
    by_cases hi : i ∈ s
    · exact (Subtype.val_injective.extend_apply y 0 ⟨i, hi⟩).trans (hxy ⟨i, hi⟩).symm
    · rw [hx0 i hi, Function.extend_val_apply' hi, Pi.zero_apply]

/-- Every shortened word is a punctured word. -/
theorem shorten_le_puncture (C : AdditiveCode A ι) (s : Set ι) :
    shorten C s ≤ puncture C s := by
  intro y hy
  obtain ⟨x, hx, _, hxy⟩ := mem_shorten.mp hy
  exact mem_puncture.mpr ⟨x, hx, hxy⟩

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
  -- The extension hom coerces definitionally to `fun y ↦ Subtype.val.extend y 0`.
  exact Function.extend_injective Subtype.val_injective _

/-- Puncturing the whole word space gives the whole retained word space. -/
@[simp]
theorem puncture_top (s : Set ι) : puncture (⊤ : AdditiveCode A ι) s = ⊤ :=
  AddSubgroup.map_top_of_surjective _ fun y ↦
    ⟨Subtype.val.extend y 0, funext fun i ↦ by
      simp [AddMonoidHom.pi_apply]⟩

/-- Shortening the whole word space gives the whole retained word space. -/
@[simp]
theorem shorten_top (s : Set ι) : shorten (⊤ : AdditiveCode A ι) s = ⊤ :=
  AddSubgroup.comap_top _

end AdditiveCode

variable {F : Type*} [Field F] {ι : Type*}

/-- Puncturing a code at `s` retains precisely the coordinates in `s`. -/
noncomputable def puncture (C : LinearCode F ι) (s : Set ι) : LinearCode F s :=
  C.map (LinearMap.funLeft F F (Subtype.val : s → ι))

/-- Puncturing is the image under restriction to the retained coordinates. -/
theorem puncture_def (C : LinearCode F ι) (s : Set ι) :
    puncture C s = C.map (LinearMap.funLeft F F (Subtype.val : s → ι)) := (rfl)

/-- Shortening a code at `s` first imposes zero outside `s`, then retains the coordinates in
`s`. -/
noncomputable def shorten (C : LinearCode F ι) (s : Set ι) : LinearCode F s :=
  (C ⊓ Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule F F)).map
    (LinearMap.funLeft F F (Subtype.val : s → ι))

/-- Shortening is the image under restriction of the words supported on the retained set. -/
theorem shorten_def (C : LinearCode F ι) (s : Set ι) :
    shorten C s = (C ⊓ Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule F F)).map
      (LinearMap.funLeft F F (Subtype.val : s → ι)) := (rfl)

/-- Forgetting scalar closure commutes with puncturing a linear code. -/
@[simp]
theorem LinearCode.puncture_toAddSubgroup (C : LinearCode F ι) (s : Set ι) :
    (puncture C s).toAddSubgroup = AdditiveCode.puncture C.toAddSubgroup s := by
  rw [puncture_def, Submodule.map_toAddSubgroup, AdditiveCode.puncture_def]
  apply congrArg C.toAddSubgroup.map
  ext x i
  simp [LinearMap.funLeft_apply]

/-- Forgetting scalar closure commutes with shortening a linear code. -/
@[simp]
theorem LinearCode.shorten_toAddSubgroup (C : LinearCode F ι) (s : Set ι) :
    (shorten C s).toAddSubgroup = AdditiveCode.shorten C.toAddSubgroup s := by
  ext y
  simp only [Submodule.mem_toAddSubgroup, shorten_def, Submodule.mem_map,
    Submodule.mem_inf, Submodule.mem_pi, Submodule.mem_bot, AdditiveCode.mem_shorten,
    LinearMap.funLeft_apply, funext_iff, Set.mem_compl_iff, and_assoc]

/-- A word belongs to the punctured code exactly when it is the restriction of a codeword. -/
@[simp]
theorem mem_puncture {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ puncture C s ↔ ∃ x ∈ C, ∀ j : s, x j = y j := by
  rw [← Submodule.mem_toAddSubgroup, LinearCode.puncture_toAddSubgroup]
  simp only [AdditiveCode.mem_puncture, Submodule.mem_toAddSubgroup]

/-- A word belongs to the shortened code exactly when its extension by zero is a codeword:
equivalently, it is the restriction of a codeword which vanishes off the retained set. -/
@[simp]
theorem mem_shorten {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ shorten C s ↔
      ∃ x ∈ C, (∀ i ∉ s, x i = 0) ∧ ∀ j : s, x j = y j := by
  rw [← Submodule.mem_toAddSubgroup, LinearCode.shorten_toAddSubgroup]
  simp only [AdditiveCode.mem_shorten, Submodule.mem_toAddSubgroup]

/-- A word on the retained coordinates belongs to the shortened code exactly when its extension
by zero belongs to the original code. -/
theorem mem_shorten_iff_extend_mem {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ shorten C s ↔ Subtype.val.extend y 0 ∈ C := by
  rw [← Submodule.mem_toAddSubgroup, LinearCode.shorten_toAddSubgroup,
    AdditiveCode.mem_shorten_iff_extend_mem, Submodule.mem_toAddSubgroup]

/-- Membership in a puncture retaining one coordinate is determined by that coordinate. -/
theorem mem_puncture_singleton {C : LinearCode F ι} {i : ι} {y : ({i} : Set ι) → F} :
    y ∈ puncture C {i} ↔ ∃ x ∈ C, x i = y ⟨i, Set.mem_singleton i⟩ := by
  rw [mem_puncture]
  constructor
  · rintro ⟨x, hxC, hxy⟩
    exact ⟨x, hxC, hxy ⟨i, Set.mem_singleton i⟩⟩
  · rintro ⟨x, hxC, hxy⟩
    refine ⟨x, hxC, fun j ↦ ?_⟩
    simpa only [Subsingleton.elim j ⟨i, Set.mem_singleton i⟩] using hxy

/-- Membership in a shortening retaining one coordinate is determined by a codeword supported
at that coordinate. -/
theorem mem_shorten_singleton {C : LinearCode F ι} {i : ι} {y : ({i} : Set ι) → F} :
    y ∈ shorten C {i} ↔
      ∃ x ∈ C, (∀ j, j ≠ i → x j = 0) ∧ x i = y ⟨i, Set.mem_singleton i⟩ := by
  rw [mem_shorten]
  constructor
  · rintro ⟨x, hxC, hx0, hxy⟩
    exact ⟨x, hxC, fun j hj ↦ hx0 j (by simpa using hj), hxy ⟨i, Set.mem_singleton i⟩⟩
  · rintro ⟨x, hxC, hx0, hxy⟩
    refine ⟨x, hxC, fun j hj ↦ hx0 j (by simpa using hj), fun j ↦ ?_⟩
    simpa only [Subsingleton.elim j ⟨i, Set.mem_singleton i⟩] using hxy

/-- Puncturing at `i` deletes that coordinate and retains all the others. -/
noncomputable def punctureAt (C : LinearCode F ι) (i : ι) :
    LinearCode F ({i}ᶜ : Set ι) :=
  puncture C {i}ᶜ

/-- Puncturing at one coordinate is puncturing with its singleton complement retained. -/
theorem punctureAt_def (C : LinearCode F ι) (i : ι) :
    punctureAt C i = puncture C {i}ᶜ := (rfl)

/-- Shortening at `i` imposes zero there and retains all the other coordinates. -/
noncomputable def shortenAt (C : LinearCode F ι) (i : ι) :
    LinearCode F ({i}ᶜ : Set ι) :=
  shorten C {i}ᶜ

/-- Shortening at one coordinate is shortening with its singleton complement retained. -/
theorem shortenAt_def (C : LinearCode F ι) (i : ι) :
    shortenAt C i = shorten C {i}ᶜ := (rfl)

/-- A word belongs to the code punctured at `i` exactly when it is the restriction of a
codeword to the other coordinates. -/
@[simp]
theorem mem_punctureAt {C : LinearCode F ι} {i : ι} {y : ({i}ᶜ : Set ι) → F} :
    y ∈ punctureAt C i ↔ ∃ x ∈ C, ∀ j : ({i}ᶜ : Set ι), x j = y j := by
  rw [punctureAt, mem_puncture]

/-- A word belongs to the code shortened at `i` exactly when it extends to a codeword which is
zero at `i`. -/
@[simp]
theorem mem_shortenAt {C : LinearCode F ι} {i : ι} {y : ({i}ᶜ : Set ι) → F} :
    y ∈ shortenAt C i ↔ ∃ x ∈ C, x i = 0 ∧ ∀ j : ({i}ᶜ : Set ι), x j = y j := by
  rw [shortenAt, mem_shorten]
  constructor
  · rintro ⟨x, hxC, hx0, hxy⟩
    exact ⟨x, hxC, hx0 i (by simp), hxy⟩
  · rintro ⟨x, hxC, hxi, hxy⟩
    refine ⟨x, hxC, ?_, hxy⟩
    intro j hj
    classical
    have hji : j = i := by
      by_contra hne
      apply hj
      simpa using hne
    subst j
    exact hxi

/-- Every shortened word is a punctured word. -/
theorem shorten_le_puncture (C : LinearCode F ι) (s : Set ι) : shorten C s ≤ puncture C s := by
  apply (Submodule.toAddSubgroup_le _ _).mp
  simpa only [LinearCode.shorten_toAddSubgroup, LinearCode.puncture_toAddSubgroup] using
    AdditiveCode.shorten_le_puncture C.toAddSubgroup s

/-- Puncturing is monotone in the code. -/
theorem puncture_mono {C D : LinearCode F ι} (h : C ≤ D) (s : Set ι) :
    puncture C s ≤ puncture D s := by
  apply (Submodule.toAddSubgroup_le _ _).mp
  simpa only [LinearCode.puncture_toAddSubgroup] using
    AdditiveCode.puncture_mono ((Submodule.toAddSubgroup_le _ _).mpr h) s

/-- Shortening is monotone in the code. -/
theorem shorten_mono {C D : LinearCode F ι} (h : C ≤ D) (s : Set ι) :
    shorten C s ≤ shorten D s := by
  apply (Submodule.toAddSubgroup_le _ _).mp
  simpa only [LinearCode.shorten_toAddSubgroup] using
    AdditiveCode.shorten_mono ((Submodule.toAddSubgroup_le _ _).mpr h) s

/-- Puncturing sends the zero code to the zero code. -/
@[simp]
theorem puncture_bot (s : Set ι) : puncture (⊥ : LinearCode F ι) s = ⊥ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.puncture_toAddSubgroup, Submodule.bot_toAddSubgroup,
    AdditiveCode.puncture_bot]

/-- Shortening sends the zero code to the zero code. -/
@[simp]
theorem shorten_bot (s : Set ι) : shorten (⊥ : LinearCode F ι) s = ⊥ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.shorten_toAddSubgroup, Submodule.bot_toAddSubgroup,
    AdditiveCode.shorten_bot]

/-- Puncturing the whole word space gives the whole word space on the retained coordinates. -/
@[simp]
theorem puncture_top (s : Set ι) : puncture (⊤ : LinearCode F ι) s = ⊤ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.puncture_toAddSubgroup, Submodule.top_toAddSubgroup,
    AdditiveCode.puncture_top]

/-- Shortening the whole word space gives the whole word space on the retained coordinates. -/
@[simp]
theorem shorten_top (s : Set ι) : shorten (⊤ : LinearCode F ι) s = ⊤ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.shorten_toAddSubgroup, Submodule.top_toAddSubgroup,
    AdditiveCode.shorten_top]

/-- Puncturing to a single retained coordinate `i` gives the whole word space on `{i}` exactly when
some codeword is nonzero at `i`. -/
theorem puncture_singleton_eq_top_iff {C : LinearCode F ι} {i : ι} :
    puncture C {i} = ⊤ ↔ ∃ x ∈ C, x i ≠ 0 := by
  constructor
  · intro h
    have h1 : (1 : ({i} : Set ι) → F) ∈ puncture C {i} := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨x, hxC, hx⟩ := mem_puncture.mp h1
    exact ⟨x, hxC, by simp [hx ⟨i, rfl⟩]⟩
  · rintro ⟨x, hxC, hxi⟩
    refine eq_top_iff.mpr fun y _ ↦
      mem_puncture.mpr ⟨(y ⟨i, rfl⟩ / x i) • x, C.smul_mem _ hxC, fun j ↦ ?_⟩
    obtain rfl : j = ⟨i, rfl⟩ := Subsingleton.elim _ _
    simp [hxi]

/-- Shortening to a single retained coordinate `i` gives the whole word space on `{i}` exactly when
the unit word at `i` is a codeword. -/
theorem shorten_singleton_eq_top_iff [DecidableEq ι] {C : LinearCode F ι} {i : ι} :
    shorten C {i} = ⊤ ↔ Pi.single i 1 ∈ C := by
  constructor
  · intro h
    have h1 : (1 : ({i} : Set ι) → F) ∈ shorten C {i} := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨x, hxC, hx0, hx⟩ := mem_shorten.mp h1
    convert hxC using 1
    ext j
    by_cases hj : j = i
    · subst hj
      simpa using (hx ⟨j, rfl⟩).symm
    · simp [hj, hx0 j hj]
  · intro h
    refine eq_top_iff.mpr fun y _ ↦
      mem_shorten.mpr ⟨y ⟨i, rfl⟩ • Pi.single i 1, C.smul_mem _ h, fun j hj ↦ ?_, fun j ↦ ?_⟩
    · rw [Set.mem_singleton_iff] at hj
      simp [hj]
    · obtain rfl : j = ⟨i, rfl⟩ := Subsingleton.elim _ _
      simp

/-- Puncturing commutes with sums of codes. -/
@[simp]
theorem puncture_sup (C D : LinearCode F ι) (s : Set ι) :
    puncture (C ⊔ D) s = puncture C s ⊔ puncture D s := by
  simp [puncture, Submodule.map_sup]

/-- Shortening commutes with intersections. -/
@[simp]
theorem shorten_inf (C D : LinearCode F ι) (s : Set ι) :
    shorten (C ⊓ D) s = shorten C s ⊓ shorten D s := by
  ext y
  simp only [mem_shorten, Submodule.mem_inf]
  constructor
  · rintro ⟨x, ⟨hxC, hxD⟩, hx0, hxy⟩
    exact ⟨⟨x, hxC, hx0, hxy⟩, ⟨x, hxD, hx0, hxy⟩⟩
  · rintro ⟨⟨x, hxC, hx0, hxy⟩, ⟨z, hzD, hz0, hzy⟩⟩
    have hxz : x = z := funext fun i ↦ by
      by_cases hi : i ∈ s
      · exact (hxy ⟨i, hi⟩).trans (hzy ⟨i, hi⟩).symm
      · exact (hx0 i hi).trans (hz0 i hi).symm
    exact ⟨x, ⟨hxC, hxz ▸ hzD⟩, hx0, hxy⟩

/-- Puncturing cannot increase dimension. -/
theorem finrank_puncture_le (C : LinearCode F ι) [FiniteDimensional F C] (s : Set ι) :
    Module.finrank F (puncture C s) ≤ Module.finrank F C := by
  rw [puncture]
  exact Submodule.finrank_map_le _ _

/-- Puncturing preserves dimension when the only codeword vanishing at every retained
coordinate is zero. -/
theorem finrank_puncture_eq (C : LinearCode F ι) (s : Set ι)
    (h : ∀ x ∈ C, (∀ j : s, x j = 0) → x = 0) :
    Module.finrank F (puncture C s) = Module.finrank F C := by
  rw [puncture, ← LinearMap.range_domRestrict]
  apply LinearMap.finrank_range_of_inj
  intro x y hxy
  refine Subtype.ext (sub_eq_zero.mp (h _ (sub_mem x.2 y.2) fun j ↦ ?_))
  simpa [sub_eq_zero] using congrFun hxy j

/-- Shortening preserves the dimension of the subcode of words supported on the retained
coordinates. -/
theorem finrank_shorten_eq (C : LinearCode F ι) (s : Set ι) :
    Module.finrank F (shorten C s) =
      Module.finrank F
        (((C : Submodule F (ι → F)) ⊓
          (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule F F))) : Submodule F (ι → F)) := by
  let f := LinearMap.funLeft F F (Subtype.val : s → ι)
  rw [shorten, ← LinearMap.range_domRestrict]
  apply LinearMap.finrank_range_of_inj
  intro x y hxy
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ s
  · simpa [f, LinearMap.funLeft_apply] using congrFun hxy ⟨i, hi⟩
  · exact (Submodule.mem_pi.mp x.2.2 i hi).trans (Submodule.mem_pi.mp y.2.2 i hi).symm

/-- Shortening cannot increase dimension. -/
theorem finrank_shorten_le (C : LinearCode F ι) [FiniteDimensional F C] (s : Set ι) :
    Module.finrank F (shorten C s) ≤ Module.finrank F C := by
  rw [finrank_shorten_eq]
  apply Submodule.finrank_mono
  exact inf_le_left

/-- **Rank–nullity for shortening and puncturing.** Restricting a code to the deleted coordinates
`sᶜ` has kernel the words vanishing off `s`, which is the shortened code; so the dimensions of
`shorten C s` and `puncture C sᶜ` add up to the dimension of `C`. -/
theorem finrank_shorten_add_finrank_puncture_compl (C : LinearCode F ι) [FiniteDimensional F C]
    (s : Set ι) :
    Module.finrank F (shorten C s) + Module.finrank F (puncture C sᶜ) = Module.finrank F C := by
  let f := LinearMap.funLeft F F (Subtype.val : ↥sᶜ → ι)
  have hker : LinearMap.ker f = Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule F F) := by
    ext x
    simp [f, Submodule.mem_pi, funext_iff, LinearMap.funLeft_apply]
  have hrange : LinearMap.range (f.domRestrict C) = puncture C sᶜ := by
    rw [LinearMap.range_domRestrict, puncture_def]
  have hkerdim : Module.finrank F (LinearMap.ker (f.domRestrict C)) =
      Module.finrank F (shorten C s) := by
    rw [finrank_shorten_eq, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
      Submodule.map_comap_subtype, hker]
  have hrn := (f.domRestrict C).finrank_range_add_finrank_ker
  rw [hrange, hkerdim] at hrn
  exact (add_comm _ _).trans hrn

/-- The dimensions of `puncture C s` and `shorten C sᶜ` add up to the dimension of `C`. -/
theorem finrank_puncture_add_finrank_shorten_compl (C : LinearCode F ι) [FiniteDimensional F C]
    (s : Set ι) :
    Module.finrank F (puncture C s) + Module.finrank F (shorten C sᶜ) = Module.finrank F C := by
  have h := finrank_shorten_add_finrank_puncture_compl C sᶜ
  rw [compl_compl] at h
  omega

/-- The dimension lost by shortening is at most the number of deleted coordinates. -/
theorem finrank_le_finrank_shorten_add_ncard_compl [Finite ι]
    (C : LinearCode F ι) (s : Set ι) :
    Module.finrank F C ≤ Module.finrank F (shorten C s) + sᶜ.ncard := by
  classical
  let _ := Fintype.ofFinite ι
  let S : Submodule F (ι → F) := Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule F F)
  have hS : S = Pi.spanSubset F s := by
    ext x
    simp [S, Submodule.mem_pi, Pi.mem_spanSubset_iff]
  have hdimS : Module.finrank F S = s.ncard := by rw [hS, Pi.dim_spanSubset]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq C S
  have hsup : Module.finrank F
      (((C : Submodule F (ι → F)) ⊔ S) : Submodule F (ι → F)) ≤
      Nat.card ι := by
    calc
      Module.finrank F
          (((C : Submodule F (ι → F)) ⊔ S) : Submodule F (ι → F)) ≤
          Module.finrank F (ι → F) :=
        Submodule.finrank_le _
      _ = Nat.card ι := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
  rw [hdimS] at hsum
  rw [finrank_shorten_eq]
  have hcard := Set.ncard_add_ncard_compl s
  have hbound : Module.finrank F C ≤
      Module.finrank F (((C : Submodule F (ι → F)) ⊓ S) : Submodule F (ι → F)) +
        sᶜ.ncard := by omega
  simpa [S] using hbound

/-- The dimension lost by puncturing is at most the number of deleted coordinates. -/
theorem finrank_le_finrank_puncture_add_ncard_compl [Finite ι]
    (C : LinearCode F ι) (s : Set ι) :
    Module.finrank F C ≤ Module.finrank F (puncture C s) + sᶜ.ncard := by
  refine (finrank_le_finrank_shorten_add_ncard_compl C s).trans ?_
  exact Nat.add_le_add_right (Submodule.finrank_mono (shorten_le_puncture C s)) _

/-! ### Deleting one coordinate -/

/-- Shortening at `i` lowers the dimension by exactly one when some codeword is nonzero at `i`. -/
theorem finrank_shortenAt_add_one_of_exists_ne_zero (C : LinearCode F ι) [FiniteDimensional F C]
    {i : ι} (h : ∃ x ∈ C, x i ≠ 0) :
    Module.finrank F (shortenAt C i) + 1 = Module.finrank F C := by
  have hdim := finrank_shorten_add_finrank_puncture_compl C {i}ᶜ
  rwa [compl_compl, puncture_singleton_eq_top_iff.mpr h, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_unique] at hdim

/-- Shortening at `i` preserves the dimension when every codeword vanishes at `i`. -/
theorem finrank_shortenAt_of_forall_eq_zero (C : LinearCode F ι) {i : ι}
    (h : ∀ x ∈ C, x i = 0) :
    Module.finrank F (shortenAt C i) = Module.finrank F C := by
  rw [shortenAt_def, finrank_shorten_eq, inf_eq_left.mpr]
  intro x hx
  refine Submodule.mem_pi.mpr fun j hj ↦ ?_
  obtain rfl : j = i := by simpa using hj
  exact h x hx

/-- Puncturing at `i` lowers the dimension by exactly one when the unit word at `i` is a
codeword. -/
theorem finrank_punctureAt_add_one_of_single_mem [DecidableEq ι] (C : LinearCode F ι)
    [FiniteDimensional F C] {i : ι} (h : Pi.single i 1 ∈ C) :
    Module.finrank F (punctureAt C i) + 1 = Module.finrank F C := by
  have hdim := finrank_puncture_add_finrank_shorten_compl C {i}ᶜ
  rwa [compl_compl, shorten_singleton_eq_top_iff.mpr h, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_unique] at hdim

/-- Puncturing at `i` preserves the dimension when the unit word at `i` is not a codeword. -/
theorem finrank_punctureAt_of_single_notMem [DecidableEq ι] (C : LinearCode F ι) {i : ι}
    (h : Pi.single i 1 ∉ C) :
    Module.finrank F (punctureAt C i) = Module.finrank F C := by
  refine finrank_puncture_eq C _ fun x hx hx0 ↦ ?_
  by_contra hne
  have hxi : x i ≠ 0 := fun hxi ↦ hne <| funext fun j ↦ by
    by_cases hj : j = i
    · exact hj ▸ hxi
    · exact hx0 ⟨j, hj⟩
  refine h ?_
  convert C.smul_mem (x i)⁻¹ hx using 1
  ext j
  by_cases hj : j = i
  · subst hj
    simp [hxi]
  · simp [hj, hx0 ⟨j, hj⟩]

end TauCeti
