/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Reindex

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
naturality under a change of coordinates, the canonical identities for repeated operations, the
comparison between shortening and puncturing, and the exact dimension of a shortened code before
coordinates are discarded.

## Main declarations

* `puncture`: restriction of a code to a retained coordinate set.
* `shorten`: restriction after imposing zero outside the retained coordinate set.
* `punctureAt` and `shortenAt`: the corresponding operations deleting one coordinate.
* `mem_puncture` and `mem_shorten`: membership characterizations.
* `finrank_puncture_le`, `finrank_puncture_eq`, and `finrank_shorten_eq`: dimension control.

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
  AddSubgroup.map_top_of_surjective _ (Subtype.val_injective.surjective_comp_right' 0)

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
theorem LinearCode.toAddSubgroup_puncture (C : LinearCode F ι) (s : Set ι) :
    (puncture C s).toAddSubgroup = AdditiveCode.puncture C.toAddSubgroup s := by
  rw [puncture_def, Submodule.map_toAddSubgroup, AdditiveCode.puncture_def]
  -- Both bundled homomorphisms restrict a word along `Subtype.val`.
  congr 1

/-- Forgetting scalar closure commutes with shortening a linear code. -/
@[simp]
theorem LinearCode.toAddSubgroup_shorten (C : LinearCode F ι) (s : Set ι) :
    (shorten C s).toAddSubgroup = AdditiveCode.shorten C.toAddSubgroup s := by
  ext y
  simp only [Submodule.mem_toAddSubgroup, shorten_def, Submodule.mem_map,
    Submodule.mem_inf, Submodule.mem_pi, Submodule.mem_bot, AdditiveCode.mem_shorten,
    LinearMap.funLeft_apply, funext_iff, Set.mem_compl_iff, and_assoc]

/-- A word belongs to the punctured code exactly when it is the restriction of a codeword. -/
@[simp]
theorem mem_puncture {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ puncture C s ↔ ∃ x ∈ C, ∀ j : s, x j = y j := by
  rw [← Submodule.mem_toAddSubgroup, LinearCode.toAddSubgroup_puncture]
  simp only [AdditiveCode.mem_puncture, Submodule.mem_toAddSubgroup]

/-- A word belongs to the shortened code exactly when its extension by zero is a codeword:
equivalently, it is the restriction of a codeword which vanishes off the retained set. -/
@[simp]
theorem mem_shorten {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ shorten C s ↔
      ∃ x ∈ C, (∀ i ∉ s, x i = 0) ∧ ∀ j : s, x j = y j := by
  rw [← Submodule.mem_toAddSubgroup, LinearCode.toAddSubgroup_shorten]
  simp only [AdditiveCode.mem_shorten, Submodule.mem_toAddSubgroup]

/-- A word on the retained coordinates belongs to the shortened code exactly when its extension
by zero belongs to the original code. -/
theorem mem_shorten_iff_extend_mem {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ shorten C s ↔ Subtype.val.extend y 0 ∈ C := by
  rw [← Submodule.mem_toAddSubgroup, LinearCode.toAddSubgroup_shorten,
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

/-- Puncturing commutes with a change of coordinates. The retained set is pulled back along the
coordinate equivalence. -/
@[simp]
theorem puncture_reindex {κ : Type*} (C : LinearCode F ι) (e : κ ≃ ι) (s : Set ι) :
    puncture (reindex C e) (e ⁻¹' s) =
      reindex (puncture C s) (e.subtypeEquiv fun _ ↦ Iff.rfl) := by
  have hmap :
      (LinearMap.funLeft F F (Subtype.val : ↥(e ⁻¹' s) → κ)).comp
          (LinearEquiv.funCongrLeft F F e).toLinearMap =
        (LinearEquiv.funCongrLeft F F (e.subtypeEquiv fun _ ↦ Iff.rfl)).toLinearMap.comp
          (LinearMap.funLeft F F (Subtype.val : s → ι)) := by
    ext x j
    simp
  rw [puncture_def, reindex_def, reindex_def, puncture_def, ← Submodule.map_comp,
    ← Submodule.map_comp, hmap]

/-- Shortening commutes with a change of coordinates. -/
@[simp]
theorem shorten_reindex {κ : Type*} (C : LinearCode F ι) (e : κ ≃ ι) (s : Set ι) :
    shorten (reindex C e) (e ⁻¹' s) =
      reindex (shorten C s) (e.subtypeEquiv fun _ ↦ Iff.rfl) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hz0, hzy⟩ := mem_shorten.mp hy
    obtain ⟨x, hxC, hxz⟩ := mem_reindex.mp hz
    have hx0 : ∀ i ∉ s, x i = 0 := by
      intro i hi
      have hk : e.symm i ∉ e ⁻¹' s := by simpa using hi
      simpa using (hxz (e.symm i)).trans (hz0 (e.symm i) hk)
    refine mem_reindex.mpr ⟨fun j : s ↦ x j,
      mem_shorten.mpr ⟨x, hxC, hx0, fun _ ↦ rfl⟩, ?_⟩
    intro j
    exact (hxz j).trans (hzy j)
  · intro hy
    obtain ⟨u, hu, huy⟩ := mem_reindex.mp hy
    obtain ⟨x, hxC, hx0, hxu⟩ := mem_shorten.mp hu
    let z : κ → F := fun j ↦ x (e j)
    refine mem_shorten.mpr ⟨z, mem_reindex.mpr ⟨x, hxC, fun _ ↦ rfl⟩, ?_, ?_⟩
    · intro j hj
      exact hx0 (e j) hj
    · intro j
      exact (hxu _).trans (huy j)

/-- Puncturing twice is puncturing once to the flattened set of retained coordinates, up to the
canonical equivalence between a subtype of a subtype and the corresponding subtype. -/
@[simp]
theorem puncture_puncture (C : LinearCode F ι) (s : Set ι) (t : Set s) :
    reindex (puncture (puncture C s) t)
        (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm =
      puncture C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} := by
  have hmap :
      (LinearEquiv.funCongrLeft F F
            (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm).toLinearMap.comp
          ((LinearMap.funLeft F F (Subtype.val : t → s)).comp
            (LinearMap.funLeft F F (Subtype.val : s → ι))) =
        LinearMap.funLeft F F (Subtype.val : {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} → ι) := by
    ext x j
    exact congrArg x
      (Equiv.subtypeSubtypeEquivSubtypeExists_symm_apply_coe_coe (· ∈ s) (· ∈ t) j)
  rw [reindex_def, puncture_def, puncture_def, puncture_def, ← Submodule.map_comp,
    ← Submodule.map_comp, LinearMap.comp_assoc, hmap]

/-- Shortening twice is shortening once to the flattened set of retained coordinates, up to the
canonical subtype equivalence. -/
@[simp]
theorem shorten_shorten (C : LinearCode F ι) (s : Set ι) (t : Set s) :
    reindex (shorten (shorten C s) t)
        (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm =
      shorten C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} := by
  ext y
  constructor
  · intro hy
    obtain ⟨v, hv, hvy⟩ := mem_reindex.mp hy
    obtain ⟨z, hz, hz0, hzv⟩ := mem_shorten.mp hv
    obtain ⟨x, hxC, hx0, hxz⟩ := mem_shorten.mp hz
    refine mem_shorten.mpr ⟨x, hxC, ?_, fun j ↦ ?_⟩
    · intro i hi
      by_cases his : i ∈ s
      · have hit : (⟨i, his⟩ : s) ∉ t := by
          intro hmem
          exact hi ⟨his, hmem⟩
        exact (hxz ⟨i, his⟩).trans (hz0 ⟨i, his⟩ hit)
      · exact hx0 i his
    · let jt : t := ⟨⟨j, j.2.choose⟩, j.2.choose_spec⟩
      have hj : (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm j = jt :=
        Subtype.ext <| Subtype.ext <|
          Equiv.subtypeSubtypeEquivSubtypeExists_symm_apply_coe_coe _ _ j
      exact (hxz jt).trans ((hzv jt).trans (hj ▸ hvy j))
  · intro hy
    obtain ⟨x, hxC, hx0, hxy⟩ := mem_shorten.mp hy
    let z : s → F := fun j ↦ x j
    let v : t → F := fun j ↦ z j
    have hzs : z ∈ shorten C s := by
      refine mem_shorten.mpr ⟨x, hxC, ?_, fun _ ↦ rfl⟩
      intro i hi
      exact hx0 i (fun ⟨his, _⟩ ↦ hi his)
    have hvt : v ∈ shorten (shorten C s) t := by
      refine mem_shorten.mpr ⟨z, hzs, ?_, fun _ ↦ rfl⟩
      intro j hj
      exact hx0 j (fun ⟨_, hjt⟩ ↦ hj hjt)
    refine mem_reindex.mpr ⟨v, hvt, ?_⟩
    intro j
    exact hxy j

/-- Every shortened word is a punctured word. -/
theorem shorten_le_puncture (C : LinearCode F ι) (s : Set ι) : shorten C s ≤ puncture C s := by
  apply (Submodule.toAddSubgroup_le _ _).mp
  simpa only [LinearCode.toAddSubgroup_shorten, LinearCode.toAddSubgroup_puncture] using
    AdditiveCode.shorten_le_puncture C.toAddSubgroup s

/-- Puncturing is monotone in the code. -/
theorem puncture_mono {C D : LinearCode F ι} (h : C ≤ D) (s : Set ι) :
    puncture C s ≤ puncture D s := by
  apply (Submodule.toAddSubgroup_le _ _).mp
  simpa only [LinearCode.toAddSubgroup_puncture] using
    AdditiveCode.puncture_mono ((Submodule.toAddSubgroup_le _ _).mpr h) s

/-- Shortening is monotone in the code. -/
theorem shorten_mono {C D : LinearCode F ι} (h : C ≤ D) (s : Set ι) :
    shorten C s ≤ shorten D s := by
  apply (Submodule.toAddSubgroup_le _ _).mp
  simpa only [LinearCode.toAddSubgroup_shorten] using
    AdditiveCode.shorten_mono ((Submodule.toAddSubgroup_le _ _).mpr h) s

/-- Puncturing sends the zero code to the zero code. -/
@[simp]
theorem puncture_bot (s : Set ι) : puncture (⊥ : LinearCode F ι) s = ⊥ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.toAddSubgroup_puncture, Submodule.bot_toAddSubgroup,
    AdditiveCode.puncture_bot]

/-- Shortening sends the zero code to the zero code. -/
@[simp]
theorem shorten_bot (s : Set ι) : shorten (⊥ : LinearCode F ι) s = ⊥ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.toAddSubgroup_shorten, Submodule.bot_toAddSubgroup,
    AdditiveCode.shorten_bot]

/-- Puncturing the whole word space gives the whole word space on the retained coordinates. -/
@[simp]
theorem puncture_top (s : Set ι) : puncture (⊤ : LinearCode F ι) s = ⊤ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.toAddSubgroup_puncture, Submodule.top_toAddSubgroup,
    AdditiveCode.puncture_top]

/-- Shortening the whole word space gives the whole word space on the retained coordinates. -/
@[simp]
theorem shorten_top (s : Set ι) : shorten (⊤ : LinearCode F ι) s = ⊤ := by
  apply Submodule.toAddSubgroup_injective
  simp only [LinearCode.toAddSubgroup_shorten, Submodule.top_toAddSubgroup,
    AdditiveCode.shorten_top]

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
  let P : Submodule F (ι → F) :=
    (C : Submodule F (ι → F)) ⊓ (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule F F))
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

end TauCeti
