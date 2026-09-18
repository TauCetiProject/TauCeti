/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Reindex

/-!
# Puncturing and shortening linear codes

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
* `finrank_puncture_le` and `finrank_shorten_eq`: dimension control.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.5 and 1.6.
-/

public section

namespace TauCeti

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

/-- A word belongs to the punctured code exactly when it is the restriction of a codeword. -/
@[simp]
theorem mem_puncture {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ puncture C s ↔ ∃ x ∈ C, ∀ j : s, x j = y j := by
  simp [puncture, Submodule.mem_map, LinearMap.funLeft_apply, funext_iff]

/-- A word belongs to the shortened code exactly when its extension by zero is a codeword:
equivalently, it is the restriction of a codeword which vanishes off the retained set. -/
@[simp]
theorem mem_shorten {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ shorten C s ↔
      ∃ x ∈ C, (∀ i ∉ s, x i = 0) ∧ ∀ j : s, x j = y j := by
  rw [shorten, Submodule.mem_map]
  constructor
  · rintro ⟨x, ⟨hxC, hxs⟩, hxy⟩
    refine ⟨x, hxC, Submodule.mem_pi.mp hxs, fun j ↦ ?_⟩
    simpa [LinearMap.funLeft_apply] using congrFun hxy j
  · rintro ⟨x, hxC, hxs, hxy⟩
    refine ⟨x, ⟨hxC, Submodule.mem_pi.mpr hxs⟩, ?_⟩
    ext j
    simpa [LinearMap.funLeft_apply] using hxy j

/-- A word on the retained coordinates belongs to the shortened code exactly when its extension
by zero belongs to the original code. -/
theorem mem_shorten_iff_extend_mem {C : LinearCode F ι} {s : Set ι} {y : s → F} :
    y ∈ shorten C s ↔ Subtype.val.extend y 0 ∈ C := by
  rw [mem_shorten]
  constructor
  · rintro ⟨x, hxC, hx0, hxy⟩
    convert hxC using 1
    funext i
    by_cases hi : i ∈ s
    · exact (Subtype.val_injective.extend_apply y 0 ⟨i, hi⟩).trans (hxy ⟨i, hi⟩).symm
    · rw [hx0 i hi, Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hi (hj ▸ j.2), Pi.zero_apply]
  · intro h
    refine ⟨_, h, fun i hi ↦ ?_, fun j ↦ Subtype.val_injective.extend_apply y 0 j⟩
    rw [Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hi (hj ▸ j.2), Pi.zero_apply]

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
  intro y hy
  obtain ⟨x, hxC, _, hxy⟩ := mem_shorten.mp hy
  exact mem_puncture.mpr ⟨x, hxC, hxy⟩

/-- Puncturing is monotone in the code. -/
theorem puncture_mono {C D : LinearCode F ι} (h : C ≤ D) (s : Set ι) :
    puncture C s ≤ puncture D s :=
  Submodule.map_mono h

/-- Shortening is monotone in the code. -/
theorem shorten_mono {C D : LinearCode F ι} (h : C ≤ D) (s : Set ι) :
    shorten C s ≤ shorten D s :=
  Submodule.map_mono (inf_le_inf h le_rfl)

/-- Puncturing sends the zero code to the zero code. -/
@[simp]
theorem puncture_bot (s : Set ι) : puncture (⊥ : LinearCode F ι) s = ⊥ := by
  simp [puncture]

/-- Shortening sends the zero code to the zero code. -/
@[simp]
theorem shorten_bot (s : Set ι) : shorten (⊥ : LinearCode F ι) s = ⊥ := by
  simp [shorten]

/-- Puncturing the whole word space gives the whole word space on the retained coordinates. -/
@[simp]
theorem puncture_top (s : Set ι) : puncture (⊤ : LinearCode F ι) s = ⊤ := by
  rw [puncture, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr <|
    LinearMap.funLeft_surjective_of_injective F F _ Subtype.val_injective

/-- Shortening the whole word space gives the whole word space on the retained coordinates. -/
@[simp]
theorem shorten_top (s : Set ι) : shorten (⊤ : LinearCode F ι) s = ⊤ := by
  ext y
  simp only [Submodule.mem_top, iff_true]
  classical
  let x : ι → F := fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else 0
  refine mem_shorten.mpr ⟨x, Submodule.mem_top, ?_, ?_⟩
  · intro i hi
    simp [x, hi]
  · intro j
    simp [x, j.2]

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
