/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.Pi

/-!
# Puncturing and shortening linear codes

A linear code on coordinates `ι` is a submodule of the word space `ι → R`. Given a set `s` of
coordinates to retain, puncturing restricts every codeword to `s`. Shortening first restricts to
the codewords which vanish outside `s`, and then forgets those zero coordinates.

The definitions in this file work over a semiring and do not require the alphabet or the
coordinate type to be finite. A division ring and finiteness are needed only for the dimension
bounds. The API records membership, order preservation, the zero and whole-space cases, the
comparison between shortening and puncturing, and the exact dimension of a shortened code before
coordinates are discarded.

## Main declarations

* `LinearCode`: the unbundled linear-code carrier `Submodule R (ι → R)`.
* `puncture`: restriction of a code to a retained coordinate set.
* `shorten`: restriction after imposing zero outside the retained coordinate set.
* `mem_puncture` and `mem_shorten`: membership characterizations.
* `finrank_puncture_le` and `finrank_shorten_eq`: dimension control.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.5 and 1.6.
-/

public section

namespace TauCeti

universe u v w

/-- A linear code over `R` on coordinates `ι`, represented by its submodule of words. -/
abbrev LinearCode (R : Type u) [Semiring R] (ι : Type v) := Submodule R (ι → R)

section Operations

variable {R : Type u} [Semiring R] {ι : Type v}

/-- Reindex a linear code along a coordinate equivalence. The equivalence points from the new
coordinate type to the old one, so the transported word has value `x (e j)` at `j`. -/
noncomputable def reindex {κ : Type w} (C : LinearCode R ι) (e : κ ≃ ι) : LinearCode R κ :=
  C.map (LinearEquiv.funCongrLeft R R e).toLinearMap

/-- Reindexing is the image under coordinate transport. -/
theorem reindex_def {κ : Type w} (C : LinearCode R ι) (e : κ ≃ ι) :
    reindex C e = C.map (LinearEquiv.funCongrLeft R R e).toLinearMap := (rfl)

/-- Membership in a reindexed code, with the direction of the coordinate equivalence explicit. -/
@[simp]
theorem mem_reindex {κ : Type w} {C : LinearCode R ι} {e : κ ≃ ι} {y : κ → R} :
    y ∈ reindex C e ↔ ∃ x ∈ C, ∀ j, x (e j) = y j := by
  rw [reindex, Submodule.mem_map]
  constructor
  · rintro ⟨x, hxC, rfl⟩
    exact ⟨x, hxC, fun _ ↦ rfl⟩
  · rintro ⟨x, hxC, hxy⟩
    refine ⟨x, hxC, ?_⟩
    ext j
    exact hxy j

@[simp]
theorem reindex_refl (C : LinearCode R ι) : reindex C (Equiv.refl ι) = C := by
  ext x
  simp only [mem_reindex, Equiv.refl_apply]
  exact ⟨fun ⟨y, hy, hxy⟩ ↦ (funext hxy).symm ▸ hy, fun hx ↦ ⟨x, hx, fun _ ↦ rfl⟩⟩

/-- Successive changes of coordinates compose in their contravariant order. -/
theorem reindex_trans {κ : Type w} {κ' : Type*} (C : LinearCode R ι)
    (e : κ ≃ ι) (f : κ' ≃ κ) :
    reindex (reindex C e) f = reindex C (f.trans e) := by
  ext x
  simp only [mem_reindex, Equiv.trans_apply]
  constructor
  · rintro ⟨y, ⟨z, hzC, hzy⟩, hyx⟩
    exact ⟨z, hzC, fun j ↦ (hzy (f j)).trans (hyx j)⟩
  · rintro ⟨z, hzC, hzx⟩
    exact ⟨fun j ↦ z (e j), ⟨z, hzC, fun _ ↦ rfl⟩, hzx⟩

/-- Reindexing is monotone in the code. -/
theorem reindex_mono {κ : Type w} {C D : LinearCode R ι} (h : C ≤ D) (e : κ ≃ ι) :
    reindex C e ≤ reindex D e :=
  Submodule.map_mono h

@[simp]
theorem reindex_bot {κ : Type w} (e : κ ≃ ι) : reindex (⊥ : LinearCode R ι) e = ⊥ := by
  simp [reindex]

@[simp]
theorem reindex_top {κ : Type w} (e : κ ≃ ι) : reindex (⊤ : LinearCode R ι) e = ⊤ := by
  simp [reindex]

/-- Puncturing a code at `s` retains precisely the coordinates in `s`. -/
noncomputable def puncture (C : LinearCode R ι) (s : Set ι) : LinearCode R s :=
  C.map (LinearMap.funLeft R R (Subtype.val : s → ι))

/-- Puncturing is the image under restriction to the retained coordinates. -/
theorem puncture_def (C : LinearCode R ι) (s : Set ι) :
    puncture C s = C.map (LinearMap.funLeft R R (Subtype.val : s → ι)) := (rfl)

/-- Shortening a code at `s` first imposes zero outside `s`, then retains the coordinates in
`s`. -/
noncomputable def shorten (C : LinearCode R ι) (s : Set ι) : LinearCode R s :=
  (C ⊓ Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule R R)).map
    (LinearMap.funLeft R R (Subtype.val : s → ι))

/-- Shortening is the image under restriction of the words supported on the retained set. -/
theorem shorten_def (C : LinearCode R ι) (s : Set ι) :
    shorten C s = (C ⊓ Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule R R)).map
      (LinearMap.funLeft R R (Subtype.val : s → ι)) := (rfl)

/-- A word belongs to the punctured code exactly when it is the restriction of a codeword. -/
@[simp]
theorem mem_puncture {C : LinearCode R ι} {s : Set ι} {y : s → R} :
    y ∈ puncture C s ↔ ∃ x ∈ C, ∀ j : s, x j = y j := by
  simp [puncture, Submodule.mem_map, LinearMap.funLeft_apply, funext_iff]

/-- A word belongs to the shortened code exactly when its extension by zero is a codeword:
equivalently, it is the restriction of a codeword which vanishes off the retained set. -/
@[simp]
theorem mem_shorten {C : LinearCode R ι} {s : Set ι} {y : s → R} :
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

/-- Membership in a puncture retaining one coordinate is determined by that coordinate. -/
theorem mem_puncture_singleton {C : LinearCode R ι} {i : ι} {y : ({i} : Set ι) → R} :
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
theorem mem_shorten_singleton {C : LinearCode R ι} {i : ι} {y : ({i} : Set ι) → R} :
    y ∈ shorten C {i} ↔
      ∃ x ∈ C, (∀ j, j ≠ i → x j = 0) ∧ x i = y ⟨i, Set.mem_singleton i⟩ := by
  rw [mem_shorten]
  constructor
  · rintro ⟨x, hxC, hx0, hxy⟩
    exact ⟨x, hxC, fun j hj ↦ hx0 j (by simpa using hj), hxy ⟨i, Set.mem_singleton i⟩⟩
  · rintro ⟨x, hxC, hx0, hxy⟩
    refine ⟨x, hxC, fun j hj ↦ hx0 j (by simpa using hj), fun j ↦ ?_⟩
    simpa only [Subsingleton.elim j ⟨i, Set.mem_singleton i⟩] using hxy

/-- Puncturing commutes with a change of coordinates. The retained set is pulled back along the
coordinate equivalence. -/
theorem puncture_reindex {κ : Type w} (C : LinearCode R ι) (e : κ ≃ ι) (s : Set ι) :
    puncture (reindex C e) (e ⁻¹' s) =
      reindex (puncture C s) (e.subtypeEquiv fun _ ↦ Iff.rfl) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := mem_puncture.mp hy
    obtain ⟨x, hxC, hxz⟩ := mem_reindex.mp hz
    refine mem_reindex.mpr ⟨fun j : s ↦ x j, mem_puncture.mpr ⟨x, hxC, fun _ ↦ rfl⟩, ?_⟩
    intro j
    exact (hxz j).trans (hzy j)
  · intro hy
    obtain ⟨u, hu, huy⟩ := mem_reindex.mp hy
    obtain ⟨x, hxC, hxu⟩ := mem_puncture.mp hu
    let z : κ → R := fun j ↦ x (e j)
    refine mem_puncture.mpr ⟨z, mem_reindex.mpr ⟨x, hxC, fun _ ↦ rfl⟩, ?_⟩
    intro j
    exact (hxu _).trans (huy j)

/-- Shortening commutes with a change of coordinates. -/
theorem shorten_reindex {κ : Type w} (C : LinearCode R ι) (e : κ ≃ ι) (s : Set ι) :
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
    let z : κ → R := fun j ↦ x (e j)
    refine mem_shorten.mpr ⟨z, mem_reindex.mpr ⟨x, hxC, fun _ ↦ rfl⟩, ?_, ?_⟩
    · intro j hj
      exact hx0 (e j) hj
    · intro j
      exact (hxu _).trans (huy j)

/-- Puncturing twice is puncturing once to the flattened set of retained coordinates, up to the
canonical equivalence between a subtype of a subtype and the corresponding subtype. -/
theorem puncture_puncture (C : LinearCode R ι) (s : Set ι) (t : Set s) :
    reindex (puncture (puncture C s) t)
        (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm =
      puncture C {i | ∃ hi : i ∈ s, (⟨i, hi⟩ : s) ∈ t} := by
  ext y
  constructor
  · intro hy
    obtain ⟨v, hv, hvy⟩ := mem_reindex.mp hy
    obtain ⟨z, hz, hzv⟩ := mem_puncture.mp hv
    obtain ⟨x, hxC, hxz⟩ := mem_puncture.mp hz
    refine mem_puncture.mpr ⟨x, hxC, fun j ↦ ?_⟩
    let jt : t := ⟨⟨j, j.2.choose⟩, j.2.choose_spec⟩
    have hj : (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm j = jt := by
      apply Subtype.ext
      exact Subtype.ext rfl
    exact (hxz jt).trans ((hzv jt).trans (hj ▸ hvy j))
  · intro hy
    obtain ⟨x, hxC, hxy⟩ := mem_puncture.mp hy
    let z : s → R := fun j ↦ x j
    let v : t → R := fun j ↦ z j
    refine mem_reindex.mpr ⟨v,
      mem_puncture.mpr ⟨z, mem_puncture.mpr ⟨x, hxC, fun _ ↦ rfl⟩, fun _ ↦ rfl⟩, ?_⟩
    intro j
    exact hxy j

/-- Shortening twice is shortening once to the flattened set of retained coordinates, up to the
canonical subtype equivalence. -/
theorem shorten_shorten (C : LinearCode R ι) (s : Set ι) (t : Set s) :
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
      have hj : (Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ s) (· ∈ t)).symm j = jt := by
        apply Subtype.ext
        exact Subtype.ext rfl
      exact (hxz jt).trans ((hzv jt).trans (hj ▸ hvy j))
  · intro hy
    obtain ⟨x, hxC, hx0, hxy⟩ := mem_shorten.mp hy
    let z : s → R := fun j ↦ x j
    let v : t → R := fun j ↦ z j
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
theorem shorten_le_puncture (C : LinearCode R ι) (s : Set ι) : shorten C s ≤ puncture C s := by
  intro y hy
  obtain ⟨x, hxC, _, hxy⟩ := mem_shorten.mp hy
  exact mem_puncture.mpr ⟨x, hxC, hxy⟩

/-- Puncturing is monotone in the code. -/
theorem puncture_mono {C D : LinearCode R ι} (h : C ≤ D) (s : Set ι) :
    puncture C s ≤ puncture D s :=
  Submodule.map_mono h

/-- Shortening is monotone in the code. -/
theorem shorten_mono {C D : LinearCode R ι} (h : C ≤ D) (s : Set ι) :
    shorten C s ≤ shorten D s :=
  Submodule.map_mono (inf_le_inf h le_rfl)

@[simp]
theorem puncture_bot (s : Set ι) : puncture (⊥ : LinearCode R ι) s = ⊥ := by
  simp [puncture]

@[simp]
theorem shorten_bot (s : Set ι) : shorten (⊥ : LinearCode R ι) s = ⊥ := by
  simp [shorten]

@[simp]
theorem puncture_top (s : Set ι) : puncture (⊤ : LinearCode R ι) s = ⊤ := by
  rw [puncture, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr <|
    LinearMap.funLeft_surjective_of_injective R R _ Subtype.val_injective

@[simp]
theorem shorten_top (s : Set ι) : shorten (⊤ : LinearCode R ι) s = ⊤ := by
  ext y
  simp only [Submodule.mem_top, iff_true]
  classical
  let x : ι → R := fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else 0
  refine mem_shorten.mpr ⟨x, Submodule.mem_top, ?_, ?_⟩
  · intro i hi
    simp [x, hi]
  · intro j
    simp [x, j.2]

@[simp]
theorem puncture_sup (C D : LinearCode R ι) (s : Set ι) :
    puncture (C ⊔ D) s = puncture C s ⊔ puncture D s := by
  simp [puncture, Submodule.map_sup]

/-- Shortening commutes with intersections. -/
@[simp]
theorem shorten_inf (C D : LinearCode R ι) (s : Set ι) :
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

end Operations

section Dimension

variable {R : Type u} [DivisionRing R] {ι : Type v}

/-- Puncturing cannot increase dimension. -/
theorem finrank_puncture_le (C : LinearCode R ι) [FiniteDimensional R C] (s : Set ι) :
    Module.finrank R (puncture C s) ≤ Module.finrank R C := by
  rw [puncture]
  exact Submodule.finrank_map_le _ _

/-- Shortening preserves the dimension of the subcode of words supported on the retained
coordinates. -/
theorem finrank_shorten_eq (C : LinearCode R ι) (s : Set ι) :
    Module.finrank R (shorten C s) =
      Module.finrank R
        (((C : Submodule R (ι → R)) ⊓
          (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule R R))) : Submodule R (ι → R)) := by
  let P : Submodule R (ι → R) :=
    (C : Submodule R (ι → R)) ⊓ (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule R R))
  let f := LinearMap.funLeft R R (Subtype.val : s → ι)
  rw [shorten, ← LinearMap.range_domRestrict]
  apply LinearMap.finrank_range_of_inj
  intro x y hxy
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ s
  · simpa [f, LinearMap.funLeft_apply] using congrFun hxy ⟨i, hi⟩
  · exact (Submodule.mem_pi.mp x.2.2 i hi).trans (Submodule.mem_pi.mp y.2.2 i hi).symm

/-- Shortening cannot increase dimension. -/
theorem finrank_shorten_le (C : LinearCode R ι) [FiniteDimensional R C] (s : Set ι) :
    Module.finrank R (shorten C s) ≤ Module.finrank R C := by
  rw [finrank_shorten_eq]
  apply Submodule.finrank_mono
  exact inf_le_left

/-- The dimension lost by shortening is at most the number of deleted coordinates. -/
theorem finrank_le_finrank_shorten_add_ncard_compl [Finite ι]
    (C : LinearCode R ι) (s : Set ι) :
    Module.finrank R C ≤ Module.finrank R (shorten C s) + sᶜ.ncard := by
  classical
  let _ := Fintype.ofFinite ι
  let S : Submodule R (ι → R) := Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule R R)
  have hS : S = Pi.spanSubset R s := by
    ext x
    simp [S, Submodule.mem_pi, Pi.mem_spanSubset_iff]
  have hdimS : Module.finrank R S = s.ncard := by rw [hS, Pi.dim_spanSubset]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq C S
  have hsup : Module.finrank R
      (((C : Submodule R (ι → R)) ⊔ S) : Submodule R (ι → R)) ≤
      Nat.card ι := by
    calc
      Module.finrank R
          (((C : Submodule R (ι → R)) ⊔ S) : Submodule R (ι → R)) ≤
          Module.finrank R (ι → R) :=
        Submodule.finrank_le _
      _ = Nat.card ι := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
  rw [hdimS] at hsum
  rw [finrank_shorten_eq]
  have hcard := Set.ncard_add_ncard_compl s
  have hbound : Module.finrank R C ≤
      Module.finrank R (((C : Submodule R (ι → R)) ⊓ S) : Submodule R (ι → R)) +
        sᶜ.ncard := by omega
  simpa [S] using hbound

/-- The dimension lost by puncturing is at most the number of deleted coordinates. -/
theorem finrank_le_finrank_puncture_add_ncard_compl [Finite ι]
    (C : LinearCode R ι) (s : Set ι) :
    Module.finrank R C ≤ Module.finrank R (puncture C s) + sᶜ.ncard := by
  refine (finrank_le_finrank_shorten_add_ncard_compl C s).trans ?_
  exact Nat.add_le_add_right (Submodule.finrank_mono (shorten_le_puncture C s)) _

/-- A coordinate equivalence preserves the dimension of a code. -/
@[simp]
theorem finrank_reindex {κ : Type w} (C : LinearCode R ι) (e : κ ≃ ι) :
    Module.finrank R (reindex C e) = Module.finrank R C := by
  rw [reindex, LinearEquiv.finrank_map_eq]

end Dimension

end TauCeti
