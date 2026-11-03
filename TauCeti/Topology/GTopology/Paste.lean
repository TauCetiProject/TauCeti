/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.GTopology.ContinuousMap

/-!
# Pasting G-topologies

Let `X` be covered by subsets `P i`, each carrying a G-topology `G i` that satisfies (G0)–(G2).
Following [BGR, §9.1.3], the *pasted* G-topology `GTopology.paste` on `X` has as admissible opens
the subsets `V` of `X` whose trace `V ∩ P i` is admissible in every piece
(`GTopology.PastedOpens`), and a covering of such a `V` is admissible when its trace on every piece
is an admissible cover there. It satisfies (G0)–(G2) (`GTopology.saturated_paste`), and each
inclusion `P i → X` is a continuous map of G-topologies (`GTopology.pasteInclusion`).

The pieces are *compatible* (`GTopology.PasteCompatible`) when every overlap `P i ∩ P j` is
admissible in `P i` and the G-topologies induced on it by `G i` and `G j` coincide. Then each
`P i` is an admissible open of the pasted G-topology (`GTopology.PasteCompatible.piece`), the
pieces form an admissible cover of `X` (`GTopology.PasteCompatible.paste_covers_top_range_piece`),
and the pasted G-topology induces `G i` on `P i`. A subset of `P i` is admissible exactly when it
is admissible in `G i` (`GTopology.PasteCompatible.mem_range_pastedOpensEmbedding_iff_of_subset`),
and likewise for covers (`GTopology.PasteCompatible.paste_covers_iff_of_le`). Conversely, any
G-topology on `X` satisfying (G0)–(G2) with these three properties has the same admissible opens
and covers as the pasted one (`GTopology.exists_orderIso_paste`).

This is how the G-topology of a rigid space is obtained from those of the affinoid spaces in an
admissible cover.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §9.1.3.
-/

public section

namespace TauCeti

open Set

universe u v w

namespace GTopology

variable {X : Type u} {I : Type w} {P : I → Set X} {B : I → Type v}
  [∀ i, SemilatticeInf (B i)] [∀ i, OrderTop (B i)] {ι : ∀ i, B i ↪o Set (P i)}

/-- The admissible opens of the G-topology obtained by pasting the G-topologies `G i` on the
pieces `P i`: the subsets of `X` whose trace on every piece is admissible. The G-topologies enter
only through their intersection axiom, which makes this family closed under intersections. -/
structure PastedOpens (G : ∀ i, GTopology (ι i)) where
  /-- The underlying subset of `X`. -/
  carrier : Set X
  /-- The trace on every piece is admissible. -/
  preimage_mem_range' : ∀ i, ((↑) : P i → X) ⁻¹' carrier ∈ range (ι i)

namespace PastedOpens

variable {G : ∀ i, GTopology (ι i)}

instance : SetLike (PastedOpens G) X where
  coe := carrier
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ ↦ by congr

instance : PartialOrder (PastedOpens G) := .ofSetLike (PastedOpens G)

@[simp]
theorem coe_mk (V : Set X) (hV : ∀ i, ((↑) : P i → X) ⁻¹' V ∈ range (ι i)) :
    ((⟨V, hV⟩ : PastedOpens G) : Set X) = V :=
  (rfl)

@[simp]
theorem mem_mk {V : Set X} {hV : ∀ i, ((↑) : P i → X) ⁻¹' V ∈ range (ι i)} {x : X} :
    x ∈ (⟨V, hV⟩ : PastedOpens G) ↔ x ∈ V :=
  Iff.rfl

@[ext]
theorem ext {V W : PastedOpens G} (h : ∀ x, x ∈ V ↔ x ∈ W) : V = W :=
  SetLike.ext h

/-- The trace of a pasted admissible open on each piece is admissible. -/
theorem preimage_mem_range (V : PastedOpens G) (i : I) :
    ((↑) : P i → X) ⁻¹' V ∈ range (ι i) :=
  V.preimage_mem_range' i

instance : Min (PastedOpens G) where
  min V W := ⟨V ∩ W, fun i ↦ by
    obtain ⟨V', hV'⟩ := V.preimage_mem_range i
    obtain ⟨W', hW'⟩ := W.preimage_mem_range i
    exact ⟨V' ⊓ W', by rw [(G i).map_inf, hV', hW', preimage_inter]⟩⟩

instance : Top (PastedOpens G) where
  top := ⟨univ, fun i ↦ ⟨⊤, by rw [(G i).map_top, preimage_univ]⟩⟩

@[simp, norm_cast]
theorem coe_inf (V W : PastedOpens G) :
    ((V ⊓ W : PastedOpens G) : Set X) = (V : Set X) ∩ (W : Set X) :=
  (rfl)

@[simp, norm_cast]
theorem coe_top : ((⊤ : PastedOpens G) : Set X) = univ :=
  (rfl)

instance : SemilatticeInf (PastedOpens G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

instance : OrderTop (PastedOpens G) :=
  OrderTop.lift ((↑) : PastedOpens G → Set X) (fun _ _ ↦ SetLike.coe_subset_coe.mp) coe_top

/-- The trace `P i ∩ V` of a pasted admissible open `V`, as an admissible open of the piece
`P i`. -/
noncomputable def toPiece (i : I) (V : PastedOpens G) : B i :=
  (V.preimage_mem_range i).choose

@[simp]
theorem coe_toPiece (i : I) (V : PastedOpens G) :
    ι i (toPiece i V) = ((↑) : P i → X) ⁻¹' V :=
  (V.preimage_mem_range i).choose_spec

theorem image_coe_toPiece (i : I) (V : PastedOpens G) :
    ((↑) : P i → X) '' ι i (toPiece i V) = P i ∩ V := by
  rw [coe_toPiece, Subtype.image_preimage_coe]

theorem toPiece_eq_iff {i : I} {V : PastedOpens G} {W : B i} :
    toPiece i V = W ↔ ι i W = ((↑) : P i → X) ⁻¹' V := by
  rw [← (ι i).injective.eq_iff, coe_toPiece, eq_comm]

@[simp]
theorem toPiece_inf (i : I) (V W : PastedOpens G) :
    toPiece i (V ⊓ W) = toPiece i V ⊓ toPiece i W := by
  rw [toPiece_eq_iff, (G i).map_inf, coe_toPiece, coe_toPiece, coe_inf, preimage_inter]

@[simp]
theorem toPiece_top (i : I) : toPiece i (⊤ : PastedOpens G) = ⊤ := by
  rw [toPiece_eq_iff, (G i).map_top, coe_top, preimage_univ]

theorem toPiece_le_toPiece_iff {i : I} {V W : PastedOpens G} :
    toPiece i V ≤ toPiece i W ↔ P i ∩ V ⊆ P i ∩ W := by
  rw [← (ι i).le_iff_le, coe_toPiece, coe_toPiece, Subtype.preimage_val_subset_preimage_val_iff]

theorem toPiece_mono (i : I) : Monotone (toPiece (G := G) i) := fun _ _ h ↦
  toPiece_le_toPiece_iff.mpr (inter_subset_inter_right _ (SetLike.coe_subset_coe.mpr h))

/-- On pieces covering `X`, pasted admissible opens are compared piecewise. -/
theorem le_of_forall_toPiece_le (hP : ⋃ i, P i = univ) {V W : PastedOpens G}
    (h : ∀ i, toPiece i V ≤ toPiece i W) : V ≤ W := by
  refine SetLike.coe_subset_coe.mp fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hP ▸ mem_univ x)
  exact (toPiece_le_toPiece_iff.mp (h i) ⟨hi, hx⟩).2

end PastedOpens

open PastedOpens

variable (G : ∀ i, GTopology (ι i))

/-- The underlying subsets of the pasted admissible opens. -/
def pastedOpensEmbedding : PastedOpens G ↪o Set X :=
  .ofMapLEIff (↑) fun _ _ ↦ SetLike.coe_subset_coe

@[simp]
theorem pastedOpensEmbedding_apply (V : PastedOpens G) : pastedOpensEmbedding G V = V :=
  (rfl)

/-- A subset of `X` is a pasted admissible open exactly when its trace on every piece is
admissible. -/
theorem mem_range_pastedOpensEmbedding_iff {V : Set X} :
    V ∈ range (pastedOpensEmbedding G) ↔ ∀ i, ((↑) : P i → X) ⁻¹' V ∈ range (ι i) :=
  ⟨fun ⟨W, hW⟩ ↦ hW ▸ W.preimage_mem_range, fun h ↦ ⟨⟨V, h⟩, rfl⟩⟩

/-- The G-topology obtained by pasting G-topologies satisfying (G0)–(G2) on pieces `P i` covering
`X` [BGR, §9.1.3]. Its admissible opens are the subsets of `X` whose trace on every piece is
admissible, and a covering family is admissible when its trace on every piece is an admissible
cover. -/
def paste (hP : ⋃ i, P i = univ) (hG : ∀ i, (G i).Saturated) :
    GTopology (pastedOpensEmbedding G) where
  map_top := rfl
  map_inf _ _ := rfl
  Covers U S := ∀ i, (G i).Covers (toPiece i U) (toPiece i '' S)
  subset h V hV := le_of_forall_toPiece_le hP fun i ↦ (G i).subset (h i) _ ⟨V, hV, rfl⟩
  union_eq {U S} h := by
    refine Subset.antisymm (sUnion_subset ?_) fun x hx ↦ ?_
    · rintro _ ⟨V, hV, rfl⟩
      exact SetLike.coe_subset_coe.mpr <|
        le_of_forall_toPiece_le hP fun i ↦ (G i).subset (h i) _ ⟨V, hV, rfl⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hP ▸ mem_univ x)
      have hx' : (⟨x, hi⟩ : P i) ∈ ι i (toPiece i U) := by simpa using hx
      rw [← (G i).union_eq (h i)] at hx'
      obtain ⟨_, ⟨_, ⟨V, hV, rfl⟩, rfl⟩, hxV⟩ := hx'
      exact ⟨V, ⟨V, hV, rfl⟩, by simpa using hxV⟩
  identity U i := by simpa only [image_singleton] using (G i).identity _
  restriction h V hVU i := by
    simpa only [image_image, toPiece_inf] using (G i).restriction (h i) _ (toPiece_mono i hVU)
  transitive {U S T} hS hT i := by
    -- Cover each trace of a member of `S` by the traces of the cover of one chosen member.
    choose! c hcS hc using fun W (hW : W ∈ toPiece i '' S) ↦ hW
    have h := (G i).transitive (T := fun W ↦ toPiece i '' T (c W)) (hS i) fun W hW ↦ by
      have h' := hT (c W) (hcS W hW) i
      rwa [hc W hW] at h'
    refine (hG i).covers_of_superset h ?_ ?_
    · simp only [iUnion_subset_iff]
      intro W hW
      exact image_mono (subset_biUnion_of_mem (u := T) (hcS W hW))
    · simp only [mem_image, mem_iUnion]
      rintro _ ⟨Z, ⟨V, hV, hZ⟩, rfl⟩
      exact ((G i).subset (hT V hV i) _ ⟨Z, hZ, rfl⟩).trans
        ((G i).subset (hS i) _ ⟨V, hV, rfl⟩)

variable {G} {hP : ⋃ i, P i = univ} {hG : ∀ i, (G i).Saturated}

@[simp]
theorem paste_covers_iff {U : PastedOpens G} {S : Set (PastedOpens G)} :
    (paste G hP hG).Covers U S ↔ ∀ i, (G i).Covers (toPiece i U) (toPiece i '' S) :=
  Iff.rfl

/-- The pasted G-topology satisfies (G0)–(G2). -/
theorem saturated_paste : (paste G hP hG).Saturated where
  empty_mem_range := (mem_range_pastedOpensEmbedding_iff G).mpr fun i ↦ by
    simpa only [preimage_empty] using (hG i).empty_mem_range
  mem_range_of_covers {U S} h V hVU hS := by
    refine (mem_range_pastedOpensEmbedding_iff G).mpr fun i ↦
      (hG i).mem_range_of_covers (h i) _ ?_ ?_
    · rw [coe_toPiece]
      exact preimage_mono hVU
    · rintro _ ⟨W, hW, rfl⟩
      rw [coe_toPiece, ← preimage_inter]
      exact (mem_range_pastedOpensEmbedding_iff G).mp (hS W hW) i
  covers_of_refinement {U S R} hS hR hRS i := by
    refine (hG i).covers_of_refinement ?_ (hR i) ?_
    · simp only [pastedOpensEmbedding_apply, sUnion_image] at hS
      simp only [sUnion_image, mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right,
        coe_toPiece, ← preimage_iUnion₂, hS]
    · rintro _ ⟨W, hW, rfl⟩
      obtain ⟨V, hV, hWV⟩ := hRS W hW
      exact ⟨toPiece i V, ⟨V, hV, rfl⟩, toPiece_mono i hWV⟩

variable (G hP hG) in
/-- The inclusion of a piece is a continuous map of G-topologies into the pasted G-topology. The
preimage of a pasted admissible open is its trace on the piece. -/
noncomputable def pasteInclusion (i : I) : (G i).ContinuousMap (paste G hP hG) where
  toFun := (↑)
  comap := toPiece i
  coe_comap' := coe_toPiece i
  covers_comap h := h i

@[simp]
theorem coe_pasteInclusion (i : I) : ⇑(pasteInclusion G hP hG i) = ((↑) : P i → X) :=
  (rfl)

@[simp]
theorem pasteInclusion_comap (i : I) : (pasteInclusion G hP hG i).comap = toPiece i :=
  (rfl)

variable (G) in
/-- The compatibility condition for pasting [BGR, §9.1.3]. Every overlap `P i ∩ P j` is admissible
in `P i`, and the G-topologies induced on it by `G i` and `G j` coincide: a subset of the overlap
is admissible in `P i` exactly when it is admissible in `P j`, and an admissible cover in `P i` of
an admissible open of the overlap is an admissible cover in `P j`. Subsets of the pieces are
compared through their images in `X`. -/
structure PasteCompatible : Prop where
  /-- The overlap `P i ∩ P j` is admissible in `P i`. -/
  preimage_mem_range : ∀ i j, ((↑) : P i → X) ⁻¹' P j ∈ range (ι i)
  /-- A subset of the overlap admissible in `P i` is admissible in `P j`. -/
  preimage_mem_range_of_subset : ∀ i j {V : Set X}, V ⊆ P i → V ⊆ P j →
    ((↑) : P i → X) ⁻¹' V ∈ range (ι i) → ((↑) : P j → X) ⁻¹' V ∈ range (ι j)
  /-- An admissible cover in `P i` of an admissible open of the overlap is admissible in `P j`. -/
  covers : ∀ i j {U : B i} {S : Set (B i)} {U' : B j} {S' : Set (B j)}, (G i).Covers U S →
    ((↑) : P j → X) '' ι j U' = ((↑) : P i → X) '' ι i U →
    (fun W ↦ ((↑) : P j → X) '' ι j W) '' S' = (fun W ↦ ((↑) : P i → X) '' ι i W) '' S →
    (G j).Covers U' S'

namespace PasteCompatible

variable (hc : PasteCompatible G)
include hc

/-- A piece `P i`, as an admissible open of the pasted G-topology. -/
def piece (i : I) : PastedOpens G :=
  ⟨P i, fun j ↦ hc.preimage_mem_range j i⟩

@[simp]
theorem coe_piece (i : I) : (hc.piece i : Set X) = P i :=
  (rfl)

@[simp]
theorem toPiece_piece_self (i : I) : toPiece i (hc.piece i) = ⊤ := by
  rw [toPiece_eq_iff, (G i).map_top, coe_piece, Subtype.coe_preimage_self]

variable (hP hG) in
/-- The pieces form an admissible cover of `X` in the pasted G-topology. -/
theorem paste_covers_top_range_piece : (paste G hP hG).Covers ⊤ (range hc.piece) := fun i ↦ by
  rw [toPiece_top]
  refine (hG i).covers_of_superset ((G i).identity ⊤) ?_ fun _ _ ↦ le_top
  rw [singleton_subset_iff]
  exact ⟨hc.piece i, mem_range_self i, hc.toPiece_piece_self i⟩

/-- The pasted G-topology induces `G i` on the piece `P i`: a subset of `P i` is a pasted
admissible open exactly when it is admissible in `G i`. -/
theorem mem_range_pastedOpensEmbedding_iff_of_subset {i : I} {V : Set X} (hV : V ⊆ P i) :
    V ∈ range (pastedOpensEmbedding G) ↔ ((↑) : P i → X) ⁻¹' V ∈ range (ι i) := by
  rw [mem_range_pastedOpensEmbedding_iff]
  refine ⟨fun h ↦ h i, fun h j ↦ ?_⟩
  -- The trace on `P j` is the subset `V ∩ P j` of the overlap, admissible in `P i`.
  have hVj : ((↑) : P i → X) ⁻¹' (V ∩ P j) ∈ range (ι i) := by
    obtain ⟨W, hW⟩ := h
    obtain ⟨W', hW'⟩ := hc.preimage_mem_range i j
    exact ⟨W ⊓ W', by rw [(G i).map_inf, hW, hW', preimage_inter]⟩
  have h' := hc.preimage_mem_range_of_subset i j (inter_subset_left.trans hV) inter_subset_right hVj
  rwa [Subtype.preimage_coe_inter_self] at h'

/-- The pasted G-topology induces `G i` on the piece `P i`: a family of pasted admissible opens
contained in `P i` covers `U ⊆ P i` exactly when its traces cover in `G i`. -/
theorem paste_covers_iff_of_le {i : I} {U : PastedOpens G} {S : Set (PastedOpens G)}
    (hU : U ≤ hc.piece i) (hS : ∀ W ∈ S, W ≤ hc.piece i) :
    (paste G hP hG).Covers U S ↔ (G i).Covers (toPiece i U) (toPiece i '' S) := by
  refine ⟨fun h ↦ h i, fun h j ↦ ?_⟩
  have hU' : (U : Set X) ⊆ P i := (SetLike.coe_subset_coe.mpr hU).trans (hc.coe_piece i).subset
  have hSi (W : PastedOpens G) (hW : W ∈ S) : (W : Set X) ⊆ P i :=
    (SetLike.coe_subset_coe.mpr (hS W hW)).trans (hc.coe_piece i).subset
  -- Members of `S` lie in `U`, since their traces on `P i` do.
  have hSU (W : PastedOpens G) (hW : W ∈ S) : (W : Set X) ⊆ U := fun x hx ↦
    (toPiece_le_toPiece_iff.mp ((G i).subset h _ ⟨W, hW, rfl⟩) ⟨hSi W hW hx, hx⟩).2
  -- Restrict the cover in `P i` to the overlap with `P j`, then move it to `P j`.
  refine hc.covers i j ((G i).restriction h (toPiece i (U ⊓ hc.piece j))
    (toPiece_mono i inf_le_left)) ?_ ?_
  · rw [image_coe_toPiece, image_coe_toPiece]
    ext x
    simp only [coe_inf, coe_piece, mem_inter_iff]
    have := @hU' x
    tauto
  · simp only [image_image, ← toPiece_inf, image_coe_toPiece]
    refine image_congr fun W hW ↦ ?_
    ext x
    simp only [coe_inf, coe_piece, mem_inter_iff]
    have := @hSU W hW x
    have := @hSi W hW x
    tauto

end PasteCompatible

variable (hP hG) in
/-- **Uniqueness of the pasted G-topology** [BGR, §9.1.3]. Let `G'` be a G-topology on `X`
satisfying (G0)–(G2), in which every piece `P i` is an admissible open `U i`, the pieces form an
admissible cover of `X`, and `G'` induces `G i` on `P i`. Then the admissible opens of `G'` are
the pasted admissible opens, and its admissible covers are those of the pasted G-topology. -/
theorem exists_orderIso_paste {B' : Type*} [SemilatticeInf B'] [OrderTop B'] {ι' : B' ↪o Set X}
    {G' : GTopology ι'} (hG' : G'.Saturated) (U : I → B') (hU : ∀ i, ι' (U i) = P i)
    (hUcov : G'.Covers ⊤ (range U))
    (hopen : ∀ i {V : Set X}, V ⊆ P i → (V ∈ range ι' ↔ ((↑) : P i → X) ⁻¹' V ∈ range (ι i)))
    (hcovers : ∀ i {V : B'} {S : Set B'} {V' : B i} {S' : Set (B i)},
      ι' V = ((↑) : P i → X) '' ι i V' → ι' '' S = (fun W ↦ ((↑) : P i → X) '' ι i W) '' S' →
      (G'.Covers V S ↔ (G i).Covers V' S')) :
    ∃ e : B' ≃o PastedOpens G, (∀ V, (e V : Set X) = ι' V) ∧
      ∀ V S, G'.Covers V S ↔ (paste G hP hG).Covers (e V) (e '' S) := by
  -- The trace of an admissible open of `G'` on a piece is admissible there.
  have hmem (V : B') (i : I) : ((↑) : P i → X) ⁻¹' ι' V ∈ range (ι i) := by
    have h := (hopen i (V := ι' (V ⊓ U i)) (by rw [G'.map_inf, hU]; exact inter_subset_right)).mp
      ⟨_, rfl⟩
    rwa [G'.map_inf, hU, Subtype.preimage_coe_inter_self] at h
  let f : B' ↪o PastedOpens G := .ofMapLEIff (fun V ↦ ⟨ι' V, hmem V⟩) fun _ _ ↦ ι'.le_iff_le
  have hf_coe (V : B') : (f V : Set X) = ι' V := (rfl)
  -- Every pasted admissible open is admissible for `G'`, by (G1) on the cover by the pieces.
  have hf : Function.Surjective f := by
    intro W
    obtain ⟨V, hV⟩ := hG'.mem_range_of_covers hUcov (W : Set X)
      (by rw [G'.map_top]; exact subset_univ _) (by
        rintro _ ⟨i, rfl⟩
        rw [hU, hopen i inter_subset_right, Subtype.preimage_coe_inter_self]
        exact W.preimage_mem_range i)
    exact ⟨V, SetLike.coe_injective hV⟩
  -- The order isomorphism `OrderIso.ofSurjective f hf` has underlying function `f`.
  refine ⟨.ofSurjective f hf, hf_coe, fun V S ↦ ?_⟩
  -- Admissibility of a cover is checked on the pieces, where `G'` agrees with `G i`.
  have key (i : I) : G'.Covers (V ⊓ U i) ((· ⊓ U i) '' S) ↔
      (G i).Covers (toPiece i (f V)) (toPiece i '' (f '' S)) := by
    refine hcovers i ?_ ?_
    · rw [image_coe_toPiece, G'.map_inf, hU, hf_coe, inter_comm]
    · simp only [image_image, image_coe_toPiece, G'.map_inf, hU, hf_coe]
      exact image_congr fun _ _ ↦ inter_comm _ _
  rw [hG'.covers_iff_restriction hUcov le_top, paste_covers_iff]
  refine ⟨fun ⟨_, h⟩ i ↦ (key i).mp (h _ ⟨i, rfl⟩), fun h ↦ ⟨fun W hW ↦ ?_, ?_⟩⟩
  · exact f.le_iff_le.mp ((paste G hP hG).subset h (f W) ⟨W, hW, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact (key i).mpr (h i)

end GTopology

end TauCeti
