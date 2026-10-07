/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Brown
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Two-sided locally bicollared maps are bicollared

A locally bicollared map `f : N → M` (`TauCeti.IsLocallyBicollared`) has, near every point of `N`,
a bicollar: an open embedding `U × ℝ → M` with zero slice `f` on `U`. Each local bicollar has two
sides, its points of positive and of negative depth. Local bicollars alone do not assemble into a
global one, since the sides need not match up: the core circle of an open Möbius band is locally
bicollared but not bicollared. They do assemble when the sides are chosen consistently.

`TauCeti.IsLocallyBicollaredWithSides f A B` says that the local bicollars can be chosen with
positive side in `A` and negative side in `B`. When `A` and `B` are disjoint open sets, this is
M. Brown's hypothesis that the image of `f` is *two-sided*, and **Brown's bicollaring theorem**
(`TauCeti.IsLocallyBicollaredWithSides.exists_isBicollar`) says that an injective such map from a
compact space into a Hausdorff space has a global bicollar, with the same two sides. Together with
the converse, this characterizes bicollared maps out of compact spaces
(`TauCeti.isBicollared_iff_injective_and_exists_isLocallyBicollaredWithSides`).

For a locally flat codimension-one sphere in a sphere, Brown takes for `A` and `B` the two
complementary regions given by the Jordan–Brouwer separation theorem. The proof of the
bicollaring theorem follows Brown.

## Main definitions

* `TauCeti.IsLocallyBicollaredWithSides f A B`: every point of the domain has an open
  neighbourhood on which `f` has a bicollar with positive side in `A` and negative side in `B`.

## Main results

* `TauCeti.IsLocallyBicollaredWithSides.exists_isBicollar`: **Brown's bicollaring theorem**: an
  injective map from a compact space into a Hausdorff space that is locally bicollared with
  disjoint open sides `A` and `B` has a bicollar with positive side in `A` and negative side
  in `B`.
* `TauCeti.isBicollared_iff_injective_and_exists_isLocallyBicollaredWithSides`: a map from a
  compact space into a Hausdorff space is bicollared exactly when it is injective and locally
  bicollared with two disjoint open sides.
* `TauCeti.IsLocallyBicollaredWithSides.mono`: the sides may be enlarged.
* `TauCeti.IsLocallyBicollaredWithSides.disjoint_range_left`,
  `TauCeti.IsLocallyBicollaredWithSides.disjoint_range_right` and
  `TauCeti.IsLocallyBicollaredWithSides.isOpen_union_union_range`: open sides are disjoint from
  the image, and together with it they form an open set.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
-/

public section

noncomputable section

namespace TauCeti

open Function Filter Metric Set Topology

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M} {A B : Set M}
  {b : N × ℝ → M}

/-- A map `f : N → M` is **locally bicollared with sides `A` and `B`** if every point of `N` has
an open neighbourhood `U` such that the restriction of `f` to `U` has a bicollar sending points of
positive depth into `A` and points of negative depth into `B`. For disjoint open `A` and `B`, this
is M. Brown's notion of a locally bicollared set that is two-sided: the local bicollars pick out
their two sides consistently. -/
def IsLocallyBicollaredWithSides (f : N → M) (A B : Set M) : Prop :=
  ∀ x, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ ∃ b : U × ℝ → M, IsBicollar (f ∘ ((↑) : U → N)) b ∧
    MapsTo b (univ ×ˢ Ioi 0) A ∧ MapsTo b (univ ×ˢ Iio 0) B

/-- Being locally bicollared with sides `A` and `B`, spelled out: every point has an open
neighbourhood on which the restriction of the map has a bicollar with positive side in `A` and
negative side in `B`. -/
theorem isLocallyBicollaredWithSides_iff : IsLocallyBicollaredWithSides f A B ↔
    ∀ x, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ ∃ b : U × ℝ → M, IsBicollar (f ∘ ((↑) : U → N)) b ∧
      MapsTo b (univ ×ˢ Ioi 0) A ∧ MapsTo b (univ ×ˢ Iio 0) B :=
  Iff.rfl

/-- A bicollar makes its map locally bicollared, with the two sides of the bicollar as sides. -/
theorem IsBicollar.isLocallyBicollaredWithSides (h : IsBicollar f b) :
    IsLocallyBicollaredWithSides f (b '' (univ ×ˢ Ioi 0)) (b '' (univ ×ˢ Iio 0)) := by
  refine fun x => ⟨univ, isOpen_univ, mem_univ x, _, h.restrict isOpen_univ, ?_, ?_⟩ <;>
    exact fun p hp => ⟨((p.1 : N), p.2), ⟨mem_univ _, hp.2⟩, rfl⟩

namespace IsLocallyBicollaredWithSides

/-- A map that is locally bicollared with prescribed sides is locally bicollared. -/
theorem isLocallyBicollared (h : IsLocallyBicollaredWithSides f A B) :
    IsLocallyBicollared f :=
  isLocallyBicollared_iff.2 fun x =>
    let ⟨U, hU, hxU, _, hb, _⟩ := h x
    ⟨U, hU, hxU, hb.isBicollared⟩

/-- Reversing the depth of the local bicollars exchanges the two sides. -/
theorem swap (h : IsLocallyBicollaredWithSides f A B) : IsLocallyBicollaredWithSides f B A := by
  intro x
  obtain ⟨U, hU, hxU, b, hb, hbA, hbB⟩ := h x
  refine ⟨U, hU, hxU, _, hb.comp_prodMap_id_neg, ?_, ?_⟩
  · exact fun p hp => hbB ⟨mem_univ _, neg_neg_of_pos hp.2⟩
  · exact fun p hp => hbA ⟨mem_univ _, neg_pos.2 hp.2⟩

/-- The sides of a locally bicollared map may be enlarged. -/
theorem mono (h : IsLocallyBicollaredWithSides f A B) {A' B' : Set M} (hA : A ⊆ A')
    (hB : B ⊆ B') : IsLocallyBicollaredWithSides f A' B' := fun x =>
  let ⟨U, hU, hxU, b, hb, hbA, hbB⟩ := h x
  ⟨U, hU, hxU, b, hb, hbA.mono_right hA, hbB.mono_right hB⟩

/-- An open side `A` is disjoint from the image: approaching `f x` from the side `B` within a
local bicollar, one would meet the neighbourhood `A` of `f x`. -/
theorem disjoint_range_left (h : IsLocallyBicollaredWithSides f A B) (hA : IsOpen A)
    (hAB : Disjoint A B) : Disjoint (range f) A := by
  refine disjoint_left.2 ?_
  rintro _ ⟨x, rfl⟩ hx
  obtain ⟨U, -, hxU, b, hb, -, hbB⟩ := h x
  have h0 : b (⟨x, hxU⟩, 0) = f x := hb.apply_zero _
  have hlim : Tendsto (fun t : ℝ => b (⟨x, hxU⟩, t)) (𝓝[<] 0) (𝓝 (f x)) := by
    rw [← h0]
    exact ((hb.isOpenEmbedding.continuous.comp (continuous_const.prodMk continuous_id)).tendsto
      0).mono_left nhdsWithin_le_nhds
  obtain ⟨t, htA, ht⟩ := ((hlim.eventually (hA.mem_nhds hx)).and self_mem_nhdsWithin).exists
  exact disjoint_left.1 hAB htA (hbB ⟨mem_univ _, ht⟩)

/-- An open side `B` is disjoint from the image. -/
theorem disjoint_range_right (h : IsLocallyBicollaredWithSides f A B) (hB : IsOpen B)
    (hAB : Disjoint A B) : Disjoint (range f) B :=
  h.swap.disjoint_range_left hB hAB.symm

/-- Two open sides together with the image form an open set: near each point of the image, a
local bicollar sweeps out an open set consisting of points of the two sides and of the image. -/
theorem isOpen_union_union_range (h : IsLocallyBicollaredWithSides f A B) (hA : IsOpen A)
    (hB : IsOpen B) : IsOpen (A ∪ B ∪ range f) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro p (hp | ⟨x, rfl⟩)
  · exact mem_of_superset ((hA.union hB).mem_nhds hp) subset_union_left
  · obtain ⟨U, -, hxU, b, hb, hbA, hbB⟩ := h x
    refine mem_of_superset
      (hb.isOpenEmbedding.isOpen_range.mem_nhds ⟨(⟨x, hxU⟩, 0), hb.apply_zero _⟩) ?_
    rintro _ ⟨⟨u, t⟩, rfl⟩
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact Or.inl (Or.inr (hbB ⟨mem_univ _, ht⟩))
    · exact Or.inr ⟨u, (hb.apply_zero u).symm⟩
    · exact Or.inl (Or.inl (hbA ⟨mem_univ _, ht⟩))

end IsLocallyBicollaredWithSides

/-! ### The proof of Brown's bicollaring theorem -/

section Brown

/-- The map `f`, viewed as a map into the side `A` together with the image of `f`. -/
private abbrev sideRestrict (f : N → M) (A : Set M) : N → ↥(A ∪ range f) :=
  codRestrict f (A ∪ range f) fun x => mem_union_right _ (mem_range_self x)

/-- A collar of `f` inside `A ∪ f(N)` lies in `A` at positive depth. -/
private theorem coe_mem_of_isCollar {c : N × Ico (0 : ℝ) 1 → ↥(A ∪ range f)}
    (hc : IsCollar (sideRestrict f A) c) {p : N × Ico (0 : ℝ) 1} (hp : (p.2 : ℝ) ≠ 0) :
    (c p : M) ∈ A := by
  rcases (c p).2 with h | ⟨y, hy⟩
  · exact h
  · refine absurd ?_ hp
    have hp' : p ∈ c ⁻¹' range (sideRestrict f A) := ⟨y, Subtype.ext hy⟩
    rw [hc.preimage_range] at hp'
    exact congrArg Subtype.val hp'.2

/-- On the side `A`, the map `f` is locally collared in `A ∪ f(N)`: the nonnegative half of each
local bicollar is a local collar there. -/
private theorem IsLocallyBicollaredWithSides.isLocallyCollared_sideRestrict
    (h : IsLocallyBicollaredWithSides f A B) (hA : IsOpen A) (hB : IsOpen B)
    (hAB : Disjoint A B) : IsLocallyCollared (sideRestrict f A) := by
  refine isLocallyCollared_iff.2 fun x => ?_
  obtain ⟨U, hU, hxU, b, hb, hbA, hbB⟩ := h x
  have hmem : ∀ p, (b ∘ Prod.map id ((↑) : Ico (0 : ℝ) 1 → ℝ)) p ∈ A ∪ range f := by
    rintro ⟨u, t, ht0, -⟩
    rcases ht0.eq_or_lt with ht | ht
    · exact Or.inr ⟨u, by simpa [← ht] using (hb.apply_zero u).symm⟩
    · exact Or.inl (hbA ⟨mem_univ _, ht⟩)
  -- The collar is open: it is the part of the open set `b (U × (-1, 1))` in `A ∪ f(N)`.
  have hrange : range (codRestrict _ _ hmem) =
      (↑) ⁻¹' (b '' (univ ×ˢ Ioo (-1 : ℝ) 1)) := by
    ext ⟨q, hq⟩
    simp only [mem_range, Subtype.ext_iff, val_codRestrict_apply, mem_preimage, mem_image]
    constructor
    · rintro ⟨⟨u, t⟩, rfl⟩
      exact ⟨(u, t), ⟨mem_univ _, by linarith [t.2.1], t.2.2⟩, rfl⟩
    · rintro ⟨⟨u, t⟩, ⟨-, -, ht1⟩, rfl⟩
      have ht0 : 0 ≤ t := by
        by_contra! ht
        exact hq.elim (disjoint_left.1 hAB · (hbB ⟨mem_univ _, ht⟩))
          (disjoint_left.1 (h.disjoint_range_right hB hAB) · (hbB ⟨mem_univ _, ht⟩))
      exact ⟨(u, ⟨t, ht0, ht1⟩), rfl⟩
  refine ⟨U, hU, hxU, codRestrict _ _ hmem, ⟨⟨?_, ?_⟩, fun u => Subtype.ext (hb.apply_zero u)⟩,
    fun ⟨u, t⟩ ⟨y, hy⟩ => ?_⟩
  · exact (hb.isOpenEmbedding.isEmbedding.comp
      (IsEmbedding.id.prodMap IsEmbedding.subtypeVal)).codRestrict _ hmem
  · rw [hrange]
    exact (hb.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Ioo)).preimage
      continuous_subtype_val
  · by_contra ht
    exact disjoint_left.1 (h.disjoint_range_left hA hAB) ⟨y, congrArg Subtype.val hy⟩
      (hbA ⟨mem_univ _, lt_of_le_of_ne t.2.1 (Ne.symm ht)⟩)

/-- The depth `|s| ∈ [0, 1)` of a point `s` of the open interval `(-1, 1)`. -/
private def depth (s : ball (0 : ℝ) 1) : Ico (0 : ℝ) 1 :=
  ⟨|(s : ℝ)|, abs_nonneg _, by
    have hs := mem_ball_zero_iff.1 s.2
    rwa [Real.norm_eq_abs] at hs⟩

/-- The point of `(-1, 1)` at depth `t` on the positive side. -/
private def posBall (t : Ico (0 : ℝ) 1) : ball (0 : ℝ) 1 :=
  ⟨t, by simpa [abs_of_nonneg t.2.1] using t.2.2⟩

/-- The point of `(-1, 1)` at depth `t` on the negative side. -/
private def negBall (t : Ico (0 : ℝ) 1) : ball (0 : ℝ) 1 :=
  ⟨-t, by simpa [abs_of_nonneg t.2.1] using t.2.2⟩

@[simp] private theorem coe_posBall (t : Ico (0 : ℝ) 1) : (posBall t : ℝ) = t := rfl

@[simp] private theorem coe_negBall (t : Ico (0 : ℝ) 1) : (negBall t : ℝ) = -t := rfl

private theorem depth_of_coe_eq_zero {s : ball (0 : ℝ) 1} (hs : (s : ℝ) = 0) :
    depth s = ⟨0, by norm_num⟩ :=
  Subtype.ext (by simp [depth, hs])

private theorem continuous_depth : Continuous depth :=
  (continuous_abs.comp continuous_subtype_val).subtype_mk _

private theorem continuous_posBall : Continuous posBall :=
  continuous_subtype_val.subtype_mk _

private theorem continuous_negBall : Continuous negBall :=
  continuous_subtype_val.neg.subtype_mk _

private theorem depth_posBall (t : Ico (0 : ℝ) 1) : depth (posBall t) = t :=
  Subtype.ext (abs_of_nonneg t.2.1)

private theorem depth_negBall (t : Ico (0 : ℝ) 1) : depth (negBall t) = t :=
  Subtype.ext ((abs_neg _).trans (abs_of_nonneg t.2.1))

private theorem posBall_depth {s : ball (0 : ℝ) 1} (hs : 0 ≤ (s : ℝ)) : posBall (depth s) = s :=
  Subtype.ext (abs_of_nonneg hs)

private theorem negBall_depth {s : ball (0 : ℝ) 1} (hs : (s : ℝ) ≤ 0) : negBall (depth s) = s :=
  Subtype.ext (by simp [negBall, depth, abs_of_nonpos hs])

/-- Two collars of `f`, on the sides `A` and `B`, glued along `f` to a map `N × (-1, 1) → M`:
nonnegative depths go to the collar on `A`, negative depths to the collar on `B`. -/
private def glue (cA : N × Ico (0 : ℝ) 1 → ↥(A ∪ range f))
    (cB : N × Ico (0 : ℝ) 1 → ↥(B ∪ range f)) (q : N × ball (0 : ℝ) 1) : M :=
  if 0 ≤ (q.2 : ℝ) then cA (q.1, depth q.2) else cB (q.1, depth q.2)

variable {cA : N × Ico (0 : ℝ) 1 → ↥(A ∪ range f)} {cB : N × Ico (0 : ℝ) 1 → ↥(B ∪ range f)}

/-- A collar of `f` inside `A ∪ f(N)` is `f` at depth zero. -/
private theorem coe_apply_zero_of_isCollar {c : N × Ico (0 : ℝ) 1 → ↥(A ∪ range f)}
    (hc : IsCollar (sideRestrict f A) c) (x : N) : (c (x, ⟨0, by norm_num⟩) : M) = f x :=
  congrArg Subtype.val (hc.apply_zero x)

private theorem glue_of_coe_eq_zero (hcA : IsCollar (sideRestrict f A) cA) (x : N)
    {s : ball (0 : ℝ) 1} (hs : (s : ℝ) = 0) : glue cA cB (x, s) = f x := by
  simp only [glue, hs, le_refl, ↓reduceIte, depth_of_coe_eq_zero hs,
    coe_apply_zero_of_isCollar hcA]

private theorem glue_mem_left (hcA : IsCollar (sideRestrict f A) cA) (x : N)
    {s : ball (0 : ℝ) 1} (hs : 0 < (s : ℝ)) : glue cA cB (x, s) ∈ A := by
  simp only [glue, hs.le, ↓reduceIte]
  exact coe_mem_of_isCollar hcA (abs_ne_zero.2 hs.ne')

private theorem glue_mem_right (hcB : IsCollar (sideRestrict f B) cB) (x : N)
    {s : ball (0 : ℝ) 1} (hs : (s : ℝ) < 0) : glue cA cB (x, s) ∈ B := by
  simp only [glue, hs.not_ge, ↓reduceIte]
  exact coe_mem_of_isCollar hcB (abs_ne_zero.2 hs.ne)

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem glue_posBall (p : N × Ico (0 : ℝ) 1) :
    glue cA cB (p.1, posBall p.2) = cA p := by
  simp only [glue, coe_posBall, p.2.2.1, ↓reduceIte, depth_posBall]

private theorem glue_negBall (hcA : IsCollar (sideRestrict f A) cA)
    (hcB : IsCollar (sideRestrict f B) cB) (p : N × Ico (0 : ℝ) 1) :
    glue cA cB (p.1, negBall p.2) = cB p := by
  obtain ⟨x, t⟩ := p
  rcases t.2.1.eq_or_lt with ht | ht
  · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht.symm
    subst ht'
    rw [glue_of_coe_eq_zero hcA x (by simp), coe_apply_zero_of_isCollar hcB]
  · have ht' : ¬ 0 ≤ -(t : ℝ) := by simpa using ht
    simp only [glue, coe_negBall, ht', ↓reduceIte, depth_negBall]

private theorem continuous_glue (hcA : IsCollar (sideRestrict f A) cA)
    (hcB : IsCollar (sideRestrict f B) cB) : Continuous (glue cA cB) := by
  refine Continuous.if_le ?_ ?_ continuous_const (continuous_subtype_val.comp continuous_snd) ?_
  · exact continuous_subtype_val.comp (hcA.isOpenEmbedding.continuous.comp
      (continuous_fst.prodMk (continuous_depth.comp continuous_snd)))
  · exact continuous_subtype_val.comp (hcB.isOpenEmbedding.continuous.comp
      (continuous_fst.prodMk (continuous_depth.comp continuous_snd)))
  · rintro ⟨x, s⟩ hs
    simp only [depth_of_coe_eq_zero hs.symm, coe_apply_zero_of_isCollar hcA,
      coe_apply_zero_of_isCollar hcB]

/-- Points of opposite signs are glued to different points: the side `B` meets neither the side
`A` nor the image of `f`. -/
private theorem glue_ne (hcB : IsCollar (sideRestrict f B) cB) (hAB : Disjoint A B)
    (hfB : Disjoint (range f) B) {x y : N} {s t : ball (0 : ℝ) 1} (hs : 0 ≤ (s : ℝ))
    (ht : (t : ℝ) < 0) : glue cA cB (x, s) ≠ glue cA cB (y, t) := by
  intro he
  have hB' := glue_mem_right (cA := cA) hcB y ht
  rw [← he] at hB'
  simp only [glue, hs, ↓reduceIte] at hB'
  exact (cA (x, depth s)).2.elim (disjoint_left.1 hAB · hB') (disjoint_left.1 hfB · hB')

private theorem injective_glue (hcA : IsCollar (sideRestrict f A) cA)
    (hcB : IsCollar (sideRestrict f B) cB) (hAB : Disjoint A B) (hfB : Disjoint (range f) B) :
    Injective (glue cA cB) := by
  rintro ⟨x, s⟩ ⟨y, t⟩ hxy
  rcases le_or_gt 0 (s : ℝ) with hs | hs <;> rcases le_or_gt 0 (t : ℝ) with ht | ht
  · simp only [glue, hs, ht, ↓reduceIte] at hxy
    obtain ⟨rfl, hd⟩ := Prod.mk.inj (hcA.isOpenEmbedding.injective (Subtype.ext hxy))
    rw [← posBall_depth hs, ← posBall_depth ht, hd]
  · exact absurd hxy (glue_ne hcB hAB hfB hs ht)
  · exact absurd hxy.symm (glue_ne hcB hAB hfB ht hs)
  · simp only [glue, hs.not_ge, ht.not_ge, ↓reduceIte] at hxy
    obtain ⟨rfl, hd⟩ := Prod.mk.inj (hcB.isOpenEmbedding.injective (Subtype.ext hxy))
    rw [← negBall_depth hs.le, ← negBall_depth ht.le, hd]

/-- The glued map is open. The image of an open set `S` is relatively open in `A ∪ f(N)` and in
`B ∪ f(N)`, cut out by open sets `O` and `O'` of `M` that contain the same points of `f(N)`. It
is therefore the union of `O ∩ A`, `O' ∩ B` and `O ∩ O' ∩ (A ∪ B ∪ f(N))`. -/
private theorem isOpenMap_glue (hcA : IsCollar (sideRestrict f A) cA)
    (hcB : IsCollar (sideRestrict f B) cB) (hA : IsOpen A) (hB : IsOpen B)
    (hW : IsOpen (A ∪ B ∪ range f)) : IsOpenMap (glue cA cB) := by
  intro S hS
  obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.1 (hcA.isOpenEmbedding.isOpenMap _
    (hS.preimage (continuous_fst.prodMk (continuous_posBall.comp continuous_snd))))
  obtain ⟨O', hO', hOS'⟩ := isOpen_induced_iff.1 (hcB.isOpenEmbedding.isOpenMap _
    (hS.preimage (continuous_fst.prodMk (continuous_negBall.comp continuous_snd))))
  -- A point of `A ∪ f(N)` in `O`, or of `B ∪ f(N)` in `O'`, is in the image of `S`.
  have hmemA : ∀ p (hp : p ∈ A ∪ range f), p ∈ O → p ∈ glue cA cB '' S := fun p hp hpO => by
    have hp' : (⟨p, hp⟩ : ↥(A ∪ range f)) ∈ ((↑) : ↥(A ∪ range f) → M) ⁻¹' O := hpO
    rw [hOS] at hp'
    obtain ⟨q, hq, hqp⟩ := hp'
    exact ⟨(q.1, posBall q.2), hq, by rw [glue_posBall, hqp]⟩
  have hmemB : ∀ p (hp : p ∈ B ∪ range f), p ∈ O' → p ∈ glue cA cB '' S := fun p hp hpO => by
    have hp' : (⟨p, hp⟩ : ↥(B ∪ range f)) ∈ ((↑) : ↥(B ∪ range f) → M) ⁻¹' O' := hpO
    rw [hOS'] at hp'
    obtain ⟨q, hq, hqp⟩ := hp'
    exact ⟨(q.1, negBall q.2), hq, by rw [glue_negBall hcA hcB, hqp]⟩
  -- Conversely, the image of `S` at nonnegative depth lies in `O`, at nonpositive depth in `O'`.
  have hO_of : ∀ x s, (x, s) ∈ S → 0 ≤ (s : ℝ) → glue cA cB (x, s) ∈ O := fun x s hxs hs => by
    have hmem : cA (x, depth s) ∈ ((↑) : ↥(A ∪ range f) → M) ⁻¹' O :=
      hOS ▸ ⟨(x, depth s), by simpa [posBall_depth hs] using hxs, rfl⟩
    simpa only [glue, hs, ↓reduceIte, mem_preimage] using hmem
  have hO'_of : ∀ x s, (x, s) ∈ S → (s : ℝ) ≤ 0 → glue cA cB (x, s) ∈ O' := fun x s hxs hs => by
    have hmem : cB (x, depth s) ∈ ((↑) : ↥(B ∪ range f) → M) ⁻¹' O' :=
      hOS' ▸ ⟨(x, depth s), by simpa [negBall_depth hs] using hxs, rfl⟩
    have hglue : glue cA cB (x, s) = cB (x, depth s) := by
      simpa only [negBall_depth hs] using glue_negBall hcA hcB (x, depth s)
    rwa [mem_preimage, ← hglue] at hmem
  have himage : glue cA cB '' S = O ∩ A ∪ O' ∩ B ∪ O ∩ O' ∩ (A ∪ B ∪ range f) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨x, s⟩, hxs, rfl⟩
      rcases lt_trichotomy (s : ℝ) 0 with hs | hs | hs
      · exact Or.inl (Or.inr ⟨hO'_of x s hxs hs.le, glue_mem_right hcB x hs⟩)
      · exact Or.inr ⟨⟨hO_of x s hxs hs.ge, hO'_of x s hxs hs.le⟩,
          Or.inr ⟨x, (glue_of_coe_eq_zero hcA x hs).symm⟩⟩
      · exact Or.inl (Or.inl ⟨hO_of x s hxs hs.le, glue_mem_left hcA x hs⟩)
    · rintro p ((⟨hpO, hpA⟩ | ⟨hpO', hpB⟩) | ⟨⟨hpO, hpO'⟩, (hpA | hpB) | hpR⟩)
      · exact hmemA p (Or.inl hpA) hpO
      · exact hmemB p (Or.inl hpB) hpO'
      · exact hmemA p (Or.inl hpA) hpO
      · exact hmemB p (Or.inl hpB) hpO'
      · exact hmemA p (Or.inr hpR) hpO
  rw [himage]
  exact ((hO.inter hA).union (hO'.inter hB)).union ((hO.inter hO').inter hW)

/-- Collars of `f` on the sides `A` and `B` glue to a bicollar of `f` with these two sides. -/
private theorem exists_isBicollar_of_isCollar (hA : IsOpen A) (hB : IsOpen B)
    (hAB : Disjoint A B) (hfB : Disjoint (range f) B) (hW : IsOpen (A ∪ B ∪ range f))
    (hcA : IsCollar (sideRestrict f A) cA) (hcB : IsCollar (sideRestrict f B) cB) :
    ∃ b : N × ℝ → M, IsBicollar f b ∧ MapsTo b (univ ×ˢ Ioi 0) A ∧
      MapsTo b (univ ×ˢ Iio 0) B := by
  have hg : IsOpenEmbedding (glue cA cB) := .of_continuous_injective_isOpenMap
    (continuous_glue hcA hcB) (injective_glue hcA hcB hAB hfB) (isOpenMap_glue hcA hcB hA hB hW)
  -- Reparametrize `(-1, 1)` as `ℝ` by `t ↦ t / √(1 + t²)`, which preserves the sign.
  let e : ℝ ≃ₜ ball (0 : ℝ) 1 := Homeomorph.unitBall
  have he : ∀ t : ℝ, (e t : ℝ) = (√(1 + ‖t‖ ^ 2))⁻¹ * t := fun t => by
    rw [Homeomorph.unitBall_apply_coe, OpenPartialHomeomorph.univUnitBall_apply, smul_eq_mul]
  have he0 : ∀ t : ℝ, 0 < (√(1 + ‖t‖ ^ 2))⁻¹ := fun t => inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  refine ⟨glue cA cB ∘ Prod.map id e,
    ⟨hg.comp ((Homeomorph.refl N).prodCongr e).isOpenEmbedding,
      fun x => glue_of_coe_eq_zero hcA x Homeomorph.coe_unitBall_apply_zero⟩, ?_, ?_⟩
  · exact fun p hp => glue_mem_left hcA _ (by rw [he]; exact mul_pos (he0 _) hp.2)
  · exact fun p hp => glue_mem_right hcB _ (by rw [he]; exact mul_neg_of_pos_of_neg (he0 _) hp.2)

end Brown

namespace IsLocallyBicollaredWithSides

/-- **Brown's bicollaring theorem**, for a compact domain: an injective map from a compact space
into a Hausdorff space that is locally bicollared with disjoint open sides `A` and `B` has a
global bicollar, with positive side in `A` and negative side in `B`. -/
theorem exists_isBicollar [CompactSpace N] [T2Space M] (h : IsLocallyBicollaredWithSides f A B)
    (hf : Injective f) (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) :
    ∃ b : N × ℝ → M, IsBicollar f b ∧ MapsTo b (univ ×ˢ Ioi 0) A ∧
      MapsTo b (univ ×ˢ Iio 0) B := by
  obtain ⟨cA, hcA⟩ := isCollared_iff.1
    ((h.isLocallyCollared_sideRestrict hA hB hAB).isCollared (hf.codRestrict _))
  obtain ⟨cB, hcB⟩ := isCollared_iff.1
    ((h.swap.isLocallyCollared_sideRestrict hB hA hAB.symm).isCollared (hf.codRestrict _))
  exact exists_isBicollar_of_isCollar hA hB hAB (h.disjoint_range_right hB hAB)
    (h.isOpen_union_union_range hA hB) hcA hcB

/-- An injective map from a compact space into a Hausdorff space that is locally bicollared with
disjoint open sides is bicollared. -/
theorem isBicollared [CompactSpace N] [T2Space M] (h : IsLocallyBicollaredWithSides f A B)
    (hf : Injective f) (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) :
    IsBicollared f :=
  let ⟨_, hb, _⟩ := h.exists_isBicollar hf hA hB hAB
  hb.isBicollared

end IsLocallyBicollaredWithSides

/-- A map from a compact space into a Hausdorff space is bicollared exactly when it is injective
and locally bicollared with two disjoint open sides. -/
theorem isBicollared_iff_injective_and_exists_isLocallyBicollaredWithSides [CompactSpace N]
    [T2Space M] : IsBicollared f ↔ Injective f ∧ ∃ A B : Set M, IsOpen A ∧ IsOpen B ∧
      Disjoint A B ∧ IsLocallyBicollaredWithSides f A B := by
  refine ⟨fun h => ?_, fun ⟨hf, _, _, hA, hB, hAB, h⟩ => h.isBicollared hf hA hB hAB⟩
  obtain ⟨b, hb⟩ := isBicollared_iff.1 h
  exact ⟨hb.injective, _, _, hb.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Ioi),
    hb.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Iio), hb.disjoint_image_Ioi_Iio,
    hb.isLocallyBicollaredWithSides⟩

end TauCeti
