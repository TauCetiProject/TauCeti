/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Basic

/-!
# Fibre bundles are Serre fibrations

A map `p : E → B` that is locally trivial, in the sense that every point of `B` lies in the base
set of some `Bundle.Trivialization F p`, has the homotopy lifting property with respect to every
cube `κ → I` with `κ` finite
(`TauCeti.hasHomotopyLiftingProperty_cube_of_exists_trivialization`).  In particular the
projection of a fibre bundle in Mathlib's sense (`FiberBundle F E`) has it
(`FiberBundle.hasHomotopyLiftingProperty_proj_cube`), and is a Serre fibration
(`TauCeti.TopCat.mem_serreFibrations_proj`).  No assumption is made on the base: in particular it
need not be paracompact.

## Main results

* `TauCeti.hasHomotopyLiftingProperty_cube_of_exists_trivialization`: a locally trivial map has the
  homotopy lifting property with respect to every cube.
* `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`: a locally trivial morphism of
  `TopCat` is a Serre fibration.
* `FiberBundle.hasHomotopyLiftingProperty_proj_cube` and `TauCeti.TopCat.mem_serreFibrations_proj`:
  the projection of a fibre bundle has the homotopy lifting property with respect to every cube,
  and is a Serre fibration.

## Implementation notes

The proof subdivides the cube.  A homotopy `H : I × (κ → I) → B` is first read as a map on the
cube `Option κ → ℝ`, where the coordinate `none` is time.  By compactness (the Lebesgue number
lemma), every sufficiently small box of the cube is sent by `H` into the base set of a single
trivialization.  Over such a box the lifting problem is solved by hand: its lower faces are a
retract of the box (push a point down along the diagonal until it meets one of them), and in the
trivialization `e` the lift sends `x` to `e.symm (H x, (e (g (r x))).2)`, where `g` is the given
lift on the lower faces and `r` is the retraction.  Cutting a box in two along one coordinate, a
lifting problem relative to some lower faces of the box is solved first on the lower half, then on
the upper half relative to one more lower face (the cut), and the two solutions glue.  Induction
on the number of cuts needed to make the boxes small solves the lifting problem on the whole cube
relative to its bottom face, which is the homotopy lifting property.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition 4.48, whose subdivision argument this file adapts.
-/

public section

noncomputable section

open Set Bundle unitInterval

universe u

namespace TauCeti

variable {ι : Type*} {E B F : Type*} [TopologicalSpace E] {p : E → B}

/-- The union of the lower faces of the box `Icc a b` in the coordinate directions in `T`. -/
private def lowerFaces (a b : ι → ℝ) (T : Finset ι) : Set (ι → ℝ) :=
  Icc a b ∩ ⋃ i ∈ T, {x | x i = a i}

private lemma isClosed_lowerFaces (a b : ι → ℝ) (T : Finset ι) : IsClosed (lowerFaces a b T) :=
  isClosed_Icc.inter <| isClosed_biUnion_finset fun i _ ↦
    isClosed_eq (continuous_apply i) continuous_const

private lemma mem_lowerFaces {a b x : ι → ℝ} {T : Finset ι} :
    x ∈ lowerFaces a b T ↔ x ∈ Icc a b ∧ ∃ i ∈ T, x i = a i := by
  simp [lowerFaces]

/-- `p` lifts the map `H` on the box `Icc a b` relative to the lower faces of the box in the
directions in `T`: every lift of `H` on those faces extends to a lift of `H` on the box. -/
private def BoxLifts (p : E → B) (H : (ι → ℝ) → B) (a b : ι → ℝ) (T : Finset ι) : Prop :=
  ∀ g : (ι → ℝ) → E, ContinuousOn g (lowerFaces a b T) →
    (∀ x ∈ lowerFaces a b T, p (g x) = H x) →
    ∃ G : (ι → ℝ) → E, ContinuousOn G (Icc a b) ∧ (∀ x ∈ Icc a b, p (G x) = H x) ∧
      ∀ x ∈ lowerFaces a b T, G x = g x

/-- The retraction of the box `Icc a b` onto its lower faces in the directions in `T`: it moves a
point down along the diagonal of the coordinates in `T` until one of them reaches its lower
bound. -/
private def lowerRetract [DecidableEq ι] (a : ι → ℝ) {T : Finset ι} (hT : T.Nonempty)
    (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ if i ∈ T then x i - T.inf' hT (fun j ↦ x j - a j) else x i

private lemma continuous_lowerRetract [DecidableEq ι] (a : ι → ℝ) {T : Finset ι}
    (hT : T.Nonempty) :
    Continuous (lowerRetract a hT) := by
  refine continuous_pi fun i ↦ ?_
  unfold lowerRetract
  split_ifs
  · exact (continuous_apply i).sub
      (Continuous.finset_inf'_apply hT fun j _ ↦ (continuous_apply j).sub continuous_const)
  · exact continuous_apply i

private lemma mapsTo_lowerRetract [DecidableEq ι] {a b : ι → ℝ} {T : Finset ι} (hT : T.Nonempty) :
    MapsTo (lowerRetract a hT) (Icc a b) (lowerFaces a b T) := by
  intro x hx
  have hle : ∀ j ∈ T, T.inf' hT (fun j ↦ x j - a j) ≤ x j - a j :=
    fun j hj ↦ Finset.inf'_le _ hj
  have h0 : 0 ≤ T.inf' hT (fun j ↦ x j - a j) :=
    (Finset.le_inf'_iff hT _).2 fun j _ ↦ sub_nonneg.2 (hx.1 j)
  obtain ⟨k, hk, hkm⟩ := Finset.exists_mem_eq_inf' hT (fun j ↦ x j - a j)
  refine mem_lowerFaces.2 ⟨⟨fun i ↦ ?_, fun i ↦ ?_⟩, k, hk, ?_⟩
  · by_cases hi : i ∈ T
    · simp only [lowerRetract, hi, ↓reduceIte]
      linarith [hle i hi]
    · simpa [lowerRetract, hi] using hx.1 i
  · by_cases hi : i ∈ T
    · simpa [lowerRetract, hi] using (sub_le_self _ h0).trans (hx.2 i)
    · simpa [lowerRetract, hi] using hx.2 i
  · simp [lowerRetract, hk, hkm]

private lemma lowerRetract_eq_self [DecidableEq ι] {a b x : ι → ℝ} {T : Finset ι}
    (hT : T.Nonempty) (hx : x ∈ lowerFaces a b T) : lowerRetract a hT x = x := by
  obtain ⟨hx, k, hk, hka⟩ := mem_lowerFaces.1 hx
  have h0 : T.inf' hT (fun j ↦ x j - a j) = 0 :=
    le_antisymm ((Finset.inf'_le _ hk).trans (by simp [hka]))
      ((Finset.le_inf'_iff hT _).2 fun j _ ↦ sub_nonneg.2 (hx.1 j))
  funext i
  simp [lowerRetract, h0]

/-- Over a box sent into the base set of a trivialization `e`, a lift on some lower faces extends
to the box: in the trivialization, keep the fibre coordinate of the lift at the image of the
point under the retraction onto those faces. -/
private lemma boxLifts_of_mapsTo [TopologicalSpace B] [TopologicalSpace F]
    (e : Trivialization F p) {H : (ι → ℝ) → B} (hH : Continuous H)
    {a b : ι → ℝ} {T : Finset ι} (hT : T.Nonempty) (hab : MapsTo H (Icc a b) e.baseSet) :
    BoxLifts p H a b T := by
  classical
  intro g hg hgH
  have hr := mapsTo_lowerRetract (b := b) (a := a) hT
  -- the given lift at the retracted point lies over the base set of `e`
  have hsrc : MapsTo (fun x ↦ g (lowerRetract a hT x)) (Icc a b) e.source := fun x hx ↦ by
    rw [e.mem_source, hgH _ (hr hx)]
    exact hab (mem_lowerFaces.1 (hr hx)).1
  have htgt : ∀ x ∈ Icc a b, (H x, (e (g (lowerRetract a hT x))).2) ∈ e.target :=
    fun x hx ↦ e.mem_target.2 (hab hx)
  refine ⟨fun x ↦ e.toOpenPartialHomeomorph.symm (H x, (e (g (lowerRetract a hT x))).2),
    ?_, fun x hx ↦ e.proj_symm_apply (htgt x hx), fun x hx ↦ ?_⟩
  · refine e.toOpenPartialHomeomorph.continuousOn_symm.comp (hH.continuousOn.prodMk ?_) htgt
    exact continuous_snd.comp_continuousOn <| e.toOpenPartialHomeomorph.continuousOn.comp
      (hg.comp (continuous_lowerRetract a hT).continuousOn hr) hsrc
  · have hsx : g x ∈ e.source := by
      rw [e.mem_source, hgH x hx]
      exact hab (mem_lowerFaces.1 hx).1
    simp only [lowerRetract_eq_self hT hx, ← hgH x hx]
    exact e.symm_apply_mk_proj hsx

private lemma lowerFaces_insert [DecidableEq ι] (a b : ι → ℝ) (T : Finset ι) (i : ι) :
    lowerFaces a b (insert i T) = lowerFaces a b {i} ∪ lowerFaces a b (T.erase i) := by
  ext x
  simp only [mem_union, mem_lowerFaces, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase]
  grind

private lemma mem_Icc_update_right [DecidableEq ι] {a b x : ι → ℝ} {i : ι} {s : ℝ}
    (hx : x ∈ Icc a b) (hxs : x i ≤ s) : x ∈ Icc a (Function.update b i s) :=
  ⟨hx.1, le_update_iff.2 ⟨hxs, fun j _ ↦ hx.2 j⟩⟩

private lemma mem_Icc_update_left [DecidableEq ι] {a b x : ι → ℝ} {i : ι} {s : ℝ}
    (hx : x ∈ Icc a b) (hsx : s ≤ x i) : x ∈ Icc (Function.update a i s) b :=
  ⟨update_le_iff.2 ⟨hsx, fun j _ ↦ hx.1 j⟩, hx.2⟩

/-- Cutting a box along the coordinate `i` at `s`: a lifting problem relative to the lower faces
in the directions `T` is solved on the lower half, then on the upper half relative to the lower
faces in the directions `T` and `i`, and the two solutions glue. -/
private lemma boxLifts_of_cut [DecidableEq ι] {H : (ι → ℝ) → B} {a b : ι → ℝ} {T : Finset ι}
    {i : ι} {s : ℝ} (has : a i ≤ s) (hsb : s ≤ b i)
    (h₁ : BoxLifts p H a (Function.update b i s) T)
    (h₂ : BoxLifts p H (Function.update a i s) b (insert i T)) : BoxLifts p H a b T := by
  set b₁ := Function.update b i s
  set a₂ := Function.update a i s
  have hb₁ : b₁ ≤ b := update_le_iff.2 ⟨hsb, fun _ _ ↦ le_rfl⟩
  have ha₂ : a ≤ a₂ := le_update_iff.2 ⟨has, fun _ _ ↦ le_rfl⟩
  have faces₁ : lowerFaces a b₁ T ⊆ lowerFaces a b T := fun x hx ↦
    let ⟨hx, h⟩ := mem_lowerFaces.1 hx
    mem_lowerFaces.2 ⟨⟨hx.1, hx.2.trans hb₁⟩, h⟩
  intro g hg hgH
  obtain ⟨G₁, hG₁, hpG₁, hG₁g⟩ := h₁ g (hg.mono faces₁) fun x hx ↦ hgH x (faces₁ hx)
  -- The lower faces of the upper half are the cut `P` and the faces `R` in the other directions
  -- of `T`.  The lift there is `G₁` on the cut and `g` on the other faces.
  let φ : (ι → ℝ) → E := fun x ↦ if x i ≤ s then G₁ x else g x
  let P := lowerFaces a₂ b {i}
  let R := lowerFaces a₂ b (T.erase i)
  have hP : ∀ x ∈ P, x ∈ Icc a₂ b ∧ x i = s := fun x hx ↦ by
    simpa [P, mem_lowerFaces, a₂] using hx
  have hP₁ : P ⊆ Icc a b₁ := fun x hx ↦
    mem_Icc_update_right ⟨ha₂.trans (hP x hx).1.1, (hP x hx).1.2⟩ (hP x hx).2.le
  have hRfaces : R ⊆ lowerFaces a b T := fun x hx ↦ by
    obtain ⟨hx, j, hj, hxj⟩ := mem_lowerFaces.1 hx
    obtain ⟨hji, hj⟩ := Finset.mem_erase.1 hj
    exact mem_lowerFaces.2 ⟨⟨ha₂.trans hx.1, hx.2⟩, j, hj, by simpa [a₂, hji] using hxj⟩
  have hφP : EqOn φ G₁ P := fun x hx ↦ by simp [φ, (hP x hx).2]
  have hφR : EqOn φ g R := fun x hx ↦ by
    by_cases hxs : x i ≤ s
    · simp only [φ, hxs, ↓reduceIte]
      have hx' := mem_lowerFaces.1 (hRfaces hx)
      exact hG₁g x (mem_lowerFaces.2 ⟨mem_Icc_update_right hx'.1 hxs, hx'.2⟩)
    · simp [φ, hxs]
  have hφc : ContinuousOn φ (lowerFaces a₂ b (insert i T)) := by
    rw [lowerFaces_insert]
    exact ((hG₁.mono hP₁).congr hφP).union_of_isClosed ((hg.mono hRfaces).congr hφR)
      (isClosed_lowerFaces _ _ _) (isClosed_lowerFaces _ _ _)
  have hφH : ∀ x ∈ lowerFaces a₂ b (insert i T), p (φ x) = H x := by
    rw [lowerFaces_insert]
    rintro x (hx | hx)
    · rw [hφP hx]; exact hpG₁ x (hP₁ hx)
    · rw [hφR hx]; exact hgH x (hRfaces hx)
  obtain ⟨G₂, hG₂, hpG₂, hG₂φ⟩ := h₂ φ hφc hφH
  have hG₂P : ∀ x ∈ P, G₂ x = G₁ x := fun x hx ↦ by
    rw [hG₂φ x (lowerFaces_insert a₂ b T i ▸ Or.inl hx), hφP hx]
  have hG₂R : ∀ x ∈ R, G₂ x = g x := fun x hx ↦ by
    rw [hG₂φ x (lowerFaces_insert a₂ b T i ▸ Or.inr hx), hφR hx]
  -- glue the two solutions along the cut
  have hIcc : Icc a b = Icc a b₁ ∪ Icc a₂ b := by
    refine Subset.antisymm (fun x hx ↦ ?_) (union_subset (Icc_subset_Icc le_rfl hb₁)
      (Icc_subset_Icc ha₂ le_rfl))
    rcases le_total (x i) s with hxs | hxs
    · exact Or.inl (mem_Icc_update_right hx hxs)
    · exact Or.inr (mem_Icc_update_left hx hxs)
  refine ⟨fun x ↦ if x i ≤ s then G₁ x else G₂ x, ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hIcc]
    refine (hG₁.congr fun x hx ↦ ?_).union_of_isClosed (hG₂.congr fun x hx ↦ ?_) isClosed_Icc
      isClosed_Icc
    · have hxs : x i ≤ s := by simpa [b₁] using hx.2 i
      simp [hxs]
    · by_cases hxs : x i ≤ s
      · have hxP : x ∈ P := by
          simpa [P, mem_lowerFaces, a₂, hx] using le_antisymm hxs (by simpa [a₂] using hx.1 i)
        simp [hxs, hG₂P x hxP]
      · simp [hxs]
  · by_cases hxs : x i ≤ s
    · simpa [hxs] using hpG₁ x (mem_Icc_update_right hx hxs)
    · simpa [hxs] using hpG₂ x (mem_Icc_update_left hx (le_of_not_ge hxs))
  · obtain ⟨hx', j, hj, hxj⟩ := mem_lowerFaces.1 hx
    by_cases hxs : x i ≤ s
    · simpa [hxs] using hG₁g x (mem_lowerFaces.2 ⟨mem_Icc_update_right hx' hxs, j, hj, hxj⟩)
    · -- above the cut, the face containing `x` is not the `i`-th one
      have hji : j ≠ i := by
        rintro rfl
        exact hxs (hxj ▸ has)
      have hxR : x ∈ R := mem_lowerFaces.2 ⟨mem_Icc_update_left hx' (le_of_not_ge hxs), j,
        Finset.mem_erase.2 ⟨hji, hj⟩, by simpa [a₂, hji] using hxj⟩
      simpa [hxs] using hG₂R x hxR

/-- If `p` lifts `H` on every box of side at most `ε` inside `Icc a₀ b₀`, relative to any nonempty
set of its lower faces, then it lifts `H` on `Icc a₀ b₀`: cut the box into such small boxes. -/
private lemma boxLifts_of_forall_small [Finite ι] {H : (ι → ℝ) → B} {ε : ℝ}
    (hε : 0 < ε) {a₀ b₀ : ι → ℝ}
    (hsmall : ∀ (a b : ι → ℝ) (T : Finset ι), T.Nonempty → a₀ ≤ a → a ≤ b → b ≤ b₀ →
      (∀ j, b j - a j ≤ ε) → BoxLifts p H a b T)
    {T : Finset ι} (hT : T.Nonempty) : BoxLifts p H a₀ b₀ T := by
  classical
  have := Fintype.ofFinite ι
  -- induction on the number of cuts needed to make the box small
  suffices key : ∀ k : ℕ, ∀ (a b : ι → ℝ) (T : Finset ι), T.Nonempty → a₀ ≤ a → b ≤ b₀ →
      ∑ j, ⌈(b j - a j) / ε⌉₊ = k → BoxLifts p H a b T from
    key _ a₀ b₀ T hT le_rfl le_rfl rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a b T hT ha hb hk
  by_cases hab : a ≤ b
  swap
  · -- an empty box
    intro g _ _
    exact ⟨g, by simp [Icc_eq_empty hab], by simp [Icc_eq_empty hab], fun _ _ ↦ rfl⟩
  by_cases hle : ∀ j, ⌈(b j - a j) / ε⌉₊ ≤ 1
  · exact hsmall a b T hT ha hab hb fun j ↦
      (div_le_one hε).1 (by exact_mod_cast Nat.ceil_le.1 (hle j))
  simp only [not_forall, not_le] at hle
  obtain ⟨i, hi⟩ := hle
  have hiε : ε < b i - a i := by
    have := Nat.lt_ceil.1 hi
    rwa [Nat.cast_one, one_lt_div hε] at this
  -- cut the box along `i` at distance `ε` from its lower face; both halves need fewer cuts
  refine boxLifts_of_cut (s := a i + ε) (by linarith) (by linarith)
    (ih _ ?_ _ _ T hT ha (update_le_iff.2 ⟨by linarith [hb i], fun j _ ↦ hb j⟩) rfl)
    (ih _ ?_ _ _ _ (Finset.insert_nonempty i T)
      (le_update_iff.2 ⟨by linarith [ha i], fun j _ ↦ ha j⟩) hb rfl)
  · rw [← hk]
    refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases eq_or_ne j i with rfl | hj
      · simp only [Function.update_self, add_sub_cancel_left, div_self hε.ne', Nat.ceil_one]
        exact hi.le
      · simp [hj]
    · simpa [div_self hε.ne'] using hi
  · rw [← hk]
    have hsub : ∀ j, j = i →
        ⌈(b j - Function.update a i (a i + ε) j) / ε⌉₊ = ⌈(b j - a j) / ε⌉₊ - 1 := by
      rintro j rfl
      rw [Function.update_self, ← Nat.ceil_sub_one]
      congr 1
      field_simp
      ring
    refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases eq_or_ne j i with rfl | hj
      · rw [hsub _ rfl]; exact Nat.sub_le _ _
      · simp [hj]
    · rw [hsub _ rfl]
      omega

/-- A locally trivial map lifts every map on a box relative to any nonempty set of its lower
faces. -/
private lemma boxLifts_of_exists_trivialization [Finite ι] [TopologicalSpace B]
    [TopologicalSpace F] (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet)
    {H : (ι → ℝ) → B} (hH : Continuous H) (a₀ b₀ : ι → ℝ) {T : Finset ι} (hT : T.Nonempty) :
    BoxLifts p H a₀ b₀ T := by
  have := Fintype.ofFinite ι
  choose e he using h
  -- every box of side at most `δ / 2` lies over the base set of a single trivialization
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := a₀) (b := b₀))
    (c := fun b ↦ H ⁻¹' (e b).baseSet) (fun b ↦ (e b).open_baseSet.preimage hH)
    fun x _ ↦ mem_iUnion.2 ⟨H x, he (H x)⟩
  refine boxLifts_of_forall_small (half_pos hδ) (fun a b T hT ha hab hb hsmall ↦ ?_) hT
  obtain ⟨c, hc⟩ := hball a ⟨ha, hab.trans hb⟩
  refine boxLifts_of_mapsTo (e c) hH hT fun x hx ↦ hc ?_
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro j
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hx.1 j))]
  linarith [hx.2 j, hsmall j, half_lt_self hδ]

/-- A locally trivial map, one for which every point of the base lies in the base set of a
trivialization with fibre `F`, has the homotopy lifting property with respect to every cube. -/
theorem hasHomotopyLiftingProperty_cube_of_exists_trivialization [TopologicalSpace B]
    [TopologicalSpace F] (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) (κ : Type*) [Finite κ] :
    HasHomotopyLiftingProperty p (κ → I) := by
  intro f H hH
  -- read the homotopy as a map on the cube `Option κ → ℝ`, with the coordinate `none` as time
  let clamp : ℝ → I := Set.projIcc 0 1 zero_le_one
  let H' : (Option κ → ℝ) → B := fun x ↦ H (clamp (x none), fun j ↦ clamp (x (some j)))
  let g : (Option κ → ℝ) → E := fun x ↦ f fun j ↦ clamp (x (some j))
  let emb : I × (κ → I) → Option κ → ℝ := fun y o ↦ o.elim (y.1 : ℝ) fun j ↦ (y.2 j : ℝ)
  have hclamp : Continuous fun x : Option κ → ℝ ↦ fun j ↦ clamp (x (some j)) :=
    continuous_pi fun j ↦ continuous_projIcc.comp (continuous_apply _)
  have hH' : Continuous H' :=
    H.continuous.comp <| (continuous_projIcc.comp (continuous_apply _)).prodMk hclamp
  have hg : Continuous g := f.continuous.comp hclamp
  have hgH : ∀ x ∈ lowerFaces 0 1 {none}, p (g x) = H' x := by
    intro x hx
    obtain ⟨-, j, hj, hxj⟩ := mem_lowerFaces.1 hx
    rw [Finset.mem_singleton] at hj
    subst hj
    have hclamp0 : clamp 0 = 0 := Set.projIcc_left zero_le_one
    simp only [H', g, hxj, Pi.zero_apply, hclamp0]
    exact (hH _).symm
  obtain ⟨G, hG, hpG, hGg⟩ := boxLifts_of_exists_trivialization h hH' 0 1
    (Finset.singleton_nonempty none) g hg.continuousOn hgH
  have hemb : Continuous emb := continuous_pi fun o ↦ by
    cases o
    · exact continuous_subtype_val.comp continuous_fst
    · exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)
  have hembI : ∀ y, emb y ∈ Icc (0 : Option κ → ℝ) 1 := fun y ↦
    ⟨fun o ↦ by cases o <;> simp [emb, unitInterval.nonneg],
      fun o ↦ by cases o <;> simp [emb, unitInterval.le_one]⟩
  have hclamp_val : ∀ t : I, clamp t = t := Set.projIcc_val zero_le_one
  refine ⟨⟨G ∘ emb, hG.comp_continuous hemb hembI⟩, funext fun y ↦ ?_, fun y ↦ ?_⟩
  · simpa [H', emb, hclamp_val] using hpG (emb y) (hembI y)
  · have hy : emb (0, y) ∈ lowerFaces 0 1 {none} :=
      mem_lowerFaces.2 ⟨hembI _, none, Finset.mem_singleton_self _, by simp [emb]⟩
    simpa [g, emb, hclamp_val] using hGg _ hy

/-- A locally trivial morphism of `TopCat`, one for which every point of the base lies in the base
set of a trivialization with fibre `F`, is a Serre fibration. -/
theorem TopCat.mem_serreFibrations_of_exists_trivialization [TopologicalSpace F]
    {E B : _root_.TopCat.{u}} {p : E ⟶ B} (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) :
    TopCat.serreFibrations p :=
  TopCat.mem_serreFibrations_iff_cube.2 fun n ↦
    hasHomotopyLiftingProperty_cube_of_exists_trivialization h (Fin n)

end TauCeti

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (F E) in
/-- The projection of a fibre bundle has the homotopy lifting property with respect to every
cube. -/
theorem hasHomotopyLiftingProperty_proj_cube (κ : Type*) [Finite κ] :
    TauCeti.HasHomotopyLiftingProperty (TotalSpace.proj : TotalSpace F E → B) (κ → I) :=
  TauCeti.hasHomotopyLiftingProperty_cube_of_exists_trivialization
    (fun b ↦ ⟨trivializationAt F E b, mem_baseSet_trivializationAt F E b⟩) κ

end FiberBundle

namespace TauCeti.TopCat

variable {B : Type u} {F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type u}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (F E) in
/-- The projection of a fibre bundle is a Serre fibration. -/
theorem mem_serreFibrations_proj :
    serreFibrations (_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
      _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B) :=
  mem_serreFibrations_iff_cube.2 fun n ↦
    FiberBundle.hasHomotopyLiftingProperty_proj_cube F E (Fin n)

end TauCeti.TopCat
