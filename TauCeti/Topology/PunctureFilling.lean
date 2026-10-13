/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Topology.DiscreteSubset

/-!
# Filling punctured-disc ends of a space

Let `E` be a topological space and let `φ i : 𝔻* → E`, for `i : ι`, be a family of maps from the
punctured unit disc `𝔻* = ball 0 1 \ {0}` of `ℂ`. The **puncture filling** `PunctureFilling φ` adds
to `E` one new point `center φ i` for each `i`, and glues the unit disc `𝔻 = ball 0 1` onto
`E ⊕ {center φ i}` along `φ i`: the map `disc φ i : 𝔻 → PunctureFilling φ` sends `0` to
`center φ i` and every other point `w` to `φ i w`. The underlying type is the sum `E ⊕ ι`, and the
topology is the final topology of the inclusion of `E` and of the discs `disc φ i`, so that a map
out of the filling is continuous exactly when its restrictions to `E` and to every filled disc are
(`PunctureFilling.continuous_iff`).

This is how a finite cover of a punctured surface is compactified: each component of the preimage
of a punctured disc about a puncture is itself a punctured disc, and the filling adds its missing
centre. The general statements here need only the charts `φ i`. When they are open embeddings,
`E` and the filled discs are open subspaces of the filling, and the neighbourhoods of `center φ i`
are the images of the discs of radius `r` (`PunctureFilling.hasBasis_nhds_center`). Under the
hypotheses describing the ends of `E` the filling is Hausdorff, compact, connected and second
countable.

## Main declarations

* `TauCeti.PunctureFilling φ`: the space `E` with the punctures of the discs `φ i` filled in,
  with the inclusion `PunctureFilling.incl`, the added points `PunctureFilling.center` and the
  filled discs `PunctureFilling.disc`.
* `TauCeti.PunctureFilling.isOpen_iff`, `TauCeti.PunctureFilling.continuous_iff`: the final
  topology and its universal property.
* `TauCeti.PunctureFilling.isOpenEmbedding_incl`, `TauCeti.PunctureFilling.isOpenEmbedding_disc`:
  `E` and the filled discs are open subspaces, and `E` is dense
  (`TauCeti.PunctureFilling.denseRange_incl`).
* `TauCeti.PunctureFilling.nhds_center`, `TauCeti.PunctureFilling.hasBasis_nhds_center`: the
  neighbourhoods of an added point.
* `TauCeti.PunctureFilling.isDiscrete_range_center`: the added points are isolated from one
  another.
* `TauCeti.PunctureFilling.t2Space`, `TauCeti.PunctureFilling.compactSpace`,
  `TauCeti.PunctureFilling.connectedSpace`, `TauCeti.PunctureFilling.secondCountableTopology`:
  the separation, compactness, connectedness and countability of the filling.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (Lemma 1.80: filling the punctures of a finite unramified cover).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorem 8.4.
-/

public section

noncomputable section

open Filter Metric Set Topology

namespace TauCeti

/-- The unit disc of `ℂ`, as a subtype. -/
local notation "𝔻" => Set.Elem (ball (0 : ℂ) 1)

/-- The punctured unit disc of `ℂ`, as a subtype. -/
local notation "𝔻*" => Set.Elem (ball (0 : ℂ) 1 \ {0})

variable {E ι : Type*}

/-- The **puncture filling** of `E` along the punctured discs `φ i : 𝔻* → E`: the space `E` with
one point `PunctureFilling.center φ i` added for every `i`, which fills the puncture of `φ i`. Its
topology is the final topology of the inclusion `PunctureFilling.incl` of `E` and of the filled
discs `PunctureFilling.disc φ i : 𝔻 → PunctureFilling φ`.

Its points are those of the sum `E ⊕ ι`; the constructor is private, and points are built with
`PunctureFilling.incl` and `PunctureFilling.center` and taken apart with
`PunctureFilling.induction`. -/
structure PunctureFilling (φ : ι → 𝔻* → E) : Type _ where
  private mk ::
  /-- A point of the puncture filling as a point of `E ⊕ ι`: a point of `E`, or the index of the
  puncture it fills. -/
  toSum : E ⊕ ι

namespace PunctureFilling

variable (φ : ι → 𝔻* → E)

/-- The inclusion of `E` into its puncture filling. -/
def incl (x : E) : PunctureFilling φ :=
  ⟨.inl x⟩

/-- The point of the puncture filling which fills the puncture of the `i`-th disc. -/
def center (i : ι) : PunctureFilling φ :=
  ⟨.inr i⟩

/-- A nonzero point of the unit disc, as a point of the punctured unit disc. -/
private def puncture {z : 𝔻} (hz : z ≠ 0) : 𝔻* :=
  ⟨z, z.2, fun h => hz (Subtype.ext h)⟩

open Classical in
/-- The `i`-th filled disc: the unit disc mapped into the puncture filling, sending `0` to the
added point `center φ i` and every other point `w` to `φ i w`. -/
def disc (i : ι) (z : 𝔻) : PunctureFilling φ :=
  if h : z = 0 then center φ i else incl φ (φ i (puncture h))

variable {φ}

/-- The inclusion of `E` into its puncture filling is injective. -/
theorem incl_injective : Function.Injective (incl φ) :=
  fun _ _ h => Sum.inl_injective (congrArg toSum h)

/-- Distinct punctures are filled by distinct points. -/
theorem center_injective : Function.Injective (center φ) :=
  fun _ _ h => Sum.inr_injective (congrArg toSum h)

@[simp]
theorem incl_inj {x y : E} : incl φ x = incl φ y ↔ x = y :=
  incl_injective.eq_iff

@[simp]
theorem center_inj {i j : ι} : center φ i = center φ j ↔ i = j :=
  center_injective.eq_iff

@[simp]
theorem incl_ne_center (x : E) (i : ι) : incl φ x ≠ center φ i :=
  fun h => Sum.inl_ne_inr (congrArg toSum h)

@[simp]
theorem center_ne_incl (i : ι) (x : E) : center φ i ≠ incl φ x :=
  (incl_ne_center x i).symm

/-- Induction on the points of the puncture filling: each is a point of `E` or an added point. -/
@[elab_as_elim]
protected theorem induction {P : PunctureFilling φ → Prop} (incl : ∀ x, P (incl φ x))
    (center : ∀ i, P (center φ i)) (y : PunctureFilling φ) : P y := by
  rcases y with ⟨x | i⟩
  exacts [incl x, center i]

/-- The added points are exactly the points of the filling outside `E`. -/
theorem isCompl_range_incl_range_center : IsCompl (range (incl φ)) (range (center φ)) := by
  refine isCompl_iff.2 ⟨disjoint_left.2 ?_, codisjoint_iff.2 (eq_univ_of_forall fun y => ?_)⟩
  · rintro _ ⟨x, rfl⟩ ⟨i, hi⟩
    exact incl_ne_center x i hi.symm
  · induction y using PunctureFilling.induction with
    | incl x => exact Or.inl (mem_range_self x)
    | center i => exact Or.inr (mem_range_self i)

@[simp]
theorem compl_range_incl : (range (incl φ))ᶜ = range (center φ) :=
  isCompl_range_incl_range_center.compl_eq

@[simp]
theorem compl_range_center : (range (center φ))ᶜ = range (incl φ) :=
  isCompl_range_incl_range_center.symm.compl_eq

/-- The centre of the `i`-th filled disc is the added point `center φ i`. -/
@[simp]
theorem disc_zero (i : ι) : disc φ i 0 = center φ i :=
  dite_eq_left rfl

/-- Off its centre, the `i`-th filled disc is the punctured disc `φ i`. -/
@[simp]
theorem disc_inclusion (i : ι) (w : 𝔻*) : disc φ i (inclusion sdiff_subset w) = incl φ (φ i w) :=
  dite_eq_right fun (h : inclusion sdiff_subset w = 0) => w.2.2 (congrArg Subtype.val h)

/-- A point of the `i`-th filled disc lies in `E` exactly when it is a point `φ i w` of the
punctured disc. -/
theorem disc_eq_incl_iff {i : ι} {z : 𝔻} {x : E} :
    disc φ i z = incl φ x ↔ ∃ w, inclusion sdiff_subset w = z ∧ φ i w = x := by
  constructor
  · intro h
    by_cases hz : z = 0
    · simp [hz] at h
    · obtain ⟨w, rfl⟩ : ∃ w, inclusion sdiff_subset w = z := ⟨puncture hz, rfl⟩
      exact ⟨w, rfl, incl_injective ((disc_inclusion i w).symm.trans h)⟩
  · rintro ⟨w, rfl, rfl⟩
    exact disc_inclusion i w

/-- The only added point on the `i`-th filled disc is its centre `center φ i`. -/
@[simp]
theorem disc_eq_center_iff {i j : ι} {z : 𝔻} : disc φ i z = center φ j ↔ z = 0 ∧ i = j := by
  constructor
  · intro h
    by_cases hz : z = 0
    · simpa [hz] using h
    · obtain ⟨w, rfl⟩ : ∃ w, inclusion sdiff_subset w = z := ⟨puncture hz, rfl⟩
      simp at h
  · rintro ⟨rfl, rfl⟩
    exact disc_zero i

/-- The `i`-th filled disc is injective when the punctured disc `φ i` is. -/
theorem disc_injective {i : ι} (hi : Function.Injective (φ i)) : Function.Injective (disc φ i) := by
  intro z z' h
  by_cases hz : z' = 0
  · rw [hz, disc_zero, disc_eq_center_iff] at h
    rw [h.1, hz]
  · obtain ⟨w', rfl⟩ : ∃ w, inclusion sdiff_subset w = z' := ⟨puncture hz, rfl⟩
    obtain ⟨w, rfl, hw⟩ := disc_eq_incl_iff.1 (h.trans (disc_inclusion i w'))
    rw [hi hw]

/-- A point of the `i`-th filled disc lies in `E` exactly when it is not the centre `0`. -/
@[simp]
theorem disc_preimage_range_incl (i : ι) : disc φ i ⁻¹' range (incl φ) = {0}ᶜ := by
  ext z
  by_cases hz : z = 0
  · simp [hz]
  · obtain ⟨w, rfl⟩ : ∃ w, inclusion sdiff_subset w = z := ⟨puncture hz, rfl⟩
    simp [hz]

/-- The points of the `i`-th filled disc which land in `incl φ '' V` are the points `w` of the
punctured disc with `φ i w ∈ V`. -/
theorem disc_preimage_image_incl (i : ι) (V : Set E) :
    disc φ i ⁻¹' (incl φ '' V) = inclusion sdiff_subset '' (φ i ⁻¹' V) := by
  ext z
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨w, rfl, rfl⟩ := disc_eq_incl_iff.1 h.symm
    exact ⟨w, hx, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨φ i w, hw, (disc_inclusion i w).symm⟩

/-- The points of `E` on the image of `W` under the `i`-th filled disc are the images under `φ i`
of the points of `W` other than the centre. -/
theorem incl_preimage_image_disc (i : ι) (W : Set 𝔻) :
    incl φ ⁻¹' (disc φ i '' W) = φ i '' (inclusion sdiff_subset ⁻¹' W) := by
  ext x
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨z, hz, h⟩
    obtain ⟨w, rfl, rfl⟩ := disc_eq_incl_iff.1 h
    exact ⟨w, hz, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, hw, disc_inclusion i w⟩

variable [TopologicalSpace E]

/-! ### The topology -/

instance : TopologicalSpace (PunctureFilling φ) :=
  .coinduced (incl φ) ‹_› ⊔ ⨆ i, .coinduced (disc φ i) inferInstance

/-- A subset of the puncture filling is open exactly when its preimages in `E` and in every filled
disc are open. -/
theorem isOpen_iff {s : Set (PunctureFilling φ)} :
    IsOpen s ↔ IsOpen (incl φ ⁻¹' s) ∧ ∀ i, IsOpen (disc φ i ⁻¹' s) :=
  isOpen_sup.trans (and_congr Iff.rfl isOpen_iSup_iff)

/-- **The universal property of the puncture filling.** A map out of the filling is continuous
exactly when its restrictions to `E` and to every filled disc are. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {g : PunctureFilling φ → Y} :
    Continuous g ↔ Continuous (g ∘ incl φ) ∧ ∀ i, Continuous (g ∘ disc φ i) :=
  continuous_sup_dom.trans <| and_congr continuous_coinduced_dom <|
    continuous_iSup_dom.trans <| forall_congr' fun _ => continuous_coinduced_dom

/-- The inclusion of `E` into its puncture filling is continuous. -/
@[fun_prop]
theorem continuous_incl : Continuous (incl φ) :=
  (continuous_iff.1 continuous_id).1

/-- Every filled disc is continuous. -/
@[fun_prop]
theorem continuous_disc (i : ι) : Continuous (disc φ i) :=
  (continuous_iff.1 continuous_id).2 i

/-- `E` is an open subset of its puncture filling. -/
theorem isOpen_range_incl : IsOpen (range (incl φ)) := by
  refine isOpen_iff.2 ⟨by simp, fun i => ?_⟩
  rw [disc_preimage_range_incl]
  exact isOpen_compl_singleton

/-- The added points form a closed subset of the puncture filling. -/
theorem isClosed_range_center : IsClosed (range (center φ)) := by
  rw [← isOpen_compl_iff, compl_range_center]
  exact isOpen_range_incl

/-- If the punctured discs `φ i` are continuous, `E` is an open subspace of its puncture
filling. -/
theorem isOpenEmbedding_incl (hφ : ∀ i, Continuous (φ i)) : IsOpenEmbedding (incl φ) := by
  refine .of_continuous_injective_isOpenMap continuous_incl incl_injective fun U hU =>
    isOpen_iff.2 ⟨by rwa [incl_injective.preimage_image], fun i => ?_⟩
  rw [disc_preimage_image_incl]
  exact (IsOpenEmbedding.inclusion _ <| (isOpen_ball.sdiff isClosed_singleton).preimage
    continuous_subtype_val).isOpenMap _ (hU.preimage (hφ i))

/-- If the punctured discs `φ j` are continuous and `φ i` is an open embedding, the `i`-th filled
disc is an open subspace of the puncture filling. -/
theorem isOpenEmbedding_disc (hφ : ∀ j, Continuous (φ j)) {i : ι} (hi : IsOpenEmbedding (φ i)) :
    IsOpenEmbedding (disc φ i) := by
  refine .of_continuous_injective_isOpenMap (continuous_disc i) (disc_injective hi.injective)
    fun W hW => ?_
  have hincl : IsOpen (incl φ ⁻¹' (disc φ i '' W)) := by
    rw [incl_preimage_image_disc]
    exact hi.isOpenMap _ (hW.preimage (continuous_inclusion _))
  refine isOpen_iff.2 ⟨hincl, fun k => ?_⟩
  by_cases hk : k = i
  · subst hk
    rwa [(disc_injective hi.injective).preimage_image]
  -- Off the centre, the `k`-th disc meets the `i`-th one only inside `E`.
  have h : disc φ k ⁻¹' (disc φ i '' W) =
      disc φ k ⁻¹' (incl φ '' (incl φ ⁻¹' (disc φ i '' W))) := by
    rw [image_preimage_eq_inter_range, preimage_inter, left_eq_inter]
    rintro z ⟨w, -, hw⟩
    rw [mem_preimage, ← mem_preimage, disc_preimage_range_incl, mem_compl_singleton_iff]
    rintro rfl
    rw [disc_zero, disc_eq_center_iff] at hw
    exact hk hw.2.symm
  rw [h, disc_preimage_image_incl]
  exact (IsOpenEmbedding.inclusion _ <| (isOpen_ball.sdiff isClosed_singleton).preimage
    continuous_subtype_val).isOpenMap _ (hincl.preimage (hφ k))

/-- `E` is dense in its puncture filling: every added point is a limit of points of `E`. -/
theorem denseRange_incl : DenseRange (incl φ) := by
  intro y
  induction y using PunctureFilling.induction with
  | incl x => exact subset_closure (mem_range_self x)
  | center i =>
    have h0 : (0 : 𝔻) ∈ closure ({0}ᶜ : Set 𝔻) := by
      rw [closure_subtype, mem_closure_iff_nhdsWithin_neBot]
      have : Subtype.val '' ({0}ᶜ : Set 𝔻) = ball (0 : ℂ) 1 ∩ {0}ᶜ := by
        ext z
        simp [and_comm]
      rw [this, unitBall.coe_zero,
        nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) one_pos))]
      infer_instance
    rw [← disc_zero]
    exact map_mem_closure (continuous_disc i) h0 fun z hz => by
      rwa [← mem_preimage, disc_preimage_range_incl]

/-! ### Neighbourhoods -/

/-- If the punctured discs are continuous, the neighbourhoods of a point of `E` in the puncture
filling are its neighbourhoods in `E`. -/
theorem nhds_incl (hφ : ∀ i, Continuous (φ i)) (x : E) :
    𝓝 (incl φ x) = map (incl φ) (𝓝 x) :=
  ((isOpenEmbedding_incl hφ).map_nhds_eq x).symm

/-- The neighbourhoods of the added point `center φ i` are those of the point itself together with
the image of the end of `φ i`, the filter of points `φ i w` with `w` near `0`. -/
theorem nhds_center (hφ : ∀ j, Continuous (φ j)) {i : ι} (hi : IsOpenEmbedding (φ i)) :
    𝓝 (center φ i) =
      pure (center φ i) ⊔ map (incl φ ∘ φ i) (comap ((↑) : 𝔻* → ℂ) (𝓝 0)) := by
  have hrange : range (inclusion (sdiff_subset : ball (0 : ℂ) 1 \ {0} ⊆ ball 0 1)) = {0}ᶜ := by
    ext z
    simp [range_inclusion, ← unitBall.coe_eq_zero]
  have hpunct : map (disc φ i) (𝓝[≠] 0) = map (incl φ ∘ φ i) (comap ((↑) : 𝔻* → ℂ) (𝓝 0)) := by
    rw [nhdsWithin, ← hrange, ← map_comap, map_map, nhds_subtype, comap_comap]
    exact congrArg₂ map (funext (disc_inclusion i)) rfl
  rw [← disc_zero, ← (isOpenEmbedding_disc hφ hi).map_nhds_eq, ← pure_sup_nhdsNE, map_sup,
    map_pure, hpunct]

/-- **The neighbourhoods of an added point.** The images under `disc φ i` of the discs of radius
`r > 0` form a basis of the neighbourhoods of `center φ i`. -/
theorem hasBasis_nhds_center (hφ : ∀ j, Continuous (φ j)) {i : ι} (hi : IsOpenEmbedding (φ i)) :
    (𝓝 (center φ i)).HasBasis (fun r : ℝ => 0 < r) fun r => disc φ i '' {z | ‖(z : ℂ)‖ < r} := by
  rw [← disc_zero, ← (isOpenEmbedding_disc hφ hi).map_nhds_eq]
  convert (nhds_basis_ball (x := (0 : 𝔻))).map (disc φ i) using 3 with r
  ext z
  simp [Subtype.dist_eq]

/-- **The added points are isolated from one another**: every set of added points is closed, as
each filled disc meets it at most in its centre. -/
theorem isDiscrete_range_center : IsDiscrete (range (center φ)) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro _ ⟨i, rfl⟩
  refine ⟨(center φ '' {i}ᶜ)ᶜ, isOpen_iff.2 ⟨?_, fun k => ?_⟩, ?_⟩
  · convert isOpen_univ
    ext x
    simp
  · rw [preimage_compl, isOpen_compl_iff]
    refine Set.Subsingleton.isClosed fun z hz z' hz' => ?_
    obtain ⟨j, -, hj⟩ := hz
    obtain ⟨j', -, hj'⟩ := hz'
    rw [(disc_eq_center_iff.1 hj.symm).1, (disc_eq_center_iff.1 hj'.symm).1]
  · ext y
    simp only [mem_inter_iff, mem_compl_iff, mem_image, mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨hy, j, rfl⟩
      by_contra hj
      exact hy ⟨j, fun h => hj (congrArg _ h), rfl⟩
    · rintro rfl
      exact ⟨fun ⟨j, hj, h⟩ => hj (center_injective h), i, rfl⟩

/-! ### Separation, compactness, connectedness and countability -/

/-- **The puncture filling is Hausdorff** when `E` is, the punctured discs are open embeddings, no
point of `E` is a limit of the end of a punctured disc, and the ends of two different punctured
discs are disjoint. -/
theorem t2Space [T2Space E] (hφ : ∀ i, IsOpenEmbedding (φ i))
    (hend : ∀ i x, Disjoint (𝓝 x) (map (φ i) (comap ((↑) : 𝔻* → ℂ) (𝓝 0))))
    (hdisj : Pairwise fun i j => Disjoint (map (φ i) (comap ((↑) : 𝔻* → ℂ) (𝓝 0)))
      (map (φ j) (comap ((↑) : 𝔻* → ℂ) (𝓝 0)))) :
    T2Space (PunctureFilling φ) := by
  have hc : ∀ i, Continuous (φ i) := fun i => (hφ i).continuous
  have hpure (i : ι) (F : Filter E) : Disjoint (pure (center φ i)) (map (incl φ) F) :=
    disjoint_of_disjoint_of_mem
      (disjoint_singleton_left.2 (by rintro ⟨x, hx⟩; exact incl_ne_center x i hx))
      (mem_pure.2 rfl) (range_mem_map)
  rw [t2Space_iff_disjoint_nhds]
  intro a b hab
  induction a using PunctureFilling.induction with
  | incl x =>
    induction b using PunctureFilling.induction with
    | incl y =>
      rw [nhds_incl hc, nhds_incl hc, disjoint_map incl_injective]
      exact disjoint_nhds_nhds.2 fun h => hab (congrArg _ h)
    | center j =>
      rw [nhds_incl hc, nhds_center hc (hφ j), disjoint_sup_right, ← map_map,
        disjoint_map incl_injective]
      exact ⟨(hpure j _).symm, hend j x⟩
  | center i =>
    induction b using PunctureFilling.induction with
    | incl y =>
      rw [nhds_incl hc, nhds_center hc (hφ i), disjoint_sup_left, ← map_map,
        disjoint_map incl_injective]
      exact ⟨hpure i _, (hend i y).symm⟩
    | center j =>
      have hij : i ≠ j := fun h => hab (congrArg _ h)
      rw [nhds_center hc (hφ i), nhds_center hc (hφ j), disjoint_sup_left, disjoint_sup_right,
        disjoint_sup_right, ← map_map, ← map_map, disjoint_map incl_injective]
      exact ⟨⟨disjoint_pure_pure.2 (center_injective.ne hij), hpure i _⟩, (hpure j _).symm,
        hdisj hij⟩

/-- **The puncture filling of finitely many punctures is compact** as soon as `E` minus the images
of the punctured discs of some radius `r < 1` is compact. -/
theorem compactSpace [Finite ι] {r : ℝ} (hr : r < 1)
    (hK : IsCompact (⋃ i, φ i '' {w | ‖(w : ℂ)‖ < r})ᶜ) : CompactSpace (PunctureFilling φ) := by
  have hdisc : IsCompact (((↑) : 𝔻 → ℂ) ⁻¹' closedBall 0 r) :=
    IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall 0 r)
      (Subtype.range_coe.symm ▸ closedBall_subset_ball hr)
  refine ⟨(((hK.image continuous_incl).union (finite_range (center φ)).isCompact).union
    (isCompact_iUnion fun i => hdisc.image (continuous_disc i))).of_isClosed_subset
    isClosed_univ fun y _ => ?_⟩
  induction y using PunctureFilling.induction with
  | incl x =>
    by_cases hx : x ∈ ⋃ i, φ i '' {w | ‖(w : ℂ)‖ < r}
    · obtain ⟨i, w, hw, rfl⟩ := mem_iUnion.1 hx
      exact Or.inr (mem_iUnion.2 ⟨i, inclusion sdiff_subset w, by simpa using hw.le,
        disc_inclusion i w⟩)
    · exact Or.inl (Or.inl (mem_image_of_mem _ hx))
  | center i => exact Or.inl (Or.inr (mem_range_self i))

/-- **The puncture filling of a connected space is connected**, since `E` is dense in it. -/
theorem connectedSpace [ConnectedSpace E] : ConnectedSpace (PunctureFilling φ) := by
  rw [connectedSpace_iff_univ, ← (denseRange_incl (φ := φ)).closure_range]
  exact (isConnected_range continuous_incl).closure

/-- **The puncture filling of a second-countable space along countably many punctured discs is
second countable.** -/
theorem secondCountableTopology [SecondCountableTopology E] [Countable ι]
    (hφ : ∀ i, IsOpenEmbedding (φ i)) : SecondCountableTopology (PunctureFilling φ) := by
  have hc : ∀ i, Continuous (φ i) := fun i => (hφ i).continuous
  let U : Option ι → Set (PunctureFilling φ) := fun o =>
    o.elim (range (incl φ)) fun i => range (disc φ i)
  have : ∀ o, SecondCountableTopology (U o) := by
    rintro (_ | i)
    · exact (isOpenEmbedding_incl hc).isEmbedding.toHomeomorph.symm.secondCountableTopology
    · exact (isOpenEmbedding_disc hc (hφ i)).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U) ?_ ?_
  · rintro (_ | i)
    · exact (isOpenEmbedding_incl hc).isOpen_range
    · exact (isOpenEmbedding_disc hc (hφ i)).isOpen_range
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    induction y using PunctureFilling.induction with
    | incl x => exact ⟨none, mem_range_self x⟩
    | center i => exact ⟨some i, 0, disc_zero i⟩

end PunctureFilling

end TauCeti
