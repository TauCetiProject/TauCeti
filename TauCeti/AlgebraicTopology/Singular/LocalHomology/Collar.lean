/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global

/-!
# The fundamental class of a manifold relative to a collared boundary

Let `X` be a compact Hausdorff space and `∂X = f(N)` the image of a map `f : N → X` with a collar
`c : N × [0, 1) → X` (`TauCeti.IsCollar`), and suppose that the complement `X ∖ ∂X` is the image
of an open embedding `j : M → X` of an oriented topological `n`-manifold `M`. This is how a
compact topological manifold with boundary, or with corners, sits over its interior: by Brown's
collaring theorem the boundary of a compact manifold with boundary is collared. The relative
homology `Hₖ(X, ∂X)` is the local homology `Hₖ(X, X ∖ (X ∖ ∂X))`, written
`localHomology R (range f)ᶜ k`.

The collar of depth `t ∈ (0, 1)`, the open set `c(N × [0, t))`, deformation retracts onto `∂X`
inside `X`: push every collar point down to depth `0` if it has depth below `t`, and damp the push
so that it is the identity beyond depth `(1 + t) / 2`. Hence the restriction
`Hₖ(X, ∂X) ⟶ Hₖ(X, c(N × [0, t)))` is an isomorphism
(`TauCeti.IsCollar.isIso_localHomologyRestriction`). Its target is local homology along the
compact set `Kₜ = X ∖ c(N × [0, t))`, which lies in the interior, so by excision it is the local
homology of `M` along the compact set `j⁻¹(Kₜ)`. Consequently `Hₖ(X, ∂X) = 0` for `k > n`
(`TauCeti.IsCollar.isZero_localHomology_compl_range`), and the fundamental class of `M` along
`j⁻¹(Kₜ)` gives a class of `Hₙ(X, ∂X; ℤ)`. It does not depend on `t`, and it is characterized by
its restrictions to the points of the interior.

This is the **fundamental class relative to the boundary**
(`TauCeti.HomologicalOrientation.relFundamentalClass`): the unique class of `Hₙ(X, ∂X; ℤ)` whose
image in `Hₙ(X, X ∖ {j x}; ℤ)` is the local orientation `o x`, read through excision, at every
point `x` of `M`. A fundamental chain of `X` relative to its boundary, such as the chains of
manifolds with corners whose boundaries are assembled from the fundamental chains of the faces, is
a relative cycle representing this class.

## Main definitions

* `TauCeti.HomologicalOrientation.relFundamentalClass`: the fundamental class `[X, ∂X]` of a
  compact space with collared boundary whose interior is an oriented manifold.

## Main results

* `TauCeti.IsCollar.isIso_localHomologyRestriction`: `Hₖ(X, ∂X) ≅ Hₖ(X, c(N × [0, t)))`.
* `TauCeti.IsCollar.isZero_localHomology_compl_range`: `Hₖ(X, ∂X) = 0` for `k` above the
  dimension of the interior.
* `TauCeti.HomologicalOrientation.localHomologyRestriction_relFundamentalClass`: the fundamental
  class restricts to the local orientation at every interior point.
* `TauCeti.HomologicalOrientation.eq_relFundamentalClass`: it is the only such class.
* `TauCeti.HomologicalOrientation.localHomologyRestriction_relFundamentalClass_eq_localHomologyMap`:
  away from the collar of depth `t` it is the fundamental class of `M` along `j⁻¹(Kₜ)`.
* `TauCeti.HomologicalOrientation.relFundamentalClass_neg`: reversing the orientation negates it.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.42 and the construction of the fundamental class of a compact
  manifold with boundary that follows it.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology
open scoped unitInterval

universe w v u

namespace TauCeti

/-! ### The depth deformation of a collar -/

section Deformation

/-- The depth of a collar point after time `τ` of the deformation onto the zero slice: a convex
combination of the original depth `u` and the target depth, which is `0` up to depth `t`, linear
from `t` to `(1 + t) / 2`, and `u` beyond. -/
private def depthPush (t τ u : ℝ) : ℝ :=
  (1 - τ) * u + τ * max 0 (min u ((u - t) * ((1 + t) / (1 - t))))

private theorem depthPush_nonneg {t τ u : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (hu : 0 ≤ u) :
    0 ≤ depthPush t τ u :=
  add_nonneg (mul_nonneg (by linarith [hτ.2]) hu) (mul_nonneg hτ.1 (le_max_left _ _))

private theorem depthPush_le {t τ u : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (hu : 0 ≤ u) :
    depthPush t τ u ≤ u := by
  have := mul_le_mul_of_nonneg_left (max_le hu (min_le_left u ((u - t) * ((1 + t) / (1 - t)))))
    hτ.1
  unfold depthPush
  linarith

private theorem depthPush_zero_left (t u : ℝ) : depthPush t 0 u = u := by
  simp [depthPush]

private theorem depthPush_zero_right (t τ : ℝ) : depthPush t τ 0 = 0 := by
  simp [depthPush]

private theorem depthPush_one_of_le {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ≤ t) :
    depthPush t 1 u = 0 := by
  have hk : 0 ≤ (1 + t) / (1 - t) := div_nonneg (by linarith [ht.1]) (by linarith [ht.2])
  have h : (u - t) * ((1 + t) / (1 - t)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hk
  simp [depthPush, max_eq_left ((min_le_right _ _).trans h)]

private theorem depthPush_of_le {t τ u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hu : (1 + t) / 2 ≤ u) :
    depthPush t τ u = u := by
  have h : u ≤ (u - t) * ((1 + t) / (1 - t)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by linarith [ht.2])]
    nlinarith [mul_le_mul_of_nonneg_left hu ht.1.le]
  have hu0 : 0 ≤ u := le_trans (by linarith [ht.1]) hu
  rw [depthPush, min_eq_left h, max_eq_right hu0]
  ring

private theorem continuous_depthPush (t : ℝ) : Continuous fun p : ℝ × ℝ ↦ depthPush t p.1 p.2 := by
  unfold depthPush
  fun_prop

variable {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

/-- The deformation of the collar parameters at time `τ`. -/
private def collarPush (t : ℝ) (τ : I) (p : N × Ico (0 : ℝ) 1) : N × Ico (0 : ℝ) 1 :=
  (p.1, ⟨depthPush t τ p.2, depthPush_nonneg τ.2 p.2.2.1,
    (depthPush_le τ.2 p.2.2.1).trans_lt p.2.2.2⟩)

private theorem continuous_collarPush (t : ℝ) :
    Continuous fun q : I × (N × Ico (0 : ℝ) 1) ↦ collarPush t q.1 q.2 :=
  (continuous_fst.comp continuous_snd).prodMk (((continuous_depthPush t).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).subtype_mk _)

open scoped Classical in
/-- The deformation of `X` pushing the collar of depth `t` onto its zero slice: on the collar it
is `collarPush`, and off the collar it is the identity. -/
private def collarDeformationFun (hc : IsCollar f c) (t : ℝ) (q : I × X) : X :=
  if h : q.2 ∈ range c then
    c (collarPush t q.1 (hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm ⟨q.2, h⟩))
  else q.2

private theorem collarDeformationFun_apply_collar (hc : IsCollar f c) (t : ℝ) (τ : I)
    (p : N × Ico (0 : ℝ) 1) : collarDeformationFun hc t (τ, c p) = c (collarPush t τ p) := by
  rw [collarDeformationFun, dite_eq_left (mem_range_self p),
    hc.isOpenEmbedding.isEmbedding.toHomeomorph_symm_apply]

private theorem collarDeformationFun_of_notMem (hc : IsCollar f c) (t : ℝ) (τ : I) {x : X}
    (hx : x ∉ range c) : collarDeformationFun hc t (τ, x) = x := by
  rw [collarDeformationFun, dite_eq_right hx]

private theorem collarDeformationFun_zero (hc : IsCollar f c) (t : ℝ) (x : X) :
    collarDeformationFun hc t (0, x) = x := by
  by_cases hx : x ∈ range c
  · obtain ⟨p, rfl⟩ := hx
    rw [collarDeformationFun_apply_collar]
    exact congrArg c (Prod.ext rfl (Subtype.ext (depthPush_zero_left t _)))
  · exact collarDeformationFun_of_notMem hc t 0 hx

/-- For a compact boundary, the collar points of depth at most `s < 1` form a closed set. -/
private theorem isClosed_image_le [CompactSpace N] [T2Space X] (hc : IsCollar f c) {s : ℝ}
    (hs : s < 1) : IsClosed (c '' {p | (p.2 : ℝ) ≤ s}) := by
  refine (IsCompact.image ?_ hc.isOpenEmbedding.continuous).isClosed
  have h : {p : N × Ico (0 : ℝ) 1 | (p.2 : ℝ) ≤ s} =
      univ ×ˢ ((↑) ⁻¹' Icc 0 s : Set (Ico (0 : ℝ) 1)) := by
    ext p
    simp [p.2.2.1]
  rw [h]
  refine isCompact_univ.prod ?_
  rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
    inter_eq_right.2 (Icc_subset_Ico_right hs)]
  exact isCompact_Icc

private theorem continuous_collarDeformationFun [CompactSpace N] [T2Space X] (hc : IsCollar f c)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : Continuous (collarDeformationFun hc t) := by
  have hslab := isClosed_image_le hc (s := (1 + t) / 2) (by linarith [ht.2])
  -- On the open collar the deformation is `c ∘ collarPush ∘ c⁻¹`; off the closed set of collar
  -- points of depth at most `(1 + t) / 2` it is the identity.
  refine continuous_of_cover_nhds (s := fun b : Bool ↦ bif b then univ ×ˢ range c
    else univ ×ˢ (c '' {p | (p.2 : ℝ) ≤ (1 + t) / 2})ᶜ) (fun q ↦ ?_) (fun b ↦ ?_)
  · by_cases hq : q.2 ∈ range c
    · exact ⟨true, (isOpen_univ.prod hc.isOpenEmbedding.isOpen_range).mem_nhds ⟨mem_univ _, hq⟩⟩
    · exact ⟨false, (isOpen_univ.prod hslab.isOpen_compl).mem_nhds
        ⟨mem_univ _, fun h ↦ hq (image_subset_range _ _ h)⟩⟩
  · cases b
    · refine continuous_snd.continuousOn.congr fun q hq ↦ ?_
      obtain ⟨τ, x⟩ := q
      by_cases hx : x ∈ range c
      · obtain ⟨p, rfl⟩ := hx
        have hp : (1 + t) / 2 < p.2 := not_le.1 fun hle ↦ hq.2 ⟨p, hle, rfl⟩
        rw [collarDeformationFun_apply_collar]
        exact congrArg c (Prod.ext rfl (Subtype.ext (depthPush_of_le ht hp.le)))
      · exact collarDeformationFun_of_notMem hc t τ hx
    · rw [Bool.cond_true, continuousOn_iff_continuous_domRestrict]
      have h : (univ ×ˢ range c).domRestrict (collarDeformationFun hc t) = fun q ↦
          c (collarPush t q.1.1 (hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm
            ⟨q.1.2, q.2.2⟩)) := by
        funext q
        exact dite_eq_left q.2.2
      rw [h]
      exact hc.isOpenEmbedding.continuous.comp ((continuous_collarPush t).comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          (hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm.continuous.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk _))))

/-- The end of the deformation: it carries the collar of depth `t` onto the zero slice. -/
private def collarRetraction [CompactSpace N] [T2Space X] (hc : IsCollar f c) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : C(X, X) :=
  ⟨fun x ↦ collarDeformationFun hc t (1, x),
    (continuous_collarDeformationFun hc ht).comp (by fun_prop)⟩

private theorem collarRetraction_apply [CompactSpace N] [T2Space X] (hc : IsCollar f c) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (x : X) :
    collarRetraction hc ht x = collarDeformationFun hc t (1, x) :=
  (rfl)

/-- The deformation of `X` onto the zero slice of the collar of depth `t`, as a homotopy. -/
private def collarHomotopy [CompactSpace N] [T2Space X] (hc : IsCollar f c) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : (ContinuousMap.id X).Homotopy (collarRetraction hc ht) where
  toFun := collarDeformationFun hc t
  continuous_toFun := continuous_collarDeformationFun hc ht
  map_zero_left := collarDeformationFun_zero hc t
  map_one_left _ := rfl

private theorem collarHomotopy_apply [CompactSpace N] [T2Space X] (hc : IsCollar f c) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (q : I × X) : collarHomotopy hc ht q = collarDeformationFun hc t q :=
  (rfl)

end Deformation

/-! ### Local homology relative to a collared boundary -/

section Collar

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {X : Type w} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

/-- The boundary lies in the collar of every positive depth. -/
theorem IsCollar.range_subset_image_lt (hc : IsCollar f c) {t : ℝ} (ht : 0 < t) :
    range f ⊆ c '' {p | (p.2 : ℝ) < t} := by
  rintro _ ⟨b, rfl⟩
  exact ⟨(b, ⟨0, by norm_num⟩), ht, hc.apply_zero b⟩

omit [TopologicalSpace X] [TopologicalSpace N] in
/-- The collar of depth `t` grows with `t`. -/
private theorem compl_image_lt_subset_compl_image_lt {s t : ℝ} (hst : s ≤ t) :
    (c '' {p | (p.2 : ℝ) < t})ᶜ ⊆ (c '' {p | (p.2 : ℝ) < s})ᶜ :=
  compl_subset_compl.2 (image_mono fun _ hp ↦ lt_of_lt_of_le hp hst)

/-- The collar of depth `t` is open. -/
theorem IsCollar.isOpen_image_lt (hc : IsCollar f c) (t : ℝ) :
    IsOpen (c '' {p | (p.2 : ℝ) < t}) :=
  hc.isOpenEmbedding.isOpenMap _ (isOpen_lt (by fun_prop) continuous_const)

/-- **A collar deformation retracts onto the boundary.** For a compact boundary `∂X = f(N)` with
a collar `c` in a Hausdorff space `X`, and `0 < t < 1`, the restriction
`Hₖ(X, ∂X) ⟶ Hₖ(X, c(N × [0, t)))` is an isomorphism. Here `Hₖ(X, ∂X)` is the local homology of
`X` along `X ∖ ∂X`, and `Hₖ(X, c(N × [0, t)))` its local homology along the complement of the
collar of depth `t`. -/
theorem IsCollar.isIso_localHomologyRestriction [T2Space X] [CompactSpace N] (hc : IsCollar f c)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    IsIso (localHomologyRestriction R
      (compl_subset_compl.2 (hc.range_subset_image_lt ht.1)) k) := by
  rw [localHomologyRestriction_def]
  refine TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy _
    (ρ := TopCat.ofHom (collarRetraction hc ht)) (collarHomotopy hc ht) ?_ ?_ ?_ R k
  · -- The deformation fixes the zero slice.
    rintro τ x hx
    rw [compl_compl] at hx ⊢
    obtain ⟨b, rfl⟩ := hx
    rw [collarHomotopy_apply, ← hc.apply_zero, collarDeformationFun_apply_collar]
    exact ⟨b, (hc.apply_zero b).symm.trans
      (congrArg c (Prod.ext rfl (Subtype.ext (depthPush_zero_right t τ).symm)))⟩
  · -- The deformation does not increase depths.
    rintro τ x hx
    rw [compl_compl] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    rw [collarHomotopy_apply, collarDeformationFun_apply_collar]
    exact ⟨_, (depthPush_le τ.2 p.2.2.1).trans_lt hp, rfl⟩
  · -- At the end, the collar of depth `t` lands in the zero slice.
    rintro x hx
    rw [compl_compl] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    rw [TopCat.ofHom_apply, collarRetraction_apply, collarDeformationFun_apply_collar]
    exact ⟨p.1, (hc.apply_zero p.1).symm.trans
      (congrArg c (Prod.ext rfl (Subtype.ext (depthPush_one_of_le ht (le_of_lt hp)).symm)))⟩

end Collar

section Interior

variable {M X N : Type} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace N]
  {j : M → X} {f : N → X} {c : N × Ico (0 : ℝ) 1 → X}

/-- The boundary of a compact space with a collared boundary and open interior is compact. -/
private theorem compactSpace_of_isCollar [CompactSpace X] (hj : IsOpenEmbedding j)
    (hc : IsCollar f c) (hjf : range j = (range f)ᶜ) : CompactSpace N :=
  IsClosedEmbedding.compactSpace ⟨hc.isEmbedding, by
    rw [← compl_compl (range f), ← hjf]
    exact hj.isOpen_range.isClosed_compl⟩

omit [TopologicalSpace M] in
/-- The complement of the collar of positive depth lies in the interior. -/
theorem IsCollar.compl_image_lt_subset_range (hc : IsCollar f c) (hjf : range j = (range f)ᶜ)
    {t : ℝ} (ht : 0 < t) : (c '' {p | (p.2 : ℝ) < t})ᶜ ⊆ range j :=
  hjf ▸ compl_subset_compl.2 (hc.range_subset_image_lt ht)

/-- The part of the interior outside the collar of positive depth is compact. -/
theorem IsCollar.isCompact_preimage_compl_image_lt [CompactSpace X] (hc : IsCollar f c)
    (hj : IsOpenEmbedding j) (hjf : range j = (range f)ᶜ) {t : ℝ} (ht : 0 < t) :
    IsCompact (j ⁻¹' (c '' {p | (p.2 : ℝ) < t})ᶜ) :=
  (hj.isInducing.isCompact_preimage_iff (hc.compl_image_lt_subset_range hjf ht)).2
    (hc.isOpen_image_lt t).isClosed_compl.isCompact

/-- The excision isomorphism from the local homology of `M` along `j⁻¹(Kₜ)` to the local homology
of `X` along `Kₜ`. -/
private theorem isIso_localHomologyMap_compl_image_lt {B : Type} [Ring B] (R : ModuleCat.{0} B)
    (hj : IsOpenEmbedding j) (hc : IsCollar f c) (hjf : range j = (range f)ᶜ) {t : ℝ}
    (ht : 0 < t) (k : ℕ) :
    IsIso (localHomologyMap R ⟨j, hj.continuous⟩
      (subset_refl (j ⁻¹' (c '' {p | (p.2 : ℝ) < t})ᶜ)) k) :=
  isIso_localHomologyMap R ⟨j, hj.continuous⟩ hj rfl (hc.isOpen_image_lt t).isClosed_compl
    (hc.compl_image_lt_subset_range hjf ht) k

/-- **The relative homology of a compact space with collared boundary vanishes above the
dimension of its interior**: `Hₖ(X, ∂X) = 0` for `k > n`, if `X ∖ ∂X` is a manifold of
dimension `n`. -/
theorem IsCollar.isZero_localHomology_compl_range [CompactSpace X] [T2Space X]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {B : Type} [Ring B] (R : ModuleCat.{0} B) {n : ℕ} (hn : finrank ℝ E = n) (hc : IsCollar f c)
    (hj : IsOpenEmbedding j) (hjf : range j = (range f)ᶜ) {k : ℕ} (hk : n < k) :
    IsZero (localHomology R (range f)ᶜ k) := by
  have := hj.isEmbedding.t2Space
  have := compactSpace_of_isCollar hj hc hjf
  have ht : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have := hc.isIso_localHomologyRestriction R ht k
  have := isIso_localHomologyMap_compl_image_lt R hj hc hjf ht.1 k
  exact (isZero_localHomology_of_isCompact R hn
    (hc.isCompact_preimage_compl_image_lt hj hjf ht.1) hk).of_iso
    (asIso (localHomologyRestriction R _ k) ≪≫ (asIso (localHomologyMap R ⟨j, hj.continuous⟩
      (subset_refl (j ⁻¹' (c '' {p | (p.2 : ℝ) < 1 / 2})ᶜ)) k)).symm)

omit [TopologicalSpace M] in
/-- Every point of `M` lies outside the collar of some positive depth below `t`. -/
private theorem exists_mem_compl_image_lt (hc : IsCollar f c) (hjf : range j = (range f)ᶜ)
    (x : M) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ s ∈ Ioo (0 : ℝ) 1, s ≤ t ∧ j x ∈ (c '' {p | (p.2 : ℝ) < s})ᶜ := by
  by_cases hx : j x ∈ range c
  · obtain ⟨p, hp⟩ := hx
    -- The depth of `j x` is positive, since `j x` is not on the boundary.
    have hp0 : 0 < (p.2 : ℝ) := by
      refine lt_of_le_of_ne p.2.2.1 fun h0 ↦ ?_
      have hjx : j x ∈ range f := ⟨p.1, by
        rw [← hp, ← hc.apply_zero]
        exact congrArg c (Prod.ext rfl (Subtype.ext h0))⟩
      exact (hjf ▸ mem_range_self x : j x ∈ (range f)ᶜ) hjx
    refine ⟨min p.2 t, ⟨lt_min hp0 ht.1, (min_le_right _ _).trans_lt ht.2⟩, min_le_right _ _,
      ?_⟩
    rintro ⟨q, hq, hqx⟩
    rw [← hp] at hqx
    have := hc.isOpenEmbedding.injective hqx
    subst this
    have hq' : (q.2 : ℝ) < min (q.2 : ℝ) t := hq
    exact (lt_irrefl _) (lt_of_lt_of_le hq' (min_le_left _ _))
  · exact ⟨t, ht, le_rfl, fun h ↦ hx (image_subset_range _ _ h)⟩

namespace HomologicalOrientation

variable [CompactSpace X] [T2Space X] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (hj : IsOpenEmbedding j)
  (hc : IsCollar f c) (hjf : range j = (range f)ᶜ)

/-- The class of `Hₙ(X, ∂X; ℤ)` restricting, away from the collar of depth `t`, to the image of
the fundamental class of `M` along `j⁻¹(Kₜ)`. -/
private def relFundamentalClassOf {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range f)ᶜ n :=
  have := compactSpace_of_isCollar hj hc hjf
  have := hc.isIso_localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) ht n
  inv (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (compl_subset_compl.2 (hc.range_subset_image_lt ht.1)) n)
    (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ (subset_refl _) n
      (o.fundamentalClassOn hn (hc.isCompact_preimage_compl_image_lt hj hjf ht.1)))

private theorem localHomologyRestriction_compl_image_lt_relFundamentalClassOf {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (compl_subset_compl.2 (hc.range_subset_image_lt ht.1)) n
        (o.relFundamentalClassOf hn hj hc hjf ht) =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ (subset_refl _) n
        (o.fundamentalClassOn hn (hc.isCompact_preimage_compl_image_lt hj hjf ht.1)) := by
  have := compactSpace_of_isCollar hj hc hjf
  have := hc.isIso_localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) ht n
  exact IsIso.inv_hom_id_apply _ _

omit [CompactSpace X] [T2Space M] in
/-- Restricting to a point and then mapping along `j` is mapping along `j` and then restricting
to the image point. -/
private theorem localHomologyIsoOfIsOpenEmbedding_hom_localHomologyRestriction {S : Set M}
    {T : Set X} (h : j ⁻¹' T ⊆ S) {y : M} (hyS : y ∈ S) (hyT : j y ∈ T)
    (α : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) S n) :
    (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj y n).hom
        (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hyS) n
          α) =
      localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hyT) n
        (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ h n α) := by
  rw [localHomologyIsoOfIsOpenEmbedding_hom, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, localHomologyRestriction_comp_localHomologyMap,
    localHomologyMap_comp_localHomologyRestriction]

include hj hc hjf in
/-- At the points of `Kₜ`, the class `relFundamentalClassOf` restricts to the local orientation. -/
private theorem localHomologyRestriction_relFundamentalClassOf_of_mem {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {x : M} (hx : j x ∈ (c '' {p | (p.2 : ℝ) < t})ᶜ) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (hjf ▸ mem_range_self x : j x ∈ (range f)ᶜ)) n
        (o.relFundamentalClassOf hn hj hc hjf ht) =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj x n).hom (o x).val := by
  refine (localHomologyRestriction_comp_apply _ (singleton_subset_iff.2 hx)
    (compl_subset_compl.2 (hc.range_subset_image_lt ht.1)) n _).symm.trans ?_
  rw [localHomologyRestriction_compl_image_lt_relFundamentalClassOf,
    ← o.localHomologyRestriction_fundamentalClassOn hn
      (hc.isCompact_preimage_compl_image_lt hj hjf ht.1) (mem_preimage.2 hx),
    localHomologyIsoOfIsOpenEmbedding_hom_localHomologyRestriction hj (subset_refl _)
      (mem_preimage.2 hx) hx]

include hn hj hc hjf in
/-- A class of `Hₙ(X, ∂X; ℤ)` is determined by its restrictions to the points of `Kₜ`. -/
private theorem ext_of_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {μ ν : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range f)ᶜ n}
    (h : ∀ (x : M) (hx : j x ∈ (c '' {p | (p.2 : ℝ) < t})ᶜ),
      localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
          (singleton_subset_iff.2 (compl_subset_compl.2 (hc.range_subset_image_lt ht.1) hx)) n
          μ =
        localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
          (singleton_subset_iff.2 (compl_subset_compl.2 (hc.range_subset_image_lt ht.1) hx)) n
          ν) :
    μ = ν := by
  have := compactSpace_of_isCollar hj hc hjf
  have := hc.isIso_localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) ht n
  have := isIso_localHomologyMap_compl_image_lt (ModuleCat.of ℤ (ULift.{0} ℤ)) hj hc hjf ht.1 n
  set ρ := localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
    (compl_subset_compl.2 (hc.range_subset_image_lt ht.1)) n
  set G := localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩
    (subset_refl (j ⁻¹' (c '' {p | (p.2 : ℝ) < t})ᶜ)) n
  -- Pull both classes back to the local homology of `M` along `j⁻¹(Kₜ)`, where classes are
  -- detected at points, and compare the restrictions there through excision at each point.
  suffices hG : inv G (ρ μ) = inv G (ρ ν) by
    have h' := congrArg (inv ρ) (congrArg G hG)
    simpa only [IsIso.inv_hom_id_apply, IsIso.hom_inv_id_apply] using h'
  refine localHomology_ext_of_isCompact (ModuleCat.of ℤ (ULift.{0} ℤ)) hn
    (hc.isCompact_preimage_compl_image_lt hj hjf ht.1) fun y hy ↦
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj y n).toLinearEquiv
        |>.injective ?_
  simp only [Iso.toLinearEquiv_apply]
  rw [localHomologyIsoOfIsOpenEmbedding_hom_localHomologyRestriction hj (subset_refl _) hy
      (mem_preimage.1 hy),
    localHomologyIsoOfIsOpenEmbedding_hom_localHomologyRestriction hj (subset_refl _) hy
      (mem_preimage.1 hy),
    IsIso.inv_hom_id_apply, IsIso.inv_hom_id_apply, localHomologyRestriction_comp_apply,
    localHomologyRestriction_comp_apply]
  exact h y hy

/-- At every point of `M`, the class `relFundamentalClassOf` restricts to the local orientation:
it does not depend on the depth `t`. -/
private theorem localHomologyRestriction_relFundamentalClassOf {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (x : M) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (hjf ▸ mem_range_self x : j x ∈ (range f)ᶜ)) n
        (o.relFundamentalClassOf hn hj hc hjf ht) =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj x n).hom (o x).val := by
  obtain ⟨s, hs, hst, hx⟩ := exists_mem_compl_image_lt hc hjf x ht
  -- The classes of depths `t` and `s` agree at the points of `Kₜ ⊆ Kₛ`, hence everywhere.
  have hts : o.relFundamentalClassOf hn hj hc hjf ht = o.relFundamentalClassOf hn hj hc hjf hs :=
    ext_of_mem hn hj hc hjf ht fun y hy ↦ by
      rw [o.localHomologyRestriction_relFundamentalClassOf_of_mem hn hj hc hjf ht hy,
        o.localHomologyRestriction_relFundamentalClassOf_of_mem hn hj hc hjf hs
          (compl_image_lt_subset_compl_image_lt hst hy)]
  rw [hts, o.localHomologyRestriction_relFundamentalClassOf_of_mem hn hj hc hjf hs hx]

include hn hj hc hjf in
private theorem existsUnique_relFundamentalClass :
    ∃! μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range f)ᶜ n,
      ∀ x : M, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
          (singleton_subset_iff.2 (hjf ▸ mem_range_self x : j x ∈ (range f)ᶜ)) n μ =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj x n).hom
          (o x).val := by
  have ht : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  refine ⟨o.relFundamentalClassOf hn hj hc hjf ht,
    o.localHomologyRestriction_relFundamentalClassOf hn hj hc hjf ht, fun μ hμ ↦ ?_⟩
  exact ext_of_mem hn hj hc hjf ht fun x _ ↦ by
    rw [hμ x, o.localHomologyRestriction_relFundamentalClassOf hn hj hc hjf ht x]

/-- **The fundamental class relative to the boundary.** Let `X` be a compact Hausdorff space whose
boundary `∂X = f(N)` has a collar `c`, and whose interior `X ∖ ∂X` is the image of an open
embedding `j` of a manifold `M` oriented by `o`. The fundamental class `[X, ∂X]` is the unique
class of `Hₙ(X, ∂X; ℤ)`, the local homology of `X` along `X ∖ ∂X`, whose restriction to
`Hₙ(X, X ∖ {j x}; ℤ)` is the local orientation `o x`, read through excision, at every `x ∈ M`. -/
def relFundamentalClass :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range f)ᶜ n :=
  (o.existsUnique_relFundamentalClass hn hj hc hjf).exists.choose

/-- The fundamental class relative to the boundary restricts to the local orientation at every
point of the interior. -/
theorem localHomologyRestriction_relFundamentalClass (x : M) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (hjf ▸ mem_range_self x : j x ∈ (range f)ᶜ)) n
        (o.relFundamentalClass hn hj hc hjf) =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj x n).hom (o x).val :=
  (o.existsUnique_relFundamentalClass hn hj hc hjf).exists.choose_spec x

/-- **Uniqueness of the fundamental class relative to the boundary**: a class of
`Hₙ(X, ∂X; ℤ)` restricting to the local orientation at every point of the interior is the
fundamental class. -/
theorem eq_relFundamentalClass
    {μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range f)ᶜ n}
    (hμ : ∀ x : M, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (hjf ▸ mem_range_self x : j x ∈ (range f)ᶜ)) n μ =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj x n).hom (o x).val) :
    μ = o.relFundamentalClass hn hj hc hjf :=
  (o.existsUnique_relFundamentalClass hn hj hc hjf).unique hμ
    (o.localHomologyRestriction_relFundamentalClass hn hj hc hjf)

/-- Away from the collar of depth `t`, the fundamental class relative to the boundary is the
fundamental class of the interior: its restriction to the local homology of `X` along
`Kₜ = X ∖ c(N × [0, t))` is the image under `j` of the fundamental class of `M` along
`j⁻¹(Kₜ)`. -/
theorem localHomologyRestriction_relFundamentalClass_eq_localHomologyMap {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (compl_subset_compl.2 (hc.range_subset_image_lt ht.1)) n
        (o.relFundamentalClass hn hj hc hjf) =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ (subset_refl _) n
        (o.fundamentalClassOn hn (hc.isCompact_preimage_compl_image_lt hj hjf ht.1)) := by
  rw [← o.eq_relFundamentalClass hn hj hc hjf
    (o.localHomologyRestriction_relFundamentalClassOf hn hj hc hjf ht)]
  exact o.localHomologyRestriction_compl_image_lt_relFundamentalClassOf hn hj hc hjf ht

/-- Reversing the orientation negates the fundamental class relative to the boundary. -/
@[simp]
theorem relFundamentalClass_neg :
    (-o).relFundamentalClass hn hj hc hjf = -o.relFundamentalClass hn hj hc hjf := by
  refine ((-o).eq_relFundamentalClass hn hj hc hjf fun x ↦ ?_).symm
  rw [map_neg, o.localHomologyRestriction_relFundamentalClass hn hj hc hjf x, neg_apply,
    LocalOrientation.coe_neg, map_neg]

end HomologicalOrientation

end Interior

end TauCeti
