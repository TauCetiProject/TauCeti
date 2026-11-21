/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The complement of a bounded star-convex set retracts onto a sphere

Let `K` be a subset of a real normed space which contains a point `p`, is star-convex about `p`,
and lies in the open ball `ball p r`. Then the complement `Kᶜ` deformation retracts onto the
sphere `sphere p r`. The retraction is the radial projection `z ↦ p + (r / ‖z - p‖) • (z - p)`,
and the homotopy is the straight line from it to the identity. Every point of such a segment has
the form `p + c • (z - p)` where `c` lies between `1` and `r / ‖z - p‖`. If `c ≥ 1`, the point
`z` lies on the segment from `p` to `p + c • (z - p)`, so star-convexity keeps the latter out of
`K`; if `c ≤ 1`, then `c ≥ r / ‖z - p‖` puts it outside `ball p r`.

In particular the complements of `K` and of `{p}` have the same homotopy type: this is the input
for comparing the relative homology groups `H(X, X ∖ K)` and `H(X, X ∖ {p})` in the local
homology of manifolds.

The same comparison holds inside a set `S` closed under outward radial moves from `p`, that is
with `p + c • (z - p) ∈ S` for `z ∈ S` and `c ≥ 1`, such as a closed half-space whose boundary
hyperplane contains `p`. There the radial projection may leave `S`, so `S \ K` is compared with
`S \ {p}` directly, by the outward push `z ↦ p + max 1 (r / ‖z - p‖) • (z - p)`, which moves
points only away from `p`. For a closed half-space `{x | 0 ≤ f x}` with `f ≠ 0` and `p` on its
boundary, the punctured half-space is star-convex about any interior point, so the complement of
`K` in the half-space is contractible. This is the local model at boundary points of manifolds
with boundary.

## Main declarations

* `StarConvex.complSphereHomotopyEquiv`: the inclusion `sphere p r → Kᶜ` as a homotopy
  equivalence, with the radial projection as homotopy inverse
  (`StarConvex.coe_complSphereHomotopyEquiv_apply`,
  `StarConvex.coe_complSphereHomotopyEquiv_symm_apply`).
* `StarConvex.complRadialHomotopy`: the straight-line deformation from the radial projection to
  the identity of `Kᶜ`.
* `StarConvex.ofHom_complSphereHomotopyEquiv_comp_snd`: the sphere inclusion into `Kᶜ`, followed
  by the subspace map of the pair map `(E, Kᶜ) ⟶ (E, {p}ᶜ)`, is the sphere inclusion into `{p}ᶜ`.
* `StarConvex.diffHomotopyEquivDiffSingleton`: inside a set `S` closed under outward radial moves
  from `p`, the inclusion `S \ K → S \ {p}` as a homotopy equivalence.
* `StarConvex.contractibleSpace_halfSpace_diff`: the complement of `K` in a closed half-space
  whose boundary contains `p` is contractible.

## References

The radial deformation retraction is the standard one; compare Hatcher, *Algebraic Topology*,
Chapter 0, where `ℝⁿ ∖ {0}` is deformation retracted onto the unit sphere by the same formula.

The construction follows the companion construction for punctured star-convex sets in
`TauCeti.Topology.Homotopy.PuncturedStarConvex`, whose `StarConvex.sphereHomotopyEquiv` retracts
`V ∖ {p}` onto a sphere inside `V`; here the sphere lies outside `K` instead, and the radial
projection is the restriction of `TauCeti.radialProjectionToSphere`.
-/

public section

noncomputable section

open CategoryTheory Metric Set unitInterval

namespace StarConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {p : E} {r : ℝ}

/-- A point `p + c • (z - p)` with `z ∉ K` stays outside `K` when `c ≥ 1`, by
star-convexity of `K` about `p`, or when `c ≥ r / ‖z - p‖`, since it then lies outside
`ball p r ⊇ K` provided `z ≠ p`. -/
theorem add_smul_sub_mem_compl (hK : StarConvex ℝ p K) (hKr : K ⊆ ball p r) {z : E}
    (hz : z ∉ K) {c : ℝ} (hc : 1 ≤ c ∨ (r / ‖z - p‖ ≤ c ∧ z ≠ p)) : p + c • (z - p) ∉ K := by
  intro h
  rcases hc with hc | ⟨hc, hzp⟩
  · -- `z` lies on the segment from `p` to `p + c • (z - p)`.
    have hmem := hK.add_smul_sub_mem h (t := c⁻¹) (by positivity) (inv_le_one_of_one_le₀ hc)
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (by positivity), one_smul,
      add_sub_cancel] at hmem
    exact hz hmem
  · have hd : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
    have hr : r ≤ c * ‖z - p‖ := (div_le_iff₀ hd).mp hc
    have hlt := hKr h
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hlt
    exact (le_abs_self c |> (mul_le_mul_of_nonneg_right · hd.le) |> hr.trans |>
      not_lt.mpr) hlt

open TauCeti

/-- The straight-line homotopy from the radial projection onto `sphere p r` to the identity of
`Kᶜ`, for `K` star-convex about `p ∈ K` and contained in `ball p r`. -/
def complRadialHomotopy (hK : StarConvex ℝ p K) (hp : p ∈ K) (hKr : K ⊆ ball p r) :
    ((ContinuousMap.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right).comp
      (complRadialProjection hp (pos_of_mem_ball (hKr hp)))).Homotopy (ContinuousMap.id ↥Kᶜ) where
  toFun x := ⟨p + ((1 - (x.1 : ℝ)) * (r / ‖(x.2 : E) - p‖) + x.1) • ((x.2 : E) - p), by
    have hzp : (x.2 : E) ≠ p := (ne_of_mem_of_not_mem hp x.2.property).symm
    have ht₀ : 0 ≤ (x.1 : ℝ) := x.1.property.1
    have ht₁ : (x.1 : ℝ) ≤ 1 := x.1.property.2
    refine hK.add_smul_sub_mem_compl hKr x.2.property ?_
    rcases le_total 1 (r / ‖(x.2 : E) - p‖) with h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr ⟨by nlinarith, hzp⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hsub : Continuous fun x : I × ↥Kᶜ ↦ (x.2 : E) - p :=
      (continuous_subtypeVal.comp continuous_snd).sub continuous_const
    have ht : Continuous fun x : I × ↥Kᶜ ↦ (x.1 : ℝ) :=
      continuous_subtypeVal.comp continuous_fst
    have hdiv : Continuous fun x : I × ↥Kᶜ ↦ r / ‖(x.2 : E) - p‖ :=
      continuous_const.div hsub.norm fun x ↦
        norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ne_of_mem_of_not_mem hp x.2.property).symm)
    exact continuous_const.add ((((continuous_const.sub ht).mul hdiv).add ht).smul hsub)
  map_zero_left z := by
    ext
    simp
  map_one_left z := by
    ext
    simp

/-- The radial deformation of `Kᶜ` has the stated pointwise straight-line formula. -/
@[simp]
theorem coe_complRadialHomotopy_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (t : I) (z : ↥Kᶜ) :
    ((hK.complRadialHomotopy hp hKr (t, z) : ↥Kᶜ) : E) =
      p + ((1 - (t : ℝ)) * (r / ‖(z : E) - p‖) + t) • ((z : E) - p) :=
  (rfl)

/-- The radial deformation of `Kᶜ` fixes every included point of the sphere throughout the
homotopy. -/
@[simp]
theorem complRadialHomotopy_apply_inclusion (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (t : I) (x : sphere p r) :
    hK.complRadialHomotopy hp hKr
        (t, Set.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right x) =
      Set.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right x := by
  ext
  have hx : ‖(x : E) - p‖ = r := by simpa [dist_eq_norm] using x.property
  simp [hx, div_self (pos_of_mem_ball (hKr hp)).ne']

/-- **The complement of a bounded star-convex set is homotopy equivalent to a sphere.** If `K`
contains `p`, is star-convex about `p` and lies in `ball p r`, then the inclusion
`sphere p r → Kᶜ` is a homotopy equivalence; its homotopy inverse is the radial projection
`z ↦ p + (r / ‖z - p‖) • (z - p)`. -/
def complSphereHomotopyEquiv (hK : StarConvex ℝ p K) (hp : p ∈ K) (hKr : K ⊆ ball p r) :
    ContinuousMap.HomotopyEquiv (sphere p r) ↥Kᶜ where
  toFun := ContinuousMap.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right
  invFun := complRadialProjection hp (pos_of_mem_ball (hKr hp))
  left_inv := by
    -- The radial projection fixes the sphere pointwise.
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (sphere p r))
    ext x
    have hx : ‖(x : E) - p‖ = r := by simpa [dist_eq_norm] using x.property
    simp [hx, div_self (pos_of_mem_ball (hKr hp)).ne']
  right_inv := ⟨hK.complRadialHomotopy hp hKr⟩

/-- The homotopy equivalence `StarConvex.complSphereHomotopyEquiv` is the inclusion of the
sphere. -/
@[simp]
theorem coe_complSphereHomotopyEquiv_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (x : sphere p r) :
    (hK.complSphereHomotopyEquiv hp hKr x : E) = x :=
  (rfl)

/-- The homotopy inverse of `StarConvex.complSphereHomotopyEquiv` is the radial projection onto
the sphere. -/
@[simp]
theorem coe_complSphereHomotopyEquiv_symm_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (z : ↥Kᶜ) :
    ((hK.complSphereHomotopyEquiv hp hKr).symm z : E) =
      p + (r / ‖(z : E) - p‖) • ((z : E) - p) :=
  coe_complRadialProjection_apply hp (pos_of_mem_ball (hKr hp)) z

/-- The sphere inclusion `sphere p r → E ∖ K` of `StarConvex.complSphereHomotopyEquiv`, followed by
the inclusion `E ∖ K ⊆ E ∖ {p}`, is the sphere inclusion `sphere p r → E ∖ {p}`. This identifies
the subspace map of `(E, E ∖ K) ⟶ (E, E ∖ {p})` up to two homotopy equivalences. -/
theorem ofHom_complSphereHomotopyEquiv_comp_snd (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) :
    (TopCat.ofHom (hK.complSphereHomotopyEquiv hp hKr).toFun :
        TopCat.of (sphere p r) ⟶ (TopPair.ofSubset (Kᶜ : Set (TopCat.of E))).snd) ≫
      TopPair.Hom.snd (TopPair.ofSubsetMap (𝟙 (TopCat.of E)) (B := Kᶜ) (B' := {p}ᶜ)
        (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hp))) =
      TopCat.ofHom ((starConvex_singleton p).complSphereHomotopyEquiv rfl
        (Set.singleton_subset_iff.2 (hKr hp))).toFun := by
  ext z
  exact Subtype.ext <| (TopPair.ofSubsetMap_snd_apply _ _ _).trans <|
    (hK.coe_complSphereHomotopyEquiv_apply hp hKr z).trans
      ((starConvex_singleton p).coe_complSphereHomotopyEquiv_apply rfl
        (Set.singleton_subset_iff.2 (hKr hp)) z).symm

end StarConvex

/-! ### Complements inside sets closed under outward radial moves -/

namespace StarConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K S T : Set E} {p : E} {r : ℝ}

open TauCeti

omit [NormedSpace ℝ E] in
/-- The scale factor `max 1 (r / ‖g x - p‖)` of the outward radial push is continuous along a
continuous map `g` avoiding `p`. -/
private lemma continuous_max_one_div_norm_sub {X : Type*} [TopologicalSpace X] {g : X → E}
    (hg : Continuous g) (hgp : ∀ x, g x ≠ p) (r : ℝ) :
    Continuous fun x ↦ max 1 (r / ‖g x - p‖) :=
  continuous_const.max (continuous_const.div (hg.sub continuous_const).norm fun x ↦
    norm_ne_zero_iff.2 (sub_ne_zero.2 (hgp x)))

/-- The outward radial push `z ↦ p + max 1 (r / ‖z - p‖) • (z - p)` of a set `T` not containing
`p` and closed under moving its points away from `p` along rays from `p`. It moves every point of
`T` to distance at least `r` from `p`. -/
private def outwardPush (hpT : p ∉ T) (hT : ∀ z ∈ T, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ T)
    (r : ℝ) : C(T, T) where
  toFun z := ⟨p + max 1 (r / ‖(z : E) - p‖) • ((z : E) - p), hT _ z.property _ (le_max_left _ _)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_const.add (Continuous.smul ?_
      (continuous_subtypeVal.sub continuous_const))) _
    exact continuous_max_one_div_norm_sub continuous_subtypeVal
      (fun z ↦ ne_of_mem_of_not_mem z.property hpT) r

/-- The value of the outward radial push. -/
private lemma coe_outwardPush_apply (hpT : p ∉ T)
    (hT : ∀ z ∈ T, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ T) (r : ℝ) (z : T) :
    (outwardPush hpT hT r z : E) = p + max 1 (r / ‖(z : E) - p‖) • ((z : E) - p) :=
  rfl

/-- A set `S` closed under outward radial moves from `p` stays so after removing `p`. -/
private lemma add_smul_sub_mem_diff_singleton
    (hS : ∀ z ∈ S, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ S) :
    ∀ z ∈ S \ {p}, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ S \ {p} := fun z hz c hc ↦
  ⟨hS _ hz.1 _ hc, fun h ↦ hz.2 <| by simpa [sub_eq_zero, (one_pos.trans_le hc).ne'] using h⟩

/-- The straight-line homotopy from the outward radial push to the identity of `T`. Every point
of the segment from `z` to its push is `p + c • (z - p)` with `c ≥ 1`. -/
private def outwardPushHomotopy (hpT : p ∉ T)
    (hT : ∀ z ∈ T, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ T) (r : ℝ) :
    (outwardPush hpT hT r).Homotopy (ContinuousMap.id T) where
  toFun x := ⟨p + ((1 - (x.1 : ℝ)) * max 1 (r / ‖(x.2 : E) - p‖) + x.1) • ((x.2 : E) - p),
    hT _ x.2.property _
        (by nlinarith [le_max_left 1 (r / ‖(x.2 : E) - p‖), x.1.property.1, x.1.property.2])⟩
  continuous_toFun := by
    have hx : Continuous fun x : I × T ↦ (x.2 : E) := continuous_subtypeVal.comp continuous_snd
    have ht : Continuous fun x : I × T ↦ (x.1 : ℝ) := continuous_subtypeVal.comp continuous_fst
    have hmax := continuous_max_one_div_norm_sub hx (fun x ↦ ne_of_mem_of_not_mem x.2.property hpT)
        r
    exact Continuous.subtype_mk (continuous_const.add
      ((((continuous_const.sub ht).mul hmax).add ht).smul (hx.sub continuous_const))) _
  map_zero_left z := by
    ext
    simp [outwardPush]
  map_one_left z := by
    ext
    simp

/-- **The complement of a bounded star-convex set inside a set closed under outward radial
moves.** Let `S` be closed under outward radial moves from `p`, in the sense that
`p + c • (z - p) ∈ S` for `z ∈ S` and `c ≥ 1`, such as a closed half-space whose boundary
contains `p`. If `K` contains `p`, is star-convex about `p` and lies in `ball p r`, then the
inclusion `S \ K → S \ {p}` is a homotopy equivalence; its homotopy inverse is the outward radial
push `z ↦ p + max 1 (r / ‖z - p‖) • (z - p)`. -/
def diffHomotopyEquivDiffSingleton (hK : StarConvex ℝ p K) (hp : p ∈ K) (hKr : K ⊆ ball p r)
    (hS : ∀ z ∈ S, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ S) :
    ContinuousMap.HomotopyEquiv ↥(S \ K) ↥(S \ {p}) where
  toFun := ContinuousMap.inclusion (sdiff_subset_sdiff_right (singleton_subset_iff.2 hp))
  -- The outward push of `S \ {p}`, which lands in `S \ K`.
  invFun :=
    { toFun z := ⟨outwardPush (T := S \ {p}) (fun h ↦ h.2 rfl)
          (add_smul_sub_mem_diff_singleton hS) r z, by
        have hd : 0 < ‖(z : E) - p‖ := norm_pos_iff.2 (sub_ne_zero.2 z.property.2)
        refine ⟨mem_of_mem_sdiff (Subtype.prop _), fun h ↦ ?_⟩
        -- The pushed point lies at distance at least `r` from `p`, outside `ball p r ⊇ K`.
        have hc : (0 : ℝ) < max 1 (r / ‖(z : E) - p‖) := one_pos.trans_le (le_max_left _ _)
        have hlt : max 1 (r / ‖(z : E) - p‖) * ‖(z : E) - p‖ < r := by
          simpa [coe_outwardPush_apply, dist_eq_norm, norm_smul, abs_of_pos hc] using hKr h
        have := (div_le_iff₀ hd).1 (le_max_right 1 (r / ‖(z : E) - p‖))
        linarith⟩
      continuous_toFun := by fun_prop }
  -- Both composites are the outward push of the respective complement.
  left_inv := by
    have hT : ∀ z ∈ S \ K, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ S \ K := fun z hz c hc ↦
      ⟨hS _ hz.1 _ hc, hK.add_smul_sub_mem_compl hKr hz.2 (Or.inl hc)⟩
    refine ⟨(outwardPushHomotopy (T := S \ K) (fun h ↦ h.2 hp) hT r).cast ?_ rfl⟩
    ext z
    simp [coe_outwardPush_apply]
  right_inv := by
    refine ⟨(outwardPushHomotopy (T := S \ {p}) (fun h ↦ h.2 rfl)
      (add_smul_sub_mem_diff_singleton hS) r).cast ?_ rfl⟩
    ext z
    simp

/-- The homotopy equivalence `StarConvex.diffHomotopyEquivDiffSingleton` is the inclusion. -/
@[simp]
theorem coe_diffHomotopyEquivDiffSingleton_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (hS : ∀ z ∈ S, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ S) (z : ↥(S \ K)) :
    (hK.diffHomotopyEquivDiffSingleton hp hKr hS z : E) = z :=
  (rfl)

/-- The homotopy inverse of `StarConvex.diffHomotopyEquivDiffSingleton` is the outward radial
push. -/
@[simp]
theorem coe_diffHomotopyEquivDiffSingleton_symm_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (hS : ∀ z ∈ S, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ S)
    (z : ↥(S \ {p})) :
    ((hK.diffHomotopyEquivDiffSingleton hp hKr hS).symm z : E) =
      p + max 1 (r / ‖(z : E) - p‖) • ((z : E) - p) :=
  (rfl)

/-- **The complement in a closed half-space of a bounded star-convex set about a boundary point is
contractible.** Let `f` be a nonzero continuous linear functional and `K` a bounded set,
star-convex about a point `p ∈ K` on the boundary hyperplane `f = 0`. Then the complement of `K`
in the half-space `{x | 0 ≤ f x}` is contractible: the half-space is closed under outward radial
moves from `p`, so `StarConvex.diffHomotopyEquivDiffSingleton` identifies the complement of `K`
with the half-space punctured at `p`, which is star-convex about any point `p + v` with
`0 < f v`. -/
theorem contractibleSpace_halfSpace_diff (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKb : Bornology.IsBounded K) {f : StrongDual ℝ E} (hf : f ≠ 0) (hfp : f p = 0) :
    ContractibleSpace ↥({x | 0 ≤ f x} \ K) := by
  obtain ⟨r, hKr⟩ := (isBounded_iff_subset_ball p).1 hKb
  have hS : ∀ z ∈ {x | 0 ≤ f x}, ∀ c : ℝ, 1 ≤ c → p + c • (z - p) ∈ {x | 0 ≤ f x} := by
    intro z hz c hc
    simp only [mem_ofPred_eq, map_add, map_smul, map_sub, hfp, sub_zero, zero_add,
      smul_eq_mul] at hz ⊢
    exact mul_nonneg (zero_le_one.trans hc) hz
  -- A vector `v` pointing into the open half-space.
  obtain ⟨v, hv⟩ : ∃ v, 0 < f v := by
    obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hf
    rcases (by simpa using hw : f w ≠ 0).lt_or_gt with h | h
    · exact ⟨-w, by simpa using h⟩
    · exact ⟨w, h⟩
  have hstar : StarConvex ℝ (p + v) ({x | 0 ≤ f x} \ {p}) := by
    intro y hy a b ha hb hab
    have hfy : 0 ≤ f y := hy.1
    have hval : f (a • (p + v) + b • y) = a * f v + b * f y := by
      simp [hfp, smul_eq_mul]
    refine ⟨by simp only [mem_ofPred_eq, hval]; positivity, fun h ↦ hy.2 ?_⟩
    rw [mem_singleton_iff] at h
    -- Evaluating `f` on `a • (p + v) + b • y = p` forces `a = 0`, hence `b = 1` and `y = p`.
    have ha0 : a = 0 := by
      have h0 : a * f v + b * f y = 0 := by rw [← hval, h, hfp]
      nlinarith [mul_nonneg hb hfy, mul_nonneg ha hv.le]
    subst ha0
    obtain rfl : b = 1 := by simpa using hab
    simpa using h
  have : ContractibleSpace ↥({x | 0 ≤ f x} \ {p}) :=
    hstar.contractibleSpace ⟨p + v, by simpa [hfp] using hv.le,
      fun h ↦ hv.ne' (by simp_all)⟩
  exact (hK.diffHomotopyEquivDiffSingleton hp hKr hS).contractibleSpace

end StarConvex
