/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import TauCeti.Topology.ContinuousMap.Algebra
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# The fixed-point index of a map of an open subset of a vector space

Let `E` be a finite-dimensional real normed space, `U ⊆ E` an open subset and `f : U → E` a
continuous map. The fixed points of `f` are the zeros of its *displacement* `z ↦ z - f z`, a map
`U → E`. When the fixed set `{z | f z = z}` is compact, the **fixed-point index** of `f`
(`ContinuousMap.fixedPointIndex`) is the local degree at `0` of the displacement: the integer `d`
such that the displacement carries the fundamental class of `U` along its fixed set to `d` times
the local orientation of `E` at `0` (`TauCeti.HomologicalOrientation.localDegree`). It counts the
fixed points of `f` with multiplicities. The **local fixed-point index** of `f` at a fixed point `x`
(`ContinuousMap.localFixedPointIndex`) is the local index of the displacement at `x`
(`TauCeti.HomologicalOrientation.localIndex`); it is nonzero only at isolated fixed points.

Both integers are defined through an orientation of `E`, but they do not depend on it: reversing
the orientation reverses it on the source `U` and on the target `E` at once, and the two sign
changes cancel (`ContinuousMap.fixedPointIndex_eq_localDegree`,
`ContinuousMap.localFixedPointIndex_eq_localIndex`). So the index needs no orientation of `E`.

The index has the following properties of the classical fixed-point index:

* **Normalization at nondegenerate fixed points.** If `f` is differentiable at the fixed point `x`
  with derivative `f'` and `1 - f'` is invertible, then the local index at `x` is the sign of
  `det (1 - f')` (`ContinuousMap.localFixedPointIndex_eq_sign_det`).
* **Summation.** If the fixed set is finite, the index is the sum of the local indices
  (`ContinuousMap.fixedPointIndex_eq_sum_localFixedPointIndex`), hence the signed count
  `∑ sign det (1 - f'(x))` when every fixed point is nondegenerate
  (`ContinuousMap.fixedPointIndex_eq_sum_sign_det`); a compact set of nondegenerate fixed points
  is finite (`ContinuousMap.finite_setOf_apply_eq`). A map without fixed points has index zero.
* **Homotopy invariance.** Maps `f₀, f₁ : U → E` joined by a homotopy `H` whose fixed set
  `{(t, z) | H (t, z) = z}` is compact have the same index
  (`ContinuousMap.fixedPointIndex_eq_of_homotopy`). The fixed points may move, appear and
  disappear along the homotopy, provided none escapes to the boundary of `U`.
* **Localization.** The local index at `x` depends only on the germ of `f` at `x`
  (`ContinuousMap.localFixedPointIndex_congr`) and not on the open set on which `f` is considered
  (`ContinuousMap.localFixedPointIndex_comp_inclusion`); on an open set whose only fixed point is
  `x`, the index is the local index at `x`
  (`ContinuousMap.fixedPointIndex_eq_localFixedPointIndex`).
* **Excision.** Restricting `f` to an open subset containing all its fixed points does not change
  the index (`ContinuousMap.fixedPointIndex_comp_inclusion`).
* **Normalization.** An affine map `z ↦ A z + v` with `1 - A` invertible has index
  `sign det (1 - A)` on every open set containing its fixed point
  (`ContinuousMap.fixedPointIndex_eq_sign_det_of_forall_eq`); in particular a constant map has
  index `1` (`ContinuousMap.fixedPointIndex_const`). In dimension zero every point is an isolated
  fixed point of local index `1` (`ContinuousMap.localFixedPointIndex_of_subsingleton`).

Together these say that whenever `f` is joined, by a homotopy with compact fixed set, to a map
with finitely many nondegenerate fixed points, the index of `f` is the sum of the signs
`sign det (1 - f')` at the fixed points of that map, whichever such perturbation is used. So the
index agrees with the definition of the fixed-point index by perturbation.

In dimension one the index is read off at the ends of an interval. If `[a, b] ⊆ U` and every fixed
point of `f : U → ℝ` lies in `(a, b)`, then `2 i(f) = sign (b - f b) - sign (a - f a)`
(`ContinuousMap.two_mul_fixedPointIndex_eq_sign_sub_sign`): the straight-line homotopy to the
affine map with the same displacement at `a` and `b` has no fixed point near the ends. For instance
the degenerate fixed point `0` of `x ↦ x + x³`, where `det (1 - f') = 0`, has index `-1`
(`ContinuousMap.fixedPointIndex_add_pow_three`), and `x ↦ x + x² - ε` has index `0` for every `ε`
(`ContinuousMap.fixedPointIndex_add_sq_sub`), whether it has two nondegenerate fixed points of
opposite signs, one degenerate fixed point or none.

## Main definitions

* `ContinuousMap.fixedPointIndex f`: the fixed-point index of `f : U → E`, which is `0` when the
  fixed set is not compact.
* `ContinuousMap.localFixedPointIndex f x`: the local fixed-point index of `f` at `x`, which is
  `0` when `x` is not a fixed point or not an isolated one.

## Main results

* `ContinuousMap.fixedPointIndex_comp_inclusion`: the index does not change on restricting to an
  open subset containing every fixed point.
* `ContinuousMap.localFixedPointIndex_eq_sign_det`: the local index at a nondegenerate fixed point
  is `sign det (1 - f')`.
* `ContinuousMap.fixedPointIndex_eq_sum_localFixedPointIndex`,
  `ContinuousMap.fixedPointIndex_eq_sum_sign_det`: the index is the sum of the local indices over a
  finite fixed set.
* `ContinuousMap.fixedPointIndex_eq_of_homotopy`: invariance under homotopies with compact fixed
  set.
* `ContinuousMap.fixedPointIndex_eq_sign_det_of_forall_eq`: an affine map `z ↦ A z + v` with
  `1 - A` invertible has index `sign det (1 - A)` on every open set containing its fixed point.
* `ContinuousMap.fixedPointIndex_const`: a constant map with value in `U` has index `1`.
* `ContinuousMap.localFixedPointIndex_of_subsingleton`,
  `ContinuousMap.fixedPointIndex_of_subsingleton`: in dimension zero the (local) index is `1`.
* `ContinuousMap.two_mul_fixedPointIndex_eq_sign_sub_sign`: in dimension one, the index on an
  interval is determined by the directions in which `f` moves its endpoints.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 (the fixed-point
  index of maps of open subsets of `ℝⁿ`).
* A. Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood retracts*,
  Topology 4 (1965), 1–8.
* R. F. Brown, *The Lefschetz Fixed Point Theorem*, Scott, Foresman and Co., 1971, Chapter IV.
-/

public section

noncomputable section

open Module Set Topology TauCeti TopologicalSpace

namespace TauCeti

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An orientation of `E`, chosen once. The fixed-point index does not depend on it
(`ContinuousMap.fixedPointIndex_eq_localDegree`). -/
private def fixedPointOrientation : HomologicalOrientation E E (finrank ℝ E) :=
  Classical.choice (HomologicalOrientation.nonempty_of_simplyConnectedSpace (M := E) rfl)

end TauCeti

namespace ContinuousMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Opens E}

/-- The **fixed-point index** of a continuous map `f : U → E` on an open subset `U` of `E`: the
local degree at `0` of the displacement `z ↦ z - f z` (`ContinuousMap.displacement`), whose zeros
are the fixed points of `f`.
It is `0` when the fixed set `{z | f z = z}` is not compact. It does not depend on an orientation
of `E` (`ContinuousMap.fixedPointIndex_eq_localDegree`). -/
def fixedPointIndex (f : C(U, E)) : ℤ :=
  (fixedPointOrientation.comap U.isOpenEmbedding').localDegree fixedPointOrientation rfl
    f.displacement 0

open scoped Classical in
/-- The **local fixed-point index** of a continuous map `f : U → E` at a fixed point `x`: the local
index at `x` of the displacement `z ↦ z - f z`. It is `0` when `x` is not a fixed point, or not an
isolated one. It does not depend on an orientation of `E`
(`ContinuousMap.localFixedPointIndex_eq_localIndex`). -/
def localFixedPointIndex (f : C(U, E)) (x : U) : ℤ :=
  if f x = x then
    (fixedPointOrientation.comap U.isOpenEmbedding').localIndex fixedPointOrientation
      f.displacement x
  else 0

/-- **The fixed-point index in an arbitrary orientation**: for every orientation `o` of `E`, the
fixed-point index of `f : U → E` is the local degree at `0` of the displacement `z ↦ z - f z`, for
the orientation `o` restricted to `U` on the source and `o` on the target. -/
theorem fixedPointIndex_eq_localDegree {n : ℕ} (o : HomologicalOrientation E E n)
    (hn : finrank ℝ E = n) (f : C(U, E)) :
    f.fixedPointIndex =
      (o.comap U.isOpenEmbedding').localDegree o hn f.displacement 0 := by
  subst hn
  rcases HomologicalOrientation.eq_or_eq_neg rfl fixedPointOrientation o with rfl | rfl
  · rfl
  · rw [fixedPointIndex, HomologicalOrientation.comap_neg,
      HomologicalOrientation.localDegree_neg_left _ _ _ rfl,
      HomologicalOrientation.localDegree_neg_right _ _ _ rfl, neg_neg]

/-- **The local fixed-point index in an arbitrary orientation**: for every orientation `o` of `E`,
the local fixed-point index of `f : U → E` at a fixed point `x` is the local index at `x` of the
displacement `z ↦ z - f z`, for the orientation `o` restricted to `U` on the source and `o` on the
target. -/
theorem localFixedPointIndex_eq_localIndex {n : ℕ} (o : HomologicalOrientation E E n)
    (hn : finrank ℝ E = n) (f : C(U, E)) {x : U} (hx : f x = x) :
    f.localFixedPointIndex x =
      (o.comap U.isOpenEmbedding').localIndex o f.displacement x := by
  subst hn
  simp only [localFixedPointIndex, hx, ↓reduceIte]
  rcases HomologicalOrientation.eq_or_eq_neg rfl fixedPointOrientation o with rfl | rfl
  · rfl
  · rw [HomologicalOrientation.comap_neg, HomologicalOrientation.localIndex_neg_left _ _ rfl,
      HomologicalOrientation.localIndex_neg_right _ _ rfl, neg_neg]

/-- The local fixed-point index vanishes at a point which is not fixed. -/
@[simp]
theorem localFixedPointIndex_of_ne (f : C(U, E)) {x : U} (hx : f x ≠ x) :
    f.localFixedPointIndex x = 0 := by
  simp [localFixedPointIndex, hx]

/-- The local fixed-point index vanishes at a fixed point which is not isolated. -/
theorem localFixedPointIndex_of_frequently_eq (f : C(U, E)) {x : U}
    (h : ∃ᶠ z in 𝓝[≠] x, f z = z) : f.localFixedPointIndex x = 0 := by
  by_cases hx : f x = x
  · rw [f.localFixedPointIndex_eq_localIndex fixedPointOrientation rfl hx]
    refine HomologicalOrientation.localIndex_of_frequently_eq _ _ _ (h.mono fun z hz ↦ ?_)
    simp [hz, hx]
  · exact f.localFixedPointIndex_of_ne hx

/-- **The local fixed-point index only depends on the germ of the map**: maps agreeing on a
neighbourhood of `x` have the same local fixed-point index at `x`. -/
theorem localFixedPointIndex_congr {f g : C(U, E)} {x : U} (hfg : f =ᶠ[𝓝 x] g) :
    f.localFixedPointIndex x = g.localFixedPointIndex x := by
  by_cases hx : f x = x
  · have hgx : g x = x := hfg.eq_of_nhds ▸ hx
    rw [f.localFixedPointIndex_eq_localIndex fixedPointOrientation rfl hx,
      g.localFixedPointIndex_eq_localIndex fixedPointOrientation rfl hgx]
    exact HomologicalOrientation.localIndex_congr _ _ rfl (hfg.mono fun z hz ↦ by simp [hz])
  · rw [f.localFixedPointIndex_of_ne hx, g.localFixedPointIndex_of_ne (hfg.eq_of_nhds ▸ hx)]

/-- **The local fixed-point index does not depend on the open set**: the local index at `x` of a
map `f : U → E` restricted to an open subset `V ⊆ U` containing `x` is the local index of `f`
at `x`. -/
theorem localFixedPointIndex_comp_inclusion {V : Opens E} (hVU : V ≤ U) (f : C(U, E)) (x : V) :
    (f.comp (inclusion hVU)).localFixedPointIndex x = f.localFixedPointIndex (inclusion hVU x) := by
  set ι : C(V, U) := inclusion hVU
  by_cases hx : f (ι x) = ι x
  · rw [(f.comp ι).localFixedPointIndex_eq_localIndex fixedPointOrientation rfl hx,
      f.localFixedPointIndex_eq_localIndex fixedPointOrientation rfl hx]
    -- The displacement of `f` restricted to `V` is that of `f` read through the inclusion `V → U`.
    have hι : IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le hVU
    have h := HomologicalOrientation.localIndex_comap rfl
      (fixedPointOrientation.comap U.isOpenEmbedding') fixedPointOrientation hι IsOpenEmbedding.id
      (f := (f.comp ι).displacement) (g := f.displacement) (x := x)
      (.of_forall fun z ↦ by rw [displacement_comp_inclusion, comp_apply, id_eq])
    rwa [HomologicalOrientation.comap_id,
      HomologicalOrientation.comap_comap_of_comp_eq _ _ hι V.isOpenEmbedding' rfl] at h
  · rw [(f.comp ι).localFixedPointIndex_of_ne hx, f.localFixedPointIndex_of_ne hx]

/-- **The local fixed-point index at a nondegenerate fixed point** is the sign of
`det (1 - f')`: if `f : U → E` agrees near the fixed point `x` with a map `φ : E → E` which is
differentiable at `x` with derivative `f'`, and `1 - f'` is invertible, then the local index of `f`
at `x` is `sign det (1 - f')`. -/
theorem localFixedPointIndex_eq_sign_det {f : C(U, E)} {x : U} (hx : f x = x) {φ : E → E}
    (hφ : ∀ᶠ z : U in 𝓝 x, φ z = f z) {f' : E →L[ℝ] E} (hd : HasFDerivAt φ f' x)
    (hdet : (1 - f').det ≠ 0) :
    f.localFixedPointIndex x = SignType.sign (1 - f').det := by
  rw [f.localFixedPointIndex_eq_localIndex fixedPointOrientation rfl hx]
  have h := fixedPointOrientation.localIndex_comap_eq_sign_det rfl U.isOpenEmbedding'
    IsOpenEmbedding.id (f := f.displacement) (φ := fun z ↦ z - φ z)
    (hφ.mono fun z hz ↦ by simp [hz]) ((hasFDerivAt_id (x : E)).sub hd) hdet
  rwa [HomologicalOrientation.comap_id] at h

/-- The fixed-point index vanishes when the fixed set is not compact. -/
theorem fixedPointIndex_of_not_isCompact (f : C(U, E)) (h : ¬IsCompact {z | f z = z}) :
    f.fixedPointIndex = 0 := by
  rw [fixedPointIndex, HomologicalOrientation.localDegree_of_not_isCompact]
  rwa [preimage_displacement_zero]

/-- A map without fixed points has fixed-point index zero. -/
theorem fixedPointIndex_eq_zero_of_forall_ne (f : C(U, E)) (h : ∀ z, f z ≠ z) :
    f.fixedPointIndex = 0 := by
  rw [fixedPointIndex, HomologicalOrientation.localDegree_eq_zero_of_notMem_range _ _ _ rfl]
  rintro ⟨z, hz⟩
  rw [displacement_apply, sub_eq_zero] at hz
  exact h z hz.symm

/-- **The fixed-point index is the sum of the local indices** over a finite fixed set. -/
theorem fixedPointIndex_eq_sum_localFixedPointIndex (f : C(U, E))
    (hfin : {z | f z = z}.Finite) :
    f.fixedPointIndex = ∑ x ∈ hfin.toFinset, f.localFixedPointIndex x := by
  have hfin' : (f.displacement ⁻¹' {0}).Finite := by
    rwa [preimage_displacement_zero]
  rw [fixedPointIndex, HomologicalOrientation.localDegree_eq_sum_localIndex _ _ rfl rfl _ hfin']
  refine Finset.sum_congr (Finite.toFinset_inj.2 (preimage_displacement_zero f))
    fun x hx ↦ ?_
  rw [Finite.mem_toFinset] at hx
  rw [f.localFixedPointIndex_eq_localIndex fixedPointOrientation rfl hx]

/-- On an open set whose only fixed point is `x`, the fixed-point index is the local index
at `x`. -/
theorem fixedPointIndex_eq_localFixedPointIndex (f : C(U, E)) {x : U}
    (h : {z | f z = z} = {x}) : f.fixedPointIndex = f.localFixedPointIndex x := by
  rw [f.fixedPointIndex_eq_sum_localFixedPointIndex (h ▸ finite_singleton x)]
  simp [h]

/-- **Excision for the fixed-point index**: restricting `f : U → E` to an open subset `V ⊆ U`
containing every fixed point of `f` does not change the fixed-point index. -/
theorem fixedPointIndex_comp_inclusion {V : Opens E} (hVU : V ≤ U) (f : C(U, E))
    (hV : ∀ z, f z = z → (z : E) ∈ V) :
    (f.comp (inclusion hVU)).fixedPointIndex = f.fixedPointIndex := by
  set ι : C(V, U) := inclusion hVU
  have hι : IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le hVU
  -- All zeros of the displacement of `f` lie in `V`.
  have hzero : f.displacement ⁻¹' {0} ⊆ range ι := by
    rw [preimage_displacement_zero]
    exact fun z hz ↦ ⟨⟨z, hV z hz⟩, rfl⟩
  rw [fixedPointIndex, fixedPointIndex, displacement_comp_inclusion,
    ← HomologicalOrientation.localDegree_comap_comp _ _ rfl rfl hι _ hzero,
    HomologicalOrientation.comap_comap_of_comp_eq _ _ hι V.isOpenEmbedding' rfl]

/-- **A compact set of nondegenerate fixed points is finite**: if `f : U → E` agrees on `U` with a
map `φ : E → E`, its fixed set is compact, and at each fixed point `x` the map `φ` has a derivative
`f' x` with `1 - f' x` invertible, then `f` has only finitely many fixed points. -/
theorem finite_setOf_apply_eq (f : C(U, E)) (hK : IsCompact {z | f z = z}) {φ : E → E}
    (hφ : ∀ z : U, φ z = f z) {f' : E → E →L[ℝ] E}
    (hd : ∀ x : U, f x = x → HasFDerivAt φ (f' x) x)
    (hdet : ∀ x : U, f x = x → (1 - f' x).det ≠ 0) : {z | f z = z}.Finite := by
  -- In `E`, the fixed points are the zeros in `U` of `z ↦ z - φ z`, whose derivative `1 - f' x` is
  -- invertible at each of them.
  have hfix (w : E) (hw : w ∈ (U : Set E) ∩ (fun z ↦ z - φ z) ⁻¹' {0}) :
      f ⟨w, hw.1⟩ = w :=
    (hφ ⟨w, hw.1⟩).symm.trans (sub_eq_zero.1 hw.2).symm
  have himage : Subtype.val '' {z | f z = z} = (U : Set E) ∩ (fun z ↦ z - φ z) ⁻¹' {0} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, sub_eq_zero.2 ((hφ z).trans hz).symm⟩
    · intro hw
      exact ⟨⟨w, hw.1⟩, hfix w hw, rfl⟩
  have hc : IsCompact ((U : Set E) ∩ (fun z ↦ z - φ z) ⁻¹' {0}) :=
    himage ▸ hK.image continuous_subtypeVal
  have hfin := hc.finite_inter_preimage_of_hasFDerivAt
    (fun w hw ↦ (hasFDerivAt_id w).sub (hd _ (hfix w hw)))
    fun w hw ↦ ⟨_, ((1 - f' w).toContinuousLinearEquivOfDetNeZero
      (hdet _ (hfix w hw))).antilipschitzWith⟩
  exact Finite.of_finite_image (himage ▸ hfin) Subtype.val_injective.injOn

/-- **The fixed-point index counts nondegenerate fixed points with signs**: if `f : U → E` agrees
on `U` with a map `φ : E → E`, the fixed set of `f` is finite, and at each fixed point `x` the map
`φ` has a derivative `f' x` with `1 - f' x` invertible, then the fixed-point index of `f` is the sum
of `sign det (1 - f' x)` over its fixed points. -/
theorem fixedPointIndex_eq_sum_sign_det (f : C(U, E)) (hfin : {z | f z = z}.Finite)
    {φ : E → E} (hφ : ∀ z : U, φ z = f z) {f' : E → E →L[ℝ] E}
    (hd : ∀ x : U, f x = x → HasFDerivAt φ (f' x) x)
    (hdet : ∀ x : U, f x = x → (1 - f' x).det ≠ 0) :
    f.fixedPointIndex = ∑ x ∈ hfin.toFinset, (SignType.sign (1 - f' x).det : ℤ) := by
  rw [f.fixedPointIndex_eq_sum_localFixedPointIndex hfin]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finite.mem_toFinset] at hx
  exact f.localFixedPointIndex_eq_sign_det hx (.of_forall hφ) (hd x hx) (hdet x hx)

/-- **Homotopy invariance of the fixed-point index**: maps `f₀, f₁ : U → E` joined by a homotopy
`H` whose fixed set `{(t, z) | H (t, z) = z}` is compact have the same fixed-point index. -/
theorem fixedPointIndex_eq_of_homotopy {f₀ f₁ : C(U, E)} (H : f₀.Homotopy f₁)
    (hH : IsCompact {p : unitInterval × U | H p = p.2}) :
    f₀.fixedPointIndex = f₁.fixedPointIndex := by
  -- The displacements of the maps `H (t, ·)` form a homotopy between the two displacements, whose
  -- zeros are the fixed points of the homotopy.
  let D : f₀.displacement.Homotopy f₁.displacement :=
    { toFun := fun p ↦ (p.2 : E) - H p
      continuous_toFun := (continuous_subtypeVal.comp continuous_snd).sub H.continuous
      map_zero_left := fun z ↦ by simp
      map_one_left := fun z ↦ by simp }
  have hD : D ⁻¹' {0} = {p | H p = p.2} := by
    ext p
    -- `D p` is `p.2 - H p` by construction.
    exact sub_eq_zero.trans eq_comm
  exact HomologicalOrientation.localDegree_eq_of_homotopy_of_isCompact _ _ rfl rfl D (hD ▸ hH)

/-- **The fixed-point index of an affine map**: if `f : U → E` is the restriction of an affine map
`z ↦ A z + v` with `1 - A` invertible, whose fixed point `x` lies in `U`, then the fixed-point index
of `f` is `sign det (1 - A)`. -/
theorem fixedPointIndex_eq_sign_det_of_forall_eq {f : C(U, E)} {A : E →L[ℝ] E} {v x : E}
    (hx : x ∈ U) (hAx : A x + v = x) (hf : ∀ z : U, f z = A z + v) (hdet : (1 - A).det ≠ 0) :
    f.fixedPointIndex = SignType.sign (1 - A).det := by
  have hinj : Function.Injective ((1 : E →L[ℝ] E) - A) :=
    ((1 - A).toContinuousLinearEquivOfDetNeZero hdet).injective
  -- Since `1 - A` is injective, `x` is the only fixed point of `f`.
  have hfix : {z | f z = z} = {⟨x, hx⟩} := by
    ext z
    rw [mem_ofPred_eq, mem_singleton_iff, hf, Subtype.ext_iff]
    refine ⟨fun hz ↦ hinj ?_, fun hz ↦ by rw [hz, hAx]⟩
    have h : (z : E) - A z = x - A x := by linear_combination (norm := module) hAx - hz
    simpa using h
  rw [f.fixedPointIndex_eq_localFixedPointIndex hfix]
  exact f.localFixedPointIndex_eq_sign_det (x := ⟨x, hx⟩) (by rw [hf, hAx])
    (.of_forall fun z ↦ (hf z).symm) (A.hasFDerivAt.add_const v) hdet

/-- **Normalization**: a constant map with value in `U` has fixed-point index `1`. -/
theorem fixedPointIndex_const {c : E} (hc : c ∈ U) : (const U c).fixedPointIndex = 1 := by
  rw [fixedPointIndex_eq_sign_det_of_forall_eq (A := 0) (v := c) hc (by simp) (fun z ↦ by simp)
    (by simp [ContinuousLinearMap.det])]
  simp [ContinuousLinearMap.det]

/-- **The fixed-point index in dimension zero**: every map of a nonempty open subset of a
zero-dimensional space has fixed-point index `1`. -/
@[simp]
theorem fixedPointIndex_of_subsingleton [Subsingleton E] [Nonempty U] (f : C(U, E)) :
    f.fixedPointIndex = 1 := by
  obtain ⟨x⟩ := ‹Nonempty U›
  rw [show f = const U (x : E) from ContinuousMap.ext fun z ↦ Subsingleton.elim _ _]
  exact fixedPointIndex_const x.property

/-- **The local fixed-point index in dimension zero**: on a zero-dimensional space every point is
an isolated fixed point, of local index `1`. -/
@[simp]
theorem localFixedPointIndex_of_subsingleton [Subsingleton E] (f : C(U, E)) (x : U) :
    f.localFixedPointIndex x = 1 := by
  have hU : ∀ z : U, z = x := fun z ↦ Subtype.ext (Subsingleton.elim _ _)
  have hfix : {z | f z = z} = {x} := by
    ext z
    simp [hU z, Subsingleton.elim (f x) (x : E)]
  rw [← f.fixedPointIndex_eq_localFixedPointIndex hfix]
  have : Nonempty U := ⟨x⟩
  exact f.fixedPointIndex_of_subsingleton

section Line

/-- For `a < b`, the affine map `ℓ` with `ℓ a = da` and `ℓ b = db` has
`(b - a) ℓ z = (b - z) da + (z - a) db`. -/
private theorem mul_affineInterp {a b da db : ℝ} (hab : a < b) (z : ℝ) :
    (b - a) * (da + (z - a) * ((db - da) / (b - a))) = (b - z) * da + (z - a) * db := by
  field_simp
  ring

/-- **The model on an interval.** For `a < b` and nonzero `da`, `db`, the map `z ↦ z - ℓ z` on
`(a, b)`, where `ℓ` is the affine map with `ℓ a = da` and `ℓ b = db`, has twice its fixed-point
index equal to `sign db - sign da`. -/
private theorem two_mul_fixedPointIndex_sub_affineInterp {a b da db : ℝ} (hab : a < b)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    2 * (⟨fun z : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ↦
        (z : ℝ) - (da + ((z : ℝ) - a) * ((db - da) / (b - a))), by fun_prop⟩ :
      C((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ), ℝ)).fixedPointIndex =
      SignType.sign db - SignType.sign da := by
  have hba : 0 < b - a := sub_pos.2 hab
  obtain ⟨s, hs⟩ : ∃ s, s = (db - da) / (b - a) := ⟨_, rfl⟩
  have hsb : s * (b - a) = db - da := by rw [hs]; field_simp
  simp only [← hs]
  rcases lt_or_gt_of_ne (mul_ne_zero hda hdb) with h | h
  · -- If `da` and `db` have opposite signs, `ℓ` has one zero `x` in `(a, b)`, which is the only
    -- fixed point of the affine map `z ↦ (1 - s) z + (s a - da)`, of index `sign s`.
    have hd : 0 < (db - da) ^ 2 := by nlinarith [mul_self_pos.2 hda, mul_self_pos.2 hdb]
    have hs0 : s ≠ 0 := by rintro rfl; nlinarith
    obtain ⟨x, hx⟩ : ∃ x, x = a - da / s := ⟨_, rfl⟩
    have hx0 : da + (x - a) * s = 0 := by rw [hx]; field_simp; ring
    have e1 : (x - a) * (db - da) = -da * (b - a) := by
      linear_combination (b - a) * hx0 - (x - a) * hsb
    have hxa : 0 < x - a := by
      refine (mul_pos_iff_of_pos_right hd).1 ?_
      rw [show (x - a) * (db - da) ^ 2 = (b - a) * (da * da - da * db) by
        linear_combination (db - da) * e1]
      exact mul_pos hba (by nlinarith [mul_self_pos.2 hda])
    have hbx : 0 < b - x := by
      refine (mul_pos_iff_of_pos_right hd).1 ?_
      rw [show (b - x) * (db - da) ^ 2 = (b - a) * (db * db - da * db) by
        linear_combination (da - db) * e1]
      exact mul_pos hba (by nlinarith [mul_self_pos.2 hdb])
    have hdet : (1 - (1 - s) • (1 : ℝ →L[ℝ] ℝ)).det = s := by simp [ContinuousLinearMap.det]
    rw [fixedPointIndex_eq_sign_det_of_forall_eq (U := ⟨Ioo a b, isOpen_Ioo⟩)
      (A := (1 - s) • (1 : ℝ →L[ℝ] ℝ)) (v := s * a - da) (x := x)
      (Opens.mem_mk.2 ⟨by linarith, by linarith⟩)
      (by simp only [_root_.smul_apply, one_apply_eq_self, smul_eq_mul]
          linear_combination -hx0)
      (fun z ↦ by
        simp only [coe_mk, _root_.smul_apply, one_apply_eq_self, smul_eq_mul]
        ring) (by rwa [hdet]), hdet]
    rcases lt_or_gt_of_ne hda with hda' | hda'
    · have hdb' : 0 < db := by nlinarith
      have hs' : 0 < s := by rw [hs]; exact div_pos (by linarith) hba
      simp [sign_neg hda', sign_pos hdb', sign_pos hs']
    · have hdb' : db < 0 := by nlinarith
      have hs' : s < 0 := by rw [hs]; exact div_neg_of_neg_of_pos (by linarith) hba
      simp [sign_pos hda', sign_neg hdb', sign_neg hs']
  · -- If `da` and `db` have the same sign, `ℓ` has no zero in `(a, b)`.
    rw [fixedPointIndex_eq_zero_of_forall_ne _ fun z hz ↦ ?_]
    · rcases lt_or_gt_of_ne hda with hda' | hda'
      · simp [sign_neg hda', sign_neg (by nlinarith : db < 0)]
      · simp [sign_pos hda', sign_pos (by nlinarith : 0 < db)]
    · obtain ⟨hza, hzb⟩ := z.property
      rw [coe_mk, sub_eq_self] at hz
      have h2 : ((b - z) * da + (z - a) * db) * da = 0 := by
        rw [← mul_affineInterp hab, ← hs, hz]
        ring
      nlinarith [mul_pos (sub_pos.2 hzb) (mul_self_pos.2 hda), mul_pos (sub_pos.2 hza) h]

/-- Let `Φ : [0, 1] × ℝ → ℝ` be continuous and nonzero at every point `(t, a)` and `(t, b)`. Then
the zeros of `Φ` in `[0, 1] × (a, b)` form a compact set: they are the zeros of `Φ` in the compact
set `[0, 1] × [a, b]`. -/
private theorem isCompact_setOf_eq_zero_Ioo {a b : ℝ} {Φ : unitInterval × ℝ → ℝ}
    (hΦ : Continuous Φ) (ha : ∀ t, Φ (t, a) ≠ 0) (hb : ∀ t, Φ (t, b) ≠ 0) :
    IsCompact {p : unitInterval × (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) | Φ (p.1, p.2) = 0} := by
  have hK : IsCompact ((univ ×ˢ Icc a b) ∩ Φ ⁻¹' {0}) :=
    (isCompact_univ.prod isCompact_Icc).inter_right (isClosed_singleton.preimage hΦ)
  have he : IsEmbedding (Prod.map id Subtype.val :
      unitInterval × (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) → unitInterval × ℝ) :=
    IsEmbedding.id.prodMap IsEmbedding.subtypeVal
  rw [he.isCompact_iff]
  convert hK using 1
  ext ⟨t, z⟩
  simp only [mem_image, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq, mem_inter_iff,
    mem_prod, mem_univ, true_and, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨t', w, hw, rfl, rfl⟩
    exact ⟨Ioo_subset_Icc_self w.property, hw⟩
  · rintro ⟨hz, hΦ0⟩
    have hza : a ≠ z := by
      rintro rfl
      exact ha t hΦ0
    have hzb : z ≠ b := by
      rintro rfl
      exact hb t hΦ0
    exact ⟨t, ⟨z, hz.1.lt_of_ne hza, hz.2.lt_of_ne hzb⟩, hΦ0, rfl, rfl⟩

/-- If `[a, b] ⊆ U`, then the open interval `(a, b)` is contained in `U` as an open set. -/
private theorem Ioo_le_of_Icc_subset {a b : ℝ} {U : Opens ℝ} (hU : Icc a b ⊆ U) :
    (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ U :=
  SetLike.coe_subset_coe.1 <| by
    rw [Opens.coe_mk]
    exact Ioo_subset_Icc_self.trans hU

/-- **Reduction to the model.** Let `f : U → ℝ` be continuous, with `[a, b] ⊆ U`, `a < b`, and no
fixed point at `a` or `b`. Its restriction to `(a, b)` has the same fixed-point index as the model
`z ↦ z - ℓ z`, where `ℓ` is the affine map agreeing with the displacement `z ↦ z - f z` at `a` and
`b`: the straight-line homotopy between them has no fixed point near `a` or `b`. -/
private theorem fixedPointIndex_comp_inclusion_eq_sub_affineInterp {U : Opens ℝ} (f : C(U, ℝ))
    {a b : U} (hab : (a : ℝ) < b) (hU : Icc (a : ℝ) b ⊆ U) (ha : f a ≠ a) (hb : f b ≠ b) :
    (f.comp (inclusion (Ioo_le_of_Icc_subset hU))).fixedPointIndex =
      (⟨fun z : (⟨Ioo (a : ℝ) b, isOpen_Ioo⟩ : Opens ℝ) ↦ (z : ℝ) - ((a - f a) + ((z : ℝ) - a) *
        (((b - f b) - (a - f a)) / (b - a))), by fun_prop⟩ :
        C((⟨Ioo (a : ℝ) b, isOpen_Ioo⟩ : Opens ℝ), ℝ)).fixedPointIndex := by
  set V : Opens ℝ := ⟨Ioo (a : ℝ) b, isOpen_Ioo⟩
  set ℓ : ℝ → ℝ := fun z ↦ ((a : ℝ) - f a) + (z - a) * (((b - f b) - (a - f a)) / (b - a))
  have hℓa : ℓ a = a - f a := by simp [ℓ]
  have hℓb : ℓ b = b - f b := by
    simp only [ℓ]
    field_simp [(sub_pos.2 hab).ne']
    ring
  -- `F` extends `f` from `[a, b]` to `ℝ`, constant beyond the endpoints.
  set F : ℝ → ℝ := fun z ↦
    f ⟨projIcc (a : ℝ) b hab.le z, hU (projIcc (a : ℝ) b hab.le z).property⟩
  have hF : Continuous F :=
    f.continuous.comp ((continuous_subtypeVal.comp continuous_projIcc).subtype_mk _)
  have hFeq (z : U) (hz : (z : ℝ) ∈ Icc (a : ℝ) b) : F z = f z := by simp [F, projIcc_of_mem _ hz]
  set g := f.comp (inclusion (Ioo_le_of_Icc_subset hU))
  set g₁ : C(V, ℝ) := ⟨fun z ↦ (z : ℝ) - ℓ z, by fun_prop⟩
  let H : g.Homotopy g₁ :=
    { toFun := fun p ↦ (1 - p.1 : ℝ) * g p.2 + p.1 * g₁ p.2
      continuous_toFun := by fun_prop
      map_zero_left := fun z ↦ by simp
      map_one_left := fun z ↦ by simp }
  -- `H (t, w)` is its defining formula, and `g w` is `f w`.
  have hHapply (t : unitInterval) (w : V) :
      H (t, w) = (1 - t : ℝ) * f ⟨w, hU (Ioo_subset_Icc_self w.property)⟩ + t * ((w : ℝ) - ℓ w) :=
        rfl
  refine fixedPointIndex_eq_of_homotopy H ?_
  -- The fixed points of `H` are the zeros of `Φ (t, z) = (1 - t) (z - F z) + t ℓ z` in
  -- `[0, 1] × (a, b)`, and at the endpoints `Φ` is `a - f a` and `b - f b`, which are nonzero.
  let Φ : unitInterval × ℝ → ℝ := fun q ↦ (1 - q.1 : ℝ) * (q.2 - F q.2) + q.1 * ℓ q.2
  have hHΦ : {p : unitInterval × V | H p = p.2} = {p | Φ (p.1, p.2) = 0} := by
    ext ⟨t, w⟩
    have hw : (w : ℝ) ∈ Icc (a : ℝ) b := Ioo_subset_Icc_self w.property
    have key : (w : ℝ) - H (t, w) = Φ (t, w) := by
      simp only [Φ, hFeq ⟨w, hU hw⟩ hw, hHapply]
      ring
    rw [mem_ofPred_eq, mem_ofPred_eq, ← key, sub_eq_zero, eq_comm]
  rw [hHΦ]
  refine isCompact_setOf_eq_zero_Ioo (by fun_prop) (fun t ↦ ?_) fun t ↦ ?_
  · simp only [Φ, hFeq a (left_mem_Icc.2 hab.le), hℓa]
    convert sub_ne_zero.2 (Ne.symm ha) using 1
    ring
  · simp only [Φ, hFeq b (right_mem_Icc.2 hab.le), hℓb]
    convert sub_ne_zero.2 (Ne.symm hb) using 1
    ring

/-- **The fixed-point index on an interval.** Let `f : U → ℝ` be continuous on an open set
`U ⊆ ℝ`, and let `a ≤ b` be points of `U` with `[a, b] ⊆ U` such that every fixed point of `f` lies
in `(a, b)`. Then twice the fixed-point index of `f` is `sign (b - f b) - sign (a - f a)`. So the
index is `1` when `f` moves `a` to the right and `b` to the left, `-1` when it moves them apart, and
`0` when it moves both the same way. -/
theorem two_mul_fixedPointIndex_eq_sign_sub_sign {U : Opens ℝ} (f : C(U, ℝ)) {a b : U}
    (hab : (a : ℝ) ≤ b) (hU : Icc (a : ℝ) b ⊆ U)
    (hfix : ∀ z, f z = z → (z : ℝ) ∈ Ioo (a : ℝ) b) :
    2 * f.fixedPointIndex =
      SignType.sign ((b : ℝ) - f b) - SignType.sign ((a : ℝ) - f a) := by
  have ha : f a ≠ a := fun h ↦ (hfix a h).1.false
  have hb : f b ≠ b := fun h ↦ (hfix b h).2.false
  rcases hab.eq_or_lt with h | h
  · -- If `a = b`, there is no fixed point and both sides vanish.
    obtain rfl : a = b := Subtype.ext h
    rw [f.fixedPointIndex_eq_zero_of_forall_ne fun z hz ↦ (hfix z hz).1.not_gt (hfix z hz).2]
    simp
  · rw [← f.fixedPointIndex_comp_inclusion (Ioo_le_of_Icc_subset hU) hfix,
      fixedPointIndex_comp_inclusion_eq_sub_affineInterp f h hU ha hb]
    exact two_mul_fixedPointIndex_sub_affineInterp h (sub_ne_zero.2 (Ne.symm ha))
      (sub_ne_zero.2 (Ne.symm hb))

/-- **A degenerate fixed point of index `-1`**: the map `x ↦ x + x³` on `ℝ`, whose fixed point `0`
is degenerate, has fixed-point index `-1`. -/
theorem fixedPointIndex_add_pow_three :
    (⟨fun z : (⊤ : Opens ℝ) ↦ (z : ℝ) + (z : ℝ) ^ 3, by fun_prop⟩ :
      C((⊤ : Opens ℝ), ℝ)).fixedPointIndex = -1 := by
  -- The displacement `-x³` is positive at `-1` and negative at `1`, and `0` is the only fixed
  -- point.
  have h := two_mul_fixedPointIndex_eq_sign_sub_sign
    (⟨fun z : (⊤ : Opens ℝ) ↦ (z : ℝ) + (z : ℝ) ^ 3, by fun_prop⟩ : C((⊤ : Opens ℝ), ℝ))
    (a := ⟨-1, trivial⟩) (b := ⟨1, trivial⟩) (by norm_num) (fun _ _ ↦ trivial) fun z hz ↦ by
      have hz3 : (z : ℝ) ^ 3 = 0 := by simpa using hz
      simp [pow_eq_zero_iff (n := 3) three_ne_zero |>.1 hz3]
  norm_num at h
  linarith

/-- **A saddle-node family**: for every `ε`, the map `x ↦ x + x² - ε` on `ℝ` has fixed-point index
`0`. For `ε > 0` it has two nondegenerate fixed points `±√ε`, of opposite signs; for `ε = 0` one
degenerate fixed point; for `ε < 0` none. -/
theorem fixedPointIndex_add_sq_sub (ε : ℝ) :
    (⟨fun z : (⊤ : Opens ℝ) ↦ (z : ℝ) + (z : ℝ) ^ 2 - ε, by fun_prop⟩ :
      C((⊤ : Opens ℝ), ℝ)).fixedPointIndex = 0 := by
  -- The displacement `ε - x²` is negative at `±(|ε| + 1)`, and every fixed point satisfies
  -- `x² = ε`, so lies strictly between them.
  set R := |ε| + 1 with hRdef
  have hR : ε < R ^ 2 := by nlinarith [le_abs_self ε, abs_nonneg ε]
  have h := two_mul_fixedPointIndex_eq_sign_sub_sign
    (⟨fun z : (⊤ : Opens ℝ) ↦ (z : ℝ) + (z : ℝ) ^ 2 - ε, by fun_prop⟩ : C((⊤ : Opens ℝ), ℝ))
    (a := ⟨-R, trivial⟩) (b := ⟨R, trivial⟩) (show -R ≤ R by linarith [abs_nonneg ε, hRdef])
    (fun _ _ ↦ trivial) fun z hz ↦ by
      have hz2 : (z : ℝ) ^ 2 = ε := by rw [coe_mk] at hz; linarith
      exact abs_lt_of_sq_lt_sq' (hz2 ▸ hR) (by positivity)
  simp only [coe_mk] at h
  rw [show R - (R + R ^ 2 - ε) = -R - (-R + (-R) ^ 2 - ε) by ring, sub_self] at h
  omega

end Line

end ContinuousMap
