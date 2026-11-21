/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import TauCeti.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

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
* **Invariance under smooth changes of coordinates.** If a map `h : E → E` with invertible strict
  derivative at a fixed point `x` of `f` conjugates `f` near `x` to a map `g`, so that
  `g (h z) = h (f z)` near `x`, then the local index of `g` at `h x` is that of `f` at `x`
  (`ContinuousMap.localFixedPointIndex_eq_of_hasStrictFDerivAt`), whether or not `h` preserves
  orientation. So the local index of a self-map of a smooth manifold at a fixed point can be
  computed in any chart: a transition map between two charts conjugates the two coordinate
  expressions of the map.

Together these say that whenever `f` is joined, by a homotopy with compact fixed set, to a map
with finitely many nondegenerate fixed points, the index of `f` is the sum of the signs
`sign det (1 - f')` at the fixed points of that map, whichever such perturbation is used. So the
index agrees with the definition of the fixed-point index by perturbation. For instance the
degenerate fixed point `0` of `x ↦ x + x³` on `ℝ`, where `det (1 - f') = 0`, has index `-1`
(`ContinuousMap.fixedPointIndex_add_pow_three`), because the homotopy `x ↦ x + x³ + t x`,
`t ∈ [0, 1]`, has no fixed point other than `0` and ends at a map with derivative `2` at `0`.

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
* `ContinuousMap.Homotopy.isCompact_setOf_apply_eq_of_isCompact`: a homotopy on an open set `W`
  has compact fixed set when its fixed points, read in `[0, 1] × X`, form a compact set.
* `ContinuousMap.Homotopy.isCompact_setOf_apply_one_eq`: the end map of a homotopy with compact
  fixed set has compact fixed set.
* `ContinuousMap.fixedPointIndex_eq_sign_det_of_forall_eq`: a linear map `A` with `1 - A`
  invertible has index `sign det (1 - A)` on every open set containing `0`.
* `ContinuousMap.localFixedPointIndex_eq_of_hasStrictFDerivAt`: the local index is invariant
  under conjugation by a map with invertible strict derivative.

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

omit [FiniteDimensional ℝ E] in
/-- Near a fixed point `x` of `f`, a map `h` with invertible strict derivative `A` at `x` moves
`z` and `f z` apart by `A (z - f z)`, up to an error at most half its norm. -/
private theorem eventually_norm_sub_sub_le_half {f : C(U, E)} {x : U} (hx : f x = x) {h : E → E}
    {A : E ≃L[ℝ] E} (hh : HasStrictFDerivAt h (A : E →L[ℝ] E) x) :
    ∀ᶠ z : U in 𝓝 x, ‖h z - h (f z) - A ((z : E) - f z)‖ ≤ ‖A ((z : E) - f z)‖ / 2 := by
  set C := ‖(A.symm : E →L[ℝ] E)‖
  have ht : Filter.Tendsto (fun z : U ↦ ((z : E), f z)) (𝓝 x) (𝓝 ((x : E), (x : E))) := by
    simpa [hx] using (continuous_subtypeVal.prodMk f.continuous).tendsto x
  filter_upwards [ht.eventually ((HasStrictFDerivAt.isLittleO hh).def
    (inv_pos.2 (by positivity : (0 : ℝ) < 2 * (C + 1))))] with z hz
  -- Since `‖v‖ ≤ C ‖A v‖`, the error `‖v‖ / (2 (C + 1))` is at most `‖A v‖ / 2`.
  have hv : ‖(z : E) - f z‖ ≤ C * ‖A ((z : E) - f z)‖ := by
    simpa using (A.symm : E →L[ℝ] E).le_opNorm (A ((z : E) - f z))
  refine hz.trans ((inv_mul_le_iff₀ (by positivity)).2 ?_)
  nlinarith [norm_nonneg (A ((z : E) - f z)), norm_nonneg (A.symm : E →L[ℝ] E)]

/-- Near a fixed point `x` of `f : U → E`, a map `h` with invertible strict derivative at `x`
conjugating `f` to `g : V → E` restricts to an open embedding `k : W → V` of an open neighbourhood
`W ⊆ U` of `x`, on which it conjugates `f` to `g` and the estimate of
`eventually_norm_sub_sub_le_half` holds. -/
private theorem exists_opens_isOpenEmbedding_conj {V : Opens E} {f : C(U, E)} {g : C(V, E)}
    {x : U} (hx : f x = x) {h : E → E} {A : E ≃L[ℝ] E}
    (hh : HasStrictFDerivAt h (A : E →L[ℝ] E) x) (hxV : h x ∈ V)
    (hconj : ∀ᶠ z : U in 𝓝 x, ∀ hz : h z ∈ V, g ⟨h z, hz⟩ = h (f z)) :
    ∃ (W : Opens E) (hWU : W ≤ U) (k : C(W, V)), (x : E) ∈ W ∧ IsOpenEmbedding k ∧
      ∀ z : W, (k z : E) = h z ∧ g (k z) = h (f (inclusion hWU z)) ∧
        ‖h z - h (f (inclusion hWU z)) - A (z - f (inclusion hWU z))‖ ≤
          ‖A (z - f (inclusion hWU z))‖ / 2 := by
  set e := HasStrictFDerivAt.toOpenPartialHomeomorph h hh
  have he : ⇑e = h := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hh
  have hsrc : ∀ᶠ z : U in 𝓝 x, (z : E) ∈ e.source ∧ h z ∈ V :=
    ((continuous_subtypeVal.tendsto x).eventually (e.open_source.mem_nhds
      (HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hh))).and
    ((continuous_subtypeVal.tendsto x).eventually
      ((HasStrictFDerivAt.continuousAt hh).preimage_mem_nhds (V.isOpen.mem_nhds hxV)))
  obtain ⟨t, ht, hto, hxt⟩ :=
    eventually_nhds_iff.1 ((hsrc.and hconj).and (eventually_norm_sub_sub_le_half hx hh))
  -- `W` is the open subset `t` of `U`, read in `E`.
  set W : Opens E := ⟨Subtype.val '' t, U.isOpenEmbedding'.isOpenMap t hto⟩
  have hWU : W ≤ U := by rintro _ ⟨z, -, rfl⟩; exact z.property
  have hWt (z : W) : inclusion hWU z ∈ t := by
    obtain ⟨z', hz', hzz'⟩ := z.property
    exact (Subtype.ext hzz' : z' = inclusion hWU z) ▸ hz'
  have hWsrc (z : W) : (z : E) ∈ e.source := (ht _ (hWt z)).1.1.1
  have hWV (z : W) : h z ∈ V := (ht _ (hWt z)).1.1.2
  have hk_cont : Continuous fun z : W ↦ h z := by
    rw [← he]; exact e.continuousOn.comp_continuous continuous_subtypeVal hWsrc
  let k : C(W, V) := ⟨fun z ↦ ⟨h z, hWV z⟩, hk_cont.subtype_mk _⟩
  -- Read in `E`, `k` is `e` composed with the inclusion of `W`, whose range lies in `e.source`.
  have hk : IsOpenEmbedding k := by
    refine (IsOpenEmbedding.of_comp_iff k V.isOpenEmbedding').1 ?_
    simpa [k, he, Function.comp_def] using
      e.isOpenEmbedding_comp W.isOpenEmbedding' (by rintro _ ⟨z, rfl⟩; exact hWsrc z)
  refine ⟨W, hWU, k, ⟨x, hxt, rfl⟩, hk, fun z ↦ ?_⟩
  obtain ⟨⟨-, hzconj⟩, hzest⟩ := ht _ (hWt z)
  exact ⟨rfl, hzconj _, hzest⟩

/-- **The local fixed-point index is invariant under smooth changes of coordinates.** Let
`f : U → E` and `g : V → E` be continuous maps of open subsets of `E`, and let `x` be a fixed point
of `f`. If a map `h : E → E` with invertible strict derivative at `x` conjugates `f` to `g` near
`x`, that is `g (h z) = h (f z)` for `z` near `x`, then the local fixed-point index of `g` at `h x`
is that of `f` at `x`. This holds whether or not `h` preserves orientation. In particular, the
local fixed-point index of a self-map of a smooth manifold at an isolated fixed point does not
depend on the chart in which it is computed. -/
theorem localFixedPointIndex_eq_of_hasStrictFDerivAt {V : Opens E} {f : C(U, E)} {g : C(V, E)}
    {x : U} (hx : f x = x) {h : E → E} {A : E ≃L[ℝ] E}
    (hh : HasStrictFDerivAt h (A : E →L[ℝ] E) x) (hxV : h x ∈ V)
    (hconj : ∀ᶠ z : U in 𝓝 x, ∀ hz : h z ∈ V, g ⟨h z, hz⟩ = h (f z)) :
    g.localFixedPointIndex ⟨h x, hxV⟩ = f.localFixedPointIndex x := by
  obtain ⟨W, hWU, k, hxW, hk, hkW⟩ := exists_opens_isOpenEmbedding_conj hx hh hxV hconj
  set o := fixedPointOrientation (E := E)
  have hdet : (A : E →L[ℝ] E).det ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  let ι : C(W, U) := inclusion hWU
  set xW : W := ⟨x, hxW⟩
  -- `ι xW` is `x`, by definition of the inclusion.
  have hιx : inclusion hWU xW = x := rfl
  have hfW : (f.comp ι) xW = xW := by rw [comp_apply, hιx]; exact hx
  have hkx : k xW = ⟨h x, hxV⟩ := Subtype.ext (hkW xW).1
  -- Read on `W`, the displacement of `g` through `k` is `z ↦ h z - h (f z)`, within half its
  -- norm of `z ↦ A (z - f z)`; so the two maps have the same local index at `x`.
  let Ac : C(E, E) := ⟨A, A.continuous⟩
  have hcomp : (o.comap W.isOpenEmbedding').localIndex o (Ac.comp (f.comp ι).displacement) xW =
      (o.comap W.isOpenEmbedding').localIndex o (g.displacement.comp k) xW := by
    have hG (z : W) : (g.displacement.comp k) z = h z - h ((f.comp ι) z) := by
      rw [comp_apply, displacement_apply, (hkW z).2.1, (hkW z).1]
      -- `f.comp ι` is `f ∘ inclusion hWU` by definition.
      rfl
    have hAD (z : W) : (Ac.comp (f.comp ι).displacement) z = A (z - (f.comp ι) z) := by
      rw [comp_apply, displacement_apply]
      -- `Ac` is `A` as a continuous map, by definition.
      rfl
    refine HomologicalOrientation.localIndex_eq_of_norm_sub_le _ _ rfl rfl one_half_lt_one
      (by rw [hG, hAD, hfW, sub_self, sub_self, map_zero]) (.of_forall fun z ↦ ?_)
    rw [hG, hAD, hAD xW, hfW, sub_self, map_zero, sub_zero, one_div_mul_eq_div]
    exact (hkW z).2.2
  -- By the chain rule, both sides are `sign det A` times a local fixed-point index.
  have hL : (o.comap W.isOpenEmbedding').localIndex o (Ac.comp (f.comp ι).displacement) xW =
      SignType.sign (A : E →L[ℝ] E).det * f.localFixedPointIndex x := by
    rw [(o.comap W.isOpenEmbedding').localIndex_comp o o rfl
        (eventually_nhdsWithin_of_forall fun z hz ↦ A.injective.ne hz),
      displacement_apply, hfW, sub_self,
      o.localIndex_eq_sign_det rfl (f := Ac) (A : E →L[ℝ] E).hasFDerivAt hdet,
      ← (f.comp ι).localFixedPointIndex_eq_localIndex o rfl hfW,
      localFixedPointIndex_comp_inclusion, hιx]
  have hR : (o.comap W.isOpenEmbedding').localIndex o (g.displacement.comp k) xW =
      SignType.sign (A : E →L[ℝ] E).det * g.localFixedPointIndex ⟨h x, hxV⟩ := by
    rw [(o.comap W.isOpenEmbedding').localIndex_comp_of_isOpenEmbedding
        (o.comap V.isOpenEmbedding') o rfl hk xW,
      o.localIndex_comap_eq_sign_det rfl W.isOpenEmbedding' V.isOpenEmbedding' (f := k) (φ := h)
        (.of_forall fun z ↦ ((hkW z).1).symm) (HasStrictFDerivAt.hasFDerivAt hh) hdet,
      ← g.localFixedPointIndex_eq_localIndex o rfl (x := k xW)
        (by rw [(hkW xW).2.1, (hkW xW).1]; exact congrArg h hfW), hkx, mul_comm]
  -- `sign det A ≠ 0` in `SignType`, and the cast `SignType → ℤ` is injective.
  have hs : (SignType.sign (A : E →L[ℝ] E).det : ℤ) ≠ 0 := by
    have hs := sign_ne_zero.2 hdet
    generalize SignType.sign (A : E →L[ℝ] E).det = s at hs ⊢
    decide +revert
  exact (mul_left_cancel₀ hs (hL.symm.trans (hcomp.trans hR))).symm

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

/-- A homotopy `H` of maps `W → X` of an open set `W` of `X` has a compact fixed set
`{(t, z) | H (t, z) = z}` when its fixed points `(t, z)`, read in `[0, 1] × X`, form a compact
set `F`. This turns a fixed set computed from an ambient formula on `[0, 1] × X` into the
hypothesis of `ContinuousMap.fixedPointIndex_eq_of_homotopy`. -/
theorem Homotopy.isCompact_setOf_apply_eq_of_isCompact {X : Type*} [TopologicalSpace X]
    {W : Opens X} {f₀ f₁ : C(W, X)} (H : f₀.Homotopy f₁) {F : Set (unitInterval × X)}
    (hF : IsCompact F) (hFW : ∀ p ∈ F, p.2 ∈ (W : Set X))
    (hHF : ∀ (t : unitInterval) (z : W), H (t, z) = z ↔ (t, (z : X)) ∈ F) :
    IsCompact {p : unitInterval × W | H p = p.2} := by
  rw [(IsEmbedding.id.prodMap IsEmbedding.subtypeVal).isCompact_iff]
  convert hF using 1
  ext ⟨t, x⟩
  constructor
  · rintro ⟨⟨t', z⟩, hp, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact (hHF t' z).1 hp
  · intro hx
    exact ⟨(t, ⟨x, hFW _ hx⟩), (hHF t ⟨x, hFW _ hx⟩).2 hx, rfl⟩

/-- The end map `f₁` of a homotopy `H` of maps `W → X` of an open set `W` of `X` whose fixed set
`{(t, z) | H (t, z) = z}` is compact has a compact fixed set. With
`ContinuousMap.fixedPointIndex_eq_of_homotopy`, this lets the index of `f₁` be computed further. -/
theorem Homotopy.isCompact_setOf_apply_one_eq {X : Type*} [TopologicalSpace X]
    {W : Opens X} {f₀ f₁ : C(W, X)} (H : f₀.Homotopy f₁)
    (hH : IsCompact {p : unitInterval × W | H p = p.2}) : IsCompact {z | f₁ z = z} := by
  have h := (hH.inter_right ((isClosed_singleton (x := (1 : unitInterval))).prod
    isClosed_univ)).image continuous_snd
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨(1, z), ⟨by simpa using hz, by simp⟩, rfl⟩
  · rintro ⟨⟨t, z⟩, ⟨hp, ht, -⟩, rfl⟩
    rw [mem_singleton_iff] at ht
    subst ht
    simpa using hp

/-- **The fixed-point index of a linear map**: if `f : U → E` is the restriction of a linear map
`A` to an open set containing `0`, and `1 - A` is invertible, then the fixed-point index of `f` is
`sign det (1 - A)`. -/
theorem fixedPointIndex_eq_sign_det_of_forall_eq {f : C(U, E)} {A : E →L[ℝ] E} (h0 : (0 : E) ∈ U)
    (hf : ∀ z : U, f z = A z) (hdet : (1 - A).det ≠ 0) :
    f.fixedPointIndex = SignType.sign (1 - A).det := by
  have hinj : Function.Injective ((1 : E →L[ℝ] E) - A) :=
    ((1 - A).toContinuousLinearEquivOfDetNeZero hdet).injective
  -- Since `1 - A` is injective, `0` is the only fixed point of `f`.
  have hfix : {z | f z = z} = {⟨0, h0⟩} := by
    ext z
    rw [mem_ofPred_eq, mem_singleton_iff, hf, Subtype.ext_iff]
    constructor
    · intro hz
      exact hinj (by simp [hz])
    · intro hz
      simp [hz]
  rw [f.fixedPointIndex_eq_localFixedPointIndex hfix]
  exact f.localFixedPointIndex_eq_sign_det (x := ⟨0, h0⟩) (by simp [hf])
    (.of_forall fun z ↦ (hf z).symm) A.hasFDerivAt hdet

/-- For `t ≥ 0`, the only fixed point of `x ↦ x + x³ + t x` on `ℝ` is `0`. -/
private theorem eq_zero_of_add_pow_three_add_mul_eq {t z : ℝ} (ht : 0 ≤ t)
    (hz : z + z ^ 3 + t * z = z) : z = 0 := by
  have h : z * (z ^ 2 + t) = 0 := by linear_combination hz
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · nlinarith [sq_nonneg z]

/-- **A degenerate fixed point of index `-1`**: the map `x ↦ x + x³` on `ℝ`, whose fixed point `0`
is degenerate, has fixed-point index `-1`. -/
theorem fixedPointIndex_add_pow_three :
    (⟨fun z : (⊤ : Opens ℝ) ↦ (z : ℝ) + (z : ℝ) ^ 3, by fun_prop⟩ :
      C((⊤ : Opens ℝ), ℝ)).fixedPointIndex = -1 := by
  set g₁ : C((⊤ : Opens ℝ), ℝ) := ⟨fun z ↦ 2 * (z : ℝ) + (z : ℝ) ^ 3, by fun_prop⟩
  -- The homotopy `x + x³ + t x`, `t ∈ [0, 1]`, from `x + x³` to `2 x + x³` has fixed set
  -- `[0, 1] × {0}`, and ends at a map with derivative `2` at its only fixed point `0`.
  let H : ContinuousMap.Homotopy (⟨fun z : (⊤ : Opens ℝ) ↦ (z : ℝ) + (z : ℝ) ^ 3, by fun_prop⟩ :
      C((⊤ : Opens ℝ), ℝ)) g₁ :=
    { toFun := fun p ↦ (p.2 : ℝ) + (p.2 : ℝ) ^ 3 + (p.1 : ℝ) * p.2
      continuous_toFun := by fun_prop
      map_zero_left := fun z ↦ by simp
      map_one_left := fun z ↦ by simp [g₁, two_mul, add_right_comm] }
  -- `H p` is its defining formula by construction.
  have hHapply (p : unitInterval × (⊤ : Opens ℝ)) :
      H p = (p.2 : ℝ) + (p.2 : ℝ) ^ 3 + (p.1 : ℝ) * p.2 := rfl
  have hH : {p : unitInterval × (⊤ : Opens ℝ) | H p = p.2} = univ ×ˢ {⟨0, trivial⟩} := by
    ext ⟨t, z⟩
    simp only [mem_ofPred_eq, mem_prod, mem_univ, mem_singleton_iff, true_and, Subtype.ext_iff,
      hHapply]
    constructor
    · exact eq_zero_of_add_pow_three_add_mul_eq t.property.1
    · intro hz
      simp [hz]
  rw [fixedPointIndex_eq_of_homotopy H (hH ▸ isCompact_univ.prod isCompact_singleton)]
  -- The map `2 x + x³` has derivative `2` at its only fixed point `0`.
  have hfix : {z | g₁ z = z} = {⟨0, trivial⟩} := by
    ext z
    simp only [mem_ofPred_eq, mem_singleton_iff, Subtype.ext_iff, g₁, ContinuousMap.coe_mk]
    constructor
    · intro hz
      exact eq_zero_of_add_pow_three_add_mul_eq zero_le_one (by linear_combination hz)
    · intro hz
      simp [hz]
  have hd :
      HasFDerivAt (fun z : ℝ ↦ 2 * z + z ^ 3) (ContinuousLinearMap.toSpanSingleton ℝ 2) 0 := by
    have h : HasDerivAt (fun z : ℝ ↦ 2 * z + z ^ 3) 2 0 := by
      convert HasDerivAt.add (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id' (0 : ℝ)))
        (hasDerivAt_pow 3 (0 : ℝ)) using 1
      norm_num
    exact h.hasFDerivAt
  have hdet : (1 - ContinuousLinearMap.toSpanSingleton ℝ (2 : ℝ)).det = -1 := by
    norm_num [ContinuousLinearMap.det]
  rw [g₁.fixedPointIndex_eq_localFixedPointIndex hfix,
    g₁.localFixedPointIndex_eq_sign_det (x := ⟨0, trivial⟩) (by simp [g₁])
      (.of_forall fun z ↦ by simp [g₁]) hd (by norm_num [hdet]), hdet]
  simp

end ContinuousMap
