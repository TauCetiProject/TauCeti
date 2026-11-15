/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
import Mathlib.Topology.Homotopy.Affine

/-!
# The local index of a map at an isolated point of its fibre

Let `M` and `N` be topological manifolds of the same dimension `n`, oriented by `o` and `o'`
(`TauCeti.HomologicalOrientation`), and let `f : M → N` be continuous. A point `x` is *isolated in
its fibre* when some open neighbourhood `U` of `x` meets `f⁻¹(f x)` only in `x`. Then `f`
restricts to a map of pairs `(U, U ∖ {x}) → (N, N ∖ {f x})`. By excision the local homology
`Hₙ(U, U ∖ {x}; ℤ)` is that of `M` at `x`, so the local orientation `o x` is a class there, and
its image is an integer multiple of the local orientation `o' (f x)`. That integer is the
**local index** `o.localIndex o' f x` of `f` at `x`. It does not depend on the choice of `U`
(`TauCeti.HomologicalOrientation.localIndex_eq_iff`), only on the germ of `f` at `x`
(`TauCeti.HomologicalOrientation.localIndex_congr`), and it is `0` by convention when `x` is not
isolated in its fibre. It is natural under open embeddings
(`TauCeti.HomologicalOrientation.localIndex_comap`): the local index of a map between open
subsets, oriented by restriction, is that of any map of the ambient manifolds extending it near
the point.

The local degree of `f` at a point `y` with finite fibre is the sum of the local indices at the
points of the fibre (`TauCeti.HomologicalOrientation.localDegree_eq_sum_localIndex`): the
fundamental class of `M` along the fibre decomposes as the sum of the local orientations at its
points, each pushed forward from a small neighbourhood of that point. For a proper map onto a
connected manifold the degree is therefore the sum of the local indices over any finite fibre
(`TauCeti.HomologicalOrientation.degree_eq_sum_localIndex`). This is how a degree is computed by
counting the preimages of a regular value with signs, once the local index at a regular point is
identified with the sign of the Jacobian. At a point where `f` is a local homeomorphism the local
index is `±1`
(`TauCeti.HomologicalOrientation.localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn`), so a
proper map whose fibre over a point of a connected target is a single such point has degree `±1`.

## Main definitions

* `TauCeti.HomologicalOrientation.localIndex o o' f x`: the local index of `f` at `x`.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_iff`: the defining property of the local index,
  in any open neighbourhood isolating `x` in its fibre.
* `TauCeti.HomologicalOrientation.localIndex_congr`: maps agreeing near `x` have the same local
  index at `x`.
* `TauCeti.HomologicalOrientation.localIndex_comap`: the local index is natural under open
  embeddings of the source and target, with the pulled-back orientations.
* `TauCeti.HomologicalOrientation.localDegree_eq_sum_localIndex`: the local degree at a point with
  finite fibre is the sum of the local indices over the fibre.
* `TauCeti.HomologicalOrientation.degree_eq_sum_localIndex`: the degree of a proper map onto a
  preconnected manifold is the sum of the local indices over any finite fibre.
* `TauCeti.HomologicalOrientation.localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn`: a
  local homeomorphism has local index `±1`.
* `TauCeti.HomologicalOrientation.degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn`: a proper
  map with a one-point fibre, at whose point it is a local homeomorphism, has degree `±1`.
* `TauCeti.HomologicalOrientation.localIndex_addRight`: translations of a finite-dimensional real
  normed space have local index one, being properly homotopic to the identity.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4 (the degree as a
  sum of local indices).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Proposition 2.30 (the degree of a map of spheres as a sum of local degrees).
-/

public section

noncomputable section

open CategoryTheory Filter Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

variable {M N E F : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  {n : ℕ} (o : HomologicalOrientation M E n) (o' : HomologicalOrientation N F n)
  (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)

omit [T2Space M] [T2Space N] in
/-- In a neighbourhood `U` of `x` meeting the fibre of `f` through `y` only in `x`, the restriction
of `f` is a map of pairs `(U, U ∖ {x}) → (N, N ∖ {y})`. -/
private theorem restrict_preimage_subset (f : C(M, N)) {x : M} {y : N} {U : Set M} (hx : x ∈ U)
    (hU : ∀ z ∈ U, f z = y → z = x) : f.restrict U ⁻¹' {y} ⊆ {⟨x, hx⟩} :=
  fun z hz ↦ Subtype.ext (hU z z.2 (by simpa using hz))

/-- The image of the local orientation `o x` under the restriction of `f` to an open neighbourhood
`U` of `x` meeting the fibre of `f` through `y` only in `x`, computed through the excision
isomorphism of the local homology of `U` at `x` with that of `M`. -/
private def localIndexClass (f : C(M, N)) {x : M} {y : N} {U : Set M} (hUo : IsOpen U)
    (hx : x ∈ U) (hU : ∀ z ∈ U, f z = y → z = x) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({y} : Set N) n :=
  localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f.restrict U)
    (restrict_preimage_subset f hx hU) n
    ((hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x)).val

omit [T2Space N] in
/-- Shrinking the isolating neighbourhood does not change the image of the local orientation. -/
private theorem localIndexClass_of_subset (f : C(M, N)) {x : M} {y : N} {U V : Set M}
    (hUo : IsOpen U) (hVo : IsOpen V) (hVU : V ⊆ U) (hx : x ∈ V)
    (hU : ∀ z ∈ U, f z = y → z = x) :
    o.localIndexClass f hVo hx (fun z hz ↦ hU z (hVU hz)) =
      o.localIndexClass f hUo (hVU hx) hU := by
  have hincl : ContinuousMap.inclusion hVU ⁻¹' {⟨x, hVU hx⟩} ⊆ {⟨x, hx⟩} :=
    fun z hz ↦ Subtype.ext (by simpa [Subtype.ext_iff] using hz)
  -- The inclusion `V → U` carries the local orientation of `V` at `x` to that of `U` at `x`.
  have hmap := hUo.localHomologyMap_inclusion_localOrientationEquiv_symm hVo hVU hx (o x) hincl
  have hcomp : (f.restrict U).comp (ContinuousMap.inclusion hVU) = f.restrict V :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [localIndexClass, localIndexClass, ← hmap, ← ConcreteCategory.comp_apply,
    localHomologyMap_comp]
  simp only [hcomp]

omit [T2Space N] in
/-- The image of the local orientation does not depend on the isolating neighbourhood. -/
private theorem localIndexClass_eq (f : C(M, N)) {x : M} {y : N} {U V : Set M} (hUo : IsOpen U)
    (hVo : IsOpen V) (hxU : x ∈ U) (hxV : x ∈ V) (hU : ∀ z ∈ U, f z = y → z = x)
    (hV : ∀ z ∈ V, f z = y → z = x) :
    o.localIndexClass f hUo hxU hU = o.localIndexClass f hVo hxV hV :=
  (o.localIndexClass_of_subset f hUo (hUo.inter hVo) inter_subset_left ⟨hxU, hxV⟩ hU).symm.trans
    (o.localIndexClass_of_subset f hVo (hUo.inter hVo) inter_subset_right ⟨hxU, hxV⟩ hV)

omit [TopologicalSpace N] [T2Space M] [T2Space N] in
/-- A point isolated in its fibre has an open neighbourhood meeting the fibre only in that point. -/
private theorem exists_isOpen_of_eventually_ne {f : M → N} {x : M}
    (h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x) :
    ∃ U : Set M, IsOpen U ∧ ∃ _ : x ∈ U, ∀ z ∈ U, f z = f x → z = x := by
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
  exact ⟨U, hUo, hxU, fun z hz hfz ↦ by_contra fun hzx ↦ hU z hz hzx hfz⟩

open scoped Classical in
/-- The **local index** of `f : M → N` at `x ∈ M`: when `x` is isolated in its fibre `f⁻¹(f x)`,
the integer `d` such that the restriction of `f` to an open neighbourhood `U` of `x` meeting the
fibre only in `x` carries the local orientation `o x` to `d • o' (f x)` in `Hₙ(N, N ∖ {f x}; ℤ)`
(`TauCeti.HomologicalOrientation.localIndex_eq_iff`), and `0` when `x` is not isolated in its
fibre. -/
def localIndex (f : C(M, N)) (x : M) : ℤ :=
  if h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x then
    have hU := exists_isOpen_of_eventually_ne h
    ((isLocalOrientation_iff _ _ _).1 (o' (f x)).property
      (o.localIndexClass f hU.choose_spec.1 hU.choose_spec.2.choose
        hU.choose_spec.2.choose_spec)).choose
  else 0

/-- In an open neighbourhood `U` of `x` meeting the fibre of `f` through `y = f x` only in `x`, the
restriction of `f` carries the local orientation `o x` to the local index times `o' y`. -/
theorem localHomologyMap_restrict_localOrientationEquiv_symm (f : C(M, N)) {x : M} {y : N}
    (hxy : f x = y) {U : Set M} (hUo : IsOpen U) (hx : x ∈ U) (hU : ∀ z ∈ U, f z = y → z = x) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f.restrict U) (S := {⟨x, hx⟩}) (T := {y})
        (fun z hz ↦ Subtype.ext (hU z z.2 (by simpa using hz))) n
        ((hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x)).val =
      o.localIndex o' f x • (o' y).val := by
  subst hxy
  have h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
    eventually_nhdsWithin_iff.2 (eventually_of_mem (hUo.mem_nhds hx)
      fun z hz hzx hfz ↦ hzx (hU z hz hfz))
  rw [localIndex, dite_eq_left h]
  have hV := exists_isOpen_of_eventually_ne h
  refine Eq.trans ?_ ((isLocalOrientation_iff _ _ _).1 (o' (f x)).property _).choose_spec.symm
  exact o.localIndexClass_eq f hUo hV.choose_spec.1 hx hV.choose_spec.2.choose hU
    hV.choose_spec.2.choose_spec

include hF in
/-- **The defining property of the local index**: in an open neighbourhood `U` of `x` meeting the
fibre of `f` through `y = f x` only in `x`, the local index is the integer `c` such that the
restriction of `f` to `U` carries the local orientation `o x`, read in `U` through excision, to
`c • o' y`. -/
theorem localIndex_eq_iff (f : C(M, N)) {x : M} {y : N} (hxy : f x = y) {U : Set M}
    (hUo : IsOpen U) (hx : x ∈ U) (hU : ∀ z ∈ U, f z = y → z = x) {c : ℤ} :
    o.localIndex o' f x = c ↔
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f.restrict U) (S := {⟨x, hx⟩}) (T := {y})
          (fun z hz ↦ Subtype.ext (hU z z.2 (by simpa using hz))) n
          ((hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x)).val =
        c • (o' y).val := by
  rw [o.localHomologyMap_restrict_localOrientationEquiv_symm o' f hxy hUo hx hU]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ o'.zsmul_left_injective hF y h⟩

/-- The local index vanishes at a point which is not isolated in its fibre. -/
theorem localIndex_of_frequently_eq (f : C(M, N)) {x : M} (h : ∃ᶠ z in 𝓝[≠] x, f z = f x) :
    o.localIndex o' f x = 0 := by
  rw [localIndex, dite_eq_right (not_eventually.2 (by simpa using h))]

include hF in
/-- **The local index only depends on the germ of the map**: maps agreeing on a neighbourhood of
`x` have the same local index at `x`. -/
theorem localIndex_congr {f g : C(M, N)} {x : M} (hfg : f =ᶠ[𝓝 x] g) :
    o.localIndex o' f x = o.localIndex o' g x := by
  have hfgx : f x = g x := hfg.eq_of_nhds
  have hfg' : ∀ᶠ z in 𝓝[≠] x, f z = g z := eventually_nhdsWithin_of_eventually_nhds hfg
  by_cases hf : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · -- An open neighbourhood isolating `x` for `f`, shrunk into a neighbourhood `W` on which the
    -- two maps agree, isolates `x` for `g`, and the two restrictions coincide there.
    obtain ⟨U, hUo, hxU, hU⟩ := exists_isOpen_of_eventually_ne hf
    obtain ⟨W, hWfg, hWo, hxW⟩ := eventually_nhds_iff.1 hfg
    have hfU : ∀ z ∈ U ∩ W, f z = f x → z = x := fun z hz ↦ hU z hz.1
    have hgU : ∀ z ∈ U ∩ W, g z = f x → z = x := fun z hz hgz ↦
      hU z hz.1 ((hWfg z hz.2).trans hgz)
    have hrestrict : g.restrict (U ∩ W) = f.restrict (U ∩ W) :=
      ContinuousMap.ext fun z ↦ (hWfg z z.2.2).symm
    rw [eq_comm, o.localIndex_eq_iff o' hF g hfgx.symm (hUo.inter hWo) (mem_inter hxU hxW) hgU,
      ← o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl (hUo.inter hWo)
        (mem_inter hxU hxW) hfU]
    simp only [hrestrict]
  · have hg : ∃ᶠ z in 𝓝[≠] x, g z = g x :=
      ((not_eventually.1 hf).and_eventually hfg').mono fun z h ↦ by
        rw [← h.2, ← hfgx]
        exact not_not.1 h.1
    rw [o.localIndex_of_frequently_eq o' f (by simpa using not_eventually.1 hf),
      o.localIndex_of_frequently_eq o' g hg]

include hF in
/-- Reversing the orientation of the source negates the local index. -/
@[simp]
theorem localIndex_neg_left (f : C(M, N)) (x : M) :
    (-o).localIndex o' f x = -o.localIndex o' f x := by
  by_cases h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · obtain ⟨U, hUo, hx, hU⟩ := exists_isOpen_of_eventually_ne h
    have hneg : (hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (-o x) =
        -(hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ n).symm (o x) :=
      (Equiv.symm_apply_eq _).2 (by
        rw [IsOpenEmbedding.localOrientationEquiv_neg, Equiv.apply_symm_apply])
    rw [(-o).localIndex_eq_iff o' hF f rfl hUo hx hU, neg_apply, hneg, LocalOrientation.coe_neg,
      map_neg, o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl hUo hx hU,
      neg_zsmul]
  · have h' : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 h
    rw [(-o).localIndex_of_frequently_eq o' f h', o.localIndex_of_frequently_eq o' f h', neg_zero]

include hF in
/-- Reversing the orientation of the target negates the local index. -/
@[simp]
theorem localIndex_neg_right (f : C(M, N)) (x : M) :
    o.localIndex (-o') f x = -o.localIndex o' f x := by
  by_cases h : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · obtain ⟨U, hUo, hx, hU⟩ := exists_isOpen_of_eventually_ne h
    rw [o.localIndex_eq_iff (-o') hF f rfl hUo hx hU,
      o.localHomologyMap_restrict_localOrientationEquiv_symm o' f rfl hUo hx hU, neg_apply,
      LocalOrientation.coe_neg, neg_zsmul, zsmul_neg, neg_neg]
  · have h' : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 h
    rw [o.localIndex_of_frequently_eq (-o') f h', o.localIndex_of_frequently_eq o' f h', neg_zero]

include hF in
/-- **The local index is natural under open embeddings.** Let `j : M → M'` and `k : N → N'` be
open embeddings, and let `f : M → N` and `g : M' → N'` satisfy `g ∘ j = k ∘ f` near `x`. Then the
local index of `f` at `x`, for the orientations pulled back along `j` and `k`, is the local index
of `g` at `j x`. In particular the local index of a map between open subsets is computed in the
ambient manifolds. -/
theorem localIndex_comap {M' N' : Type} [TopologicalSpace M'] [T2Space M'] [ChartedSpace E M']
    [TopologicalSpace N'] [T2Space N'] [ChartedSpace F N'] (O : HomologicalOrientation M' E n)
    (O' : HomologicalOrientation N' F n) {j : M → M'} (hj : IsOpenEmbedding j) {k : N → N'}
    (hk : IsOpenEmbedding k) {f : C(M, N)} {g : C(M', N')} {x : M}
    (h : ∀ᶠ z in 𝓝 x, g (j z) = k (f z)) :
    (O.comap hj).localIndex (O'.comap hk) f x = O.localIndex O' g (j x) := by
  by_cases hfx : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · -- An open neighbourhood `U` of `x` isolating `x` in its fibre, on which `g ∘ j = k ∘ f`; its
    -- image `j '' U` isolates `j x` in its fibre under `g`.
    obtain ⟨W, hWo, hxW, hW⟩ := exists_isOpen_of_eventually_ne hfx
    obtain ⟨W₁, hW₁, hW₁o, hxW₁⟩ := eventually_nhds_iff.1 h
    have hUo : IsOpen (W ∩ W₁) := hWo.inter hW₁o
    have hxU : x ∈ W ∩ W₁ := ⟨hxW, hxW₁⟩
    have hU : ∀ z ∈ W ∩ W₁, f z = f x → z = x := fun z hz ↦ hW z hz.1
    have hU'o : IsOpen (j '' (W ∩ W₁)) := hj.isOpenMap _ hUo
    have hxU' : j x ∈ j '' (W ∩ W₁) := mem_image_of_mem j hxU
    have hU' : ∀ z ∈ j '' (W ∩ W₁), g z = k (f x) → z = j x := by
      rintro _ ⟨z, hz, rfl⟩ hgz
      rw [hW₁ z hz.2] at hgz
      rw [hU z hz (hk.injective hgz)]
    -- `j` identifies `U` with `j '' U`, compatibly with the local orientations at `x` and `j x`.
    let ψ : C(↥(W ∩ W₁), ↥(j '' (W ∩ W₁))) :=
      ⟨fun z ↦ ⟨j z, mem_image_of_mem j z.2⟩,
        (hj.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hψ : IsOpenEmbedding ψ :=
      (IsOpenEmbedding.of_comp_iff ψ hU'o.isOpenEmbedding_subtypeVal).1
        (hj.comp hUo.isOpenEmbedding_subtypeVal)
    have hclass : (hUo.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hxU⟩ n).symm
        (O.comap hj x) = (hψ.localOrientationEquiv ⟨x, hxU⟩ n).symm
          ((hU'o.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨j x, hxU'⟩ n).symm
            (O (j x))) := by
      rw [comap_apply, ← Equiv.symm_trans_apply, IsOpenEmbedding.localOrientationEquiv_trans,
        ← Equiv.symm_trans_apply]
      -- Both sides are the local orientation equivalence of `j ∘ Subtype.val = Subtype.val ∘ ψ`.
      exact (congrArg (fun e ↦ e.symm (O (j x))) (IsOpenEmbedding.localOrientationEquiv_trans hψ
        hU'o.isOpenEmbedding_subtypeVal ⟨x, hxU⟩ n)).symm
    have hψx : ψ ⁻¹' {ψ ⟨x, hxU⟩} ⊆ {⟨x, hxU⟩} := fun z hz ↦ hψ.injective hz
    have hkx : (⟨k, hk.continuous⟩ : C(N, N')) ⁻¹' {k (f x)} ⊆ {f x} :=
      fun z hz ↦ hk.injective hz
    -- Push the defining identity of the local index of `f` forward along `k`.
    have hA := (O.comap hj).localHomologyMap_restrict_localOrientationEquiv_symm (O'.comap hk) f
      rfl hUo hxU hU
    have h2 := congrArg (ConcreteCategory.hom (localHomologyMap (A := ModuleCat.{0} ℤ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨k, hk.continuous⟩ hkx n)) hA
    rw [map_zsmul, comap_apply O' hk, hk.localHomologyMap_localOrientationEquiv_symm _ _ hkx] at h2
    -- Pull the local orientation of `j '' U` at `j x` back along `ψ`.
    have h3 := hψ.localHomologyMap_localOrientationEquiv_symm ⟨x, hxU⟩
      ((hU'o.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨j x, hxU'⟩ n).symm (O (j x))) hψx
    -- The two composites `W ∩ W₁ → N'` agree.
    have e : (g.restrict (j '' (W ∩ W₁))).comp ⟨ψ, hψ.continuous⟩ =
        (⟨k, hk.continuous⟩ : C(N, N')).comp (f.restrict (W ∩ W₁)) :=
      ContinuousMap.ext fun z ↦ hW₁ z z.2.2
    -- Both composites act on local homology as the composites of the induced maps.
    have hc : ∀ {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (a : C(↥(W ∩ W₁), P))
        (b : C(P, Q)) {S : Set P} {T : Set Q} (ha : a ⁻¹' S ⊆ {⟨x, hxU⟩}) (hb : b ⁻¹' T ⊆ S) z,
        ConcreteCategory.hom (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) b hb n)
            (ConcreteCategory.hom (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) a ha n) z) =
          ConcreteCategory.hom (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (b.comp a)
            ((preimage_mono hb).trans ha) n) z := by
      intros
      rw [← localHomologyMap_comp]
      rfl
    rw [eq_comm, O.localIndex_eq_iff O' hF g (hW₁ x hxW₁) hU'o hxU' hU', ← h2, hclass]
    exact (congrArg _ h3.symm).trans ((hc _ _ _ _ _).trans
      ((ConcreteCategory.congr_hom (localHomologyMap_congr _ e _ n) _).trans
        (hc _ _ _ _ _).symm))
  · -- If `x` is not isolated in its fibre, neither is `j x`, and both local indices vanish.
    have hf : ∃ᶠ z in 𝓝[≠] x, f z = f x := by simpa using not_eventually.1 hfx
    have hj' : Tendsto j (𝓝[≠] x) (𝓝[≠] (j x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hj.continuous.tendsto x |>.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun z hz ↦ hj.injective.ne hz)
    have hg : ∃ᶠ z in 𝓝[≠] (j x), g z = g (j x) :=
      hj'.frequently ((hf.and_eventually (eventually_nhdsWithin_of_eventually_nhds h)).mono
        fun z hz ↦ hz.2.trans ((congrArg k hz.1).trans h.self_of_nhds.symm))
    rw [(O.comap hj).localIndex_of_frequently_eq (O'.comap hk) f hf,
      O.localIndex_of_frequently_eq O' g hg]

omit [T2Space M] in
/-- The complement of `S ∖ {x}` meets `S` only in `x`. -/
private theorem compl_diff_preimage_subset (S : Set M) (x : M) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(S \ {x})ᶜ, M)) ⁻¹' S ⊆
      {⟨x, fun h ↦ h.2 rfl⟩} :=
  fun z hz ↦ Subtype.ext (by_contra fun h ↦ z.2 ⟨hz, h⟩)

/-- The local orientation at a point `x` of a finite set `S`, pushed forward from the complement of
`S ∖ {x}` to a class of `Hₙ(M, M ∖ S)`. -/
private def compClass {S : Set M} (hS : S.Finite) (x : M) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) S n :=
  localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨Subtype.val, continuous_subtype_val⟩
    (compl_diff_preimage_subset S x) n
    (((hS.sdiff.isClosed.isOpen_compl).isOpenEmbedding_subtypeVal.localOrientationEquiv
      ⟨x, fun h ↦ h.2 rfl⟩ n).symm (o x)).val

/-- The class of `x` restricts to the local orientation `o x` at `x`. -/
private theorem localHomologyRestriction_compClass_self {S : Set M} (hS : S.Finite) {x : M}
    (hx : x ∈ S) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hx) n
      (o.compClass hS x) = (o x).val := by
  rw [compClass, ← ConcreteCategory.comp_apply, localHomologyMap_comp_localHomologyRestriction]
  exact IsOpenEmbedding.localHomologyMap_localOrientationEquiv_symm
    (hS.sdiff.isClosed.isOpen_compl).isOpenEmbedding_subtypeVal ⟨x, fun h ↦ h.2 rfl⟩ (o x) _

/-- The class of `x` restricts to `0` at every other point `x'` of `S`: the complement of
`S ∖ {x}` misses `x'`, so the restriction factors through `Hₙ(U, U) = 0`. -/
private theorem localHomologyRestriction_compClass_of_ne {S : Set M} (hS : S.Finite) {x x' : M}
    (hx' : x' ∈ S) (hxx' : x ≠ x') :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hx') n
      (o.compClass hS x) = 0 := by
  have hempty : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(S \ {x})ᶜ, M)) ⁻¹' {x'} ⊆ ∅ :=
    fun z (hz : (z : M) = x') ↦ z.2 ⟨hz ▸ hx', fun h ↦ hxx' (hz ▸ h).symm⟩
  rw [compClass, ← ConcreteCategory.comp_apply, localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap _ _ (empty_subset _) hempty,
    ConcreteCategory.comp_apply,
    (isZero_localHomology_empty (A := ModuleCat.{0} ℤ) _ n).eq_of_tgt
      (localHomologyRestriction _ (empty_subset _) n) 0]
  simp

/-- The classes of the points of a finite set `S` sum to the fundamental class along `S`. -/
private theorem sum_compClass {S : Set M} (hS : S.Finite) :
    ∑ x ∈ hS.toFinset, o.compClass hS x = o.fundamentalClassOn hE hS.isCompact := by
  refine o.eq_fundamentalClassOn hE hS.isCompact fun x' hx' ↦ ?_
  rw [map_sum, Finset.sum_eq_single_of_mem x' (hS.mem_toFinset.2 hx')
    fun x _ hxx' ↦ o.localHomologyRestriction_compClass_of_ne hS hx' hxx',
    o.localHomologyRestriction_compClass_self hS hx']

include hF in
/-- **The local degree is the sum of the local indices over the fibre**: if the fibre of `f` over
`y` is finite, the local degree of `f` at `y` is the sum of the local indices of `f` at the points
of the fibre. -/
theorem localDegree_eq_sum_localIndex (f : C(M, N)) {y : N} (hy : (f ⁻¹' {y}).Finite) :
    o.localDegree o' hE f y = ∑ x ∈ hy.toFinset, o.localIndex o' f x := by
  rw [localDegree_eq_iff o o' hE hF f hy.isCompact, ← o.sum_compClass hE hy, map_sum]
  -- The class of each point `x` of the fibre is carried by `f` to the local index at `x` times
  -- `o' y`, the complement of the rest of the fibre being a neighbourhood isolating `x`.
  -- The scalar action on the homology group is `zsmul`, so `Finset.sum_smul` is used with the
  -- `ℤ`-module structure `AddCommGroup.toIntModule` rather than the one of `ModuleCat`.
  refine (Finset.sum_congr rfl fun x hx ↦ ?_).trans
    (@Finset.sum_smul _ _ _ _ _ (AddCommGroup.toIntModule _) _ _ _).symm
  rw [compClass, ← ConcreteCategory.comp_apply, localHomologyMap_comp]
  exact o.localHomologyMap_restrict_localOrientationEquiv_symm o' f (hy.mem_toFinset.1 hx)
    hy.sdiff.isClosed.isOpen_compl (fun h ↦ h.2 rfl) fun z hz hfz ↦ by_contra fun h ↦ hz ⟨hfz, h⟩

include hF in
/-- If `x` is the only point of `M` sent to `y`, the local degree of `f` at `y` is the local index
of `f` at `x`. -/
theorem localDegree_eq_localIndex (f : C(M, N)) {x : M} {y : N} (h : f ⁻¹' {y} = {x}) :
    o.localDegree o' hE f y = o.localIndex o' f x := by
  have hfin : (f ⁻¹' {y}).Finite := h ▸ finite_singleton x
  have hs : hfin.toFinset = {x} := by ext; simp [h]
  rw [o.localDegree_eq_sum_localIndex o' hE hF f hfin, hs, Finset.sum_singleton]

include hF in
/-- **The degree is the sum of the local indices over any finite fibre**: for a proper map `f`
onto a preconnected manifold and a point `y` whose fibre is finite, the degree of `f` is the sum
of the local indices of `f` at the points of the fibre over `y`. -/
theorem degree_eq_sum_localIndex [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f) {y : N}
    (hy : (f ⁻¹' {y}).Finite) :
    o.degree o' hE f = ∑ x ∈ hy.toFinset, o.localIndex o' f x := by
  rw [← o.localDegree_eq_degree o' hE hF hf y, o.localDegree_eq_sum_localIndex o' hE hF f hy]

include hE in
/-- The identity has local index `1` at every point. -/
@[simp]
theorem localIndex_id (x : M) : o.localIndex o (ContinuousMap.id M) x = 1 := by
  rw [← o.localDegree_eq_localIndex o hE hE _ (preimage_id (s := {x})), localDegree_id]

include hF in
/-- **A local homeomorphism has local index `±1`.** If `f` is a local homeomorphism at `x`, it
identifies the local homology of `M` at `x` with that of `N` at `f x`. So it carries the local
orientation `o x` to a generator of `Hₙ(N, N ∖ {f x}; ℤ)`, which is `o' (f x)` or its
negative. -/
theorem localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn {f : C(M, N)} {s : Set M}
    (hf : IsLocalHomeomorphOn f s) {x : M} (hx : x ∈ s) :
    o.localIndex o' f x = 1 ∨ o.localIndex o' f x = -1 := by
  obtain ⟨e, hxe, hfe⟩ := hf x hx
  have hU : IsOpenEmbedding (f.restrict e.source) := by
    rw [ContinuousMap.coe_restrict, hfe]
    exact e.isOpenEmbedding_restrict
  have hfib : ∀ z ∈ e.source, f z = f x → z = x := fun z hz hfz ↦
    congrArg Subtype.val (hU.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨x, hxe⟩) hfz)
  -- The restriction of `f` to `e.source` carries the local orientation `o x`, read in
  -- `e.source`, to the local orientation of `N` at `f x` corresponding to it, which is
  -- `± o' (f x)`.
  let w := hU.localOrientationEquiv ⟨x, hxe⟩ n
    ((e.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hxe⟩ n).symm (o x))
  have hw := hU.localHomologyMap_localOrientationEquiv_symm ⟨x, hxe⟩ w
    (fun z hz ↦ Subtype.ext (hfib z z.2 hz))
  rw [Equiv.symm_apply_apply] at hw
  have key (c : ℤ) (hc : w.val = c • (o' (f x)).val) : o.localIndex o' f x = c :=
    (o.localIndex_eq_iff o' hF f rfl e.open_source hxe hfib).2 (hw.trans hc)
  subst hF
  rcases IsLocalOrientation.eq_or_eq_neg
      (singularHomologyComplSingletonFinrankIso _ (chartAt F (f x)) (mem_chart_source F (f x)))
      (o' (f x)).property w.property with h | h
  · exact Or.inl (key 1 (by rw [h, one_zsmul]))
  · exact Or.inr (key (-1) (by rw [h, neg_one_zsmul]))

include hF in
/-- **A map with a one-point fibre at which it is a local homeomorphism has degree `±1`.** For a
proper map `f` onto a preconnected manifold, if `x` is the only point sent to `f x` and `f` is a
local homeomorphism at `x`, then the degree of `f` is `1` or `-1`. -/
theorem degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn [PreconnectedSpace N] {f : C(M, N)}
    (hf : IsProperMap f) {x : M} (hfib : f ⁻¹' {f x} = {x}) {s : Set M}
    (hs : IsLocalHomeomorphOn f s) (hx : x ∈ s) :
    o.degree o' hE f = 1 ∨ o.degree o' hE f = -1 := by
  rw [← o.localDegree_eq_degree o' hE hF hf (f x), o.localDegree_eq_localIndex o' hE hF f hfib]
  exact o.localIndex_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn o' hF hs hx

end HomologicalOrientation

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n)

include hE in
/-- Translations preserve every orientation of a finite-dimensional real normed space: the
translation by `v` has local index `1` at every point, since it is properly homotopic to the
identity. -/
@[simp]
theorem localIndex_addRight (v x : E) : o.localIndex o (ContinuousMap.addRight v) x = 1 := by
  -- The straight-line homotopy from the identity to the translation is proper: it is the
  -- projection `[0, 1] × E → E` composed with the homeomorphism `(t, y) ↦ (t, y + t v)`.
  have hH : IsProperMap (ContinuousMap.Homotopy.affine (ContinuousMap.id E)
      (ContinuousMap.addRight v)) := by
    let Φ : unitInterval × E ≃ₜ unitInterval × E :=
      { toFun := fun p ↦ (p.1, p.2 + (p.1 : ℝ) • v)
        invFun := fun p ↦ (p.1, p.2 - (p.1 : ℝ) • v)
        left_inv := fun p ↦ by simp
        right_inv := fun p ↦ by simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h : ⇑(ContinuousMap.Homotopy.affine (ContinuousMap.id E) (ContinuousMap.addRight v)) =
        Prod.snd ∘ Φ := by
      ext p
      simp [Φ, AffineMap.lineMap_apply_module', add_comm]
    rw [h]
    exact isProperMap_snd_of_compactSpace.comp Φ.isProperMap
  have hdeg := o.degree_eq_of_homotopy o hE hE (ContinuousMap.Homotopy.affine _ _) hH
  rw [degree_id] at hdeg
  have hfib : ContinuousMap.addRight v ⁻¹' {x + v} = {x} := by ext; simp
  rw [← o.localDegree_eq_localIndex o hE hE _ hfib,
    o.localDegree_eq_degree o hE hE (Homeomorph.addRight v).isProperMap, ← hdeg]

end HomologicalOrientation

end TauCeti
