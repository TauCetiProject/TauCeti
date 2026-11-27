/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Derivative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TauCeti.AlgebraicTopology.Singular.LocalHomology.ProperExtension
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.Sard.EqualDimension
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Local indices at regular points and degrees at regular values

Let `E` be a finite-dimensional real normed space, regarded as a manifold modelled on itself and
oriented by a homological orientation `o` (`TauCeti.HomologicalOrientation`). A continuous map
`f : E → E` which is differentiable at `x` with derivative `f'` of nonzero determinant has local
index `sign (det f')` at `x` (`TauCeti.HomologicalOrientation.localIndex_eq_sign_det`), for the
orientation `o` on both source and target. Consequently the degree of a proper map is the signed
count of the preimages of a regular value: if every point of the fibre over `y` has an invertible
derivative, then

`deg f = ∑_{f x = y} sign (det Df(x))`

(`TauCeti.HomologicalOrientation.degree_eq_sum_sign_det`). The fibre is finite as soon as it is
compact (`IsCompact.finite_of_hasFDerivAt`), which is automatic for a proper map.

The local index at a regular point compares `f` with its affine linearization, which acts on
local homology by the sign of its determinant relative to a translation
(`TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`), and translations have
local index one for every orientation (`TauCeti.HomologicalOrientation.localIndex_addRight`).

This identifies the homological degree of a smooth proper map with the classical differential
topological degree.

The same holds for a map `f : U → V` between open subsets of `E`, oriented by restricting `o`
(`TauCeti.HomologicalOrientation.comap`), which agrees on `U` with a map `φ : E → E`, such as a
self-map of an open disc, and more generally for a map read near the point through open embeddings
into `E`. The local index is local, so by its naturality under open embeddings
(`TauCeti.HomologicalOrientation.localIndex_comap`) it can be computed for a map of `E` agreeing
with `φ` near the point, obtained from Tietze's extension theorem
(`TauCeti.HomologicalOrientation.exists_eventuallyEq_and_localIndex_comap_eq`). At a point where
`φ` has invertible derivative it is again the sign of the Jacobian
(`TauCeti.HomologicalOrientation.localIndex_comap_eq_sign_det`), and the degree of a proper map
onto a preconnected open set is the signed count of the preimages of a regular value
(`TauCeti.HomologicalOrientation.degree_comap_eq_sum_sign_det`,
`TauCeti.HomologicalOrientation.degree_comap_eq_ncard_sub_ncard`).

**Changes of coordinates.** Local indices transform under `C¹` changes of coordinates by the sign
of the Jacobian. On the source this is the chain rule: if `φ` is strictly differentiable at `x` with
derivative `φ'` of nonzero determinant, the local index of `F ∘ φ` at `x` is that of `F` at `φ x`
times `sign (det φ')` (`TauCeti.HomologicalOrientation.localIndex_comp_eq_mul_sign_det`). On the
target, the relevant maps are differences `F = a - b`, whose zeros are the coincidences of `a` and
`b`, such as the intersection points of two discs in local intersection numbers. Reading `a` and `b`
through a change of coordinates `Ψ`, strictly differentiable at the common value `a x = b x` with
derivative `L`, multiplies the local index of the difference by `sign (det L)`
(`TauCeti.HomologicalOrientation.localIndex_eq_sign_det_mul_of_apply_eq_sub`). Here `Ψ ∘ a - Ψ ∘ b`
is not a composite of `F` with a map of the target, but it is `L ∘ F` up to an error which is small
compared with `F`, so Rouché's principle
`TauCeti.HomologicalOrientation.localIndex_eq_of_norm_sub_le` and the chain rule apply.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_sign_det`: the local index at a regular point is
  the sign of the Jacobian determinant.
* `TauCeti.HomologicalOrientation.degree_eq_sum_sign_det`: the degree of a proper map is the signed
  count of the preimages of a regular value.
* `TauCeti.HomologicalOrientation.degree_eq_ncard_of_det_pos`: when every preimage of a value has
  positive Jacobian determinant, the degree is the number of preimages.
* `TauCeti.HomologicalOrientation.degree_pos_of_hasFDerivAt`: a proper map differentiable on a set
  containing all fibres near `G x` has positive degree if its Jacobian determinant is nonnegative
  on that set and nonzero at `x`.
* `TauCeti.HomologicalOrientation.localIndex_comap_eq_sign_det`,
  `TauCeti.HomologicalOrientation.degree_comap_eq_sum_sign_det`: the same for maps between open
  subsets of `E`.
* `TauCeti.HomologicalOrientation.localIndex_comp_eq_mul_sign_det`: the local index under a change
  of coordinates of the source.
* `TauCeti.HomologicalOrientation.localIndex_eq_sign_det_mul_of_apply_eq_sub`: the local index of a
  difference under a change of coordinates of the target.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
-/

public section

noncomputable section

open CategoryTheory Filter Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n)

include hE in
/-- **The local index at a regular point is the sign of the Jacobian.** If `f : E → E` is
differentiable at `x` with derivative `f'` of nonzero determinant, then its local index at `x`, for
the same orientation of `E` on source and target, is `sign (det f')`. -/
theorem localIndex_eq_sign_det {f : C(E, E)} {f' : E →L[ℝ] E} {x : E} (hf : HasFDerivAt f f' x)
    (hdet : f'.det ≠ 0) : o.localIndex o f x = SignType.sign f'.det := by
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1
    (hf.eventually_ne (c := f x)
      ⟨_, (f'.toContinuousLinearEquivOfDetNeZero hdet).antilipschitzWith⟩))
  have hUx : ∀ z ∈ U, f z = f x → z = x := fun z hz hfz ↦ by_contra fun h ↦ hU z hz h hfz
  -- The translation by `f x - x` carries `x` to `f x` and has local index one, computed in `U`.
  have hτ := o.localIndex_addRight hE (f x - x) x
  rw [o.localIndex_eq_iff o hE _ (y := f x) (add_sub_cancel x (f x)) hUo hxU
    (fun z _ hfz ↦ by simpa using congrArg (· - (f x - x)) hfz)] at hτ
  rw [o.localIndex_eq_iff o hE f rfl hUo hxU hUx]
  -- On local homology at `x`, the restriction of `f` to `U` is `sign (det f')` times that of the
  -- translation.
  have h := localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (hUo.mem_nhds hxU) f.continuous.continuousOn hf hdet hUx n
  -- Both sides are `f` evaluated at the underlying point of `U`.
  have e1 : ContinuousMap.restrict U f =
      ⟨U.domRestrict f, f.continuous.continuousOn.domRestrict⟩ :=
    ContinuousMap.ext fun _ ↦ rfl
  have e2 : ContinuousMap.restrict U (ContinuousMap.addRight (f x - x)) =
      ⟨fun y : U ↦ f x + (y - x), by fun_prop⟩ :=
    ContinuousMap.ext fun y ↦ by
      simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_addRight, ContinuousMap.coe_mk]
      abel
  simp only [e2] at hτ
  simp only [e1, h, ModuleCat.hom_zsmul]
  -- The integer multiple of a linear map is evaluated pointwise.
  exact congrArg ((SignType.sign f'.det : ℤ) • ·) (hτ.trans (one_smul _ _))

include hE in
/-- **The local index at a regular point, in open coordinates.** Let `j : M → E` and `k : N → E`
be open embeddings, with the orientations pulled back from `o`, and let `f : M → N` be given near
`x` in these coordinates by a map `φ : E → E`, so that `φ (j z) = k (f z)` near `x`. If `φ` is
differentiable at `j x` with derivative `f'` of nonzero determinant, then the local index of `f` at
`x` is `sign (det f')`. This applies to a map between open subsets of `E`, oriented by restricting
`o`. -/
theorem localIndex_comap_eq_sign_det {M N : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace E M] [TopologicalSpace N] [T2Space N] [ChartedSpace E N] {j : M → E}
    (hj : IsOpenEmbedding j) {k : N → E} (hk : IsOpenEmbedding k) {f : C(M, N)} {φ : E → E}
    {x : M} (hφ : ∀ᶠ z in 𝓝 x, φ (j z) = k (f z)) {f' : E →L[ℝ] E} (hd : HasFDerivAt φ f' (j x))
    (hdet : f'.det ≠ 0) :
    (o.comap hj).localIndex (o.comap hk) f x = SignType.sign f'.det := by
  obtain ⟨G, hGφ, h⟩ := o.exists_eventuallyEq_and_localIndex_comap_eq o hE hj hk hφ
  rw [h, o.localIndex_eq_sign_det hE (hd.congr_of_eventuallyEq hGφ) hdet]

include hE in
/-- **The degree of a map between open subsets is the sum of the Jacobian signs over a regular
fibre.** Let `U` and `V` be open subsets of `E`, oriented by restricting `o`, with `V`
preconnected, and let `f : U → V` be a proper map agreeing on `U` with `φ : E → E`. If the fibre of
`f` over `y` is finite and consists of points where `φ` has a derivative `f' x` of nonzero
determinant, then the degree of `f` is the sum of `sign (det f' x)` over the fibre. -/
theorem degree_comap_eq_sum_sign_det {U V : TopologicalSpace.Opens E} [PreconnectedSpace V]
    {f : C(U, V)} (hf : IsProperMap f) {φ : E → E} (hφ : ∀ z : U, φ z = f z)
    {f' : E → E →L[ℝ] E} {y : V} (hfin : (f ⁻¹' {y}).Finite)
    (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt φ (f' x) x) (hdet : ∀ x ∈ f ⁻¹' {y}, (f' x).det ≠ 0) :
    (o.comap U.isOpenEmbedding').degree (o.comap V.isOpenEmbedding') hE f =
      ∑ x ∈ hfin.toFinset, (SignType.sign (f' x).det : ℤ) := by
  rw [(o.comap _).degree_eq_sum_localIndex (o.comap _) hE hE hf hfin]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finite.mem_toFinset] at hx
  exact o.localIndex_comap_eq_sign_det hE U.isOpenEmbedding' V.isOpenEmbedding' (.of_forall hφ)
    (hderiv x hx) (hdet x hx)

include hE in
/-- **The degree of a map between open subsets counts the preimages of a regular value with
orientation signs.** Let `U` and `V` be open subsets of `E`, oriented by restricting `o`, with `V`
preconnected, and let `f : U → V` be a proper map agreeing on `U` with `φ : E → E`. If every point
of the fibre of `f` over `y` has a derivative `f' x` of `φ` with nonzero determinant, then the
degree of `f` is the number of points of `U ∩ φ⁻¹(y)` where `det f' x` is positive minus the number
where it is negative. -/
theorem degree_comap_eq_ncard_sub_ncard {U V : TopologicalSpace.Opens E} [PreconnectedSpace V]
    {f : C(U, V)} (hf : IsProperMap f) {φ : E → E} (hφ : ∀ z : U, φ z = f z)
    {f' : E → E →L[ℝ] E} {y : V} (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt φ (f' x) x)
    (hdet : ∀ x ∈ f ⁻¹' {y}, (f' x).det ≠ 0) :
    (o.comap U.isOpenEmbedding').degree (o.comap V.isOpenEmbedding') hE f =
      ((U : Set E) ∩ {x | 0 < (f' x).det} ∩ φ ⁻¹' {(y : E)}).ncard -
        ((U : Set E) ∩ {x | (f' x).det < 0} ∩ φ ⁻¹' {(y : E)}).ncard := by
  -- The fibre of `f` is the fibre of `φ` in `U`, a compact set of points with invertible
  -- derivative, hence finite.
  have himage : Subtype.val '' (f ⁻¹' {y}) = (U : Set E) ∩ φ ⁻¹' {(y : E)} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, (hφ z).trans (congrArg Subtype.val hz)⟩
    · rintro ⟨hwU, hw⟩
      exact ⟨⟨w, hwU⟩, Subtype.ext ((hφ ⟨w, hwU⟩).symm.trans hw), rfl⟩
  have hmem : ∀ w (hw : w ∈ (U : Set E) ∩ φ ⁻¹' {(y : E)}), (⟨w, hw.1⟩ : U) ∈ f ⁻¹' {y} :=
    fun w hw ↦ Subtype.ext ((hφ ⟨w, hw.1⟩).symm.trans hw.2)
  have hK : IsCompact ((U : Set E) ∩ φ ⁻¹' {(y : E)}) :=
    himage ▸ (hf.isCompact_preimage isCompact_singleton).image continuous_subtypeVal
  have hKfin : ((U : Set E) ∩ φ ⁻¹' {(y : E)}).Finite :=
    hK.finite_inter_preimage_of_hasFDerivAt (fun w hw ↦ hderiv _ (hmem w hw)) fun w hw ↦
      ⟨_, ((f' w).toContinuousLinearEquivOfDetNeZero (hdet _ (hmem w hw))).antilipschitzWith⟩
  have hfin : (f ⁻¹' {y}).Finite :=
    Finite.of_finite_image (himage ▸ hKfin) Subtype.val_injective.injOn
  rw [o.degree_comap_eq_sum_sign_det hE hf hφ hfin hderiv hdet]
  -- Split the signs, and read the two counts in `E` through the injective inclusion of `U`.
  have e (t : ℝ) :
      (SignType.sign t : ℤ) = (if 0 < t then 1 else 0) - (if t < 0 then 1 else 0) := by
    rcases lt_trichotomy t 0 with h | h | h <;> simp [h, h.not_gt]
  have hcount (p : ℝ → Prop) [DecidablePred p] :
      ((U : Set E) ∩ {x | p (f' x).det} ∩ φ ⁻¹' {(y : E)}).ncard =
        (hfin.toFinset.filter fun x : U ↦ p (f' x).det).card := by
    rw [← ncard_coe_finset, ← ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, Finset.coe_filter,
      Finite.mem_toFinset, mem_image]
    constructor
    · rintro ⟨⟨hwU, hp⟩, hw⟩
      exact ⟨⟨w, hwU⟩, ⟨hmem w ⟨hwU, hw⟩, hp⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hp⟩, rfl⟩
      exact ⟨⟨z.property, hp⟩, (hφ z).trans (congrArg Subtype.val hz)⟩
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole,
    hcount (fun t ↦ 0 < t), hcount (fun t ↦ t < 0)]

include hE in
/-- **The degree is the sum of the Jacobian signs over a regular fibre.** Let `f : E → E` be a
proper map and `y` a point whose fibre is finite and consists of points where `f` has a derivative
`f' x` of nonzero determinant. Then the degree of `f` is the sum of `sign (det f' x)` over the
fibre. The finiteness of the fibre follows from the other hypotheses by
`IsCompact.finite_of_hasFDerivAt`. -/
theorem degree_eq_sum_sign_det {f : C(E, E)} (hf : IsProperMap f) {f' : E → E →L[ℝ] E} {y : E}
    (hfin : (f ⁻¹' {y}).Finite) (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ f ⁻¹' {y}, (f' x).det ≠ 0) :
    o.degree o hE f = ∑ x ∈ hfin.toFinset, (SignType.sign (f' x).det : ℤ) := by
  rw [o.degree_eq_sum_localIndex o hE hE hf hfin]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finite.mem_toFinset] at hx
  exact o.localIndex_eq_sign_det hE (hderiv x hx) (hdet x hx)

include hE in
/-- **The degree counts the preimages of a regular value with orientation signs.** If every point
of the fibre of the proper map `f : E → E` over `y` has a derivative `f' x` of nonzero
determinant, then the degree of `f` is the number of these points where `det f' x` is positive
minus the number where it is negative. -/
theorem degree_eq_ncard_sub_ncard {f : C(E, E)} (hf : IsProperMap f) {f' : E → E →L[ℝ] E}
    {y : E} (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ f ⁻¹' {y}, (f' x).det ≠ 0) :
    o.degree o hE f = ({x | 0 < (f' x).det} ∩ f ⁻¹' {y}).ncard -
      ({x | (f' x).det < 0} ∩ f ⁻¹' {y}).ncard := by
  have hfin := (hf.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt hderiv
    fun x hx ↦ ⟨_, ((f' x).toContinuousLinearEquivOfDetNeZero (hdet x hx)).antilipschitzWith⟩
  rw [o.degree_eq_sum_sign_det hE hf hfin hderiv hdet]
  have e (t : ℝ) :
      (SignType.sign t : ℤ) = (if 0 < t then 1 else 0) - (if t < 0 then 1 else 0) := by
    rcases lt_trichotomy t 0 with h | h | h <;> simp [h, h.not_gt]
  have hpos : {x | 0 < (f' x).det} ∩ f ⁻¹' {y} =
      ↑(hfin.toFinset.filter fun x ↦ 0 < (f' x).det) := by
    ext x; simp [and_comm]
  have hneg : {x | (f' x).det < 0} ∩ f ⁻¹' {y} =
      ↑(hfin.toFinset.filter fun x ↦ (f' x).det < 0) := by
    ext x; simp [and_comm]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hpos, hneg, ncard_coe_finset,
    ncard_coe_finset]

/-- **The degree counts the preimages of a positively oriented regular value.** If every preimage
of `y` under the proper map `f : E → E` is a point where `f` is differentiable with positive
Jacobian determinant, then the degree of `f` is the number of preimages of `y`. -/
theorem degree_eq_ncard_of_det_pos {f : C(E, E)} (hf : IsProperMap f) {f' : E → E →L[ℝ] E} {y : E}
    (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hpos : ∀ x ∈ f ⁻¹' {y}, 0 < (f' x).det) :
    o.degree o hE f = (f ⁻¹' {y}).ncard := by
  have h₁ : {x | 0 < (f' x).det} ∩ f ⁻¹' {y} = f ⁻¹' {y} := inter_eq_right.2 hpos
  have h₂ : {x | (f' x).det < 0} ∩ f ⁻¹' {y} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx ↦ (hpos x hx.2).not_gt hx.1
  rw [o.degree_eq_ncard_sub_ncard hE hf hderiv (fun x hx ↦ (hpos x hx).ne'), h₁, h₂,
    ncard_empty, Nat.cast_zero, sub_zero]

/-- Let `G : E → E` be proper and differentiable on `U`, with derivatives `D z` of
nonnegative determinant, such that `U` contains the fibres of all values near `G x`. If `D x` has
nonzero determinant, then the degree of `G` is positive. -/
theorem degree_pos_of_hasFDerivAt {G : C(E, E)} (hG : IsProperMap G) {U : Set E}
    {D : E → E →L[ℝ] E} (hGd : ∀ z ∈ U, HasFDerivAt G (D z) z) (hdet : ∀ z ∈ U, 0 ≤ (D z).det)
    {x : E} (hDx : (D x).det ≠ 0) (hfib : ∀ᶠ y in 𝓝 (G x), G ⁻¹' {y} ⊆ U) :
    0 < o.degree o hE G := by
  have hU : U ∈ 𝓝 x := (G.continuous.continuousAt.eventually hfib).mono fun _ hz ↦ hz rfl
  have hidx : o.localIndex o G x ≠ 0 := by
    have hpos : 0 < (D x).det := (hdet x (mem_of_mem_nhds hU)).lt_of_ne' hDx
    rw [o.localIndex_eq_sign_det hE (hGd x (mem_of_mem_nhds hU)) hDx, sign_pos hpos,
      SignType.coe_one]
    exact one_ne_zero
  have hW : G '' U ∩ {y' | G ⁻¹' {y'} ⊆ U} ∈ 𝓝 (G x) :=
    inter_mem (o.image_mem_nhds_of_localIndex_ne_zero o hE hidx hU) hfib
  -- By Sard's theorem the regular values of `G` on `U` are dense, so some value in the interior of
  -- this neighbourhood has only regular preimages.
  borelize E
  obtain ⟨y', hy'W, hy'S⟩ := (dense_setOf_forall_surjective_fderiv (s := U) (f := G)
    (fun z hz ↦ (hGd z hz).differentiableAt) rfl).inter_open_nonempty
    (interior (G '' U ∩ {y' | G ⁻¹' {y'} ⊆ U})) isOpen_interior
    ⟨G x, mem_interior_iff_mem_nhds.2 hW⟩
  obtain ⟨⟨z₀, -, hGz₀⟩, hy'U⟩ := interior_subset hy'W
  have hpos {z : E} (hz : z ∈ G ⁻¹' {y'}) : 0 < (D z).det := by
    have hsurj := hy'S z (hy'U hz) hz
    rw [(hGd z (hy'U hz)).fderiv] at hsurj
    have hdetz : (D z).det ≠ 0 := fun h ↦
      LinearMap.det_eq_zero_iff_ker_ne_bot.1 h
        (LinearMap.ker_eq_bot.2 (LinearMap.injective_iff_surjective.2 hsurj))
    exact (hdet z (hy'U hz)).lt_of_ne' hdetz
  have hfin : (G ⁻¹' {y'}).Finite :=
    (hG.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt
      (fun z hz ↦ hGd z (hy'U hz)) fun z hz ↦
        ⟨_, ((D z).toContinuousLinearEquivOfDetNeZero (hpos hz).ne').antilipschitzWith⟩
  rw [o.degree_eq_ncard_of_det_pos hE hG (f' := D) (y := y')
    (fun z hz ↦ hGd z (hy'U hz)) fun z hz ↦ hpos hz]
  exact_mod_cast (ncard_pos hfin).2 ⟨z₀, hGz₀⟩

end HomologicalOrientation

/-! ### Changes of coordinates -/

namespace HomologicalOrientation

section TargetChange

variable {M G V : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [ChartedSpace G M] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} (o : HomologicalOrientation M G n)
  (o' : HomologicalOrientation V V n) (hV : finrank ℝ V = n)

include hV in
/-- **The local index of a difference under a change of coordinates of the target.** Let
`F p = a p - b p` for maps `a, b : M → V` continuous at `x` with `a x = b x`, so that `x` is a
point of `F⁻¹(0)`, such as an intersection point of two maps into `V` when `F` is their difference.
If `Ψ : V → V` is strictly differentiable at `a x` with derivative `L` of nonzero determinant, then
the difference `G' p = Ψ (a p) - Ψ (b p)` of the maps read through `Ψ` has local index
`sign (det L)` times that of `F` at `x`. In particular the local index is unchanged when `det L`
is positive. -/
theorem localIndex_eq_sign_det_mul_of_apply_eq_sub {F G' : C(M, V)} {a b : M → V} {Ψ : V → V}
    {L : V →L[ℝ] V} {x : M} (hF : ∀ p, F p = a p - b p) (hG' : ∀ p, G' p = Ψ (a p) - Ψ (b p))
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hab : a x = b x)
    (hΨ : HasStrictFDerivAt Ψ L (a x)) (hL : L.det ≠ 0) :
    o.localIndex o' G' x = SignType.sign L.det * o.localIndex o' F x := by
  set e := L.toContinuousLinearEquivOfDetNeZero hL
  have he : (e : V →L[ℝ] V) = L := L.coe_toContinuousLinearEquivOfDetNeZero hL
  have hF0 : F x = 0 := by rw [hF, hab, sub_self]
  set LF : C(M, V) := (⟨L, L.continuous⟩ : C(V, V)).comp F
  -- By the chain rule, `L ∘ F` has local index `sign (det L)` times that of `F`.
  have hcomp : o.localIndex o' LF x = SignType.sign L.det * o.localIndex o' F x := by
    rw [o.localIndex_comp o' o' hV (eventually_nhdsWithin_of_forall fun z hz ↦ ?_), hF0,
      o'.localIndex_eq_sign_det hV L.hasFDerivAt hL]
    rw [← he]
    exact e.injective.ne hz
  rw [← hcomp]
  -- `G'` differs from `L ∘ F` by `o(‖F‖)`, which is small compared with `‖L ∘ F‖`, so Rouché's
  -- principle applies.
  refine (o.localIndex_eq_of_norm_sub_le o' hV (c := 1 / 2) (by norm_num) ?_).symm
  set C := ‖(e.symm : V →L[ℝ] V)‖ + 1
  have hC : 0 < C := by positivity
  have hT : Tendsto (fun p ↦ (a p, b p)) (𝓝 x) (𝓝 (a x, a x)) := by
    simpa [hab] using ha.prodMk_nhds hb
  filter_upwards [hT.eventually (hΨ.isLittleO.def (c := 1 / (2 * C)) (by positivity))] with p hp
  have hinv : ‖F p‖ ≤ C * ‖L (F p)‖ := by
    calc ‖F p‖ = ‖(e.symm : V →L[ℝ] V) (e (F p))‖ := by simp
      _ ≤ ‖(e.symm : V →L[ℝ] V)‖ * ‖e (F p)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖L (F p)‖ := by
        rw [← he]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
  calc ‖G' p - LF p‖ = ‖Ψ (a p) - Ψ (b p) - L (a p - b p)‖ := by simp [LF, hG', hF]
    _ ≤ 1 / (2 * C) * ‖F p‖ := by rw [hF]; exact hp
    _ ≤ 1 / (2 * C) * (C * ‖L (F p)‖) := by gcongr
    _ = 1 / 2 * ‖LF p - LF x‖ := by
      simp only [LF, ContinuousMap.comp_apply, ContinuousMap.coe_mk, hF0, map_zero, sub_zero]
      field_simp

end TargetChange

section SourceChange

variable {E N G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace N] [T2Space N] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [ChartedSpace G N] {n : ℕ} (o : HomologicalOrientation E E n)
  (o' : HomologicalOrientation N G n)

/-- **The local index under a change of coordinates of the source.** If `φ : E → E` is strictly
differentiable at `x` with derivative `φ'` of nonzero determinant, then the local index of
`F ∘ φ` at `x` is that of `F` at `φ x` times `sign (det φ')`. Only the target dimension must equal
`n`; the source dimension may differ. -/
theorem localIndex_comp_eq_mul_sign_det (hG : finrank ℝ G = n) {F : C(E, N)} {φ : C(E, E)}
    {φ' : E →L[ℝ] E} {x : E} (hφ : HasStrictFDerivAt φ φ' x) (hdet : φ'.det ≠ 0) :
    o.localIndex o' (F.comp φ) x = o.localIndex o' F (φ x) * SignType.sign φ'.det := by
  by_cases hE : finrank ℝ E = n
  swap
  · rw [o.localIndex_eq_zero_of_finrank_ne o' hE hG, o.localIndex_eq_zero_of_finrank_ne o' hE hG,
      zero_mul]
  by_cases hiso : ∀ᶠ y in 𝓝[≠] φ x, F y ≠ F (φ x)
  · rw [o.localIndex_comp o o' hG hiso, o.localIndex_eq_sign_det hE hφ.hasFDerivAt hdet]
  have hfr : ∃ᶠ y in 𝓝[≠] φ x, F y = F (φ x) := by simpa using not_eventually.1 hiso
  -- When `φ x` is not isolated in its fibre under `F`, neither is `x` under `F ∘ φ`, and both sides
  -- vanish: near `x`, `φ` is a homeomorphism onto a neighbourhood of `φ x`, so it maps the
  -- punctured neighbourhoods of `x` onto those of `φ x`.
  have hφe : HasStrictFDerivAt φ
      ((φ'.toContinuousLinearEquivOfDetNeZero hdet : E ≃L[ℝ] E) : E →L[ℝ] E) x := by
    rwa [φ'.coe_toContinuousLinearEquivOfDetNeZero hdet]
  have hmap : map φ (𝓝[≠] x) = 𝓝[≠] φ x := by
    simpa using (hφe.toOpenPartialHomeomorph φ).map_nhdsNE_eq hφe.mem_toOpenPartialHomeomorph_source
  have hfr' : ∃ᶠ z in 𝓝[≠] x, F.comp φ z = F.comp φ x := by
    rw [← hmap] at hfr
    exact frequently_map.1 hfr
  rw [o.localIndex_of_frequently_eq o' _ hfr', o.localIndex_of_frequently_eq o' F hfr, zero_mul]

end SourceChange

end HomologicalOrientation

end TauCeti
