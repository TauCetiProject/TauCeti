/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The connected sum with a sphere

The connected sum `M # Sⁿ` of a manifold with a sphere is diffeomorphic to `M`. This is the first
computation with the connected sum `TauCeti.ConnectedSum e₁ e₂` of
`TauCeti.Geometry.Manifold.ConnectedSum.Basic`, which removes the centres of two balls
`e₁ : E → M`, `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`.

The sphere enters through a pair of balls. A ball `s' : E → N` is complementary to a ball
`s : E → N` (`TauCeti.IsComplementaryBall s s'`) when it is an open embedding onto `N ∖ {s 0}` and
`s' w = s (inversion 0 1 w)` for `w ≠ 0`: the two balls are the two stereographic charts of a
sphere. Then the punctured summand `N ∖ {s 0}` of a connected sum along `s` is the ball `s'`
(`TauCeti.IsComplementaryBall.homeomorphPuncture`), and the connected sum along `e : E → M` and `s`
maps back to `M` by the identity on `M ∖ {e 0}` and by `e ∘ s'⁻¹` on `N ∖ {s 0}`; the pole `s' 0`
fills the removed centre `e 0`. The two pieces agree on the glued punctured balls because
`s' w = s (inversion 0 1 w)`. This map is a homeomorphism
(`TauCeti.IsComplementaryBall.connectedSumHomeomorph`), and a `C^n` diffeomorphism for the charts
of the connected sum when the three balls are `C^n` local diffeomorphisms
(`TauCeti.IsComplementaryBall.connectedSumDiffeomorph`).

For the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space, the balls are
inverse stereographic projections. Read through the inversion in the sphere of radius `2`, Mathlib's
inverse stereographic projection `(stereographic' n v).symm` from `v` is the antipode of itself read
through `x ↦ -x`. So the ball `TauCeti.sphereBall v w = (stereographic' n v).symm (2 • w)`,
centred at `-v`, has as complementary ball the antipodal ball `w ↦ -sphereBall v (-w)`, centred at
`v` (`TauCeti.isComplementaryBall_sphereBall`). This gives `M # Sⁿ ≃ M` for every `n`-dimensional
`C^k` manifold `M` (`TauCeti.connectedSumSphereDiffeomorph`), and in particular `Sⁿ # Sⁿ ≃ Sⁿ`
(`TauCeti.nonempty_diffeomorph_connectedSum_sphereBall`).

## Main definitions

* `TauCeti.IsComplementaryBall s s'`: the balls `s` and `s'` are the two charts of a sphere, glued
  by the inversion in the unit sphere.
* `TauCeti.IsComplementaryBall.connectedSumHomeomorph`: the homeomorphism from the connected sum
  with such a sphere to the other summand.
* `TauCeti.IsComplementaryBall.connectedSumDiffeomorph`: the same map, as a `C^n` diffeomorphism.
* `TauCeti.sphereBall v`: the ball of the unit sphere centred at `-v`, a rescaled inverse
  stereographic projection.
* `TauCeti.connectedSumSphereDiffeomorph`: the diffeomorphism `M # Sⁿ ≃ M`.

## Main results

* `TauCeti.isComplementaryBall_sphereBall`: the antipodal ball is complementary to `sphereBall v`.
* `TauCeti.nonempty_diffeomorph_connectedSum_sphereBall`: `Sⁿ # Sⁿ` is diffeomorphic to `Sⁿ`.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1 (the connected
  sum, glued by the inversion of the punctured balls).
-/

public section

noncomputable section

open Set Function Topology EuclideanGeometry
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {N : Type*} [TopologicalSpace N] [T1Space N]

/-- The ball `s' : E → N` is **complementary** to the ball `s : E → N` when it is an open embedding
onto the complement of the centre `s 0`, glued to `s` by the inversion of `E` in its unit sphere:
`s' w = s (inversion 0 1 w)` for `w ≠ 0`. Then the two balls cover `N` and overlap along their
punctures, glued by the inversion, as the two stereographic charts of a round sphere are
(`TauCeti.isComplementaryBall_sphereBall`); `s 0` and `s' 0` are the two poles. -/
structure IsComplementaryBall (s s' : E → N) : Prop where
  /-- The complementary ball is an open embedding. -/
  isOpenEmbedding : IsOpenEmbedding s'
  /-- The complementary ball covers everything except the centre of the first ball. -/
  range_eq : range s' = {s 0}ᶜ
  /-- Away from the centres, the two balls are glued by the inversion. -/
  apply_eq_inversion : ∀ w ≠ 0, s' w = s (inversion 0 1 w)

namespace IsComplementaryBall

open ConnectedSum

variable {s s' : E → N} (h : IsComplementaryBall s s')

include h in
/-- The complementary ball avoids the centre of the first ball. -/
theorem apply_mem_puncture (w : E) : s' w ∈ ConnectedSum.puncture s := by
  rw [ConnectedSum.mem_puncture, ← mem_compl_singleton_iff, ← h.range_eq]
  exact mem_range_self w

include h in
/-- A ball admitting a complementary ball is injective: away from its centre it is the
complementary ball read through the inversion, which misses the centre. -/
theorem injective : Injective s := by
  have key : ∀ w ≠ 0, s w = s' (inversion 0 1 w) := fun w hw ↦ by
    rw [h.apply_eq_inversion _ fun h0 ↦ hw ((inversion_eq_center one_ne_zero).1 h0),
      inversion_inversion _ one_ne_zero]
  intro w w' hww'
  rcases eq_or_ne w 0 with rfl | hw <;> rcases eq_or_ne w' 0 with rfl | hw'
  · rfl
  · exact absurd hww'.symm (by rw [key w' hw']; exact mem_puncture.1 (h.apply_mem_puncture _))
  · exact absurd hww' (by rw [key w hw]; exact mem_puncture.1 (h.apply_mem_puncture _))
  · rw [key w hw, key w' hw'] at hww'
    exact inversion_injective 0 one_ne_zero (h.isOpenEmbedding.injective hww')

/-- A complementary ball of `s` parametrizes the punctured summand `N ∖ {s 0}` of a connected sum
along `s`. -/
def homeomorphPuncture : E ≃ₜ ConnectedSum.puncture s :=
  h.isOpenEmbedding.toIsEmbedding.toHomeomorph.trans
    (.setCongr (h.range_eq.trans (Set.ext fun _ ↦ ConnectedSum.mem_puncture.symm)))

@[simp]
theorem coe_homeomorphPuncture (w : E) : (h.homeomorphPuncture w : N) = s' w :=
  (rfl)

theorem homeomorphPuncture_symm_apply_eq_iff {y : ConnectedSum.puncture s} {w : E} :
    h.homeomorphPuncture.symm y = w ↔ (y : N) = s' w := by
  rw [Homeomorph.symm_apply_eq, Subtype.ext_iff, coe_homeomorphPuncture]

@[simp]
theorem homeomorphPuncture_symm_apply (w : E) :
    h.homeomorphPuncture.symm ⟨s' w, h.apply_mem_puncture w⟩ = w :=
  h.homeomorphPuncture_symm_apply_eq_iff.2 rfl

/-! ### The connected sum with a sphere is homeomorphic to the other summand -/

variable (e : E → M)

/-- The map from the connected sum with a sphere back to the other summand: the identity on the
punctured summand `M ∖ {e 0}`, and the complementary ball read through `e` on `N ∖ {s 0}`, which
sends the remaining pole `s' 0` to the removed centre `e 0`. -/
def connectedSumMap : ConnectedSum e s → M :=
  lift Subtype.val (e ∘ h.homeomorphPuncture.symm) fun v hv _ _ ↦
    congrArg e (h.homeomorphPuncture_symm_apply_eq_iff.2 (h.apply_eq_inversion v hv).symm).symm

@[simp]
theorem connectedSumMap_inl (x : puncture e) : h.connectedSumMap e (ConnectedSum.inl e s x) = x :=
  lift_inl _ _ _ x

@[simp]
theorem connectedSumMap_inr_homeomorphPuncture (w : E) :
    h.connectedSumMap e (ConnectedSum.inr e s (h.homeomorphPuncture w)) = e w := by
  simp [connectedSumMap]

theorem connectedSumMap_comp_mk : h.connectedSumMap e ∘ ConnectedSum.mk e s =
    Sum.elim Subtype.val (e ∘ h.homeomorphPuncture.symm) :=
  lift_comp_mk _ _ _

variable {e}

theorem continuous_connectedSumMap (he : Continuous e) : Continuous (h.connectedSumMap e) :=
  continuous_lift _ _ _ continuous_subtype_val (he.comp h.homeomorphPuncture.symm.continuous)

theorem connectedSumMap_injective (he : Injective e) : Injective (h.connectedSumMap e) := by
  -- A point of the punctured `M` and a point `s' w` of the punctured `N` with the same image
  -- `e w` are glued, since `w ≠ 0` and `s' w = s (inversion 0 1 w)`.
  have key : ∀ (x : puncture e) (w : E), (x : M) = e w →
      ConnectedSum.inl e s x = ConnectedSum.inr e s (h.homeomorphPuncture w) := fun x w hxw ↦ by
    have hw : w ≠ 0 := by rintro rfl; exact mem_puncture.1 x.2 hxw
    rw [inl_eq_inr_iff he h.injective]
    exact ⟨w, hw, hxw.symm, by simp [h.apply_eq_inversion w hw]⟩
  intro p q hpq
  obtain ⟨x | y, rfl⟩ := ConnectedSum.mk_surjective e s p <;>
    obtain ⟨x' | y', rfl⟩ := ConnectedSum.mk_surjective e s q
  · simp only [ConnectedSum.mk_inl, connectedSumMap_inl] at hpq
    rw [Subtype.ext hpq]
  · obtain ⟨w, rfl⟩ := h.homeomorphPuncture.surjective y'
    simpa using key x w (by simpa using hpq)
  · obtain ⟨w, rfl⟩ := h.homeomorphPuncture.surjective y
    simpa using (key x' w (by simpa using hpq.symm)).symm
  · obtain ⟨w, rfl⟩ := h.homeomorphPuncture.surjective y
    obtain ⟨w', rfl⟩ := h.homeomorphPuncture.surjective y'
    simp only [ConnectedSum.mk_inr, connectedSumMap_inr_homeomorphPuncture] at hpq
    rw [he hpq]

theorem connectedSumMap_surjective : Surjective (h.connectedSumMap e) := fun x ↦ by
  by_cases hx : x = e 0
  · exact ⟨ConnectedSum.inr e s (h.homeomorphPuncture 0), by simp [hx]⟩
  · exact ⟨ConnectedSum.inl e s ⟨x, mem_puncture.2 hx⟩, by simp⟩

theorem isOpenMap_connectedSumMap (he : IsOpenEmbedding e) :
    IsOpenMap (h.connectedSumMap e) := fun U hU ↦ by
  rw [← (ConnectedSum.mk_surjective e s).image_preimage U, ← image_comp, connectedSumMap_comp_mk]
  exact ((puncture e).isOpen.isOpenMap_subtype_val.sumElim
    (he.isOpenMap.comp h.homeomorphPuncture.symm.isOpenMap)) _
    (hU.preimage (ConnectedSum.continuous_mk e s))

/-- **The connected sum with a sphere is homeomorphic to the other summand.** If `s'` is a ball
complementary to `s`, so that `N` is a sphere, the connected sum of `M` and `N` along `e` and `s` is
homeomorphic to `M`, by the identity on `M ∖ {e 0}` and by `e ∘ s'⁻¹` on `N ∖ {s 0}`. -/
def connectedSumHomeomorph (he : IsOpenEmbedding e) : ConnectedSum e s ≃ₜ M :=
  (Equiv.ofBijective _ ⟨h.connectedSumMap_injective he.injective,
    h.connectedSumMap_surjective⟩).toHomeomorphOfContinuousOpen
    (h.continuous_connectedSumMap he.continuous) (h.isOpenMap_connectedSumMap he)

variable (he : IsOpenEmbedding e)

@[simp]
theorem coe_connectedSumHomeomorph : ⇑(h.connectedSumHomeomorph he) = h.connectedSumMap e :=
  (rfl)

theorem connectedSumHomeomorph_symm_apply_of_ne {x : M} (hx : x ≠ e 0) :
    (h.connectedSumHomeomorph he).symm x = ConnectedSum.inl e s ⟨x, mem_puncture.2 hx⟩ := by
  rw [Homeomorph.symm_apply_eq]
  simp

theorem connectedSumHomeomorph_symm_apply (w : E) :
    (h.connectedSumHomeomorph he).symm (e w) =
      ConnectedSum.inr e s (h.homeomorphPuncture w) := by
  rw [Homeomorph.symm_apply_eq]
  simp

/-! ### The smooth structure -/

section Smooth

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
  [ChartedSpace H M] [ChartedSpace H N]

/-- The inverse of a complementary ball which is a `C^n` local diffeomorphism is `C^n` on the
punctured summand. -/
theorem contMDiff_homeomorphPuncture_symm (ds' : IsLocalDiffeomorph 𝓘(ℝ, E) I n s') :
    ContMDiff I 𝓘(ℝ, E) n h.homeomorphPuncture.symm := by
  refine ContMDiff.of_comp_isLocalDiffeomorph ds' h.homeomorphPuncture.symm.continuous ?_
  convert contMDiff_subtype_val (I := I) (n := n) (U := puncture s) using 1
  ext y
  obtain ⟨w, rfl⟩ := h.homeomorphPuncture.surjective y
  simp

/-- A complementary ball which is a `C^n` local diffeomorphism is `C^n` as a map into the punctured
summand. -/
theorem contMDiff_homeomorphPuncture (ds' : IsLocalDiffeomorph 𝓘(ℝ, E) I n s') :
    ContMDiff 𝓘(ℝ, E) I n h.homeomorphPuncture :=
  ContMDiff.of_comp_isLocalDiffeomorph isLocalDiffeomorph_subtype_val
    h.homeomorphPuncture.continuous (by convert ds'.contMDiff using 1; ext; simp)

variable [IsManifold I n M] [IsManifold I n N]
  (he : IsOpenEmbedding e) (hs : IsOpenEmbedding s) (de : IsLocalDiffeomorph 𝓘(ℝ, E) I n e)
  (ds : IsLocalDiffeomorph 𝓘(ℝ, E) I n s) (ds' : IsLocalDiffeomorph 𝓘(ℝ, E) I n s')

/-- **The connected sum with a sphere is diffeomorphic to the other summand.** If the balls `e`,
`s` and the complementary ball `s'` are `C^n` local diffeomorphisms, the homeomorphism
`TauCeti.IsComplementaryBall.connectedSumHomeomorph` from the connected sum of `M` and the sphere
`N` to `M` is a `C^n` diffeomorphism, for the charts of the connected sum
(`TauCeti.ConnectedSum.chartedSpace`). -/
def connectedSumDiffeomorph :
    letI := ConnectedSum.chartedSpace (H := H) he hs
    ConnectedSum e s ≃ₘ^n⟮I, I⟯ M :=
  letI := ConnectedSum.chartedSpace (H := H) he hs
  haveI := ConnectedSum.isManifold he hs de ds
  have hmk := ConnectedSum.isLocalDiffeomorph_mk he hs de ds
  { toEquiv := (h.connectedSumHomeomorph he).toEquiv
    contMDiff_toFun := by
      -- Read on the disjoint union of the punctured summands, the map is the inclusion of
      -- `M ∖ {e 0}` and `e ∘ s'⁻¹`.
      rw [Homeomorph.coe_toEquiv, coe_connectedSumHomeomorph,
        ← hmk.contMDiff_comp_iff (ConnectedSum.mk_surjective e s) le_rfl,
        connectedSumMap_comp_mk]
      exact contMDiff_subtype_val.sumElim
        (de.contMDiff.comp (h.contMDiff_homeomorphPuncture_symm ds'))
    contMDiff_invFun := fun x ↦ by
      -- Near `e 0` the inverse is read through the ball `e`, and elsewhere through the inclusion
      -- of the open set `M ∖ {e 0}`.
      rw [Homeomorph.coe_symm_toEquiv]
      by_cases hx : x = e 0
      · subst hx
        refine ((de 0).contMDiffAt_comp_iff le_rfl).1 ?_
        have : (h.connectedSumHomeomorph he).symm ∘ e =
            ConnectedSum.mk e s ∘ Sum.inr ∘ h.homeomorphPuncture := by
          ext w
          simp [connectedSumHomeomorph_symm_apply]
        rw [this]
        exact (hmk.contMDiff.comp (ContMDiff.inr.comp
          (h.contMDiff_homeomorphPuncture ds'))).contMDiffAt
      · refine ((isLocalDiffeomorph_subtype_val (U := puncture e)
          ⟨x, mem_puncture.2 hx⟩).contMDiffAt_comp_iff le_rfl).1 ?_
        have : (h.connectedSumHomeomorph he).symm ∘ Subtype.val =
            ConnectedSum.mk e s ∘ Sum.inl (β := puncture s) := by
          ext ⟨y, hy⟩
          simp [connectedSumHomeomorph_symm_apply_of_ne _ _ (mem_puncture.1 hy)]
        rw [this]
        exact (hmk.contMDiff.comp ContMDiff.inl).contMDiffAt }

@[simp]
theorem coe_connectedSumDiffeomorph :
    letI := ConnectedSum.chartedSpace (H := H) he hs
    ⇑(h.connectedSumDiffeomorph he hs de ds ds') = h.connectedSumMap e :=
  (rfl)

/-- The diffeomorphism `TauCeti.IsComplementaryBall.connectedSumDiffeomorph` is the homeomorphism
`TauCeti.IsComplementaryBall.connectedSumHomeomorph`. -/
@[simp]
theorem toHomeomorph_connectedSumDiffeomorph :
    letI := ConnectedSum.chartedSpace (H := H) he hs
    (h.connectedSumDiffeomorph he hs de ds ds').toHomeomorph = h.connectedSumHomeomorph he :=
  (rfl)

@[simp]
theorem coe_connectedSumDiffeomorph_symm :
    letI := ConnectedSum.chartedSpace (H := H) he hs
    ⇑(h.connectedSumDiffeomorph he hs de ds ds').symm = (h.connectedSumHomeomorph he).symm :=
  (rfl)

end Smooth

end IsComplementaryBall

/-! ### The round sphere -/

section RoundSphere

open Metric Module

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
  [Fact (finrank ℝ F = n + 1)]

/-- The **coordinate ball of the unit sphere centred at `-v`**: the inverse of the stereographic
projection `stereographic' n v` from `v`, precomposed with the dilation by `2`. The dilation
rescales Mathlib's projection so that the antipodal ball `w ↦ -sphereBall v (-w)` is this ball read
through the inversion in the unit sphere, the gluing of the connected sum
(`TauCeti.isComplementaryBall_sphereBall`). -/
def sphereBall (v : sphere (0 : F) 1) (w : EuclideanSpace ℝ (Fin n)) : sphere (0 : F) 1 :=
  (stereographic' n v).symm ((2 : ℝ) • w)

/-- The coordinates of a point of the ball `sphereBall v`, in the ambient space. -/
private theorem coe_sphereBall (v : sphere (0 : F) 1) (w : EuclideanSpace ℝ (Fin n)) :
    (sphereBall v w : F) = (4 * ‖w‖ ^ 2 + 4)⁻¹ • ((8 : ℝ) •
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.symm w
        : F) + (4 * ‖w‖ ^ 2 - 4) • (v : F)) := by
  rw [sphereBall, stereographic'_symm_apply]
  simp only [map_smul, Submodule.coe_smul, norm_smul, Submodule.norm_coe,
    LinearIsometryEquiv.norm_map, Real.norm_ofNat, smul_add, smul_smul]
  congr 2 <;> ring

/-- The ball `sphereBall v` is centred at `-v`. -/
@[simp]
theorem sphereBall_zero (v : sphere (0 : F) 1) : sphereBall (n := n) v 0 = -v := by
  ext
  rw [coe_sphereBall]
  simp only [norm_zero, map_zero, Submodule.coe_zero, smul_zero, zero_add, smul_smul,
    coe_neg_sphere]
  norm_num

/-- Away from its centre, the ball `sphereBall v` read through the inversion in the unit sphere is
the antipode of the ball `sphereBall v` read through `w ↦ -w`. -/
theorem sphereBall_inversion (v : sphere (0 : F) 1) {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    sphereBall v (inversion 0 1 w) = -sphereBall v (-w) := by
  ext
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  rw [coe_sphereBall, coe_neg_sphere, coe_sphereBall]
  simp only [inversion, dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, norm_smul,
    norm_neg, map_smul, map_neg, Submodule.coe_smul, Submodule.coe_neg, smul_neg, smul_add,
    smul_smul, neg_add, ← neg_smul, norm_pow, norm_div, norm_one, Real.norm_eq_abs, abs_norm]
  congr 2
  · field_simp; ring
  · field_simp; ring

/-- The ball `sphereBall v` covers the sphere except the point `v`. -/
@[simp]
theorem range_sphereBall (v : sphere (0 : F) 1) : range (sphereBall (n := n) v) = {v}ᶜ := by
  have h2 : range (fun w : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) • w) = univ :=
    (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).surjective.range_eq
  rw [← stereographic'_source (n := n) v, ← (stereographic' n v).symm_image_target_eq_source,
    stereographic'_target, ← h2, ← range_comp]
  rfl

theorem isOpenEmbedding_sphereBall (v : sphere (0 : F) 1) :
    IsOpenEmbedding (sphereBall (n := n) v) :=
  ((stereographic' n v).symm.isOpenEmbedding (by simp)).comp
    (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).isOpenEmbedding

/-- The ball `sphereBall v` is a `C^m` local diffeomorphism, for every `m`. -/
theorem isLocalDiffeomorph_sphereBall (v : sphere (0 : F) 1) (m : ℕ∞ω) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) m (sphereBall (n := n) v) := fun w ↦ by
  have : IsManifold (𝓡 n) m (sphere (0 : F) 1) := .of_le le_top
  have hchart : stereographic' n v ∈ IsManifold.maximalAtlas (𝓡 n) m (sphere (0 : F) 1) :=
    IsManifold.subset_maximalAtlas ⟨v, rfl⟩
  -- The dilation by `2`, as a diffeomorphism of the model space.
  let δ : EuclideanSpace ℝ (Fin n) ≃ₘ^m⟮𝓡 n, 𝓡 n⟯ EuclideanSpace ℝ (Fin n) :=
    { toEquiv := (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).toEquiv
      contMDiff_toFun := (contDiff_const_smul (2 : ℝ)).contMDiff
      contMDiff_invFun := (contDiff_const_smul (2⁻¹ : ℝ)).contMDiff }
  exact (δ.isLocalDiffeomorph w).comp (hg :=
    (stereographic' n v).isLocalDiffeomorphAt_symm_of_mem_maximalAtlas hchart (by simp))

/-- **The antipodal ball is complementary.** The ball `w ↦ -sphereBall v (-w)`, centred at `v`, is
complementary to the ball `sphereBall v` centred at `-v`: the two cover the sphere and are glued by
the inversion in the unit sphere. -/
theorem isComplementaryBall_sphereBall (v : sphere (0 : F) 1) :
    IsComplementaryBall (sphereBall (n := n) v) fun w ↦ -sphereBall v (-w) where
  isOpenEmbedding := (Homeomorph.neg _).isOpenEmbedding.comp
    ((isOpenEmbedding_sphereBall v).comp (Homeomorph.neg _).isOpenEmbedding)
  range_eq := by
    ext x
    simp only [mem_range, sphereBall_zero, mem_compl_singleton_iff]
    constructor
    · rintro ⟨y, rfl⟩ hy
      have := mem_range_self (f := sphereBall (n := n) v) (-y)
      rw [range_sphereBall] at this
      exact this (neg_inj.1 hy)
    · intro hx
      have : -x ∈ range (sphereBall (n := n) v) := by
        rw [range_sphereBall]
        exact fun h ↦ hx (by rw [← h, neg_neg])
      obtain ⟨y, hy⟩ := this
      exact ⟨-y, by rw [neg_neg, hy, neg_neg]⟩
  apply_eq_inversion _ hw := (sphereBall_inversion v hw).symm

/-- The antipodal ball `w ↦ -sphereBall v (-w)` is a `C^m` local diffeomorphism. -/
private theorem isLocalDiffeomorph_neg_sphereBall_neg (v : sphere (0 : F) 1) (m : ℕ∞ω) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) m fun w ↦ -sphereBall (n := n) v (-w) := fun w ↦ by
  -- The antipodal maps of the model space and of the sphere, as diffeomorphisms.
  let μ : EuclideanSpace ℝ (Fin n) ≃ₘ^m⟮𝓡 n, 𝓡 n⟯ EuclideanSpace ℝ (Fin n) :=
    { toEquiv := Equiv.neg _
      contMDiff_toFun := contDiff_neg.contMDiff
      contMDiff_invFun := contDiff_neg.contMDiff }
  let ν : sphere (0 : F) 1 ≃ₘ^m⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1 :=
    { toEquiv := Equiv.neg _
      contMDiff_toFun := contMDiff_neg_sphere
      contMDiff_invFun := contMDiff_neg_sphere }
  exact (μ.isLocalDiffeomorph w).comp
    (hg := (isLocalDiffeomorph_sphereBall v m (-w)).comp (hg := ν.isLocalDiffeomorph _))

variable {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {k : ℕ∞} [IsManifold (𝓡 n) k M] {e : EuclideanSpace ℝ (Fin n) → M}

/-- **The connected sum with a sphere is trivial**: the connected sum `M # Sⁿ` of an
`n`-dimensional `C^k` manifold `M` and the unit sphere `Sⁿ`, along a ball `e` of `M` and the ball
`sphereBall v` of the sphere, is `C^k` diffeomorphic to `M`. -/
def connectedSumSphereDiffeomorph (he : IsOpenEmbedding e)
    (de : IsLocalDiffeomorph (𝓡 n) (𝓡 n) k e) (v : sphere (0 : F) 1) :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin n)) he
      (isOpenEmbedding_sphereBall v)
    ConnectedSum e (sphereBall v) ≃ₘ^k⟮𝓡 n, 𝓡 n⟯ M :=
  (isComplementaryBall_sphereBall v).connectedSumDiffeomorph he (isOpenEmbedding_sphereBall v) de
    (isLocalDiffeomorph_sphereBall v k) (isLocalDiffeomorph_neg_sphereBall_neg v k)

/-- The diffeomorphism `M # Sⁿ ≃ M` is the identity away from the removed centre of `M`. -/
@[simp]
theorem connectedSumSphereDiffeomorph_inl (he : IsOpenEmbedding e)
    (de : IsLocalDiffeomorph (𝓡 n) (𝓡 n) k e) (v : sphere (0 : F) 1)
    (x : ConnectedSum.puncture e) :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin n)) he
      (isOpenEmbedding_sphereBall v)
    connectedSumSphereDiffeomorph he de v (ConnectedSum.inl e (sphereBall v) x) = x := by
  simp [connectedSumSphereDiffeomorph]

/-- The diffeomorphism `M # Sⁿ ≃ M` reads the punctured sphere through the antipodal ball
`w ↦ -sphereBall v (-w)` and sends it into `M` through the ball `e`. -/
@[simp]
theorem connectedSumSphereDiffeomorph_inr (he : IsOpenEmbedding e)
    (de : IsLocalDiffeomorph (𝓡 n) (𝓡 n) k e) (v : sphere (0 : F) 1)
    (w : EuclideanSpace ℝ (Fin n)) :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin n)) he
      (isOpenEmbedding_sphereBall v)
    connectedSumSphereDiffeomorph he de v
      (ConnectedSum.inr e (sphereBall v)
        ((isComplementaryBall_sphereBall v).homeomorphPuncture w)) = e w := by
  simp [connectedSumSphereDiffeomorph]

/-- The inverse of the diffeomorphism `M # Sⁿ ≃ M` is the inclusion away from the removed centre
of `M`. -/
theorem connectedSumSphereDiffeomorph_symm_apply_of_ne (he : IsOpenEmbedding e)
    (de : IsLocalDiffeomorph (𝓡 n) (𝓡 n) k e) (v : sphere (0 : F) 1) {x : M} (hx : x ≠ e 0) :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin n)) he
      (isOpenEmbedding_sphereBall v)
    (connectedSumSphereDiffeomorph he de v).symm x =
      ConnectedSum.inl e (sphereBall v) ⟨x, ConnectedSum.mem_puncture.2 hx⟩ :=
  (isComplementaryBall_sphereBall v).connectedSumHomeomorph_symm_apply_of_ne he hx

/-- The inverse of the diffeomorphism `M # Sⁿ ≃ M` sends the ball `e` to the punctured sphere,
through the antipodal ball `w ↦ -sphereBall v (-w)`. -/
theorem connectedSumSphereDiffeomorph_symm_apply (he : IsOpenEmbedding e)
    (de : IsLocalDiffeomorph (𝓡 n) (𝓡 n) k e) (v : sphere (0 : F) 1)
    (w : EuclideanSpace ℝ (Fin n)) :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin n)) he
      (isOpenEmbedding_sphereBall v)
    (connectedSumSphereDiffeomorph he de v).symm (e w) =
      ConnectedSum.inr e (sphereBall v)
        ((isComplementaryBall_sphereBall v).homeomorphPuncture w) :=
  (isComplementaryBall_sphereBall v).connectedSumHomeomorph_symm_apply he w

/-- **`Sⁿ # Sⁿ ≃ Sⁿ`**: the connected sum of two copies of the unit sphere `Sⁿ`, along the balls
`sphereBall v` and `sphereBall w`, is `C^k` diffeomorphic to `Sⁿ`. -/
theorem nonempty_diffeomorph_connectedSum_sphereBall (k : ℕ∞) (v w : sphere (0 : F) 1) :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin n))
      (isOpenEmbedding_sphereBall (n := n) v) (isOpenEmbedding_sphereBall w)
    Nonempty (ConnectedSum (sphereBall (n := n) v) (sphereBall w) ≃ₘ^k⟮𝓡 n, 𝓡 n⟯
      sphere (0 : F) 1) :=
  ⟨connectedSumSphereDiffeomorph (isOpenEmbedding_sphereBall v)
    (isLocalDiffeomorph_sphereBall v k) w⟩

end RoundSphere

end TauCeti
