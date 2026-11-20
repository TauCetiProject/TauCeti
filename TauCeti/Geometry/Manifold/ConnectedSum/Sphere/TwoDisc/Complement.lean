/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere.Basic
public import TauCeti.Geometry.Manifold.Instances.OpenBall.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Euclidean.Inversion
import TauCeti.Geometry.Manifold.Instances.Cylinder
import TauCeti.Geometry.Manifold.Diffeomorph.RealLine
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Disc complements in the three-sphere and standard cylinder coordinates

Two smooth embeddings of the open unit ball specify two actual closed discs, by restricting each
embedding to the closed ball of radius `1/2`. Their complement is an open submanifold of the native
unit three-sphere. The radial collar keeps the supplied coordinate `((1 + s) / 2) • z`.

For the two small complementary stereographic discs, polar coordinates identify the complement
with the unit two-sphere times `(0,1)`. A smooth increasing change of time makes both original
radial collars linear, with one common positive speed. This supplies the standard coordinates
used by `exists_sphereTwoDiscCylinder` for arbitrary supplied embeddings.

The standard two-disc complement, stereographic cylinder coordinates and radial collar
comparison are adapted from
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture), with
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) as a
supporting formalization reference.
-/

public section

noncomputable section

open Set Function Filter Metric Topology TopologicalSpace EuclideanGeometry
open scoped Manifold ContDiff

namespace TauCeti

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- Two antipodal stereographic embeddings of the open unit ball, scaled by `1/2`. -/
def sphereStandardDisc (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (i : Fin 2) :
  (TauCeti.SmoothEmbedding (𝓡 3) (𝓡 3) ∞ (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3)))
  (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) := by
  let δ := Diffeomorph.smulAdd ∞ (1 / 2 : ℝ) (0 : (EuclideanSpace ℝ (Fin 3))) (by norm_num)
  let a := (TauCeti.SmoothEmbedding.ofOpens (I := 𝓡 3) (n := ∞)
    (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3)))).transDiffeomorph δ
  let g : (EuclideanSpace ℝ (Fin 3)) → (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := if i = 0 then
    TauCeti.sphereBall (n := 3) v else
    fun w ↦ -TauCeti.sphereBall (n := 3) v (-w)
  have hl : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ g := by
    dsimp [g]
    split_ifs
    · exact TauCeti.isLocalDiffeomorph_sphereBall v ∞
    · exact TauCeti.isLocalDiffeomorph_neg_sphereBall_neg v ∞
  have he : IsEmbedding g := by
    dsimp [g]
    split_ifs
    · exact (TauCeti.isOpenEmbedding_sphereBall v).isEmbedding
    · exact (TauCeti.isComplementaryBall_sphereBall v).isOpenEmbedding.isEmbedding
  exact TauCeti.SmoothEmbedding.ofIsSmoothEmbedding (g ∘ a)
    ⟨TauCeti.isImmersion_isLocalDiffeomorphAt_comp (fun p ↦ hl _) a.isImmersion,
      he.comp a.isEmbedding⟩

/-- The first standard disc is the scaled stereographic chart. -/
@[simp]
theorem sphereStandardDisc_zero (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (p :
  TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) :
    sphereStandardDisc v 0 p = TauCeti.sphereBall (n := 3) v ((1 / 2 : ℝ) • (p : (EuclideanSpace ℝ
      (Fin 3)))) := by
  simp [sphereStandardDisc]

/-- The second standard disc uses the antipodal complementary chart. -/
@[simp]
theorem sphereStandardDisc_one (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (p :
  TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) :
    sphereStandardDisc v 1 p = -TauCeti.sphereBall (n := 3) v (-((1 / 2 : ℝ) • (p :
      (EuclideanSpace ℝ (Fin 3))))) := by
  simp [sphereStandardDisc]

/-- The two standard open disc images are disjoint. -/
theorem sphereStandardDisc_disjoint (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    Pairwise (Disjoint on fun i ↦ range (sphereStandardDisc v i)) := by
  have hd : Disjoint (range (sphereStandardDisc v 0)) (range (sphereStandardDisc v 1)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
    rw [sphereStandardDisc_zero, sphereStandardDisc_one] at hq
    have hpn : ‖(1 / 2 : ℝ) • (p : (EuclideanSpace ℝ (Fin 3)))‖ < 1 := by
      have hp := TauCeti.mem_unitBallOpens.1 p.property
      rw [norm_smul, Real.norm_eq_abs]
      norm_num
      linarith
    have hqn : ‖(1 / 2 : ℝ) • (q : (EuclideanSpace ℝ (Fin 3)))‖ < 1 := by
      have hq := TauCeti.mem_unitBallOpens.1 q.property
      rw [norm_smul, Real.norm_eq_abs]
      norm_num
      linarith
    by_cases hq0 : (1 / 2 : ℝ) • (q : (EuclideanSpace ℝ (Fin 3))) = 0
    · have hmem := mem_range_self (f := TauCeti.sphereBall (n := 3) v)
        ((1 / 2 : ℝ) • (p : (EuclideanSpace ℝ (Fin 3))))
      rw [TauCeti.range_sphereBall] at hmem
      rw [hq0, neg_zero, TauCeti.sphereBall_zero, neg_neg] at hq
      exact hmem hq.symm
    · rw [(TauCeti.isComplementaryBall_sphereBall v).apply_eq_inversion _ hq0] at hq
      have he := (TauCeti.isOpenEmbedding_sphereBall (n := 3) v).injective hq
      have hn : ‖inversion 0 1 ((1 / 2 : ℝ) • (q : (EuclideanSpace ℝ (Fin 3))))‖ =
          ‖(1 / 2 : ℝ) • (q : (EuclideanSpace ℝ (Fin 3)))‖⁻¹ := by
        exact EuclideanGeometry.norm_inversion_zero_one _
      have hpos := norm_pos_iff.2 hq0
      have hlt : 1 < ‖(1 / 2 : ℝ) • (q : (EuclideanSpace ℝ (Fin 3)))‖⁻¹ := by
        exact (one_lt_inv₀ hpos).2 hqn
      rw [← he, hn] at hpn
      linarith
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hd
  · exact hd.symm
  · exact (hij rfl).elim

/-- The closed radius-`1/2` disc lies in the open unit ball. -/
def sphereHalfDiscInclusion (p : closedBall (0 : (EuclideanSpace ℝ (Fin 3))) (1 / 2)) :
  TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3)) :=
  ⟨p, TauCeti.mem_unitBallOpens.2 ((mem_closedBall_zero_iff.1 p.property).trans_lt (by norm_num))⟩

/-- The inclusion of the half-disc keeps its original Euclidean coordinates. -/
@[simp]
theorem coe_sphereHalfDiscInclusion (p : closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) :
    (sphereHalfDiscInclusion p : EuclideanSpace ℝ (Fin 3)) = p := by
  simp [sphereHalfDiscInclusion]

/-- The literal open complement of the two supplied closed radius-`1/2` discs. -/
def sphereTwoDiscComplementOpens (f : Fin 2 → (TauCeti.SmoothEmbedding (𝓡 3) (𝓡 3) ∞
  (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))) :
  Opens (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  ⟨(range (f 0 ∘ sphereHalfDiscInclusion) ∪ range (f 1 ∘ sphereHalfDiscInclusion))ᶜ, by
    have hc (i : Fin 2) : Continuous (f i ∘ sphereHalfDiscInclusion) :=
      (f i).contMDiff.continuous.comp (continuous_subtypeVal.subtype_mk _)
    exact ((isCompact_range (hc 0)).union (isCompact_range (hc 1))).isClosed.isOpen_compl⟩

/-- Membership in the literal complement of the two supplied closed discs. -/
@[simp]
theorem mem_sphereTwoDiscComplementOpens
    (f : Fin 2 → SmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (unitBallOpens (EuclideanSpace ℝ (Fin 3))) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    x ∈ sphereTwoDiscComplementOpens f ↔
      x ∉ range (f 0 ∘ sphereHalfDiscInclusion) ∧
        x ∉ range (f 1 ∘ sphereHalfDiscInclusion) := by
  exact not_or

/-- The original radial collar point `((1+s)/2) • z` in the open unit ball. -/
def sphereDiscCollarPoint (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 /
  8)) : TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3)) :=
  ⟨((1 + (s : ℝ)) / 2) • (z : (EuclideanSpace ℝ (Fin 3))), TauCeti.mem_unitBallOpens.2 (by
    rw [norm_smul, norm_eq_of_mem_sphere z, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith [s.property.1])]
    linarith [s.property.2])⟩

/-- The radial collar point retains the supplied Euclidean coordinates. -/
@[simp]
theorem sphereDiscCollarPoint_coe (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (s : Ioo (0 : ℝ) (1 / 8)) :
    (sphereDiscCollarPoint z s : EuclideanSpace ℝ (Fin 3)) = ((1 + (s : ℝ)) / 2) • (z : _) := by
  simp [sphereDiscCollarPoint]

/-- The Euclidean radius of an original collar point is `(1+s)/2`. -/
theorem sphereDiscCollarPoint_norm (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 :
  ℝ) (1 / 8)) :
    ‖(sphereDiscCollarPoint z s : (EuclideanSpace ℝ (Fin 3)))‖ = (1 + (s : ℝ)) / 2 := by
  simp only [sphereDiscCollarPoint_coe, norm_smul, norm_eq_of_mem_sphere z, mul_one,
    Real.norm_eq_abs]
  exact abs_of_pos (by linarith [s.property.1])



/-- The standard supplied discs remove the two stereographic closed radius-`1/4` balls. -/
theorem coe_sphereTwoDiscComplementOpens_standardDisc
    (v : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    (sphereTwoDiscComplementOpens (sphereStandardDisc v) :
      Set (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) =
      (TauCeti.sphereBall (n := 3) v '' closedBall 0 (1 / 4) ∪
        (fun w : EuclideanSpace ℝ (Fin 3) ↦ -TauCeti.sphereBall (n := 3) v (-w)) ''
          closedBall 0 (1 / 4))ᶜ := by
  have h0 : range (sphereStandardDisc v 0 ∘ sphereHalfDiscInclusion) =
      TauCeti.sphereBall (n := 3) v '' closedBall 0 (1 / 4) := by
    simp only [Function.comp_def, sphereStandardDisc_zero, coe_sphereHalfDiscInclusion]
    -- Regroup the pointwise formula to apply range_comp and smul_image_closedBall.
    change range (TauCeti.sphereBall (n := 3) v ∘
      (((1 / 2 : ℝ) • ·) ∘ (Subtype.val : closedBall (0 : EuclideanSpace ℝ (Fin 3))
        (1 / 2) → EuclideanSpace ℝ (Fin 3)))) = _
    rw [range_comp, range_comp, Subtype.range_coe,
      Metric.smul_image_closedBall (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    norm_num
  have h1 : range (sphereStandardDisc v 1 ∘ sphereHalfDiscInclusion) =
      (fun w : (EuclideanSpace ℝ (Fin 3)) ↦ -TauCeti.sphereBall (n := 3) v (-w)) '' closedBall 0
        (1 / 4) := by
    simp only [Function.comp_def, sphereStandardDisc_one, coe_sphereHalfDiscInclusion]
    -- Factor the antipodal chart from the dilation and subtype inclusion to compute its range.
    change range ((fun w : EuclideanSpace ℝ (Fin 3) ↦ -TauCeti.sphereBall (n := 3) v (-w)) ∘
      (((1 / 2 : ℝ) • ·) ∘ (Subtype.val : closedBall (0 : EuclideanSpace ℝ (Fin 3))
        (1 / 2) → EuclideanSpace ℝ (Fin 3)))) = _
    rw [range_comp, range_comp, Subtype.range_coe,
      Metric.smul_image_closedBall (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    norm_num
  ext x
  simp only [SetLike.mem_coe, mem_sphereTwoDiscComplementOpens, mem_compl_iff, mem_union,
    not_or, h0, h1]


private def timeStrip : Opens ((sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ) :=
  ⟨univ ×ˢ Ioo (-Real.log 4) (Real.log 4), isOpen_univ.prod isOpen_Ioo⟩

private theorem mem_timeStrip (p : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ) :
    p ∈ timeStrip ↔ -Real.log 4 < p.2 ∧ p.2 < Real.log 4 := by
  simp [timeStrip]

private def cylinderMap (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (p : (sphere (0 :
  EuclideanSpace ℝ (Fin 3)) 1) × ℝ) : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  TauCeti.sphereBall (n := 3) v (Real.exp p.2 • (p.1 : (EuclideanSpace ℝ (Fin 3))))

private theorem cylinderMap_apply (v : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (p : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ) :
    cylinderMap v p = sphereBall v (Real.exp p.2 • (p.1 : EuclideanSpace ℝ (Fin 3))) := rfl

private theorem cylinderMap_injective (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) : Injective
  (cylinderMap v) := by
  intro p q h
  apply (TauCeti.sphereProdRealDiffeomorph (V := (EuclideanSpace ℝ (Fin 3))) (n := 2)).injective
  apply Subtype.ext
  simp only [Diffeomorph.coe_toEquiv]
  rw [coe_sphereProdRealDiffeomorph_apply, coe_sphereProdRealDiffeomorph_apply]
  exact (TauCeti.isOpenEmbedding_sphereBall (n := 3) v).injective h

private theorem cylinderMap_local (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
  IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ (cylinderMap v) := by
  have he : cylinderMap v = sphereBall v ∘ Subtype.val ∘
      sphereProdRealDiffeomorph (V := EuclideanSpace ℝ (Fin 3)) (n := 2) := by
    funext p
    simp [cylinderMap, Function.comp_def]
  rw [he]
  intro p
  exact (((TauCeti.sphereProdRealDiffeomorph (V := (EuclideanSpace ℝ (Fin 3))) (n :=
    2)).isLocalDiffeomorph p).comp
    (hg := TauCeti.isLocalDiffeomorph_subtype_val
      (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin 3)))) (n := ∞) _)).comp
    (hg := TauCeti.isLocalDiffeomorph_sphereBall (n := 3) v ∞ _)

private theorem mem_complement_sphereBall (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (w :
  (EuclideanSpace ℝ (Fin 3))) :
    TauCeti.sphereBall (n := 3) v w ∈ sphereTwoDiscComplementOpens (sphereStandardDisc v) ↔
      (1 / 4 : ℝ) < ‖w‖ ∧ ‖w‖ < 4 := by
  rw [← SetLike.mem_coe, coe_sphereTwoDiscComplementOpens_standardDisc]
  have hs := TauCeti.isComplementaryBall_sphereBall (n := 3) v
  have hi := (TauCeti.isOpenEmbedding_sphereBall (n := 3) v).injective
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hfour : (0 : ℝ) < 4 := by norm_num
  constructor
  · intro h
    have h₀ : w ∉ closedBall 0 (1 / 4) := by
      intro hw
      exact h (Or.inl (mem_image_of_mem _ hw))
    have hw : w ≠ 0 := by
      intro hw
      exact h₀ (by simp [hw])
    have h₁ : inversion 0 1 w ∉ closedBall 0 (1 / 4) := by
      intro hw'
      apply h
      right
      refine ⟨inversion 0 1 w, hw', ?_⟩
      exact (hs.apply_eq_inversion _ ((inversion_eq_center one_ne_zero).not.2 hw)).trans
        (congrArg (TauCeti.sphereBall (n := 3) v) (inversion_inversion _ one_ne_zero w))
    have hnorm : 0 < ‖w‖ := norm_pos_iff.2 hw
    simp only [mem_closedBall_zero_iff, not_le] at h₀ h₁
    rw [EuclideanGeometry.norm_inversion_zero_one] at h₁
    refine ⟨h₀, ?_⟩
    have hbound := (lt_inv_comm₀ hquarter hnorm).1 h₁
    norm_num at hbound
    exact hbound
  · rintro ⟨hl, hu⟩ (h₀ | h₁)
    · obtain ⟨z, hz, he⟩ := h₀
      have hzw := hi he
      exact (not_le_of_gt hl) (hzw ▸ mem_closedBall_zero_iff.1 hz)
    · obtain ⟨z, hz, he⟩ := h₁
      by_cases hz0 : z = 0
      · have hmem : TauCeti.sphereBall (n := 3) v w ∈
            range (TauCeti.sphereBall (n := 3) v) := mem_range_self w
        rw [TauCeti.range_sphereBall] at hmem
        exact hmem (by simpa [hz0, TauCeti.sphereBall_zero] using he.symm)
      · dsimp only at he
        rw [hs.apply_eq_inversion z hz0] at he
        have hzw := hi he
        have hnorm : 0 < ‖z‖ := norm_pos_iff.2 hz0
        have hsmall : ‖z‖ ≤ 1 / 4 := mem_closedBall_zero_iff.1 hz
        have hlarge : 4 ≤ ‖z‖⁻¹ := by
          apply (le_inv_comm₀ hfour hnorm).2
          norm_num
          exact hsmall
        exact (not_le_of_gt hu) (by
          rw [← hzw, EuclideanGeometry.norm_inversion_zero_one]
          exact hlarge)

private theorem cylinderMap_mem_complement (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (p :
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ) :
    cylinderMap v p ∈ sphereTwoDiscComplementOpens (sphereStandardDisc v) ↔ p ∈ timeStrip := by
  rw [cylinderMap, mem_complement_sphereBall]
  have hn : ‖Real.exp p.2 • (p.1 : (EuclideanSpace ℝ (Fin 3)))‖ = Real.exp p.2 := by
    simp [norm_smul, norm_eq_of_mem_sphere p.1]
  rw [hn]
  rw [mem_timeStrip]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 4), Real.exp_lt_exp,
    ← Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
  simp [one_div, Real.log_inv]

private theorem image_cylinderMap_strip (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
  cylinderMap v '' timeStrip = sphereTwoDiscComplementOpens (sphereStandardDisc v) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact (cylinderMap_mem_complement v p).2 hp
  · intro x hx
    have hxv : x ≠ v := by
      intro h
      have hx' : x ∈ (sphereTwoDiscComplementOpens (sphereStandardDisc v) : Set _) := hx
      rw [coe_sphereTwoDiscComplementOpens_standardDisc] at hx'
      apply hx'
      right
      refine ⟨0, by simp, ?_⟩
      simp [h]
    obtain ⟨w, rfl⟩ : x ∈ range (TauCeti.sphereBall (n := 3) v) := by
      rwa [TauCeti.range_sphereBall]
    have hw : w ≠ 0 := by
      have hnorm := (mem_complement_sphereBall v w).1 hx
      exact norm_ne_zero_iff.1 (ne_of_gt (lt_trans (by norm_num) hnorm.1))
    let p := (TauCeti.sphereProdRealDiffeomorph (V := (EuclideanSpace ℝ (Fin 3))) (n := 2)).symm
      ⟨w, mem_puncturedSpace.2 hw⟩
    have hp : cylinderMap v p = TauCeti.sphereBall (n := 3) v w := by
      have h := congrArg Subtype.val
        ((TauCeti.sphereProdRealDiffeomorph (V := EuclideanSpace ℝ (Fin 3))
          (n := 2)).apply_symm_apply
          ⟨w, mem_puncturedSpace.2 hw⟩)
      simpa only [cylinderMap, coe_sphereProdRealDiffeomorph_apply] using
        congrArg (TauCeti.sphereBall (n := 3) v) h
    exact ⟨p, (cylinderMap_mem_complement v p).1 (hp ▸ hx), hp⟩

private def canonicalCylinder (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) : timeStrip ≃ₘ^∞⟮((𝓡
  2).prod 𝓘(ℝ)), 𝓡 3⟯ sphereTwoDiscComplementOpens (sphereStandardDisc v) := by
  let f := cylinderMap v ∘ (Subtype.val : timeStrip → (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ)
  have hf : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ f := fun p ↦
    (TauCeti.isLocalDiffeomorph_subtype_val (I := ((𝓡 2).prod 𝓘(ℝ))) (n := ∞) p).comp
      (hg := cylinderMap_local v p)
  have hinj : Injective f := (cylinderMap_injective v).comp Subtype.val_injective
  have hrange : range f = sphereTwoDiscComplementOpens (sphereStandardDisc v) := by
    dsimp only [f]
    rw [range_comp, Subtype.range_coe, image_cylinderMap_strip]
  exact (hf.diffeomorphOfInjective hinj).trans
    ((Diffeomorph.refl (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞).subtype fun x ↦ by
      -- The ambient identity restricts to the open subsets identified by hrange.
      change x ∈ range f ↔ x ∈ sphereTwoDiscComplementOpens (sphereStandardDisc v)
      rw [hrange]
      rfl)

/-- The radial collar point in either standard stereographic disc chart. -/
def sphereStandardDiscCollar (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (i : Fin 2) (z :
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : ℝ) : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  if i = 0 then TauCeti.sphereBall (n := 3) v (((1 + s) / 4) • (z : (EuclideanSpace ℝ (Fin 3))))
    else
    -TauCeti.sphereBall (n := 3) v (-(((1 + s) / 4) • (z : (EuclideanSpace ℝ (Fin 3)))))


/-- The first standard collar is expressed in the original stereographic chart. -/
@[simp]
theorem sphereStandardDiscCollar_zero (v : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    sphereStandardDiscCollar v 0 z s =
      sphereBall v (((1 + s) / 4) • (z : EuclideanSpace ℝ (Fin 3))) := by
  simp [sphereStandardDiscCollar]

/-- The second standard collar is expressed in the antipodal stereographic chart. -/
@[simp]
theorem sphereStandardDiscCollar_one (v : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    sphereStandardDiscCollar v 1 z s =
      -sphereBall v (-(((1 + s) / 4) • (z : EuclideanSpace ℝ (Fin 3)))) := by
  simp [sphereStandardDiscCollar]

/-- The explicit standard collar equals the original supplied-disc collar. -/
theorem sphereStandardDisc_collarPoint (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (i : Fin 2)
  (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (s : Ioo (0 : ℝ) (1 / 8)) :
    sphereStandardDisc v i (sphereDiscCollarPoint z s) = sphereStandardDiscCollar v i z s := by
  have he : (1 / 2 : ℝ) • (sphereDiscCollarPoint z s : (EuclideanSpace ℝ (Fin 3))) = ((1 + (s :
    ℝ)) / 4) • (z : (EuclideanSpace ℝ (Fin 3))) := by
    rw [sphereDiscCollarPoint_coe, smul_smul]
    congr 1
    ring
  fin_cases i
  · -- Normalize the first Fin 2 label selected by fin_cases to use the public disc formula.
    change sphereStandardDisc v 0 (sphereDiscCollarPoint z s) = sphereStandardDiscCollar v 0 z s
    rw [sphereStandardDisc_zero, he]
    rw [sphereStandardDiscCollar_zero]
  · -- Normalize the second Fin 2 label selected by fin_cases to use the public disc formula.
    change sphereStandardDisc v 1 (sphereDiscCollarPoint z s) = sphereStandardDiscCollar v 1 z s
    rw [sphereStandardDisc_one, he]
    rw [sphereStandardDiscCollar_one]


/-- The native unit two-sphere times the open interval `(0,1)`. -/
def sphereUnitCylinderOpens : Opens ((sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ) :=
  ⟨univ ×ˢ Ioo 0 1, isOpen_univ.prod isOpen_Ioo⟩

/-- A sphere-cylinder point lies in the unit cylinder exactly when its time lies in `(0,1)`. -/
@[simp]
theorem mem_sphereUnitCylinderOpens (p : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ) :
    p ∈ sphereUnitCylinderOpens ↔ 0 < p.2 ∧ p.2 < 1 := by
  simp [sphereUnitCylinderOpens]

private def rescaleStrip : timeStrip ≃ₘ^∞⟮((𝓡 2).prod 𝓘(ℝ)), ((𝓡 2).prod 𝓘(ℝ))⟯
  sphereUnitCylinderOpens := by
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let a := Diffeomorph.smulAdd ∞ (2 * Real.log 4)⁻¹ (1 / 2 : ℝ) (by positivity)
  refine ((Diffeomorph.refl (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
    a).subtype ?_
  intro p
  simp only [mem_timeStrip, mem_sphereUnitCylinderOpens, Diffeomorph.coe_prodCongr,
    Prod.map_snd]
  simp only [a, Diffeomorph.smulAdd_apply, smul_eq_mul]
  rw [inv_mul_eq_div]
  have hc : 0 < 2 * Real.log 4 := mul_pos (by norm_num) hl
  constructor
  · rintro ⟨hl', hu'⟩
    constructor
    · have hlower : -(1 / 2) * (2 * Real.log 4) < p.2 := by nlinarith
      have := (lt_div_iff₀ hc).2 hlower
      linarith
    · have hupper : p.2 < (1 / 2) * (2 * Real.log 4) := by nlinarith
      have := (div_lt_iff₀ hc).2 hupper
      linarith
  · rintro ⟨hl', hu'⟩
    have hlow : -(1 / 2) < p.2 / (2 * Real.log 4) := by linarith
    have hupp : p.2 / (2 * Real.log 4) < 1 / 2 := by linarith
    have := (lt_div_iff₀ hc).1 hlow
    have := (div_lt_iff₀ hc).1 hupp
    exact ⟨by nlinarith, by nlinarith⟩

private def straightenStrip (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) :
    sphereUnitCylinderOpens ≃ₘ^∞⟮((𝓡 2).prod 𝓘(ℝ)), ((𝓡 2).prod 𝓘(ℝ))⟯ sphereUnitCylinderOpens := by
  have hmono : StrictMono Ψ := by
    rcases Ψ.continuous.strictMono_of_inj Ψ.injective with h | h
    · exact h
    · have h01 : (0 : ℝ) < 1 := by norm_num
      have h' := h h01
      rw [h0, h1] at h'
      linarith
  exact ((Diffeomorph.refl (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr Ψ).subtype
    fun p ↦ by
    simp only [mem_sphereUnitCylinderOpens, Diffeomorph.coe_prodCongr, Prod.map_snd]
    have hl : 0 < Ψ p.2 ↔ 0 < p.2 := by
      simpa only [h0] using (hmono.lt_iff_lt (a := 0) (b := p.2))
    have hu : Ψ p.2 < 1 ↔ p.2 < 1 := by
      simpa only [h1] using (hmono.lt_iff_lt (a := p.2) (b := 1))
    rw [hl, hu]

private theorem canonicalCylinder_apply (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (p :
  timeStrip) :
    (canonicalCylinder v p : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) = cylinderMap v p := by
  simp only [canonicalCylinder, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.subtype_apply_coe, Diffeomorph.coe_refl, id_eq]
  exact IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ p

private def alignedCanonical (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ),
  𝓘(ℝ)⟯ ℝ)
    (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) :
    sphereTwoDiscComplementOpens (sphereStandardDisc v) ≃ₘ^∞⟮𝓡 3, ((𝓡 2).prod 𝓘(ℝ))⟯
      sphereUnitCylinderOpens :=
  (canonicalCylinder v).symm.trans (rescaleStrip.trans (straightenStrip Ψ h0 h1))

private theorem alignedCanonical_cylinderMap (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (p : timeStrip) :
    ((alignedCanonical v Ψ h0 h1) (canonicalCylinder v p) : (sphere (0 : EuclideanSpace ℝ
      (Fin 3)) 1) × ℝ) =
      (p.val.1, Ψ ((2 * Real.log 4)⁻¹ * p.val.2 + 1 / 2)) := by
  simp [alignedCanonical, rescaleStrip, straightenStrip, Prod.map]


private theorem log_collar_bounds (s : Ioo (0 : ℝ) (1 / 8)) :
    0 < Real.log (1 + (s : ℝ)) ∧ Real.log (1 + (s : ℝ)) < Real.log 4 := by
  constructor
  · exact Real.log_pos (by linarith [s.property.1])
  · exact Real.log_lt_log (by linarith [s.property.1]) (by linarith [s.property.2])

private def lowerStripPoint (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 /
  8)) : timeStrip :=
  ⟨(z, Real.log (1 + (s : ℝ)) - Real.log 4), by
    have hlog := log_collar_bounds s
    exact ⟨mem_univ _, by linarith, by linarith⟩⟩

private def upperStripPoint (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 /
  8)) : timeStrip :=
  ⟨(z, Real.log 4 - Real.log (1 + (s : ℝ))), by
    have hlog := log_collar_bounds s
    exact ⟨mem_univ _, by linarith, by linarith⟩⟩

private theorem canonicalCylinder_lower (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (z :
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 / 8)) :
    (canonicalCylinder v (lowerStripPoint z s) : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) =
      sphereStandardDisc v 0 (sphereDiscCollarPoint z s) := by
  rw [canonicalCylinder_apply, sphereStandardDisc_zero, sphereDiscCollarPoint_coe,
    cylinderMap_apply]
  simp only [lowerStripPoint]
  rw [Real.exp_sub, Real.exp_log (by linarith [s.property.1]),
    Real.exp_log (by norm_num : (0 : ℝ) < 4), smul_smul]
  congr 2
  ring

private theorem canonicalCylinder_upper (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (z :
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 / 8)) :
    (canonicalCylinder v (upperStripPoint z s) : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) =
      sphereStandardDisc v 1 (sphereDiscCollarPoint z s) := by
  rw [canonicalCylinder_apply, sphereStandardDisc_one]
  let a : ℝ := (1 + (s : ℝ)) / 4
  have ha : 0 < a := by dsimp [a]; linarith [s.property.1]
  have hne : a • (z : (EuclideanSpace ℝ (Fin 3))) ≠ 0 := smul_ne_zero ha.ne'
    (ne_zero_of_mem_unit_sphere z)
  have he : (1 / 2 : ℝ) • (sphereDiscCollarPoint z s : (EuclideanSpace ℝ (Fin 3))) = a • (z :
    (EuclideanSpace ℝ (Fin 3))) := by
    rw [sphereDiscCollarPoint_coe, smul_smul]
    congr 1
    dsimp [a]
    ring
  rw [he, (TauCeti.isComplementaryBall_sphereBall v).apply_eq_inversion _ hne]
  rw [cylinderMap_apply]
  simp only [upperStripPoint]
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4),
    Real.exp_log (by linarith [s.property.1])]
  have hinv : inversion 0 1 (a • (z : (EuclideanSpace ℝ (Fin 3)))) = a⁻¹ • (z : (EuclideanSpace ℝ
    (Fin 3))) := by
    simp only [inversion, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, norm_eq_of_mem_sphere z, mul_one, vsub_eq_sub, sub_zero, vadd_eq_add,
      add_zero, smul_smul]
    congr 1
    field_simp
  rw [hinv]
  congr 2
  dsimp [a]
  field_simp

private theorem alignedCanonical_lower (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 /
      8)) :
    (alignedCanonical v Ψ h0 h1 (canonicalCylinder v (lowerStripPoint z s)) : (sphere (0 :
      EuclideanSpace ℝ (Fin 3)) 1) × ℝ) =
      (z, Ψ (Real.log (1 + (s : ℝ)) / (2 * Real.log 4))) := by
  rw [alignedCanonical_cylinderMap]
  congr 2
  simp only [lowerStripPoint]
  have hl : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne'
  field_simp
  ring

private theorem alignedCanonical_upper (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 /
      8)) :
    (alignedCanonical v Ψ h0 h1 (canonicalCylinder v (upperStripPoint z s)) : (sphere (0 :
      EuclideanSpace ℝ (Fin 3)) 1) × ℝ) =
      (z, Ψ (1 - Real.log (1 + (s : ℝ)) / (2 * Real.log 4))) := by
  rw [alignedCanonical_cylinderMap]
  congr 2
  simp only [upperStripPoint]
  have hl : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne'
  field_simp
  ring

private theorem collarSpeed_le_half : (2 * Real.log 4)⁻¹ ≤ (1 / 2 : ℝ) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1; norm_num
  have hl : 1 ≤ Real.log 4 := by rw [h4]; norm_num at h2; linarith
  simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2)
    (by linarith [hl] : (2 : ℝ) ≤ 2 * Real.log 4)


/-- Both original standard radial collars lie outside the two removed closed discs. -/
theorem sphereStandardDiscCollar_mem
    (v : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (i : Fin 2)
    (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) (hs : 0 < s) (hs8 : s < 1 / 8) :
    sphereStandardDiscCollar v i z s ∈ sphereTwoDiscComplementOpens (sphereStandardDisc v) := by
  let t : Ioo (0 : ℝ) (1 / 8) := ⟨s, hs, hs8⟩
  rw [← sphereStandardDisc_collarPoint v i z t]
  fin_cases i
  · -- Normalize the first Fin 2 label selected by fin_cases to use the public disc formula.
    change sphereStandardDisc v 0 (sphereDiscCollarPoint z t) ∈
    sphereTwoDiscComplementOpens (sphereStandardDisc v)
    rw [← canonicalCylinder_lower]
    exact (canonicalCylinder v (lowerStripPoint z t)).property
  · -- Normalize the second Fin 2 label selected by fin_cases to use the public disc formula.
    change sphereStandardDisc v 1 (sphereDiscCollarPoint z t) ∈
    sphereTwoDiscComplementOpens (sphereStandardDisc v)
    rw [← canonicalCylinder_upper]
    exact (canonicalCylinder v (upperStripPoint z t)).property

/-- The standard two-disc complement is a cylinder with exact linear coordinates on both collars. -/
theorem exists_sphereStandardDiscCylinder (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    ∃ k η : ℝ, 0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∃ C : sphereTwoDiscComplementOpens (sphereStandardDisc v) ≃ₘ^∞⟮𝓡 3, ((𝓡 2).prod 𝓘(ℝ))⟯
        sphereUnitCylinderOpens,
        (∀ i z s, 0 < s → s < 1 / 8 → sphereStandardDiscCollar v i z s ∈
          sphereTwoDiscComplementOpens (sphereStandardDisc v)) ∧
        (∀ z s, 0 < s → s < η → ∀ hx : sphereStandardDiscCollar v 0 z s ∈
          sphereTwoDiscComplementOpens (sphereStandardDisc v),
          (C ⟨sphereStandardDiscCollar v 0 z s, hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ×
            ℝ) = (z, k * s)) ∧
        (∀ z s, 0 < s → s < η → ∀ hx : sphereStandardDiscCollar v 1 z s ∈
          sphereTwoDiscComplementOpens (sphereStandardDisc v),
          (C ⟨sphereStandardDiscCollar v 1 z s, hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ×
            ℝ) = (z, 1 - k * s)) := by
  have hc : 0 < 2 * Real.log 4 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨Ψ, η, h0, h1, hη, hη8, hΨ⟩ :=
    exists_diffeomorph_log_collars (2 * Real.log 4)
  refine ⟨(2 * Real.log 4)⁻¹, η, inv_pos.2 hc, collarSpeed_le_half, hη, hη8,
    alignedCanonical v Ψ h0 h1, sphereStandardDiscCollar_mem v, ?_, ?_⟩
  · intro z s hs hsη hx
    let t : Ioo (0 : ℝ) (1 / 8) := ⟨s, hs, hsη.trans_le hη8⟩
    have he : (⟨sphereStandardDiscCollar v 0 z s, hx⟩ :
        sphereTwoDiscComplementOpens (sphereStandardDisc v)) =
        canonicalCylinder v (lowerStripPoint z t) := by
      apply Subtype.ext
      rw [canonicalCylinder_lower, sphereStandardDisc_collarPoint]
    rw [he, alignedCanonical_lower, (hΨ s hs hsη).1]
    exact Prod.ext rfl (by ring)
  · intro z s hs hsη hx
    let t : Ioo (0 : ℝ) (1 / 8) := ⟨s, hs, hsη.trans_le hη8⟩
    have he : (⟨sphereStandardDiscCollar v 1 z s, hx⟩ :
        sphereTwoDiscComplementOpens (sphereStandardDisc v)) =
        canonicalCylinder v (upperStripPoint z t) := by
      apply Subtype.ext
      rw [canonicalCylinder_upper, sphereStandardDisc_collarPoint]
    rw [he, alignedCanonical_upper, (hΨ s hs hsη).2]
    exact Prod.ext rfl (by ring)

end TauCeti
