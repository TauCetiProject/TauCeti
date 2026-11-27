/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.Interval
public import TauCeti.Geometry.Manifold.Instances.OpenBall.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Euclidean.Inversion
import TauCeti.Geometry.Manifold.Instances.Cylinder
import TauCeti.Geometry.Manifold.Diffeomorph.Germ
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Disc complements in spheres and standard cylinder coordinates

Two smooth embeddings of the open unit ball specify two actual closed discs, by restricting each
embedding to the closed ball of radius `1/2`. Their complement is an open submanifold of the native
unit `n`-sphere. The radial collar keeps the supplied coordinate `((1 + s) / 2) • z`.

For the two small complementary stereographic discs, polar coordinates identify the complement
with the unit `(n - 1)`-sphere times `(0,1)`. A smooth increasing change of time makes both original
radial collars linear near the removed discs, for collar times below some `η ≤ 1/8`, with one
common positive speed. This supplies the standard coordinates
used by `exists_diffeomorph_sphereTwoDiscComplementOpens_prodIooOpens` for arbitrary supplied
embeddings.

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

variable {n : ℕ}

namespace SphereTwoDisc

/-- The native sphere chart has the expected successor dimension. -/
scoped instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨by simp⟩

/-- A nonzero Euclidean dimension is a successor of its predecessor. -/
scoped instance [NeZero n] :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1) :=
  ⟨by simp; have h := NeZero.ne n; omega⟩

/-- The dimension bound for the ambient disc theorem implies a nonempty coordinate index. -/
scoped instance [Fact (2 ≤ n)] : NeZero n :=
  ⟨by have h := Fact.out (p := 2 ≤ n); omega⟩

end SphereTwoDisc

open scoped SphereTwoDisc

private theorem sphereStandardDisc_isLocalDiffeomorph
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i : Fin 2) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
      (if i = 0 then TauCeti.sphereBall (n := n) v else
        fun w ↦ -TauCeti.sphereBall (n := n) v (-w)) := by
  split_ifs
  · exact TauCeti.isLocalDiffeomorph_sphereBall v ∞
  · exact TauCeti.isLocalDiffeomorph_neg_sphereBall_neg v ∞

private theorem sphereStandardDisc_isEmbedding
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i : Fin 2) :
    IsEmbedding (if i = 0 then TauCeti.sphereBall (n := n) v else
      fun w ↦ -TauCeti.sphereBall (n := n) v (-w)) := by
  split_ifs
  · exact (TauCeti.isOpenEmbedding_sphereBall v).isEmbedding
  · exact (TauCeti.isComplementaryBall_sphereBall v).isOpenEmbedding.isEmbedding

/-- Two antipodal stereographic embeddings of the open unit ball, scaled by `1/2`. -/
def sphereStandardDisc (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (i : Fin 2) :
  (TauCeti.SmoothEmbedding (𝓡 n) (𝓡 n) ∞ (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin n)))
  (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
  let δ := Diffeomorph.smulAdd ∞ (1 / 2 : ℝ) (0 : EuclideanSpace ℝ (Fin n)) (by norm_num)
  let a := (TauCeti.SmoothEmbedding.ofOpens (I := 𝓡 n) (n := ∞)
    (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin n)))).transDiffeomorph δ
  let g : EuclideanSpace ℝ (Fin n) → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    if i = 0 then TauCeti.sphereBall (n := n) v else
      fun w ↦ -TauCeti.sphereBall (n := n) v (-w)
  TauCeti.SmoothEmbedding.ofIsSmoothEmbedding (g ∘ a)
    ⟨TauCeti.isImmersion_isLocalDiffeomorphAt_comp
    (fun p ↦ sphereStandardDisc_isLocalDiffeomorph v i (a p)) a.isImmersion,
      (sphereStandardDisc_isEmbedding v i).comp a.isEmbedding⟩

/-- The first standard disc is the scaled stereographic chart. -/
@[simp]
theorem sphereStandardDisc_zero (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (p :
  TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin n))) :
    sphereStandardDisc v 0 p = TauCeti.sphereBall (n := n) v ((1 / 2 : ℝ) • (p : (EuclideanSpace ℝ
      (Fin n)))) := by
  simp only [sphereStandardDisc, ↓reduceIte, SmoothEmbedding.ofIsSmoothEmbedding_apply,
    Function.comp_apply, SmoothEmbedding.transDiffeomorph_apply,
    SmoothEmbedding.ofOpens_apply, Diffeomorph.smulAdd_apply, add_zero]

/-- The second standard disc uses the antipodal complementary chart. -/
@[simp]
theorem sphereStandardDisc_one (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (p :
  TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin n))) :
    sphereStandardDisc v 1 p = -TauCeti.sphereBall (n := n) v (-((1 / 2 : ℝ) • (p :
      (EuclideanSpace ℝ (Fin n))))) := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp only [sphereStandardDisc, ite_eq_right h, SmoothEmbedding.ofIsSmoothEmbedding_apply,
    Function.comp_apply, SmoothEmbedding.transDiffeomorph_apply,
    SmoothEmbedding.ofOpens_apply, Diffeomorph.smulAdd_apply, add_zero]

private theorem norm_half_smul_lt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : unitBallOpens E) : ‖(1 / 2 : ℝ) • (p : E)‖ < 1 := by
  have hp := mem_unitBallOpens.1 p.property
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
  linarith

private theorem sphereBall_ne_complementary_center
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (w : EuclideanSpace ℝ (Fin n)) :
    sphereBall v w ≠ -sphereBall (n := n) v (-0) := by
  have hmem := mem_range_self (f := sphereBall (n := n) v) w
  simpa only [range_sphereBall, mem_compl_singleton_iff, neg_zero, sphereBall_zero, neg_neg]
    using hmem

private theorem inv_radius_le_norm_of_complementary_eq
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {w z : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hz : ‖z‖ ≤ r)
    (he : -sphereBall v (-z) = sphereBall v w) : r⁻¹ ≤ ‖w‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    exact sphereBall_ne_complementary_center v w (by simpa only [h] using he.symm)
  rw [(isComplementaryBall_sphereBall v).apply_eq_inversion z hz0] at he
  have hzw := (isOpenEmbedding_sphereBall (n := n) v).injective he
  rw [← hzw, EuclideanGeometry.norm_inversion_zero_one]
  exact (inv_le_inv₀ ((norm_pos_iff.2 hz0).trans_le hz) (norm_pos_iff.2 hz0)).2 hz

/-- The two standard open disc images are disjoint. -/
theorem sphereStandardDisc_disjoint (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Pairwise (Disjoint on fun i ↦ range (sphereStandardDisc v i)) := by
  have hd : Disjoint (range (sphereStandardDisc v 0)) (range (sphereStandardDisc v 1)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
    rw [sphereStandardDisc_zero, sphereStandardDisc_one] at hq
    have hpn := norm_half_smul_lt_one p
    have hlarge := inv_radius_le_norm_of_complementary_eq v
      (norm_half_smul_lt_one q).le hq
    norm_num at hlarge
    linarith
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hd
  · exact hd.symm
  · exact (hij rfl).elim

/-- The closed radius-`1/2` disc lies in the open unit ball. -/
def sphereHalfDiscInclusion (p : closedBall (0 : (EuclideanSpace ℝ (Fin n))) (1 / 2)) :
  TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin n)) :=
  ⟨p, TauCeti.mem_unitBallOpens.2 ((mem_closedBall_zero_iff.1 p.property).trans_lt (by norm_num))⟩

/-- The inclusion of the half-disc keeps its original Euclidean coordinates. -/
@[simp]
theorem coe_sphereHalfDiscInclusion (p : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) :
    (sphereHalfDiscInclusion p : EuclideanSpace ℝ (Fin n)) = p := by
  simp [sphereHalfDiscInclusion]

/-- The literal open complement of the two supplied closed radius-`1/2` discs. -/
def sphereTwoDiscComplementOpens
    (f : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞ (unitBallOpens (EuclideanSpace ℝ (Fin n)))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
  Opens (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨(range (f 0 ∘ sphereHalfDiscInclusion) ∪ range (f 1 ∘ sphereHalfDiscInclusion))ᶜ, by
    have hc (i : Fin 2) : Continuous (f i ∘ sphereHalfDiscInclusion) :=
      (f i).contMDiff.continuous.comp (continuous_subtypeVal.subtype_mk _)
    exact ((isCompact_range (hc 0)).union (isCompact_range (hc 1))).isClosed.isOpen_compl⟩

/-- Membership in the literal complement of the two supplied closed discs. -/
@[simp]
theorem mem_sphereTwoDiscComplementOpens
    (f : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞
      (unitBallOpens (EuclideanSpace ℝ (Fin n))) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    x ∈ sphereTwoDiscComplementOpens f ↔
      x ∉ range (f 0 ∘ sphereHalfDiscInclusion) ∧
        x ∉ range (f 1 ∘ sphereHalfDiscInclusion) := by
  exact not_or

/-- The original radial collar point `((1+s)/2) • z` in the open unit ball. -/
def sphereDiscCollarPoint (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 : ℝ) 1) :
    TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin n)) :=
  ⟨((1 + (s : ℝ)) / 2) • (z : (EuclideanSpace ℝ (Fin n))), TauCeti.mem_unitBallOpens.2 (by
    rw [norm_smul, norm_eq_of_mem_sphere z, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith [s.property.1])]
    linarith [s.property.2])⟩

/-- The radial collar point retains the supplied Euclidean coordinates. -/
@[simp]
theorem coe_sphereDiscCollarPoint (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (s : Ioo (0 : ℝ) 1) :
    (sphereDiscCollarPoint z s : EuclideanSpace ℝ (Fin n)) = ((1 + (s : ℝ)) / 2) • (z : _) := by
  rfl

/-- The Euclidean radius of an original collar point is `(1+s)/2`. -/
theorem norm_sphereDiscCollarPoint (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 :
    ℝ) 1) :
    ‖(sphereDiscCollarPoint z s : (EuclideanSpace ℝ (Fin n)))‖ = (1 + (s : ℝ)) / 2 := by
  simp only [coe_sphereDiscCollarPoint, norm_smul, norm_eq_of_mem_sphere z, mul_one,
    Real.norm_eq_abs]
  exact abs_of_pos (by linarith [s.property.1])



/-- An original collar point lies outside its own closed half-disc and outside the other
closed disc when the two full embedding images are disjoint. -/
theorem sphereDiscCollarPoint_mem_sphereTwoDiscComplementOpens
    (f : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞
      (unitBallOpens (EuclideanSpace ℝ (Fin n)))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i)))
    (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (s : Ioo (0 : ℝ) 1) :
    f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f := by
  have hnot (j : Fin 2) :
      f i (sphereDiscCollarPoint z s) ∉ range (f j ∘ sphereHalfDiscInclusion) := by
    rintro ⟨p, hp⟩
    by_cases hij : i = j
    · subst j
      have he : sphereHalfDiscInclusion p = sphereDiscCollarPoint z s :=
        (f i).isEmbedding.injective hp
      have hn := mem_closedBall_zero_iff.1 p.property
      rw [← coe_sphereHalfDiscInclusion p, he, norm_sphereDiscCollarPoint] at hn
      linarith [s.property.1]
    · exact Set.disjoint_left.1 (hfd hij) (mem_range_self _) ⟨sphereHalfDiscInclusion p, hp⟩
  exact (mem_sphereTwoDiscComplementOpens f _).2 ⟨hnot 0, hnot 1⟩

private def smallCollarToUnit (s : Ioo (0 : ℝ) (1 / 8)) : Ioo (0 : ℝ) 1 :=
  ⟨s, s.property.1, s.property.2.trans (by norm_num)⟩

private theorem range_half_smul_closedBall {X : Type*}
    (F : EuclideanSpace ℝ (Fin n) → X) :
    range (fun p : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ↦
      F ((1 / 2 : ℝ) • (p : EuclideanSpace ℝ (Fin n)))) = F '' closedBall 0 (1 / 4) := by
  calc
    _ = F '' range (fun p : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ↦
        (1 / 2 : ℝ) • (p : EuclideanSpace ℝ (Fin n))) := range_comp F _
    _ = F '' (((1 / 2 : ℝ) • ·) '' closedBall 0 (1 / 2)) := by
      apply congrArg (F '' ·)
      exact (range_comp ((1 / 2 : ℝ) • ·)
        (Subtype.val : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) →
          EuclideanSpace ℝ (Fin n))).trans
        (congrArg (((1 / 2 : ℝ) • ·) '' ·) Subtype.range_coe)
    _ = _ := by
      rw [Metric.smul_image_closedBall (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      norm_num

/-- The standard supplied discs remove the two stereographic closed radius-`1/4` balls. -/
theorem coe_sphereTwoDiscComplementOpens_sphereStandardDisc
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (sphereTwoDiscComplementOpens (sphereStandardDisc v) :
      Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) =
      (TauCeti.sphereBall (n := n) v '' closedBall 0 (1 / 4) ∪
        (fun w : EuclideanSpace ℝ (Fin n) ↦ -TauCeti.sphereBall (n := n) v (-w)) ''
          closedBall 0 (1 / 4))ᶜ := by
  simp only [sphereTwoDiscComplementOpens, Opens.coe_mk, Function.comp_def,
    sphereStandardDisc_zero, sphereStandardDisc_one, coe_sphereHalfDiscInclusion]
  rw [range_half_smul_closedBall (sphereBall (n := n) v),
    range_half_smul_closedBall (fun w : EuclideanSpace ℝ (Fin n) ↦ -sphereBall v (-w))]

private abbrev timeStrip (n : ℕ) : Opens ((sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) :=
  prodIooOpens _ (-Real.log 4) (Real.log 4)

private theorem mem_timeStrip (p : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) :
    p ∈ (timeStrip n) ↔ -Real.log 4 < p.2 ∧ p.2 < Real.log 4 := by
  simp [timeStrip]

private def cylinderMap (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (p : (sphere (0 :
  EuclideanSpace ℝ (Fin n)) 1) × ℝ) : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  TauCeti.sphereBall (n := n) v (Real.exp p.2 • (p.1 : (EuclideanSpace ℝ (Fin n))))

private theorem cylinderMap_apply (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (p : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) :
    cylinderMap v p = sphereBall v (Real.exp p.2 • (p.1 : EuclideanSpace ℝ (Fin n))) := rfl

private theorem cylinderMap_injective [NeZero n]
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Injective (cylinderMap v) := by
  intro p q h
  apply (TauCeti.sphereProdRealDiffeomorph (V := (EuclideanSpace ℝ (Fin n))) (n := n - 1)).injective
  apply Subtype.ext
  simp only [Diffeomorph.coe_toEquiv]
  rw [coe_sphereProdRealDiffeomorph_apply, coe_sphereProdRealDiffeomorph_apply]
  exact (TauCeti.isOpenEmbedding_sphereBall (n := n) v).injective h

private theorem cylinderMap_local [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
  IsLocalDiffeomorph ((𝓡 (n - 1)).prod 𝓘(ℝ)) (𝓡 n) ∞ (cylinderMap v) := by
  have he : cylinderMap v = sphereBall v ∘ Subtype.val ∘
      sphereProdRealDiffeomorph (V := EuclideanSpace ℝ (Fin n)) (n := n - 1) := by
    funext p
    simp [cylinderMap, Function.comp_def]
  rw [he]
  intro p
  exact (((TauCeti.sphereProdRealDiffeomorph (V := EuclideanSpace ℝ (Fin n))
    (n := n - 1)).isLocalDiffeomorph p).comp
    (hg := TauCeti.isLocalDiffeomorph_subtype_val
      (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (n := ∞) _)).comp
    (hg := TauCeti.isLocalDiffeomorph_sphereBall (n := n) v ∞ _)

private theorem mem_complement_sphereBall (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (w :
  (EuclideanSpace ℝ (Fin n))) :
    TauCeti.sphereBall (n := n) v w ∈ sphereTwoDiscComplementOpens (sphereStandardDisc v) ↔
      (1 / 4 : ℝ) < ‖w‖ ∧ ‖w‖ < 4 := by
  rw [← SetLike.mem_coe, coe_sphereTwoDiscComplementOpens_sphereStandardDisc]
  have hs := TauCeti.isComplementaryBall_sphereBall (n := n) v
  have hi := (TauCeti.isOpenEmbedding_sphereBall (n := n) v).injective
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
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
        (congrArg (TauCeti.sphereBall (n := n) v) (inversion_inversion _ one_ne_zero w))
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
      have hlarge := inv_radius_le_norm_of_complementary_eq v
        (mem_closedBall_zero_iff.1 hz) he
      norm_num at hlarge
      exact (not_le_of_gt hu) hlarge

private theorem cylinderMap_mem_complement
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (p :
  (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) :
    cylinderMap v p ∈ sphereTwoDiscComplementOpens (sphereStandardDisc v) ↔ p ∈ (timeStrip n) := by
  rw [cylinderMap, mem_complement_sphereBall]
  have hn : ‖Real.exp p.2 • (p.1 : (EuclideanSpace ℝ (Fin n)))‖ = Real.exp p.2 := by
    simp [norm_smul, norm_eq_of_mem_sphere p.1]
  rw [hn]
  rw [mem_timeStrip]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 4), Real.exp_lt_exp,
    ← Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
  simp [one_div, Real.log_inv]

private theorem image_cylinderMap_strip [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
  cylinderMap v '' (timeStrip n) = sphereTwoDiscComplementOpens (sphereStandardDisc v) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact (cylinderMap_mem_complement v p).2 hp
  · intro x hx
    have hxv : x ≠ v := by
      intro h
      have hx' : x ∈ (sphereTwoDiscComplementOpens (sphereStandardDisc v) : Set _) := hx
      rw [coe_sphereTwoDiscComplementOpens_sphereStandardDisc] at hx'
      apply hx'
      right
      refine ⟨0, by simp, ?_⟩
      simp [h]
    obtain ⟨w, rfl⟩ : x ∈ range (TauCeti.sphereBall (n := n) v) := by
      rwa [TauCeti.range_sphereBall]
    have hw : w ≠ 0 := by
      have hnorm := (mem_complement_sphereBall v w).1 hx
      exact norm_ne_zero_iff.1 (ne_of_gt (lt_trans (by norm_num) hnorm.1))
    let p := (TauCeti.sphereProdRealDiffeomorph (V := (EuclideanSpace ℝ (Fin n))) (n := n - 1)).symm
      ⟨w, mem_puncturedSpace.2 hw⟩
    have hp : cylinderMap v p = TauCeti.sphereBall (n := n) v w := by
      have h := congrArg Subtype.val
        ((TauCeti.sphereProdRealDiffeomorph (V := EuclideanSpace ℝ (Fin n))
          (n := n - 1)).apply_symm_apply
          ⟨w, mem_puncturedSpace.2 hw⟩)
      simpa only [cylinderMap, coe_sphereProdRealDiffeomorph_apply] using
        congrArg (TauCeti.sphereBall (n := n) v) h
    exact ⟨p, (cylinderMap_mem_complement v p).1 (hp ▸ hx), hp⟩

private theorem cylinderMap_subtype_local [NeZero n]
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    IsLocalDiffeomorph ((𝓡 (n - 1)).prod 𝓘(ℝ)) (𝓡 n) ∞
      (cylinderMap v ∘ (Subtype.val : timeStrip n → _)) := fun p ↦
  (TauCeti.isLocalDiffeomorph_subtype_val (I := ((𝓡 (n - 1)).prod 𝓘(ℝ))) (n := ∞) p).comp
    (hg := cylinderMap_local v p)

private theorem range_cylinderMap_subtype [NeZero n]
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    range (cylinderMap v ∘ (Subtype.val : timeStrip n → _)) =
      sphereTwoDiscComplementOpens (sphereStandardDisc v) := by
  rw [range_comp, Subtype.range_coe, image_cylinderMap_strip]

private def canonicalCylinder [NeZero n]
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (timeStrip n) ≃ₘ^∞⟮((𝓡 (n - 1)).prod 𝓘(ℝ)), 𝓡 n⟯
      sphereTwoDiscComplementOpens (sphereStandardDisc v) :=
  (cylinderMap_subtype_local v).diffeomorphOfInjectiveOfRangeEq
    ((cylinderMap_injective v).comp Subtype.val_injective) (range_cylinderMap_subtype v)

/-- The radial collar point in either standard stereographic disc chart. -/
def sphereStandardDiscCollar (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i : Fin 2)
    (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (s : ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  if i = 0 then TauCeti.sphereBall (n := n) v (((1 + s) / 4) • (z : (EuclideanSpace ℝ (Fin n))))
    else
    -TauCeti.sphereBall (n := n) v (-(((1 + s) / 4) • (z : (EuclideanSpace ℝ (Fin n)))))


/-- The first standard collar is expressed in the original stereographic chart. -/
@[simp]
theorem sphereStandardDiscCollar_zero (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (s : ℝ) :
    sphereStandardDiscCollar v 0 z s =
      sphereBall v (((1 + s) / 4) • (z : EuclideanSpace ℝ (Fin n))) := by
  exact ite_eq_left rfl

/-- The second standard collar is expressed in the antipodal stereographic chart. -/
@[simp]
theorem sphereStandardDiscCollar_one (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (s : ℝ) :
    sphereStandardDiscCollar v 1 z s =
      -sphereBall v (-(((1 + s) / 4) • (z : EuclideanSpace ℝ (Fin n)))) := by
  exact ite_eq_right (by decide : (1 : Fin 2) ≠ 0)

/-- The explicit standard collar equals the original supplied-disc collar. -/
theorem sphereStandardDisc_sphereDiscCollarPoint
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i : Fin 2)
  (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (s : Ioo (0 : ℝ) 1) :
    sphereStandardDisc v i (sphereDiscCollarPoint z s) = sphereStandardDiscCollar v i z s := by
  have he : (1 / 2 : ℝ) • (sphereDiscCollarPoint z s : (EuclideanSpace ℝ (Fin n))) = ((1 + (s :
    ℝ)) / 4) • (z : (EuclideanSpace ℝ (Fin n))) := by
    rw [coe_sphereDiscCollarPoint, smul_smul]
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


private def rescaleTime : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ :=
  Diffeomorph.smulAdd ∞ (2 * Real.log 4)⁻¹ (1 / 2 : ℝ)
    (inv_ne_zero (mul_pos (by norm_num) (Real.log_pos (by norm_num))).ne')

private theorem rescaleTime_strictMono : StrictMono rescaleTime := by
  intro x y hxy
  simp only [rescaleTime, Diffeomorph.smulAdd_apply, smul_eq_mul]
  have ha : 0 < (2 * Real.log 4)⁻¹ :=
    inv_pos.2 (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  linarith [mul_lt_mul_of_pos_left hxy ha]

private theorem rescaleTime_lower : rescaleTime (-Real.log 4) = 0 := by
  simp only [rescaleTime, Diffeomorph.smulAdd_apply, smul_eq_mul]
  field_simp
  ring

private theorem rescaleTime_upper : rescaleTime (Real.log 4) = 1 := by
  simp only [rescaleTime, Diffeomorph.smulAdd_apply, smul_eq_mul]
  field_simp
  ring

private def rescaleStrip [NeZero n] :
    (timeStrip n) ≃ₘ^∞⟮((𝓡 (n - 1)).prod 𝓘(ℝ)), ((𝓡 (n - 1)).prod 𝓘(ℝ))⟯
      prodIooOpens (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) 0 1 :=
  rescaleTime.prodIoo rescaleTime_strictMono rescaleTime_lower rescaleTime_upper

private theorem rescaleStrip_apply [NeZero n]
    (p : (timeStrip n)) :
    (rescaleStrip p : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) =
      (p.val.1, (2 * Real.log 4)⁻¹ * p.val.2 + 1 / 2) := by
  simp only [rescaleStrip, Diffeomorph.prodIoo_apply_coe, rescaleTime,
    Diffeomorph.smulAdd_apply, smul_eq_mul]

private theorem strictMono_of_zero_one
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) :
    StrictMono Ψ := by
  rcases Ψ.continuous.strictMono_of_inj Ψ.injective with h | h
  · exact h
  · have h' := h (by norm_num : (0 : ℝ) < 1)
    rw [h0, h1] at h'
    linarith

private def straightenStrip [NeZero n]
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) :
    prodIooOpens (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) 0 1
      ≃ₘ^∞⟮((𝓡 (n - 1)).prod 𝓘(ℝ)), ((𝓡 (n - 1)).prod 𝓘(ℝ))⟯
        prodIooOpens (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) 0 1 :=
  Ψ.prodIoo (strictMono_of_zero_one Ψ h0 h1) h0 h1

private theorem straightenStrip_apply [NeZero n]
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ)
    (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (p : prodIooOpens (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) 0 1) :
    (straightenStrip Ψ h0 h1 p : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) =
      (p.val.1, Ψ p.val.2) := by
  simp only [straightenStrip, Diffeomorph.prodIoo_apply_coe]

private theorem canonicalCylinder_apply [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (p :
  (timeStrip n)) :
    (canonicalCylinder v p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
      cylinderMap v p := by
  simp only [canonicalCylinder,
    IsLocalDiffeomorph.diffeomorphOfInjectiveOfRangeEq_apply_coe, Function.comp_apply]

private def alignedCanonical [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ),
  𝓘(ℝ)⟯ ℝ)
    (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) :
    sphereTwoDiscComplementOpens (sphereStandardDisc v) ≃ₘ^∞⟮𝓡 n, ((𝓡 (n - 1)).prod 𝓘(ℝ))⟯
      prodIooOpens (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) 0 1 :=
  (canonicalCylinder v).symm.trans (rescaleStrip.trans (straightenStrip Ψ h0 h1))

private theorem alignedCanonical_cylinderMap [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (p : (timeStrip n)) :
    ((alignedCanonical v Ψ h0 h1) (canonicalCylinder v p) : (sphere (0 : EuclideanSpace ℝ
      (Fin n)) 1) × ℝ) =
      (p.val.1, Ψ ((2 * Real.log 4)⁻¹ * p.val.2 + 1 / 2)) := by
  unfold alignedCanonical
  rw [Diffeomorph.coe_trans]
  simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
  rw [Diffeomorph.coe_trans]
  simp only [Function.comp_apply]
  rw [straightenStrip_apply, rescaleStrip_apply]


/-- Separate compactly supported corrections realize the exponential germs at `0` and `1`. -/
private theorem exists_diffeomorphs_eventuallyEq_exp_at_zero_one {c : ℝ} (hc : c ≠ 0) :
    ∃ Ψ₀ Ψ₁ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ,
      (Ψ₀ =ᶠ[𝓝 (0 : ℝ)] fun t ↦ (Real.exp (c * t) - 1) / c) ∧
      EqOn Ψ₀ id (Ioo (-1 / 4 : ℝ) (1 / 4))ᶜ ∧
      (Ψ₁ =ᶠ[𝓝 (1 : ℝ)] fun t ↦ 1 - (Real.exp (c * (1 - t)) - 1) / c) ∧
      EqOn Ψ₁ id (Ioo (3 / 4 : ℝ) (5 / 4))ᶜ := by
  let f₀ : ℝ → ℝ := fun t ↦ (Real.exp (c * t) - 1) / c
  let f₁ : ℝ → ℝ := fun t ↦ 1 - f₀ (1 - t)
  have hd₀ : HasDerivAt f₀ 1 0 := by
    convert (((Real.hasDerivAt_exp (c * 0)).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_mul c)).sub_const 1).div_const c using 1 <;>
      simp [f₀, hc]
  have hd₁ : HasDerivAt f₁ 1 1 := by
    have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) 1 :=
      (hasDerivAt_id 1).const_sub 1
    have hd₀' : HasDerivAt f₀ 1 ((fun t : ℝ ↦ 1 - t) 1) := by
      simpa only [sub_self] using hd₀
    have h := (hd₀'.comp 1 hsub).const_sub 1
    simpa only [f₁, Function.comp_def, one_mul, neg_neg] using h
  have hspan : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp
  have hdet {f : ℝ → ℝ} {x : ℝ} (hd : HasDerivAt f 1 x) :
      0 < (fderiv ℝ f x).det := by
    rw [hd.hasFDerivAt.fderiv, hspan]
    simp
  obtain ⟨Ψ₀, K₀, -, hK₀, hfix₀, hΨ₀⟩ :=
    exists_diffeomorph_eventuallyEq_of_det_fderiv_pos (n := ⊤) (by simp)
      (g := f₀) (by filter_upwards with x; fun_prop) (by norm_num [f₀]) (hdet hd₀)
      (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))
  obtain ⟨Ψ₁, K₁, -, hK₁, hfix₁, hΨ₁⟩ :=
    exists_diffeomorph_eventuallyEq_of_det_fderiv_pos (n := ⊤) (by simp)
      (g := f₁) (by filter_upwards with x; fun_prop) (by norm_num [f₁, f₀]) (hdet hd₁)
      (isOpen_Ioo.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioo (3 / 4) (5 / 4)))
  exact ⟨Ψ₀, Ψ₁, hΨ₀, fun x hx ↦ hfix₀ (fun hxK ↦ hx (hK₀ hxK)),
    hΨ₁, fun x hx ↦ hfix₁ (fun hxK ↦ hx (hK₁ hxK))⟩

/-- A real diffeomorphism fixing `0` and `1` realizes both endpoint exponential germs. -/
private theorem exists_diffeomorph_eventuallyEq_exp_at_zero_one {c : ℝ} (hc : c ≠ 0) :
    ∃ Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ,
      Ψ 0 = 0 ∧ Ψ 1 = 1 ∧
      (Ψ =ᶠ[𝓝 (0 : ℝ)] fun t ↦ (Real.exp (c * t) - 1) / c) ∧
      (Ψ =ᶠ[𝓝 (1 : ℝ)] fun t ↦ 1 - (Real.exp (c * (1 - t)) - 1) / c) := by
  obtain ⟨Ψ₀, Ψ₁, hΨ₀, hfix₀, hΨ₁, hfix₁⟩ := exists_diffeomorphs_eventuallyEq_exp_at_zero_one hc
  have h₀ : Ψ₀ 0 = 0 := by simpa  using hΨ₀.self_of_nhds
  have h₁ : Ψ₁ 1 = 1 := by simpa  using hΨ₁.self_of_nhds
  have hfix₀' : Ψ₀ =ᶠ[𝓝 (1 : ℝ)] id := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1)] with x hx
    exact hfix₀ (by rintro ⟨_, hx'⟩; exact lt_asymm hx hx')
  have hfix₁' : Ψ₁ =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 3 / 4)] with x hx
    exact hfix₁ (by rintro ⟨hx', _⟩; exact lt_asymm hx hx')
  let Ψ := Ψ₀.trans Ψ₁
  have hΨ0 : Ψ 0 = 0 := by
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    rw [h₀, hfix₁'.self_of_nhds]
    rfl
  have hΨ1 : Ψ 1 = 1 := by
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    rw [hfix₀'.self_of_nhds]
    exact h₁
  have ht : Tendsto Ψ₀ (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [h₀] using Ψ₀.continuous.tendsto (0 : ℝ)
  refine ⟨Ψ, hΨ0, hΨ1, ?_, ?_⟩
  · filter_upwards [hΨ₀, hfix₁'.comp_tendsto ht] with t ht ht'
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    exact ht'.trans ht
  · filter_upwards [hΨ₁, hfix₀'] with t ht ht'
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    rw [ht']
    exact ht


/-- One real diffeomorphism simultaneously linearizes both logarithmic endpoint coordinates. -/
private theorem exists_diffeomorph_log_collars (c : ℝ) (hc : c ≠ 0) :
    ∃ Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ, ∃ η : ℝ,
      Ψ 0 = 0 ∧ Ψ 1 = 1 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∀ s : ℝ, 0 < s → s < η →
        Ψ (Real.log (1 + s) / c) = s / c ∧
        Ψ (1 - Real.log (1 + s) / c) = 1 - s / c := by
  obtain ⟨Ψ, h0, h1, hlo, hup⟩ := exists_diffeomorph_eventuallyEq_exp_at_zero_one hc
  have hlog : Tendsto (fun s : ℝ ↦ Real.log (1 + s) / c) (𝓝 0) (𝓝 0) := by
    have hlin : ContinuousAt (fun s : ℝ ↦ 1 + s) 0 := continuousAt_const.add continuousAt_id
    have h : ContinuousAt (fun s : ℝ ↦ Real.log (1 + s) / c) 0 :=
      hlin.log (by norm_num) |>.div_const c
    simpa using h.tendsto
  have hlog' : Tendsto (fun s : ℝ ↦ 1 - Real.log (1 + s) / c) (𝓝 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hlog
  have hboth := (hlo.comp_tendsto hlog).and (hup.comp_tendsto hlog')
  obtain ⟨ε, hε, heq⟩ := Metric.eventually_nhds_iff.1 hboth
  refine ⟨Ψ, min ε (1 / 8), h0, h1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro s hs hsη
  have hsε : dist s 0 < ε := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
    exact hsη.trans_le (min_le_left _ _)
  obtain ⟨hlo', hup'⟩ := heq hsε
  simp only [Function.comp_apply] at hlo' hup'
  have hexp : Real.exp (c * (Real.log (1 + s) / c)) = 1 + s := by
    rw [mul_div_cancel₀ _ hc, Real.exp_log (by linarith)]
  constructor
  · rw [hlo', hexp]
    ring
  · rw [hup']
    have harg : c * (1 - (1 - Real.log (1 + s) / c)) =
        c * (Real.log (1 + s) / c) := by ring
    rw [harg, hexp]
    ring


private theorem log_collar_bounds (s : Ioo (0 : ℝ) (1 / 8)) :
    0 < Real.log (1 + (s : ℝ)) ∧ Real.log (1 + (s : ℝ)) < Real.log 4 := by
  constructor
  · exact Real.log_pos (by linarith [s.property.1])
  · exact Real.log_lt_log (by linarith [s.property.1]) (by linarith [s.property.2])

private def lowerStripPoint (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 : ℝ) (1 /
  8)) : (timeStrip n) :=
  ⟨(z, Real.log (1 + (s : ℝ)) - Real.log 4), by
    have hlog := log_collar_bounds s
    exact (mem_timeStrip _).2 ⟨by linarith, by linarith⟩⟩

private def upperStripPoint (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 : ℝ) (1 /
  8)) : (timeStrip n) :=
  ⟨(z, Real.log 4 - Real.log (1 + (s : ℝ))), by
    have hlog := log_collar_bounds s
    exact (mem_timeStrip _).2 ⟨by linarith, by linarith⟩⟩

private theorem canonicalCylinder_lower [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (z :
  (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 : ℝ) (1 / 8)) :
    (canonicalCylinder v (lowerStripPoint z s) : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) =
      sphereStandardDisc v 0 (sphereDiscCollarPoint z (smallCollarToUnit s)) := by
  rw [canonicalCylinder_apply, sphereStandardDisc_zero, coe_sphereDiscCollarPoint,
    cylinderMap_apply]
  simp only [lowerStripPoint]
  rw [Real.exp_sub, Real.exp_log (by linarith [s.property.1]),
    Real.exp_log (by norm_num : (0 : ℝ) < 4), smul_smul]
  simp only [smallCollarToUnit]
  congr 2
  ring

private theorem canonicalCylinder_upper [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (z :
  (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 : ℝ) (1 / 8)) :
    (canonicalCylinder v (upperStripPoint z s) : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) =
      sphereStandardDisc v 1 (sphereDiscCollarPoint z (smallCollarToUnit s)) := by
  rw [canonicalCylinder_apply, sphereStandardDisc_one]
  let a : ℝ := (1 + (s : ℝ)) / 4
  have ha : 0 < a := by dsimp [a]; linarith [s.property.1]
  have hne : a • (z : (EuclideanSpace ℝ (Fin n))) ≠ 0 := smul_ne_zero ha.ne'
    (ne_zero_of_mem_unit_sphere z)
  have he : (1 / 2 : ℝ) • (sphereDiscCollarPoint z (smallCollarToUnit s) :
      (EuclideanSpace ℝ (Fin n))) = a • (z :
    (EuclideanSpace ℝ (Fin n))) := by
    rw [coe_sphereDiscCollarPoint, smul_smul]
    congr 1
    dsimp [a, smallCollarToUnit]
    ring
  rw [he, (TauCeti.isComplementaryBall_sphereBall v).apply_eq_inversion _ hne]
  rw [cylinderMap_apply]
  simp only [upperStripPoint]
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4),
    Real.exp_log (by linarith [s.property.1])]
  have hinv : inversion 0 1 (a • (z : (EuclideanSpace ℝ (Fin n)))) = a⁻¹ • (z : (EuclideanSpace ℝ
    (Fin n))) := by
    simp only [inversion, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, norm_eq_of_mem_sphere z, mul_one, vsub_eq_sub, sub_zero, vadd_eq_add,
      add_zero, smul_smul]
    congr 1
    field_simp
  rw [hinv]
  congr 2
  dsimp [a]
  field_simp

private theorem alignedCanonical_time [NeZero n]
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (p : timeStrip n) :
    (alignedCanonical v Ψ h0 h1 (canonicalCylinder v p) :
      (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) =
      (p.val.1, Ψ ((p.val.2 + Real.log 4) / (2 * Real.log 4))) := by
  rw [alignedCanonical_cylinderMap]
  congr 2
  have hl : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne'
  field_simp

private theorem alignedCanonical_lower [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 : ℝ) (1 /
      8)) :
    (alignedCanonical v Ψ h0 h1 (canonicalCylinder v (lowerStripPoint z s)) : (sphere (0 :
      EuclideanSpace ℝ (Fin n)) 1) × ℝ) =
      (z, Ψ (Real.log (1 + (s : ℝ)) / (2 * Real.log 4))) := by
  simpa only [lowerStripPoint, sub_add_cancel] using
    alignedCanonical_time v Ψ h0 h1 (lowerStripPoint z s)

private theorem alignedCanonical_upper [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1)
    (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (s : Ioo (0 : ℝ) (1 /
      8)) :
    (alignedCanonical v Ψ h0 h1 (canonicalCylinder v (upperStripPoint z s)) : (sphere (0 :
      EuclideanSpace ℝ (Fin n)) 1) × ℝ) =
      (z, Ψ (1 - Real.log (1 + (s : ℝ)) / (2 * Real.log 4))) := by
  rw [alignedCanonical_time]
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
theorem sphereStandardDiscCollar_mem_sphereTwoDiscComplementOpens
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i : Fin 2)
    (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    sphereStandardDiscCollar v i z s ∈ sphereTwoDiscComplementOpens (sphereStandardDisc v) := by
  let t : Ioo (0 : ℝ) 1 := ⟨s, hs, hs1⟩
  rw [← sphereStandardDisc_sphereDiscCollarPoint v i z t]
  exact sphereDiscCollarPoint_mem_sphereTwoDiscComplementOpens
    (sphereStandardDisc v) (sphereStandardDisc_disjoint v) i z t

/-- The standard two-disc complement is a cylinder with linear coordinates on both collars near
the removed discs, for collar times below some `η ≤ 1/8`. -/
theorem exists_diffeomorph_sphereTwoDiscComplementOpens_sphereStandardDisc_prodIooOpens [NeZero n]
    (v : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ∃ k η : ℝ, 0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∃ C : sphereTwoDiscComplementOpens (sphereStandardDisc v) ≃ₘ^∞⟮𝓡 n, ((𝓡 (n - 1)).prod 𝓘(ℝ))⟯
        prodIooOpens (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) 0 1,
        (∀ i z s, 0 < s → s < 1 → sphereStandardDiscCollar v i z s ∈
          sphereTwoDiscComplementOpens (sphereStandardDisc v)) ∧
        (∀ z s, 0 < s → s < η → ∀ hx : sphereStandardDiscCollar v 0 z s ∈
          sphereTwoDiscComplementOpens (sphereStandardDisc v),
          (C ⟨sphereStandardDiscCollar v 0 z s, hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ×
            ℝ) = (z, k * s)) ∧
        (∀ z s, 0 < s → s < η → ∀ hx : sphereStandardDiscCollar v 1 z s ∈
          sphereTwoDiscComplementOpens (sphereStandardDisc v),
          (C ⟨sphereStandardDiscCollar v 1 z s, hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ×
            ℝ) = (z, 1 - k * s)) := by
  have hc : 0 < 2 * Real.log 4 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨Ψ, η, h0, h1, hη, hη8, hΨ⟩ :=
    exists_diffeomorph_log_collars (2 * Real.log 4) hc.ne'
  have he (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (s : Ioo (0 : ℝ) (1 / 8))
      (hx : sphereStandardDiscCollar v i z s ∈
        sphereTwoDiscComplementOpens (sphereStandardDisc v)) :
      (⟨sphereStandardDiscCollar v i z s, hx⟩ :
        sphereTwoDiscComplementOpens (sphereStandardDisc v)) =
        canonicalCylinder v (if i = 0 then lowerStripPoint z s else upperStripPoint z s) := by
    apply Subtype.ext
    dsimp only
    -- `smallCollarToUnit` widens only the time subtype; its underlying real value is `s`.
    -- This presents the same collar point in the domain of the original collar API.
    change sphereStandardDiscCollar v i z (smallCollarToUnit s) = _
    rw [← sphereStandardDisc_sphereDiscCollarPoint v i z (smallCollarToUnit s)]
    fin_cases i <;> simp [canonicalCylinder_lower, canonicalCylinder_upper]
  refine ⟨(2 * Real.log 4)⁻¹, η, inv_pos.2 hc, collarSpeed_le_half, hη, hη8,
    alignedCanonical v Ψ h0 h1,
    sphereStandardDiscCollar_mem_sphereTwoDiscComplementOpens v, ?_, ?_⟩
  · intro z s hs hsη hx
    let t : Ioo (0 : ℝ) (1 / 8) := ⟨s, hs, hsη.trans_le hη8⟩
    rw [he 0 z t hx, ite_eq_left rfl, alignedCanonical_lower, (hΨ s hs hsη).1]
    exact Prod.ext rfl (by ring)
  · intro z s hs hsη hx
    let t : Ioo (0 : ℝ) (1 / 8) := ⟨s, hs, hsη.trans_le hη8⟩
    rw [he 1 z t hx, ite_eq_right (by decide), alignedCanonical_upper, (hΨ s hs hsη).2]
    exact Prod.ext rfl (by ring)

end TauCeti
