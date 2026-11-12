/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Homotopy.Extension.Ball
public import TauCeti.Topology.Category.TopCat.Pushout

/-!
# Attaching a handle is attaching its core, up to deformation

A handle of index `k` and coindex `m` is the product `D^k × D^m` of two closed unit discs,
attached to a space `X` along its attaching region `∂D^k × D^m` by a map
`α : ∂D^k × D^m → X`. Its core is the disc `D^k × {0}`, attached along `∂D^k × {0}`. This file
shows that attaching handles and attaching their cores give the same space up to a deformation
fixing `X`: the space `P = X ∪_α ⨆ᵢ (D^{k i} × D^{m i})` strong deformation retracts onto the image
of `X` and of the cores, which is the space `Q = X ∪_{α₀} ⨆ᵢ D^{k i}` obtained by attaching one
`k i`-cell along each restriction `α₀ i = α i (·, 0)`
(`TauCeti.TopCat.exists_leftInverse_homotopicRel_of_isPushout_handles`). Applied to the pushout
square of Milnor's handle attachment across a critical level of a Morse function
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`), it replaces the handle attached at each
critical point by a cell of dimension its index, up to a deformation fixing the image of the lower
sublevel.

The geometric input is a retraction of the product of two closed unit balls onto the union
`B × {0} ∪ S × B'` of the core and the attaching region (`TauCeti.ballProdRetraction`), where `S`
is the unit sphere of the first factor. It is the radial projection of the cylinder `I × B` onto
its bottom and sides (`TauCeti.ballRadialProjection`), applied with the height `‖y‖` of a point
`(x, y)`, the second coordinate being rescaled along its own direction to the new height. The
straight-line homotopy from the identity to this retraction fixes the core and the attaching
region, so it descends to the handle attachment `P` together with the constant homotopy on `X`.
The retraction itself descends to a map `P → Q`: it sends the part of the handle where it lands in
the core to the cell, and the part where it lands in the attaching region to `X` through `α`.

## Main declarations

* `TauCeti.ballProdRetraction`: the retraction of the product of two closed unit balls onto the
  union of the core and the attaching region, with `TauCeti.ballProdRetraction_mem` and
  `TauCeti.ballProdRetraction_eq_self`.
* `TauCeti.TopCat.handleCoreInclusion` and `TauCeti.TopCat.handleCoreBoundaryInclusion`: the core
  `D^k × {0}` of a handle and its boundary `∂D^k × {0}`.
* `TauCeti.TopCat.exists_leftInverse_homotopicRel_of_isPushout_handles`: **a handle attachment
  strong deformation retracts onto the attachment of the cores**, relative to the space they are
  attached to.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2, where the lower sublevel with a handle attached is deformed onto the lower
  sublevel with the core of the handle attached.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, proof of Proposition 0.16, the radial projection of `Dⁿ × I` onto
  `Dⁿ × {0} ∪ ∂Dⁿ × I`.
-/

public section

noncomputable section

open Metric Set unitInterval

namespace TauCeti

section BallProd

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The point `(‖y‖, x)` of the cylinder `I × B` over the closed unit ball of `E`, for a point
`(x, y)` of the product of the closed unit balls of `E` and `F`. -/
def ballProdHeight (p : closedBall (0 : E) 1 × closedBall (0 : F) 1) :
    I × closedBall (0 : E) 1 :=
  (⟨‖(p.2 : F)‖, Set.mem_Icc.2 ⟨norm_nonneg _, mem_closedBall_zero_iff.1 p.2.2⟩⟩, p.1)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem ballProdHeight_def (p : closedBall (0 : E) 1 × closedBall (0 : F) 1) :
    ballProdHeight p =
      (⟨‖(p.2 : F)‖, Set.mem_Icc.2 ⟨norm_nonneg _, mem_closedBall_zero_iff.1 p.2.2⟩⟩, p.1) :=
  (rfl)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_ballProdHeight :
    Continuous (ballProdHeight (E := E) (F := F)) :=
  ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _).prodMk
    continuous_fst

omit [NormedSpace ℝ F] in
/-- The height reached by the radial projection of `(‖y‖, x)` is at most `‖y‖`. -/
private theorem ballRadialProjection_ballProdHeight_fst_le
    (p : closedBall (0 : E) 1 × closedBall (0 : F) 1) :
    (ballRadialProjection (ballProdHeight p)).1 ≤ ‖(p.2 : F)‖ := by
  have hs := mem_closedBall_zero_iff.1 p.2.2
  have hx := mem_closedBall_zero_iff.1 p.1.2
  have hd : 0 < 2 - ‖(p.2 : F)‖ := by linarith
  have hd₁ : 2 - ‖(p.2 : F)‖ ≤ max (2 - ‖(p.2 : F)‖) (2 * ‖(p.1 : E)‖) := le_max_left _ _
  have hd₂ : max (2 - ‖(p.2 : F)‖) (2 * ‖(p.1 : E)‖) ≤ 2 :=
    max_le (by linarith [norm_nonneg (p.2 : F)]) (by linarith)
  rw [ballRadialProjection_def, ballRadialDen_def]
  simp only [ballProdHeight]
  rw [sub_le_comm, le_div_iff₀ (hd.trans_le hd₁)]
  nlinarith

/-- **The retraction of a handle onto its core and its attaching region.** For a point `(x, y)`
of the product of the closed unit balls of `E` and `F`, project `(‖y‖, x)` radially from the point
`(2, 0)` onto the bottom and sides of the cylinder `I × B` over the ball `B` of `E`
(`TauCeti.ballRadialProjection`), and rescale `y` to the height so reached. The result lies in the
union `B × {0} ∪ S × B'` of the core and the attaching region, `S` the unit sphere of `E`
(`TauCeti.ballProdRetraction_mem`), and it fixes that union (`TauCeti.ballProdRetraction_eq_self`).
-/
def ballProdRetraction (p : closedBall (0 : E) 1 × closedBall (0 : F) 1) : E × F :=
  ((ballRadialProjection (ballProdHeight p)).2,
    ((ballRadialProjection (ballProdHeight p)).1 / ‖(p.2 : F)‖) • (p.2 : F))

theorem ballProdRetraction_def (p : closedBall (0 : E) 1 × closedBall (0 : F) 1) :
    ballProdRetraction p =
      ((ballRadialProjection (ballProdHeight p)).2,
        ((ballRadialProjection (ballProdHeight p)).1 / ‖(p.2 : F)‖) • (p.2 : F)) := (rfl)

omit [NormedSpace ℝ F] in
/-- The rescaling factor of the second coordinate lies in `[0, 1]`. -/
private theorem ballProdRetraction_coeff_mem (p : closedBall (0 : E) 1 × closedBall (0 : F) 1) :
    0 ≤ (ballRadialProjection (ballProdHeight p)).1 / ‖(p.2 : F)‖ ∧
      (ballRadialProjection (ballProdHeight p)).1 / ‖(p.2 : F)‖ ≤ 1 := by
  have h0 := (ballRadialProjection_spec (ballProdHeight p)).1.1
  have h1 := ballRadialProjection_ballProdHeight_fst_le p
  refine ⟨div_nonneg h0 (norm_nonneg _), ?_⟩
  rcases (norm_nonneg (p.2 : F)).eq_or_lt with h | h
  · simp [← h]
  · exact (div_le_one h).2 h1

theorem continuous_ballProdRetraction : Continuous (ballProdRetraction (E := E) (F := F)) := by
  have hR := continuous_ballRadialProjection.comp (continuous_ballProdHeight (E := E) (F := F))
  refine hR.snd.prodMk (continuous_iff_continuousAt.2 fun p ↦ ?_)
  by_cases hp : (p.2 : F) = 0
  · -- Near a point of the core the second coordinate is rescaled by a factor in `[0, 1]`, so it
    -- tends to `0` with `y`.
    have hy : Filter.Tendsto (fun q : closedBall (0 : E) 1 × closedBall (0 : F) 1 ↦
        ‖(q.2 : F)‖) (nhds p) (nhds 0) := by
      simpa [hp] using ((by fun_prop : Continuous fun q : closedBall (0 : E) 1 ×
        closedBall (0 : F) 1 ↦ ‖(q.2 : F)‖).tendsto p)
    rw [ContinuousAt, hp, smul_zero]
    refine squeeze_zero_norm (fun q ↦ ?_) hy
    have h := ballProdRetraction_coeff_mem q
    rw [norm_smul, Real.norm_of_nonneg h.1]
    exact mul_le_of_le_one_left (norm_nonneg _) h.2
  · exact (hR.fst.continuousAt.div
      (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).continuousAt
      (norm_ne_zero_iff.2 hp)).smul (continuous_subtype_val.comp continuous_snd).continuousAt

/-- The retraction lands in the product of the closed unit balls, in the union of the core
`B × {0}` and of the attaching region `S × B'`. -/
theorem ballProdRetraction_mem (p : closedBall (0 : E) 1 × closedBall (0 : F) 1) :
    (ballProdRetraction p).1 ∈ closedBall (0 : E) 1 ∧
      (ballProdRetraction p).2 ∈ closedBall (0 : F) 1 ∧
      ((ballProdRetraction p).2 = 0 ∨ (ballProdRetraction p).1 ∈ sphere (0 : E) 1) := by
  have hspec := ballRadialProjection_spec (ballProdHeight p)
  have h := ballProdRetraction_coeff_mem p
  refine ⟨hspec.2.1, ?_, hspec.2.2.imp (fun h0 ↦ ?_) id⟩
  · rw [mem_closedBall_zero_iff, ballProdRetraction_def, norm_smul, Real.norm_of_nonneg h.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) h.2).trans (mem_closedBall_zero_iff.1 p.2.2)
  · simp [ballProdRetraction_def, h0]

/-- The retraction fixes the core `B × {0}` and the attaching region `S × B'`. -/
theorem ballProdRetraction_eq_self (p : closedBall (0 : E) 1 × closedBall (0 : F) 1)
    (hp : (p.2 : F) = 0 ∨ (p.1 : E) ∈ sphere (0 : E) 1) :
    ballProdRetraction p = ((p.1 : E), (p.2 : F)) := by
  have hR := ballRadialProjection_eq_self (ballProdHeight p) <| by
    rw [mem_cylinderExtensionDomain_iff]
    refine hp.imp (fun h ↦ Subtype.ext ?_) id
    simp [ballProdHeight, h]
  simp only [ballProdRetraction_def, hR]
  refine Prod.ext rfl ?_
  rcases eq_or_ne (p.2 : F) 0 with h | h
  · simp [h]
  · simp [ballProdHeight, div_self (norm_ne_zero_iff.2 h)]

end BallProd

end TauCeti

namespace TauCeti.TopCat

open CategoryTheory Limits Topology

universe u

section Handle

/-- The core `D^k × {0}` of the handle `D^k × D^m`, as an inclusion of the disc `D^k`. -/
def handleCoreInclusion (k m : ℕ) :
    TopCat.disk.{u} k ⟶ TopCat.of (TopCat.disk.{u} k × TopCat.disk.{u} m) :=
  TopCat.ofHom ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (diskCenter.{u} m)))

@[simp]
theorem handleCoreInclusion_apply (k m : ℕ) (w : TopCat.disk.{u} k) :
    handleCoreInclusion k m w = (w, diskCenter.{u} m) := (rfl)

/-- The boundary `∂D^k × {0}` of the core of the handle `D^k × D^m`, as an inclusion of the
sphere `∂D^k` into the attaching region `∂D^k × D^m`. -/
def handleCoreBoundaryInclusion (k m : ℕ) :
    TopCat.diskBoundary.{u} k ⟶ TopCat.of (TopCat.diskBoundary.{u} k × TopCat.disk.{u} m) :=
  TopCat.ofHom ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (diskCenter.{u} m)))

@[simp]
theorem handleCoreBoundaryInclusion_apply (k m : ℕ) (s : TopCat.diskBoundary.{u} k) :
    handleCoreBoundaryInclusion k m s = (s, diskCenter.{u} m) := (rfl)

/-- The boundary of the core is the part of the attaching region lying on the core. -/
@[reassoc]
theorem diskBoundaryInclusion_comp_handleCoreInclusion (k m : ℕ) :
    TopCat.diskBoundaryInclusion.{u} k ≫ handleCoreInclusion k m =
      handleCoreBoundaryInclusion k m ≫
        TopCat.ofHom ((TopCat.diskBoundaryInclusion.{u} k).hom.prodMap (ContinuousMap.id _)) :=
  (rfl)

variable {k m : ℕ}

/-- The disc `TopCat.disk n` is the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/
private abbrev diskHomeomorph (n : ℕ) :
    TopCat.disk.{u} n ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  Homeomorph.ulift

/-- The boundary `TopCat.diskBoundary n` is the unit sphere of `EuclideanSpace ℝ (Fin n)`. -/
private abbrev diskBoundaryHomeomorph' (n : ℕ) :
    TopCat.diskBoundary.{u} n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  Homeomorph.ulift

/-- A point of the boundary of the disc `TopCat.disk n` is the same point of the closed unit ball
as of the unit sphere. -/
private theorem coe_diskHomeomorph_diskBoundaryInclusion (n : ℕ)
    (s : TopCat.diskBoundary.{u} n) :
    (diskHomeomorph n (TopCat.diskBoundaryInclusion n s) : EuclideanSpace ℝ (Fin n)) =
      diskBoundaryHomeomorph' n s :=
  coe_diskBoundaryInclusion_apply_down n s

/-- The centre of the disc `TopCat.disk n` is the centre `0` of the closed unit ball. -/
private theorem coe_diskHomeomorph_diskCenter (n : ℕ) :
    (diskHomeomorph n (diskCenter.{u} n) : EuclideanSpace ℝ (Fin n)) = 0 :=
  coe_diskCenter_down n

/-- The handle `D^k × D^m` is the product of two closed unit balls. -/
private abbrev handleHomeomorph (k m : ℕ) :
    TopCat.disk.{u} k × TopCat.disk.{u} m ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 × closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 :=
  (diskHomeomorph k).prodCongr (diskHomeomorph m)

/-- A point `(s, y)` of the attaching region `∂D^k × D^m` lies over the unit sphere. -/
private theorem handleHomeomorph_diskBoundaryInclusion_mem
    (s : TopCat.diskBoundary.{u} k × TopCat.disk.{u} m) :
    ((handleHomeomorph k m (TopCat.diskBoundaryInclusion k s.1, s.2)).1 :
      EuclideanSpace ℝ (Fin k)) ∈ sphere 0 1 := by
  rw [Homeomorph.coe_prodCongr, Prod.map_fst, coe_diskHomeomorph_diskBoundaryInclusion]
  exact (diskBoundaryHomeomorph' k s.1).2

/-- A point `(w, 0)` of the core `D^k × {0}` has second coordinate `0`. -/
private theorem handleHomeomorph_diskCenter (w : TopCat.disk.{u} k) :
    ((handleHomeomorph k m (w, diskCenter.{u} m)).2 : EuclideanSpace ℝ (Fin m)) = 0 := by
  rw [Homeomorph.coe_prodCongr, Prod.map_snd, coe_diskHomeomorph_diskCenter]

/-- The retraction `TauCeti.ballProdRetraction` of a handle, read on a point of the handle. -/
private abbrev handleRetraction (p : TopCat.disk.{u} k × TopCat.disk.{u} m) :
    EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) :=
  ballProdRetraction (handleHomeomorph k m p)

private theorem continuous_handleRetraction :
    Continuous fun p : TopCat.disk.{u} k × TopCat.disk.{u} m ↦ handleRetraction p :=
  continuous_ballProdRetraction.comp (handleHomeomorph k m).continuous

/-- The straight-line homotopy from the identity of the handle to its retraction onto the core
and the attaching region. -/
private def handleHomotopy (k m : ℕ) :
    C(unitInterval × (TopCat.disk.{u} k × TopCat.disk.{u} m),
      TopCat.disk.{u} k × TopCat.disk.{u} m) where
  toFun q := (handleHomeomorph k m).symm
    (⟨(1 - (q.1 : ℝ)) • ((handleHomeomorph k m q.2).1 : EuclideanSpace ℝ (Fin k)) +
        (q.1 : ℝ) • (handleRetraction q.2).1,
      convex_closedBall _ _ (handleHomeomorph k m q.2).1.2 (ballProdRetraction_mem _).1
        (sub_nonneg.2 q.1.2.2) q.1.2.1 (sub_add_cancel 1 _)⟩,
    ⟨(1 - (q.1 : ℝ)) • ((handleHomeomorph k m q.2).2 : EuclideanSpace ℝ (Fin m)) +
        (q.1 : ℝ) • (handleRetraction q.2).2,
      convex_closedBall _ _ (handleHomeomorph k m q.2).2.2 (ballProdRetraction_mem _).2.1
        (sub_nonneg.2 q.1.2.2) q.1.2.1 (sub_add_cancel 1 _)⟩)
  continuous_toFun := by
    have hr := continuous_handleRetraction.{u} (k := k) (m := m)
    have he := (handleHomeomorph.{u} k m).continuous
    refine (handleHomeomorph k m).symm.continuous.comp ?_
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp ((continuous_fst.comp he).comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).smul ((hr.comp continuous_snd).fst))
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp ((continuous_snd.comp he).comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).smul ((hr.comp continuous_snd).snd))

/-- The homotopy of the handle starts at the identity. -/
private theorem handleHomotopy_zero (p : TopCat.disk.{u} k × TopCat.disk.{u} m) :
    handleHomotopy k m (0, p) = p := by
  simp [handleHomotopy]

/-- The homotopy of the handle ends at its retraction onto the core and the attaching region. -/
private theorem handleHomotopy_one (p : TopCat.disk.{u} k × TopCat.disk.{u} m) :
    handleHomotopy k m (1, p) = (handleHomeomorph k m).symm
      (⟨(handleRetraction p).1, (ballProdRetraction_mem _).1⟩,
        ⟨(handleRetraction p).2, (ballProdRetraction_mem _).2.1⟩) := by
  simp [handleHomotopy]

/-- The homotopy of the handle fixes the core and the attaching region. -/
private theorem handleHomotopy_eq_self (t : unitInterval)
    (p : TopCat.disk.{u} k × TopCat.disk.{u} m)
    (hp : ((handleHomeomorph k m p).2 : EuclideanSpace ℝ (Fin m)) = 0 ∨
      ((handleHomeomorph k m p).1 : EuclideanSpace ℝ (Fin k)) ∈ sphere 0 1) :
    handleHomotopy k m (t, p) = p := by
  have h := ballProdRetraction_eq_self _ hp
  apply (handleHomeomorph k m).injective
  simp only [handleHomotopy, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply, handleRetraction,
    h]
  ext <;> simp [← add_smul]

/-- The homotopy of the handle fixes the attaching region `∂D^k × D^m`. -/
private theorem handleHomotopy_diskBoundaryInclusion (t : unitInterval)
    (s : TopCat.diskBoundary.{u} k × TopCat.disk.{u} m) :
    handleHomotopy k m (t, (TopCat.diskBoundaryInclusion k s.1, s.2)) =
      (TopCat.diskBoundaryInclusion k s.1, s.2) :=
  handleHomotopy_eq_self t _ (Or.inr (handleHomeomorph_diskBoundaryInclusion_mem s))

/-- The homotopy of the handle fixes the core `D^k × {0}`. -/
private theorem handleHomotopy_diskCenter (t : unitInterval) (w : TopCat.disk.{u} k) :
    handleHomotopy k m (t, (w, diskCenter.{u} m)) = (w, diskCenter.{u} m) :=
  handleHomotopy_eq_self t _ (Or.inl (handleHomeomorph_diskCenter w))

end Handle

section Attachment

variable {ι : Type u} {k m : ι → ℕ} {X P Q : TopCat.{u}}
  {α : ∀ i, TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (m i)) ⟶ X}
  {inlP : X ⟶ P}
  {inrP : (∐ fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) ⟶ P}
  {inlQ : X ⟶ Q} {inrQ : (∐ fun i ↦ TopCat.disk.{u} (k i)) ⟶ Q}

/-- The retraction of the `i`-th handle onto its core and its attaching region, followed by the
attachment of the cores: a map from the handle to `Q` which is the `i`-th cell where the retraction
lands in the core and `α i` where it lands in the attaching region. -/
private theorem exists_handle_desc
    (hQ : IsPushout (Sigma.desc fun i ↦ handleCoreBoundaryInclusion (k i) (m i) ≫ α i)
      (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (k i)) inlQ inrQ) (i : ι) :
    ∃ h : TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i)) ⟶ Q,
      (∀ p, (handleRetraction p).2 = 0 →
        h p = inrQ (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i
          ((diskHomeomorph (k i)).symm ⟨(handleRetraction p).1, (ballProdRetraction_mem _).1⟩))) ∧
      ∀ p (hp : (handleRetraction p).1 ∈ sphere 0 1),
        h p = inlQ (α i ((diskBoundaryHomeomorph' (k i)).symm ⟨_, hp⟩,
          (diskHomeomorph (m i)).symm
            ⟨(handleRetraction p).2, (ballProdRetraction_mem _).2.1⟩)) := by
  have hρ := continuous_handleRetraction.{u} (k := k i) (m := m i)
  set R₁ := {p : TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i) | (handleRetraction p).2 = 0}
  set R₂ :=
    {p : TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i) | (handleRetraction p).1 ∈ sphere 0 1}
  have hR₁ : IsClosed R₁ := isClosed_eq hρ.snd continuous_const
  have hR₂ : IsClosed R₂ := isClosed_sphere.preimage hρ.fst
  let a : TopCat.of R₁ ⟶ Q := TopCat.ofHom
    ⟨fun x ↦ inrQ (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i ((diskHomeomorph (k i)).symm
      ⟨(handleRetraction x.1).1, (ballProdRetraction_mem _).1⟩)),
      inrQ.hom.continuous.comp ((Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i).hom.continuous.comp
        ((diskHomeomorph (k i)).symm.continuous.comp
          ((hρ.fst.comp continuous_subtype_val).subtype_mk _)))⟩
  let b : TopCat.of R₂ ⟶ Q := TopCat.ofHom
    ⟨fun x ↦ inlQ (α i ((diskBoundaryHomeomorph' (k i)).symm ⟨_, x.2⟩,
      (diskHomeomorph (m i)).symm ⟨(handleRetraction x.1).2, (ballProdRetraction_mem _).2.1⟩)),
      inlQ.hom.continuous.comp ((α i).hom.continuous.comp
        (((diskBoundaryHomeomorph' (k i)).symm.continuous.comp
          ((hρ.fst.comp continuous_subtype_val).subtype_mk _)).prodMk
        ((diskHomeomorph (m i)).symm.continuous.comp
          ((hρ.snd.comp continuous_subtype_val).subtype_mk _))))⟩
  obtain ⟨h, ha, hb⟩ := _root_.TopCat.exists_glue_of_isClosedEmbedding
    (i := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (j := fun _ : Unit ↦ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    hR₁.isClosedEmbedding_subtypeVal (fun _ ↦ hR₂.isClosedEmbedding_subtypeVal)
    (by
      refine eq_univ_of_forall fun p ↦ ?_
      rcases (ballProdRetraction_mem (handleHomeomorph (k i) (m i) p)).2.2 with h | h
      · exact Or.inl ⟨⟨p, h⟩, rfl⟩
      · exact Or.inr (mem_iUnion.2 ⟨(), ⟨p, h⟩, rfl⟩))
    (fun x y hxy ↦ (hxy (Subsingleton.elim x y)).elim) a (fun _ ↦ b)
    (fun _ x y hxy ↦ by
      -- On the overlap the retraction lands on the boundary of the core, where the two pieces
      -- agree by the pushout square of `Q`.
      obtain ⟨p, hp₁⟩ := x
      obtain ⟨q, hp₂⟩ := y
      obtain rfl : p = q := hxy
      have hc : (diskHomeomorph (k i)).symm ⟨(handleRetraction p).1, (ballProdRetraction_mem _).1⟩ =
          TopCat.diskBoundaryInclusion (k i) ((diskBoundaryHomeomorph' (k i)).symm ⟨_, hp₂⟩) := by
        apply (diskHomeomorph (k i)).injective
        ext1
        rw [Homeomorph.apply_symm_apply, coe_diskHomeomorph_diskBoundaryInclusion,
          Homeomorph.apply_symm_apply]
      have hm : (diskHomeomorph (m i)).symm
          ⟨(handleRetraction p).2, (ballProdRetraction_mem _).2.1⟩ = diskCenter.{u} (m i) := by
        apply (diskHomeomorph (m i)).injective
        ext1
        rw [Homeomorph.apply_symm_apply, coe_diskHomeomorph_diskCenter]
        exact hp₁
      have hw := hQ.w_apply (Sigma.ι (fun i ↦ TopCat.diskBoundary.{u} (k i)) i
        ((diskBoundaryHomeomorph' (k i)).symm ⟨_, hp₂⟩))
      simp only [ConcreteCategory.comp_apply, Sigma.ι_comp_desc_apply, Sigma.ι_map_apply] at hw
      simp only [a, b, TopCat.hom_ofHom, ContinuousMap.coe_mk]
      rw [hc, hm, ← hw, handleCoreBoundaryInclusion_apply])
  refine ⟨h, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · exact ConcreteCategory.congr_hom ha ⟨p, hp⟩
  · exact ConcreteCategory.congr_hom (hb ()) ⟨p, hp⟩

/-- The pushout square of the handle attachment `P`, read on points of the attaching regions. -/
private theorem inlP_apply_eq_inrP_of_isPushout_handles
    (hP : IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) inlP inrP)
    (i : ι) (s : TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (m i)) :
    inlP (α i s) = inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) ×
      TopCat.disk.{u} (m i))) i (TopCat.diskBoundaryInclusion (k i) s.1, s.2)) := by
  have := hP.w_apply
    (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (m i))) i s)
  simp only [Sigma.ι_comp_desc_apply, Sigma.ι_map_apply] at this
  exact this

/-- The retraction of the handle attachment `P` onto the attachment `Q` of the cores: a map
`g : P → Q` which is the identity on `X` and on the cores, and which, followed by `φ`, is the end of
the straight-line homotopy of each handle. -/
private theorem exists_handleCoreRetraction
    (hP : IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) inlP inrP)
    (hQ : IsPushout (Sigma.desc fun i ↦ handleCoreBoundaryInclusion (k i) (m i) ≫ α i)
      (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (k i)) inlQ inrQ)
    (φ : Q ⟶ P) (hφl : ∀ x, φ (inlQ x) = inlP x)
    (hφr : ∀ i w, φ (inrQ (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i w)) =
      inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i
        (w, diskCenter.{u} (m i)))) :
    ∃ g : P ⟶ Q, (∀ x, g (inlP x) = inlQ x) ∧
      (∀ i w, g (inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i
          (w, diskCenter.{u} (m i)))) = inrQ (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i w)) ∧
      ∀ i p, inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i
          (handleHomotopy (k i) (m i) (1, p))) =
        φ (g (inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) ×
          TopCat.disk.{u} (m i))) i p))) := by
  choose h hcore hside using fun i ↦ exists_handle_desc (α := α) hQ i
  -- On the attaching region the retraction is the identity, so `h i` is `α i` there.
  have hhα (i : ι) (s : TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (m i)) :
      h i (TopCat.diskBoundaryInclusion (k i) s.1, s.2) = inlQ (α i s) := by
    have hs := handleHomeomorph_diskBoundaryInclusion_mem s
    have hρ := ballProdRetraction_eq_self _ (Or.inr hs)
    rw [hside i _ (by rw [handleRetraction, hρ]; exact hs)]
    congr 2
    obtain ⟨s₁, s₂⟩ := s
    refine Prod.ext ?_ ?_
    · apply (diskBoundaryHomeomorph' (k i)).injective
      simp only [Homeomorph.apply_symm_apply]
      exact Subtype.ext (congrArg Prod.fst hρ)
    · apply (diskHomeomorph (m i)).injective
      simp only [Homeomorph.apply_symm_apply]
      exact Subtype.ext (congrArg Prod.snd hρ)
  -- The map `g : P → Q` induced by the inclusion of `X` and the maps `h i`.
  have hw : Sigma.desc α ≫ inlQ = Limits.Sigma.map (fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) ≫ Sigma.desc h :=
    Sigma.hom_ext _ _ fun i ↦ by
      ext s
      simp only [ConcreteCategory.comp_apply, Sigma.ι_comp_desc_apply, Sigma.ι_map_apply]
      exact (hhα i s).symm
  let g : P ⟶ Q := hP.desc inlQ (Sigma.desc h) hw
  have hgl (x : X) : g (inlP x) = inlQ x := ConcreteCategory.congr_hom (hP.inl_desc _ _ hw) x
  have hgr (i : ι) (p : TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i)) :
      g (inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i p)) =
        h i p := by
    have := ConcreteCategory.congr_hom (hP.inr_desc inlQ (Sigma.desc h) hw)
      (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i p)
    rw [ConcreteCategory.comp_apply, Sigma.ι_comp_desc_apply] at this
    exact this
  -- On the core the retraction is the identity, so `h i` is the `i`-th cell there.
  have hhcore (i : ι) (w : TopCat.disk.{u} (k i)) :
      h i (w, diskCenter.{u} (m i)) = inrQ (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i w) := by
    have h0 := handleHomeomorph_diskCenter (m := m i) w
    have hρ := ballProdRetraction_eq_self _ (Or.inl h0)
    rw [hcore i _ (by rw [handleRetraction, hρ]; exact h0)]
    congr 2
    apply (diskHomeomorph (k i)).injective
    simp only [Homeomorph.apply_symm_apply]
    exact Subtype.ext (congrArg Prod.fst hρ)
  -- At the end of the homotopy of the `i`-th handle, `inrP` agrees with `φ ∘ h i`.
  have hend (i : ι) (p : TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i)) :
      inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i
        (handleHomotopy (k i) (m i) (1, p))) = φ (h i p) := by
    rw [handleHomotopy_one]
    rcases (ballProdRetraction_mem (handleHomeomorph (k i) (m i) p)).2.2 with h0 | hs
    · rw [hcore i p h0, hφr]
      congr 2
      apply (handleHomeomorph (k i) (m i)).injective
      rw [Homeomorph.apply_symm_apply]
      refine Prod.ext (by simp) (Subtype.ext ?_)
      exact h0.trans (handleHomeomorph_diskCenter _).symm
    · rw [hside i p hs, hφl, inlP_apply_eq_inrP_of_isPushout_handles hP]
      congr 2
  exact ⟨g, hgl, fun i w ↦ (hgr i _).trans (hhcore i w), fun i p ↦ (hend i p).trans
    (congrArg φ (hgr i p).symm)⟩

/-- **A handle attachment deformation retracts onto the attachment of the cores.** Let `P` be
obtained from `X` by attaching handles `D^{k i} × D^{m i}` along maps
`α i : ∂D^{k i} × D^{m i} → X` of their attaching regions, and let `Q` be obtained from `X` by
attaching cells `D^{k i}` along the restrictions `α i (·, 0)` to the boundaries of the cores, both
given as pushout squares in `TopCat`. Let `φ : Q → P` be the map which is the identity on `X` and
the inclusion of the core `D^{k i} × {0}` on the `i`-th cell. Then `φ` is the inclusion of a strong
deformation retract: it has a left inverse `g`, and `φ ∘ g` is homotopic to the identity of `P`
relative to the image of `φ`, which contains `X`. In particular `φ` is a homotopy equivalence
relative to `X`. -/
theorem exists_leftInverse_homotopicRel_of_isPushout_handles
    (hP : IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) inlP inrP)
    (hQ : IsPushout (Sigma.desc fun i ↦ handleCoreBoundaryInclusion (k i) (m i) ≫ α i)
      (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (k i)) inlQ inrQ)
    (φ : Q ⟶ P) (hφl : inlQ ≫ φ = inlP)
    (hφr : ∀ i, Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i ≫ inrQ ≫ φ =
      handleCoreInclusion (k i) (m i) ≫
        Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i ≫ inrP) :
    ∃ g : C(P, Q), Function.LeftInverse g φ ∧
      (ContinuousMap.id P).HomotopicRel (φ.hom.comp g) (range φ) := by
  have hφl' (x : X) : φ (inlQ x) = inlP x := ConcreteCategory.congr_hom hφl x
  have hφr' (i : ι) (w : TopCat.disk.{u} (k i)) :
      φ (inrQ (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i w)) =
        inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i
          (w, diskCenter.{u} (m i))) :=
    ConcreteCategory.congr_hom (hφr i) w
  obtain ⟨g, hgl, hgcore, hend⟩ := exists_handleCoreRetraction hP hQ φ hφl' hφr'
  -- On `X` the homotopy is constant, and on each handle it is the straight-line homotopy.
  let HY : ((ContinuousMap.id P).comp inlP.hom).Homotopy ((φ.hom.comp g.hom).comp inlP.hom) :=
    (ContinuousMap.Homotopy.refl inlP.hom).cast (by ext x; rfl)
      (by ext x; exact (congrArg φ (hgl x)).trans (hφl' x) |>.symm)
  let HZ : ((ContinuousMap.id P).comp inrP.hom).Homotopy ((φ.hom.comp g.hom).comp inrP.hom) :=
    TopCat.sigmaHomotopy fun i ↦
      { toContinuousMap :=
          (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i ≫
            inrP).hom.comp (handleHomotopy (k i) (m i))
        map_zero_left := fun p ↦ by simp [handleHomotopy_zero]
        map_one_left := fun p ↦ by simpa using hend i p }
  have hHZ (t : unitInterval) (i : ι) (p : TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i)) :
      HZ (t, Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i p) =
        inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i
          (handleHomotopy (k i) (m i) (t, p))) := by
    simp only [HZ]
    rw [TopCat.sigmaHomotopy_apply_ι]
    rfl
  have hYZ (t : unitInterval)
      (b : (∐ fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (m i)) :
        TopCat.{u})) :
      HY (t, Sigma.desc α b) = HZ (t, Limits.Sigma.map (fun i ↦ TopCat.ofHom
        ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) b) := by
    obtain ⟨i, s, rfl⟩ := TopCat.exists_sigma_ι_eq _ b
    rw [Sigma.ι_comp_desc_apply, Sigma.ι_map_apply, hHZ]
    simp only [HY, ContinuousMap.Homotopy.cast_apply, ContinuousMap.Homotopy.refl_apply]
    -- `Sigma.map` acts on the `i`-th attaching region as `(s, y) ↦ (s, y)`, fixed by the homotopy.
    exact (inlP_apply_eq_inrP_of_isPushout_handles hP i s).trans (congrArg (fun p ↦
      inrP (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (m i))) i p))
      (handleHomotopy_diskBoundaryInclusion t s).symm)
  let F := hP.homotopyDesc HY HZ hYZ
  refine ⟨g.hom, fun q ↦ ?_, ⟨{ toHomotopy := F, prop' := fun t y hy ↦ ?_ }⟩⟩
  · rcases exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma hQ q with ⟨x, rfl⟩ | ⟨i, w, rfl⟩
    · rw [hφl', hgl]
    · rw [hφr', hgcore]
  · obtain ⟨q, rfl⟩ := hy
    rcases exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma hQ q with ⟨x, rfl⟩ | ⟨i, w, rfl⟩
    · simp [F, HY, hφl']
    · simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap,
        ContinuousMap.coe_mk, ContinuousMap.id_apply]
      rw [hφr', hP.homotopyDesc_apply_inr, hHZ, handleHomotopy_diskCenter]

end Attachment

end TauCeti.TopCat
