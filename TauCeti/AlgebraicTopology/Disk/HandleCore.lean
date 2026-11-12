/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.Topology.Homotopy.Extension.Ball
public import TauCeti.Topology.Category.TopCat.Pushout

/-!
# Attached handles deformation retract onto their cores

A handle of index `k` is the product `𝔻 k × 𝔻 l` of two Euclidean disks, attached along its
attaching region `∂𝔻 k × 𝔻 l`. Its *core* is the disk `𝔻 k × {0}`, whose boundary sphere
`∂𝔻 k × {0}` lies in the attaching region. This file shows that attaching handles is, up to
homotopy, attaching their cores: the space obtained by attaching handles to `X` deformation
retracts, relative to `X`, onto `X` with the cores attached.

The local statement is that the handle retracts onto its core together with its attaching region,
the set `TauCeti.TopCat.handleCoreUnionAttachingRegion k l` of points `(u, v)` with `‖u‖ = 1` or
`v = 0`. The retraction `TauCeti.TopCat.handleCoreRetraction k l` reads `(u, v)` as the point
`(‖v‖, u)` of the cylinder `I × 𝔻 k` and applies the radial projection of that cylinder from the
point at height `2` on its axis onto its bottom `{0} × 𝔻 k` and its side `I × ∂𝔻 k`
(`TauCeti.ballRadialProjection`, which also gives the homotopy extension property of the sphere in
the ball). The new height is the new length of `v`. A point projected onto the bottom lands on the
core, and a point projected onto the side lands on the attaching region. The retraction fixes
exactly the core and the attaching region (`TauCeti.TopCat.handleCoreRetraction_eq_self_iff`), and
the straight-line homotopy joins it to the identity relative to them
(`TauCeti.TopCat.handleCoreDeformation`).

Now let `P` be obtained from `X` by attaching handles `𝔻 (k i) × 𝔻 (l i)` along a map
`φ : ∐ᵢ ∂𝔻 (k i) × 𝔻 (l i) → X`, and let `Q` be obtained from `X` by attaching the cells
`𝔻 (k i)` along the restriction `s ↦ φ (s, 0)` of `φ` to the boundaries of the cores. Both are
pushouts in `TopCat`. The inclusion of the cores gives a map `c : Q → P` which is the identity on
`X`. Reading the retraction of each handle in `Q` gives a map `g : P → Q`, again the identity on
`X`, with `g ∘ c = id`; and the deformations of the handles glue to a homotopy from the identity of
`P` to `c ∘ g` relative to the image of `c`
(`TauCeti.TopCat.exists_leftInverse_homotopicRel_of_isPushout_handles`). So `c` is the inclusion
of a strong deformation retract, and `P` is homotopy equivalent to `Q` relative to `X`.

This is the comparison between the two forms of Milnor's attachment across a critical level of a
Morse function: the handle form (`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches a
handle `𝔻 λ × 𝔻 (n - λ)` at each critical point of index `λ`, and up to homotopy relative to the
lower sublevel this is attaching the `λ`-cell `𝔻 λ` along the boundary of the core.

## Main declarations

* `TauCeti.TopCat.handleCoreUnionAttachingRegion`: the core of a handle together with its
  attaching region.
* `TauCeti.TopCat.handleCoreRetraction`: the retraction of a handle onto its core and its
  attaching region.
* `TauCeti.TopCat.handleCoreDeformation`: the straight-line homotopy from this retraction to the
  identity, relative to the core and the attaching region.
* `TauCeti.TopCat.handleCoreInclusion`, `TauCeti.TopCat.handleCoreBoundaryInclusion`: the
  inclusions `u ↦ (u, 0)` of the core into the handle and of its boundary sphere into the
  attaching region.
* `TauCeti.TopCat.exists_leftInverse_homotopicRel_of_isPushout_handles`: attaching handles
  deformation retracts, relative to the base, onto attaching their cores.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3: the handle `Dᵏ × Dⁿ⁻ᵏ` attached along `∂Dᵏ × Dⁿ⁻ᵏ` and the cell `Dᵏ × 0` attached along
  `∂Dᵏ × 0`.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, the retraction of
  `Dⁿ × I` onto `Dⁿ × {0} ∪ ∂Dⁿ × I` by radial projection from a point above the cylinder.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set unitInterval

universe u

namespace TauCeti.TopCat

section Retraction

variable {k l : ℕ}

/-- The core `𝔻 k × {0}` of the handle `𝔻 k × 𝔻 l` together with its attaching region
`∂𝔻 k × 𝔻 l`: the points `(u, v)` with `‖u‖ = 1` or `v = 0`. -/
def handleCoreUnionAttachingRegion (k l : ℕ) : Set (TopCat.disk.{u} k × TopCat.disk.{u} l) :=
  {x | ‖x.1.down.1‖ = 1 ∨ x.2 = diskCenter l}

@[simp]
theorem mem_handleCoreUnionAttachingRegion {x : TopCat.disk.{u} k × TopCat.disk.{u} l} :
    x ∈ handleCoreUnionAttachingRegion k l ↔ ‖x.1.down.1‖ = 1 ∨ x.2 = diskCenter l :=
  Iff.rfl

private theorem eq_diskCenter_iff {n : ℕ} (x : TopCat.disk.{u} n) :
    x = diskCenter n ↔ x.down.1 = 0 :=
  ⟨fun h ↦ h ▸ coe_diskCenter_down n,
    fun h ↦ ULift.ext (Subtype.ext (h.trans (coe_diskCenter_down n).symm))⟩

/-- The point `(‖v‖, u)` of the cylinder `I × 𝔻 k` read off from a point `(u, v)` of the handle:
the height is the radial coordinate of `v`. -/
private def handleCylinderPoint (x : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    I × closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
  (⟨‖x.2.down.1‖, norm_nonneg _, mem_closedBall_zero_iff.1 x.2.down.2⟩, x.1.down)

private theorem continuous_handleCylinderPoint :
    Continuous (handleCylinderPoint.{u} (k := k) (l := l)) :=
  ((by fun_prop : Continuous fun x : TopCat.disk.{u} k × TopCat.disk.{u} l ↦
    ‖x.2.down.1‖).subtype_mk _).prodMk (continuous_uliftDown.comp continuous_fst)

private theorem norm_radialRetraction_ballRadialProjection_le
    (x : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    ‖radialRetraction (ballRadialProjection (handleCylinderPoint x)).1 x.2.down.1‖ ≤ 1 := by
  rw [norm_radialRetraction (ballRadialProjection_spec _).1.1]
  exact (min_le_left _ _).trans (mem_closedBall_zero_iff.1 x.2.down.2)

/-- **The retraction of a handle onto its core and its attaching region.** Read the point `(u, v)`
of `𝔻 k × 𝔻 l` as the point `(‖v‖, u)` of the cylinder `I × 𝔻 k`, and project it radially from the
point at height `2` on the axis onto the bottom and sides of the cylinder
(`TauCeti.ballRadialProjection`), giving a point `(t', u')`. The retraction sends `(u, v)` to
`(u', v')`, where `v'` is `v` radially shortened to the length `t'`. -/
def handleCoreRetraction (k l : ℕ) :
    C(TopCat.disk.{u} k × TopCat.disk.{u} l, TopCat.disk.{u} k × TopCat.disk.{u} l) where
  toFun x :=
    (ULift.up ⟨(ballRadialProjection (handleCylinderPoint x)).2,
        (ballRadialProjection_spec _).2.1⟩,
      ULift.up ⟨radialRetraction (ballRadialProjection (handleCylinderPoint x)).1 x.2.down.1,
        mem_closedBall_zero_iff.2 (norm_radialRetraction_ballRadialProjection_le x)⟩)
  continuous_toFun := by
    have hp := continuous_ballRadialProjection.comp
      (continuous_handleCylinderPoint.{u} (k := k) (l := l))
    have hr : Continuous fun x : TopCat.disk.{u} k × TopCat.disk.{u} l ↦
        radialRetraction (ballRadialProjection (handleCylinderPoint x)).1 x.2.down.1 :=
      hp.fst.radialRetraction (fun x ↦ (ballRadialProjection_spec _).1.1) (by fun_prop)
    exact (continuous_uliftUp.comp (hp.snd.subtype_mk _)).prodMk
      (continuous_uliftUp.comp (hr.subtype_mk _))

/-- The first component of the retraction is the base point of the radial projection of
`(‖v‖, u)`. -/
theorem coe_fst_handleCoreRetraction_down (x : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    ((handleCoreRetraction k l x).1.down : EuclideanSpace ℝ (Fin k)) =
      (ballRadialProjection
        ((⟨‖x.2.down.1‖, norm_nonneg _, mem_closedBall_zero_iff.1 x.2.down.2⟩ : I), x.1.down)).2 :=
  (rfl)

/-- The second component of the retraction is `v` radially shortened to the height of the radial
projection of `(‖v‖, u)`. -/
theorem coe_snd_handleCoreRetraction_down (x : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    ((handleCoreRetraction k l x).2.down : EuclideanSpace ℝ (Fin l)) =
      radialRetraction (ballRadialProjection
        ((⟨‖x.2.down.1‖, norm_nonneg _, mem_closedBall_zero_iff.1 x.2.down.2⟩ : I), x.1.down)).1
        x.2.down.1 :=
  (rfl)

/-- The retraction takes values in the core and the attaching region. -/
theorem handleCoreRetraction_mem (x : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    handleCoreRetraction k l x ∈ handleCoreUnionAttachingRegion k l := by
  rw [mem_handleCoreUnionAttachingRegion, eq_diskCenter_iff, coe_fst_handleCoreRetraction_down,
    coe_snd_handleCoreRetraction_down, ← mem_sphere_zero_iff_norm]
  rcases (ballRadialProjection_spec (handleCylinderPoint x)).2.2 with h | h
  · -- A point projected onto the bottom of the cylinder lands on the core.
    refine Or.inr ?_
    rw [← norm_eq_zero, norm_radialRetraction (ballRadialProjection_spec _).1.1]
    exact (congrArg (min ‖x.2.down.1‖) h).trans (min_eq_right (norm_nonneg _))
  · -- A point projected onto the side of the cylinder lands on the attaching region.
    exact Or.inl h

/-- The retraction fixes exactly the core and the attaching region. -/
theorem handleCoreRetraction_eq_self_iff {x : TopCat.disk.{u} k × TopCat.disk.{u} l} :
    handleCoreRetraction k l x = x ↔ x ∈ handleCoreUnionAttachingRegion k l := by
  refine ⟨fun h ↦ h ▸ handleCoreRetraction_mem x, fun hx ↦ ?_⟩
  have hp : ballRadialProjection (handleCylinderPoint x) = (‖x.2.down.1‖, x.1.down.1) := by
    refine ballRadialProjection_eq_self _ (mem_cylinderExtensionDomain_iff.2 ?_)
    rcases hx with hx | hx
    · exact Or.inr (mem_sphere_zero_iff_norm.2 hx)
    · refine Or.inl (Subtype.ext ?_)
      simp [handleCylinderPoint, (eq_diskCenter_iff _).1 hx]
  refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_))
  · rw [coe_fst_handleCoreRetraction_down]
    exact congrArg Prod.snd hp
  · rw [coe_snd_handleCoreRetraction_down]
    exact (congrArg (radialRetraction · x.2.down.1) (congrArg Prod.fst hp)).trans
      (radialRetraction_of_norm_le le_rfl)

/-- The function underlying `TauCeti.TopCat.handleCoreDeformation`: the point
`(1 - t) r(x) + t x` of the handle, for the retraction `r`. -/
private def handleCoreDeformationFun (p : I × (TopCat.disk.{u} k × TopCat.disk.{u} l)) :
    TopCat.disk.{u} k × TopCat.disk.{u} l :=
  (ULift.up ⟨(1 - (p.1 : ℝ)) • (handleCoreRetraction k l p.2).1.down.1 + (p.1 : ℝ) • p.2.1.down.1,
      convex_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 (handleCoreRetraction k l p.2).1.down.2
        p.2.1.down.2 (sub_nonneg.2 p.1.2.2) p.1.2.1 (sub_add_cancel 1 _)⟩,
    ULift.up ⟨(1 - (p.1 : ℝ)) • (handleCoreRetraction k l p.2).2.down.1 + (p.1 : ℝ) • p.2.2.down.1,
      convex_closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 (handleCoreRetraction k l p.2).2.down.2
        p.2.2.down.2 (sub_nonneg.2 p.1.2.2) p.1.2.1 (sub_add_cancel 1 _)⟩)

/-- **The deformation of a handle onto its core and its attaching region**: the straight-line
homotopy `(t, x) ↦ (1 - t) r(x) + t x` from the retraction `r = handleCoreRetraction k l` to the
identity, which fixes the core and the attaching region throughout. -/
def handleCoreDeformation (k l : ℕ) :
    (handleCoreRetraction.{u} k l).HomotopyRel (ContinuousMap.id _)
      (handleCoreUnionAttachingRegion k l) where
  toFun := handleCoreDeformationFun
  continuous_toFun := by
    have hr := (handleCoreRetraction.{u} k l).continuous
    unfold handleCoreDeformationFun
    fun_prop
  map_zero_left x := by
    refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_)) <;>
      simp [handleCoreDeformationFun]
  map_one_left x := by
    refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_)) <;>
      simp [handleCoreDeformationFun]
  prop' t x hx := by
    have h := handleCoreRetraction_eq_self_iff.2 hx
    refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_)) <;>
      simp [handleCoreDeformationFun, h, ← add_smul]

@[simp]
theorem coe_fst_handleCoreDeformation_down (t : I)
    (x : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    ((handleCoreDeformation k l (t, x)).1.down : EuclideanSpace ℝ (Fin k)) =
      (1 - (t : ℝ)) • (handleCoreRetraction k l x).1.down.1 + (t : ℝ) • x.1.down.1 :=
  (rfl)

@[simp]
theorem coe_snd_handleCoreDeformation_down (t : I)
    (x : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    ((handleCoreDeformation k l (t, x)).2.down : EuclideanSpace ℝ (Fin l)) =
      (1 - (t : ℝ)) • (handleCoreRetraction k l x).2.down.1 + (t : ℝ) • x.2.down.1 :=
  (rfl)

end Retraction

section Attachment

/-- The inclusion `u ↦ (u, 0)` of the core `𝔻 k` into the handle `𝔻 k × 𝔻 l`. -/
def handleCoreInclusion (k l : ℕ) :
    TopCat.disk.{u} k ⟶ TopCat.of (TopCat.disk.{u} k × TopCat.disk.{u} l) :=
  TopCat.ofHom ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (diskCenter l)))

@[simp]
theorem handleCoreInclusion_apply (k l : ℕ) (u : TopCat.disk.{u} k) :
    handleCoreInclusion k l u = (u, diskCenter l) :=
  (rfl)

/-- The inclusion `s ↦ (s, 0)` of the boundary sphere `∂𝔻 k` of the core of the handle
`𝔻 k × 𝔻 l` into its attaching region `∂𝔻 k × 𝔻 l`. -/
def handleCoreBoundaryInclusion (k l : ℕ) :
    TopCat.diskBoundary.{u} k ⟶ TopCat.of (TopCat.diskBoundary.{u} k × TopCat.disk.{u} l) :=
  TopCat.ofHom ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (diskCenter l)))

@[simp]
theorem handleCoreBoundaryInclusion_apply (k l : ℕ) (s : TopCat.diskBoundary.{u} k) :
    handleCoreBoundaryInclusion k l s = (s, diskCenter l) :=
  (rfl)

variable {ι : Type u} {k l : ι → ℕ} {X P Q : TopCat.{u}}
  {φ : ∐ (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (l i))) ⟶ X}
  {j : X ⟶ P} {χ : ∐ (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) ⟶ P}
  {j' : X ⟶ Q} {χ' : ∐ (fun i ↦ TopCat.disk.{u} (k i)) ⟶ Q}

/-- The map of a handle into the space `Q` obtained by attaching the cores: a point `(s, v)` of the
attaching region goes to `φ (s, v)`, and every other point `(u, v)` to the point `u` of the attached
core. It is continuous on the core and the attaching region
(`TauCeti.TopCat.continuousOn_handleCoreFun`), where the two descriptions agree. -/
private def handleCoreFun (φ : ∐ (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
      TopCat.disk.{u} (l i))) ⟶ X) (j' : X ⟶ Q) (χ' : ∐ (fun i ↦ TopCat.disk.{u} (k i)) ⟶ Q)
    (i : ι) (x : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) : Q :=
  if h : ‖x.1.down.1‖ = 1 then
    j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (l i))) i
      (ULift.up ⟨x.1.down.1, mem_sphere_zero_iff_norm.2 h⟩, x.2)))
  else χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i x.1)

private theorem handleCoreFun_diskBoundaryInclusion (i : ι) (s : TopCat.diskBoundary.{u} (k i))
    (v : TopCat.disk.{u} (l i)) :
    handleCoreFun φ j' χ' i (TopCat.diskBoundaryInclusion (k i) s, v) =
      j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
        TopCat.disk.{u} (l i))) i (s, v))) :=
  dite_eq_left (norm_diskBoundaryInclusion s)

/-- The attaching map of the cores is `s ↦ φ (s, 0)`, so on the boundary sphere of a core the
two descriptions of `TauCeti.TopCat.handleCoreFun` agree. -/
private theorem handleCoreFun_of_snd_eq
    (hcore : ∀ i (s : TopCat.diskBoundary.{u} (k i)),
      j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
        TopCat.disk.{u} (l i))) i (s, diskCenter (l i)))) =
        χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i (TopCat.diskBoundaryInclusion (k i) s)))
    (i : ι) {x : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)} (hx : x.2 = diskCenter (l i)) :
    handleCoreFun φ j' χ' i x = χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i x.1) := by
  by_cases h : ‖x.1.down.1‖ = 1
  · rw [handleCoreFun, dite_eq_left h, hx]
    exact hcore i (ULift.up ⟨x.1.down.1, mem_sphere_zero_iff_norm.2 h⟩)
  · exact dite_eq_right h

private theorem continuousOn_handleCoreFun
    (hcore : ∀ i (s : TopCat.diskBoundary.{u} (k i)),
      j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
        TopCat.disk.{u} (l i))) i (s, diskCenter (l i)))) =
        χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i (TopCat.diskBoundaryInclusion (k i) s)))
    (i : ι) :
    ContinuousOn (handleCoreFun φ j' χ' i) (handleCoreUnionAttachingRegion (k i) (l i)) := by
  have hn : Continuous fun x : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i) ↦ ‖x.1.down.1‖ := by
    fun_prop
  have h₁ : ContinuousOn (handleCoreFun φ j' χ' i) {x | ‖x.1.down.1‖ = 1} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : domRestrict {x | ‖x.1.down.1‖ = 1} (handleCoreFun φ j' χ' i) =
        fun x ↦ j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
          TopCat.disk.{u} (l i))) i (ULift.up ⟨x.1.1.down.1, mem_sphere_zero_iff_norm.2 x.2⟩,
            x.1.2))) :=
      funext fun x ↦ dite_eq_left x.2
    rw [he]
    have hs : Continuous fun x : {x : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i) |
        ‖x.1.down.1‖ = 1} ↦
          (ULift.up ⟨x.1.1.down.1, mem_sphere_zero_iff_norm.2 x.2⟩ :
            TopCat.diskBoundary.{u} (k i)) :=
      continuous_uliftUp.comp ((by fun_prop :
        Continuous fun x : {x : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i) |
          ‖x.1.down.1‖ = 1} ↦ x.1.1.down.1).subtype_mk _)
    exact j'.hom.continuous.comp (φ.hom.continuous.comp ((Sigma.ι (fun i ↦ TopCat.of
      (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (l i))) i).hom.continuous.comp
        (hs.prodMk (by fun_prop))))
  have h₂ : ContinuousOn (handleCoreFun φ j' χ' i) {x | x.2 = diskCenter (l i)} :=
    ((χ'.hom.continuous.comp ((Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i).hom.continuous.comp
      continuous_fst)).continuousOn).congr
      fun x hx ↦ handleCoreFun_of_snd_eq hcore i hx
  have hA : handleCoreUnionAttachingRegion (k i) (l i) =
      {x | ‖x.1.down.1‖ = 1} ∪ {x | x.2 = diskCenter (l i)} := (rfl)
  rw [hA]
  exact h₁.union_of_isClosed h₂ (isClosed_eq hn continuous_const)
    (isClosed_eq continuous_snd continuous_const)

/-- The retraction of a handle onto its core and its attaching region, followed by
`TauCeti.TopCat.handleCoreFun`: the map of the handle `i` into the space with the cores attached. -/
private def handleCoreMap
    (hcore : ∀ i (s : TopCat.diskBoundary.{u} (k i)),
      j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
        TopCat.disk.{u} (l i))) i (s, diskCenter (l i)))) =
        χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i (TopCat.diskBoundaryInclusion (k i) s)))
    (i : ι) : C(TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i), Q) where
  toFun x := handleCoreFun φ j' χ' i (handleCoreRetraction (k i) (l i) x)
  continuous_toFun := (continuousOn_handleCoreFun hcore i).comp_continuous
    (handleCoreRetraction (k i) (l i)).continuous handleCoreRetraction_mem

private theorem handleCoreMap_apply
    (hcore : ∀ i (s : TopCat.diskBoundary.{u} (k i)),
      j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
        TopCat.disk.{u} (l i))) i (s, diskCenter (l i)))) =
        χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i (TopCat.diskBoundaryInclusion (k i) s)))
    (i : ι) (x : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) :
    handleCoreMap hcore i x = handleCoreFun φ j' χ' i (handleCoreRetraction (k i) (l i) x) :=
  (rfl)

/-- **Attached handles deformation retract onto their cores.** Let `P` be obtained from `X` by
attaching handles `𝔻 (k i) × 𝔻 (l i)` along their attaching regions `∂𝔻 (k i) × 𝔻 (l i)` by a map
`φ`, and let `Q` be obtained from `X` by attaching the cells `𝔻 (k i)` along the restriction
`s ↦ φ (s, 0)` of `φ` to the boundary spheres of the cores, both as pushouts in `TopCat`. Then the
map `c : Q ⟶ P` which is the identity on `X` and sends each cell to the core `u ↦ (u, 0)` of its
handle is the inclusion of a strong deformation retract relative to `X`: it has a left inverse
`g : P ⟶ Q` which is the identity on `X`, and `c ∘ g` is homotopic to the identity of `P` relative
to the image of `c`. -/
theorem exists_leftInverse_homotopicRel_of_isPushout_handles
    (sq : IsPushout φ (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) j χ)
    (sq' : IsPushout (Limits.Sigma.map (fun i ↦ handleCoreBoundaryInclusion (k i) (l i)) ≫ φ)
      (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (k i)) j' χ') :
    ∃ c : Q ⟶ P, j' ≫ c = j ∧
      χ' ≫ c = Limits.Sigma.map (fun i ↦ handleCoreInclusion (k i) (l i)) ≫ χ ∧
      ∃ g : P ⟶ Q, j ≫ g = j' ∧ Function.LeftInverse g c ∧
        (ContinuousMap.id P).HomotopicRel (c.hom.comp g.hom) (range c) := by
  -- The two squares, read pointwise on the summand `i`.
  have hhandle (i : ι) (s : TopCat.diskBoundary.{u} (k i)) (v : TopCat.disk.{u} (l i)) :
      j (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
        TopCat.disk.{u} (l i))) i (s, v))) =
        χ (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i
          (TopCat.diskBoundaryInclusion (k i) s, v)) := by
    rw [sq.w_apply, Sigma.ι_map_apply]
    rfl
  have hcore (i : ι) (s : TopCat.diskBoundary.{u} (k i)) :
      j' (φ (Sigma.ι (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) ×
        TopCat.disk.{u} (l i))) i (s, diskCenter (l i)))) =
        χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i (TopCat.diskBoundaryInclusion (k i) s)) := by
    have h := sq'.w_apply (Sigma.ι (fun i ↦ TopCat.diskBoundary.{u} (k i)) i s)
    rw [ConcreteCategory.comp_apply, Sigma.ι_map_apply, Sigma.ι_map_apply] at h
    exact h
  -- The inclusion of the cores.
  let c : Q ⟶ P := sq'.desc j (Limits.Sigma.map (fun i ↦ handleCoreInclusion (k i) (l i)) ≫ χ) <|
    Sigma.hom_ext _ _ fun i ↦ by
      ext s
      simp only [ConcreteCategory.comp_apply, Sigma.ι_map_apply]
      exact hhandle i s _
  have hcj (x : X) : c (j' x) = j x := ConcreteCategory.congr_hom (sq'.inl_desc _ _ _) x
  have hcχ (i : ι) (u : TopCat.disk.{u} (k i)) :
      c (χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i u)) =
        χ (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i
          (u, diskCenter (l i))) := by
    rw [← ConcreteCategory.comp_apply, sq'.inr_desc, ConcreteCategory.comp_apply,
      Sigma.ι_map_apply]
    rfl
  -- On the core and the attaching region, the map into `Q` followed by `c` is the handle itself.
  have hcF (i : ι) {y : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)}
      (hy : y ∈ handleCoreUnionAttachingRegion (k i) (l i)) :
      c (handleCoreFun φ j' χ' i y) =
        χ (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i y) := by
    rcases hy with hy | hy
    · rw [handleCoreFun, dite_eq_left hy, hcj]
      exact hhandle i (ULift.up ⟨y.1.down.1, mem_sphere_zero_iff_norm.2 hy⟩) y.2
    · rw [handleCoreFun_of_snd_eq hcore i hy, hcχ, ← hy]
  -- The retraction of the handles, read in `Q`.
  let g : P ⟶ Q := sq.desc j' (Sigma.desc fun i ↦ (TopCat.ofHom (handleCoreMap hcore i) :
      TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) ⟶ Q)) <|
    Sigma.hom_ext _ _ fun i ↦ by
      rw [Sigma.ι_map_assoc, Sigma.ι_comp_desc]
      ext ⟨s, v⟩
      simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom]
      rw [ContinuousMap.prodMap_apply, Prod.map_apply, handleCoreMap_apply,
        ContinuousMap.id_apply]
      have hr : handleCoreRetraction (k i) (l i) (TopCat.diskBoundaryInclusion (k i) s, v) =
          (TopCat.diskBoundaryInclusion (k i) s, v) :=
        handleCoreRetraction_eq_self_iff.2 (Or.inl (norm_diskBoundaryInclusion s))
      exact ((congrArg (handleCoreFun φ j' χ' i) hr).trans
        (handleCoreFun_diskBoundaryInclusion i s v)).symm
  have hgj (x : X) : g (j x) = j' x := ConcreteCategory.congr_hom (sq.inl_desc _ _ _) x
  have hgχ (i : ι) (y : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) :
      g (χ (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i y)) =
        handleCoreFun φ j' χ' i (handleCoreRetraction (k i) (l i) y) := by
    rw [← ConcreteCategory.comp_apply, sq.inr_desc, Sigma.ι_comp_desc_apply]
    rfl
  -- Every point of `Q` comes from `X` or from a cell.
  have hQ (q : Q) : (∃ x, j' x = q) ∨
      ∃ i u, χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i u) = q :=
    exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma sq' q
  have hgc : Function.LeftInverse g c := fun q ↦ by
    obtain ⟨x, rfl⟩ | ⟨i, u, rfl⟩ := hQ q
    · rw [hcj, hgj]
    · rw [hcχ, hgχ, handleCoreRetraction_eq_self_iff.2 (Or.inr rfl),
        handleCoreFun_of_snd_eq hcore i rfl]
  refine ⟨c, sq'.inl_desc _ _ _, sq'.inr_desc _ _ _, g, sq.inl_desc _ _ _, hgc, ⟨?_⟩⟩
  -- The deformations of the handles from the identity to their retractions, read in `P`.
  let K : C(I × (∐ fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) :
      TopCat.{u}), P) :=
    TopCat.sigmaCylinderDesc (F := fun i ↦ TopCat.of (TopCat.disk.{u} (k i) ×
      TopCat.disk.{u} (l i))) fun i ↦ (χ.hom.comp (Sigma.ι (fun i ↦
      TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i).hom).comp
        (handleCoreDeformation (k i) (l i)).symm.toContinuousMap
  have hK (t : I) (i : ι) (y : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) :
      K (t, Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i y) =
        χ (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i
          ((handleCoreDeformation (k i) (l i)).symm (t, y))) :=
    TopCat.sigmaCylinderDesc_ι (F := fun i ↦ TopCat.of (TopCat.disk.{u} (k i) ×
      TopCat.disk.{u} (l i))) _ t i y
  -- They fix the cores and the attaching regions.
  have hKA (t : I) (i : ι) {y : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)}
      (hy : y ∈ handleCoreUnionAttachingRegion (k i) (l i)) :
      K (t, Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i y) =
        χ (Sigma.ι (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i y) := by
    rw [hK, (handleCoreDeformation (k i) (l i)).symm.eq_fst t hy, ContinuousMap.id_apply]
  let HZ : ((ContinuousMap.id P).comp χ.hom).Homotopy ((c.hom.comp g.hom).comp χ.hom) :=
    { toContinuousMap := K
      map_zero_left z := by
        obtain ⟨i, y, rfl⟩ := TopCat.exists_sigma_ι_eq _ z
        rw [ContinuousMap.toFun_eq_coe, hK, ContinuousMap.HomotopyWith.apply_zero,
          ContinuousMap.id_apply, ContinuousMap.comp_apply, ContinuousMap.id_apply]
      map_one_left z := by
        obtain ⟨i, y, rfl⟩ := TopCat.exists_sigma_ι_eq _ z
        rw [ContinuousMap.toFun_eq_coe, hK, ContinuousMap.HomotopyWith.apply_one,
          ContinuousMap.comp_apply, ContinuousMap.comp_apply]
        exact ((congrArg c (hgχ i y)).trans (hcF i (handleCoreRetraction_mem y))).symm }
  let HY : ((ContinuousMap.id P).comp j.hom).Homotopy ((c.hom.comp g.hom).comp j.hom) :=
    (ContinuousMap.Homotopy.refl _).cast rfl <| ContinuousMap.ext fun x ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        ContinuousMap.id_apply]
      exact ((congrArg c (hgj x)).trans (hcj x)).symm
  have hY (t : I) (x : X) : HY (t, x) = j x := (rfl)
  have hZ (t : I) (z : (∐ fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) :
      TopCat.{u})) : HZ (t, z) = K (t, z) := (rfl)
  let H := sq.homotopyDesc HY HZ fun t b ↦ by
    obtain ⟨i, x, rfl⟩ := TopCat.exists_sigma_ι_eq _ b
    rw [hY, Sigma.ι_map_apply, hZ, TopCat.ofHom_apply, ContinuousMap.prodMap_apply,
      Prod.map_apply, ContinuousMap.id_apply]
    exact (hhandle i x.1 x.2).trans
      (hKA t i (y := (TopCat.diskBoundaryInclusion (k i) x.1, x.2))
        (Or.inl (norm_diskBoundaryInclusion x.1))).symm
  refine { toHomotopy := H, prop' := fun t x hx ↦ ?_ }
  obtain ⟨q, rfl⟩ := hx
  -- The goal is stated for the slice of `H` at time `t`; read it pointwise.
  change H (t, c q) = c q
  obtain ⟨x, rfl⟩ | ⟨i, u, rfl⟩ := hQ q
  · rw [hcj, sq.homotopyDesc_apply_inl, hY]
  · rw [hcχ, sq.homotopyDesc_apply_inr]
    exact hKA t i (Or.inr rfl)

end Attachment

end TauCeti.TopCat
