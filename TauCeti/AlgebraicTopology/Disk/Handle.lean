/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Category.TopCat.Pushout
import TauCeti.Analysis.Normed.Module.Normalize

/-!
# A handle attachment deformation retracts onto the attachment of its cores

A handle of index `k` and coindex `l` is the product `D^k × D^l` of two closed Euclidean disks
(`TopCat.disk`). It is attached to a space `X` along its attaching region `∂D^k × D^l`, and its
core is the disk `D^k × {0}`, which meets the attaching region in the core sphere `∂D^k × {0}`.

The handle deformation retracts onto the union of its core and its attaching region, relative to
that union (`TauCeti.TopCat.handleCoreRetraction`, `TauCeti.TopCat.handleCoreHomotopy`). Write a
point of the handle as `(x, y)`. Over each direction `y / ‖y‖`, the pair `(‖y‖, x)` lies in the
cylinder `[0, 1] × D^k`, and it is moved by the radial projection of that cylinder onto its bottom
`{0} × D^k` and its side `[0, 1] × ∂D^k` from the point at height `2` on its axis
(`TauCeti.ballRadialProjection`); the bottom is the core and the side is the attaching region.
The straight-line homotopy to this retraction stays in the handle, which is convex.

Attaching handles along maps `α i : ∂D^{k i} × D^{l i} → X` therefore deformation retracts,
relative to `X`, onto `X` with the cores attached along the restrictions of `α i` to the core
spheres `∂D^{k i} × {0}`: the comparison map from this cell attachment to the handle attachment
has a left inverse `g`, and its composite with `g` is homotopic to the identity relative to its
image (`CategoryTheory.IsPushout.exists_coreAttachment_deformation`). So a space obtained by
attaching handles is homotopy equivalent, relative to `X`, to the space obtained by attaching
cells of the same indices along the core spheres. This is how a handle decomposition, for instance
the one given by a Morse function across a critical level, yields a cell decomposition. The
handles may be infinitely many and of any indices; a handle of index `0` has an empty attaching
region and its core is a disk attached along the empty sphere.

## Main declarations

* `TauCeti.TopCat.handleCoreRetraction`: the retraction of `D^k × D^l` onto
  `D^k × {0} ∪ ∂D^k × D^l`.
* `TauCeti.TopCat.handleCoreRetraction_apply_of_mem`,
  `TauCeti.TopCat.handleCoreRetraction_mem`: it fixes that union and lands in it.
* `TauCeti.TopCat.handleCoreHomotopy`: the straight-line homotopy from the identity to the
  retraction, relative to the union.
* `CategoryTheory.IsPushout.exists_coreAttachment_deformation`: a handle attachment deformation
  retracts, relative to the attached space, onto the attachment of the cores along the core
  spheres.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, proof of Proposition 0.16, for the radial projection of `Dⁿ × I` onto
  `Dⁿ × {0} ∪ ∂Dⁿ × I`.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, proof of Theorem 3.2, which deforms a handle onto its core cell.
-/

public section

noncomputable section

open CategoryTheory Function Limits Metric Set Topology unitInterval

universe u

namespace TauCeti.TopCat

section Retraction

variable {k l : ℕ}

/-- The point `(‖y‖, x)` of the cylinder `[0, 1] × D^k` over the first factor, read off a point
`(x, y)` of the handle `D^k × D^l`. -/
private def handleCylinderPoint (p : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    I × closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
  (⟨‖p.2.down.1‖, norm_nonneg _, mem_closedBall_zero_iff.1 p.2.down.2⟩, p.1.down)

private lemma continuous_handleCylinderPoint :
    Continuous (handleCylinderPoint : TopCat.disk.{u} k × TopCat.disk.{u} l → _) :=
  ((continuous_norm.comp (continuous_subtype_val.comp
    (continuous_uliftDown.comp continuous_snd))).subtype_mk _).prodMk
      (continuous_uliftDown.comp continuous_fst)

/-- The height of the radial projection of `handleCylinderPoint p` is at most `‖y‖`. -/
private lemma ballRadialProjection_handleCylinderPoint_fst_le
    (p : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    (ballRadialProjection (handleCylinderPoint p)).1 ≤ ‖p.2.down.1‖ :=
  ballRadialProjection_fst_le _

/-- **The retraction of a handle onto its core and its attaching region.** For a point `(x, y)`
of `D^k × D^l`, the pair `(‖y‖, x)` of the cylinder `[0, 1] × D^k` is moved to `(t', x')` by the
radial projection `TauCeti.ballRadialProjection` onto the bottom and the side of the cylinder, and
`(x, y)` is sent to `(x', (t' / ‖y‖) • y)`. This lands in `D^k × {0} ∪ ∂D^k × D^l`
(`TauCeti.TopCat.handleCoreRetraction_mem`) and fixes it
(`TauCeti.TopCat.handleCoreRetraction_apply_of_mem`). -/
def handleCoreRetraction (k l : ℕ) :
    C(TopCat.disk.{u} k × TopCat.disk.{u} l, TopCat.disk.{u} k × TopCat.disk.{u} l) where
  toFun p :=
    (ULift.up ⟨(ballRadialProjection (handleCylinderPoint p)).2,
        (ballRadialProjection_spec _).2.1⟩,
      ULift.up ⟨((ballRadialProjection (handleCylinderPoint p)).1 / ‖p.2.down.1‖) • p.2.down.1,
        mem_closedBall_zero_iff.2 <|
          (norm_div_norm_smul_le _ (ballRadialProjection_spec _).1.1).trans
            ((ballRadialProjection_handleCylinderPoint_fst_le p).trans
              (mem_closedBall_zero_iff.1 p.2.down.2))⟩)
  continuous_toFun := by
    have hp := continuous_ballRadialProjection.comp
      (continuous_handleCylinderPoint (k := k) (l := l))
    have hy : Continuous fun p : TopCat.disk.{u} k × TopCat.disk.{u} l ↦ p.2.down.1 :=
      continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd)
    exact (continuous_uliftUp.comp (hp.snd.subtype_mk _)).prodMk
      (continuous_uliftUp.comp ((hp.fst.div_norm_smul hy
        (fun p ↦ (ballRadialProjection_spec _).1.1)
        ballRadialProjection_handleCylinderPoint_fst_le).subtype_mk _))

@[simp]
private theorem coe_handleCoreRetraction_fst (p : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    ((handleCoreRetraction k l p).1.down : EuclideanSpace ℝ (Fin k)) =
      (ballRadialProjection (handleCylinderPoint p)).2 :=
  (rfl)

@[simp]
private theorem coe_handleCoreRetraction_snd (p : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    ((handleCoreRetraction k l p).2.down : EuclideanSpace ℝ (Fin l)) =
      ((ballRadialProjection (handleCylinderPoint p)).1 / ‖p.2.down.1‖) • p.2.down.1 :=
  (rfl)

/-- The retraction `TauCeti.TopCat.handleCoreRetraction` fixes the attaching region
`∂D^k × D^l` and the core `D^k × {0}` of the handle. -/
theorem handleCoreRetraction_apply_of_mem {p : TopCat.disk.{u} k × TopCat.disk.{u} l}
    (hp : p ∈ {q : TopCat.disk.{u} k × TopCat.disk.{u} l | ‖q.1.down.1‖ = 1 ∨ q.2 = diskCenter l}) :
    handleCoreRetraction k l p = p := by
  have hmem : handleCylinderPoint p ∈
      cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin k)) 1) := by
    rw [mem_cylinderExtensionDomain_iff]
    rcases hp with hx | hy
    · exact Or.inr (mem_sphere_zero_iff_norm.2 hx)
    · refine Or.inl (Subtype.ext ?_)
      simp [handleCylinderPoint, hy]
  have h := ballRadialProjection_eq_self _ hmem
  refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_))
  · rw [coe_handleCoreRetraction_fst, h]
    rfl
  · rw [coe_handleCoreRetraction_snd, h]
    -- The height of `handleCylinderPoint p` is `‖y‖` by definition.
    change (‖p.2.down.1‖ / ‖p.2.down.1‖) • p.2.down.1 = p.2.down.1
    rcases eq_or_ne p.2.down.1 0 with h0 | h0
    · simp [h0]
    · rw [div_self (norm_ne_zero_iff.2 h0), one_smul]

/-- The retraction fixes the attaching region `∂D^k × D^l` of the handle. -/
@[simp]
theorem handleCoreRetraction_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} k)
    (y : TopCat.disk.{u} l) :
    handleCoreRetraction k l (TopCat.diskBoundaryInclusion k s, y) =
      (TopCat.diskBoundaryInclusion k s, y) :=
  handleCoreRetraction_apply_of_mem (Or.inl (norm_diskBoundaryInclusion s))

/-- The retraction fixes the core `D^k × {0}` of the handle. -/
@[simp]
theorem handleCoreRetraction_diskCenter (x : TopCat.disk.{u} k) :
    handleCoreRetraction k l (x, diskCenter l) = (x, diskCenter l) :=
  handleCoreRetraction_apply_of_mem (Or.inr rfl)

/-- The retraction `TauCeti.TopCat.handleCoreRetraction` lands in the union of the attaching
region `∂D^k × D^l` and the core `D^k × {0}` of the handle. -/
theorem handleCoreRetraction_mem (p : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    handleCoreRetraction k l p ∈
      {q : TopCat.disk.{u} k × TopCat.disk.{u} l | ‖q.1.down.1‖ = 1 ∨ q.2 = diskCenter l} := by
  rcases (ballRadialProjection_spec (handleCylinderPoint p)).2.2 with h0 | hs
  · refine Or.inr (ULift.ext (Subtype.ext ?_))
    rw [coe_handleCoreRetraction_snd, h0, zero_div, zero_smul, coe_diskCenter_down]
  · exact Or.inl (mem_sphere_zero_iff_norm.1 hs)

/-- **A handle deformation retracts onto its core and its attaching region.** The straight-line
homotopy from the identity of `D^k × D^l` to `TauCeti.TopCat.handleCoreRetraction`, relative to
the union `D^k × {0} ∪ ∂D^k × D^l` of the core and the attaching region. -/
def handleCoreHomotopy (k l : ℕ) :
    (ContinuousMap.id (TopCat.disk.{u} k × TopCat.disk.{u} l)).HomotopyRel
      (handleCoreRetraction k l) {p | ‖p.1.down.1‖ = 1 ∨ p.2 = diskCenter l} where
  toFun q :=
    (ULift.up ⟨(1 - (q.1 : ℝ)) • q.2.1.down.1 +
          (q.1 : ℝ) • (handleCoreRetraction k l q.2).1.down.1,
        convex_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 q.2.1.down.2
          (handleCoreRetraction k l q.2).1.down.2 (sub_nonneg.2 q.1.2.2) q.1.2.1
          (sub_add_cancel 1 _)⟩,
      ULift.up ⟨(1 - (q.1 : ℝ)) • q.2.2.down.1 +
          (q.1 : ℝ) • (handleCoreRetraction k l q.2).2.down.1,
        convex_closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 q.2.2.down.2
          (handleCoreRetraction k l q.2).2.down.2 (sub_nonneg.2 q.1.2.2) q.1.2.1
          (sub_add_cancel 1 _)⟩)
  continuous_toFun := by
    refine Continuous.prodMk (continuous_uliftUp.comp (Continuous.subtype_mk ?_ _))
      (continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)) <;> fun_prop
  map_zero_left p := by
    refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_)) <;> simp
  map_one_left p := by
    refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_)) <;> simp
  prop' t p hp := by
    have h := handleCoreRetraction_apply_of_mem hp
    -- The time-`t` slice of the homotopy is the straight-line formula, coordinatewise.
    refine Prod.ext (ULift.ext (Subtype.ext ?_)) (ULift.ext (Subtype.ext ?_))
    · change (1 - (t : ℝ)) • p.1.down.1 + (t : ℝ) • (handleCoreRetraction k l p).1.down.1 =
        p.1.down.1
      rw [h, ← add_smul, sub_add_cancel, one_smul]
    · change (1 - (t : ℝ)) • p.2.down.1 + (t : ℝ) • (handleCoreRetraction k l p).2.down.1 =
        p.2.down.1
      rw [h, ← add_smul, sub_add_cancel, one_smul]

/-- The homotopy `TauCeti.TopCat.handleCoreHomotopy` fixes the attaching region of the handle. -/
@[simp]
theorem handleCoreHomotopy_diskBoundaryInclusion (t : I) (s : TopCat.diskBoundary.{u} k)
    (y : TopCat.disk.{u} l) :
    handleCoreHomotopy k l (t, (TopCat.diskBoundaryInclusion k s, y)) =
      (TopCat.diskBoundaryInclusion k s, y) :=
  (handleCoreHomotopy k l).eq_fst (x := (TopCat.diskBoundaryInclusion k s, y)) t
    (Or.inl (norm_diskBoundaryInclusion s))

/-- The homotopy `TauCeti.TopCat.handleCoreHomotopy` fixes the core of the handle. -/
@[simp]
theorem handleCoreHomotopy_diskCenter (t : I) (x : TopCat.disk.{u} k) :
    handleCoreHomotopy k l (t, (x, diskCenter l)) = (x, diskCenter l) :=
  (handleCoreHomotopy k l).eq_fst (x := (x, diskCenter l)) t (Or.inr rfl)

end Retraction

section Attachment

variable {k l : ℕ}

/-- On the union of the attaching region `∂D^k × D^l` and the core `D^k × {0}` of a handle, the
map to a space `Q` given by `a` on the attaching region and by `c` on the core. Off that union it
is `c` of the first coordinate, a value that plays no role. -/
private def coreAttachmentValue {Q : Type*} (a : TopCat.diskBoundary.{u} k × TopCat.disk.{u} l → Q)
    (c : TopCat.disk.{u} k → Q) (p : TopCat.disk.{u} k × TopCat.disk.{u} l) : Q :=
  if h : ‖p.1.down.1‖ = 1 then a (ULift.up ⟨p.1.down.1, mem_sphere_zero_iff_norm.2 h⟩, p.2)
  else c p.1

/-- On the attaching region, `coreAttachmentValue a c` is `a`. -/
private lemma coreAttachmentValue_diskBoundaryInclusion {Q : Type*}
    (a : TopCat.diskBoundary.{u} k × TopCat.disk.{u} l → Q) (c : TopCat.disk.{u} k → Q)
    (s : TopCat.diskBoundary.{u} k) (y : TopCat.disk.{u} l) :
    coreAttachmentValue a c (TopCat.diskBoundaryInclusion k s, y) = a (s, y) := by
  simp only [coreAttachmentValue, norm_diskBoundaryInclusion, ↓reduceDIte]
  rfl

/-- On the core, `coreAttachmentValue a c` is `c`, when `a` and `c` agree on the core sphere. -/
private lemma coreAttachmentValue_diskCenter {Q : Type*}
    {a : TopCat.diskBoundary.{u} k × TopCat.disk.{u} l → Q} {c : TopCat.disk.{u} k → Q}
    (hac : ∀ s, a (s, diskCenter l) = c (TopCat.diskBoundaryInclusion k s))
    (x : TopCat.disk.{u} k) : coreAttachmentValue a c (x, diskCenter l) = c x := by
  rw [coreAttachmentValue]
  split_ifs with h
  · exact hac _
  · rfl

/-- `coreAttachmentValue a c` is continuous on the union of the attaching region and the core. -/
private lemma continuousOn_coreAttachmentValue {Q : Type*} [TopologicalSpace Q]
    {a : TopCat.diskBoundary.{u} k × TopCat.disk.{u} l → Q} {c : TopCat.disk.{u} k → Q}
    (ha : Continuous a) (hc : Continuous c)
    (hac : ∀ s, a (s, diskCenter l) = c (TopCat.diskBoundaryInclusion k s)) :
    ContinuousOn (coreAttachmentValue a c) {p | ‖p.1.down.1‖ = 1 ∨ p.2 = diskCenter l} := by
  have hx : Continuous fun p : TopCat.disk.{u} k × TopCat.disk.{u} l ↦ ‖p.1.down.1‖ :=
    continuous_norm.comp (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_fst))
  have hS : IsClosed {p : TopCat.disk.{u} k × TopCat.disk.{u} l | ‖p.1.down.1‖ = 1} :=
    isClosed_eq hx continuous_const
  have hC : IsClosed {p : TopCat.disk.{u} k × TopCat.disk.{u} l | p.2 = diskCenter l} :=
    isClosed_eq continuous_snd continuous_const
  refine ContinuousOn.union_of_isClosed ?_ ?_ hS hC
  · -- On the attaching region the value is `a`, read through the boundary sphere.
    rw [continuousOn_iff_continuous_domRestrict]
    have hσ : Continuous fun p : {p : TopCat.disk.{u} k × TopCat.disk.{u} l | ‖p.1.down.1‖ = 1} ↦
        ((ULift.up ⟨p.1.1.down.1, mem_sphere_zero_iff_norm.2 p.2⟩ : TopCat.diskBoundary.{u} k),
          p.1.2) := by
      refine Continuous.prodMk (continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)) (by fun_prop)
      fun_prop
    refine (ha.comp hσ).congr fun p ↦ ?_
    simp only [Set.domRestrict_apply, coreAttachmentValue]
    split_ifs with h
    · rfl
    · exact absurd p.2 h
  · -- On the core the value is `c` of the first coordinate.
    refine (hc.comp continuous_fst).continuousOn.congr fun p hp ↦ ?_
    obtain ⟨x, y⟩ := p
    obtain rfl : y = diskCenter l := hp
    exact coreAttachmentValue_diskCenter hac x

end Attachment

end TauCeti.TopCat

namespace CategoryTheory.IsPushout

open TauCeti TauCeti.TopCat

section HandleAttachment

variable {ι : Type u} {k l : ι → ℕ} {X P Q : _root_.TopCat.{u}}
  {α : ∀ i, _root_.TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (l i)) ⟶ X}
  {j : X ⟶ P} {χ : ∀ i, _root_.TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)) ⟶ P}
  {j' : X ⟶ Q} {χ' : ∀ i, TopCat.disk.{u} (k i) ⟶ Q}

/-- The pushout square of a handle attachment, read at a point of an attaching region. -/
private lemma handle_w_apply
    (hP : IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) j (Sigma.desc χ))
    (i : ι) (s : TopCat.diskBoundary.{u} (k i)) (y : TopCat.disk.{u} (l i)) :
    j (α i (s, y)) = χ i (TopCat.diskBoundaryInclusion (k i) s, y) := by
  simpa using ConcreteCategory.congr_hom (Sigma.ι (fun i ↦ _root_.TopCat.of
    (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (l i))) i ≫= hP.w) (s, y)

/-- The homotopy of a handle attachment `P` which is constant on `X` and is
`TauCeti.TopCat.handleCoreHomotopy` on each handle. -/
private lemma exists_handleAttachment_homotopy
    (hP : IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) j (Sigma.desc χ)) :
    ∃ K : C(I × P, P), (∀ t x, K (t, j x) = j x) ∧
      ∀ t i p, K (t, χ i p) = χ i (handleCoreHomotopy (k i) (l i) (t, p)) := by
  refine ⟨hP.cylinderDesc (j.hom.comp ContinuousMap.snd)
    (_root_.TopCat.sigmaCylinderDesc fun i ↦
      (χ i).hom.comp (handleCoreHomotopy (k i) (l i)).toContinuousMap)
    (fun t b ↦ ?_), hP.cylinderDesc_inl _ _ _, fun t i p ↦ ?_⟩
  · -- Both pieces are constant on the attaching regions.
    obtain ⟨i, ⟨s, y⟩, rfl⟩ := _root_.TopCat.exists_sigma_ι_eq _ b
    have h₁ : Sigma.desc α (Sigma.ι (fun i ↦ _root_.TopCat.of
        (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (l i))) i (s, y)) = α i (s, y) := by
      simp
    have h₂ : (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
        ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _)))
        (Sigma.ι (fun i ↦ _root_.TopCat.of
          (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (l i))) i (s, y)) =
        Sigma.ι (fun i ↦ _root_.TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i
          (TopCat.diskBoundaryInclusion _ s, y) := by
      simp [Sigma.ι_map_apply]
    simp only [ContinuousMap.comp_apply, ContinuousMap.snd_apply]
    rw [h₁, h₂, _root_.TopCat.sigmaCylinderDesc_ι, ContinuousMap.comp_apply,
      ContinuousMap.HomotopyWith.coe_toContinuousMap, handleCoreHomotopy_diskBoundaryInclusion]
    exact handle_w_apply hP i s y
  · have hp : Sigma.desc χ (Sigma.ι (fun i ↦
        _root_.TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i p) = χ i p := by
      simp
    rw [← hp, hP.cylinderDesc_inr, _root_.TopCat.sigmaCylinderDesc_ι]
    rfl

/-- The collapse of a handle attachment `P` onto the attachment `Q` of the cores: `j'` on `X`, and
on each handle the core retraction followed by `α i` on the attaching region and by the
characteristic map `χ' i` of the cell on the core. -/
private lemma exists_handleAttachment_collapse
    (hP : IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) j (Sigma.desc χ))
    (hwQ : ∀ i s, j' (α i (s, diskCenter (l i))) = χ' i (TopCat.diskBoundaryInclusion (k i) s)) :
    ∃ g : P ⟶ Q, (∀ x, g (j x) = j' x) ∧ ∀ i p, g (χ i p) =
      coreAttachmentValue (fun p ↦ j' (α i p)) (χ' i) (handleCoreRetraction (k i) (l i) p) := by
  obtain ⟨G, hG⟩ : ∃ G : ∀ i, C(TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i), Q),
      ∀ i p, G i p = coreAttachmentValue (fun p ↦ j' (α i p)) (χ' i)
        (handleCoreRetraction (k i) (l i) p) :=
    ⟨fun i ↦ ⟨_, (continuousOn_coreAttachmentValue (j'.hom.continuous.comp (α i).hom.continuous)
        (χ' i).hom.continuous (hwQ i)).comp_continuous (handleCoreRetraction _ _).continuous
        fun p ↦ handleCoreRetraction_mem p⟩, fun _ _ ↦ rfl⟩
  have hw : Sigma.desc α ≫ j' = (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) ≫
        Sigma.desc fun i ↦ _root_.TopCat.ofHom (G i) := Sigma.hom_ext _ _ fun i ↦ by
    ext ⟨s, y⟩
    have h : G i (TopCat.diskBoundaryInclusion _ s, y) = j' (α i (s, y)) := by
      rw [hG, handleCoreRetraction_diskBoundaryInclusion,
        coreAttachmentValue_diskBoundaryInclusion]
    simpa [Sigma.ι_map_apply] using h.symm
  obtain ⟨g, hgj, hgχ⟩ : ∃ g : P ⟶ Q, j ≫ g = j' ∧
      Sigma.desc χ ≫ g = Sigma.desc fun i ↦ _root_.TopCat.ofHom (G i) :=
    ⟨hP.desc _ _ hw, hP.inl_desc _ _ hw, hP.inr_desc _ _ hw⟩
  refine ⟨g, fun x ↦ ConcreteCategory.congr_hom hgj x, fun i p ↦ ?_⟩
  rw [← hG]
  simpa using ConcreteCategory.congr_hom hgχ (Sigma.ι (fun i ↦
    _root_.TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i))) i p)

/-- **A handle attachment deformation retracts onto the attachment of its cores.** Let `P` be
obtained from `X` by attaching handles `D^{k i} × D^{l i}` along maps
`α i : ∂D^{k i} × D^{l i} → X` of their attaching regions, with characteristic maps `χ i`, and let
`Q` be obtained from `X` by attaching disks `D^{k i}` along the restrictions
`s ↦ α i (s, 0)` of the `α i` to the core spheres, with characteristic maps `χ' i`; both are
pushouts in `TopCat`. Then the comparison map `Φ : Q → P`, which is the inclusion of `X` and
sends the `i`-th disk onto the core `D^{k i} × {0}` of the `i`-th handle, has image the union of
`X` and of the cores, and it has a left inverse `g` such that `Φ ∘ g` is homotopic to the identity
of `P` relative to that image. In particular `Φ` is a homotopy equivalence relative to `X`. -/
theorem exists_coreAttachment_deformation
    (hP : IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _))) j (Sigma.desc χ))
    (hQ : IsPushout (Sigma.desc fun i ↦ _root_.TopCat.ofHom
      ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (diskCenter (l i)))) ≫ α i)
      (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion (k i)) j' (Sigma.desc χ')) :
    ∃ (Φ : Q ⟶ P) (g : C(P, Q)), j' ≫ Φ = j ∧
      (∀ i, χ' i ≫ Φ = _root_.TopCat.ofHom
        ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (diskCenter (l i)))) ≫ χ i) ∧
      range Φ = range j ∪ ⋃ i, range (fun x ↦ χ i (x, diskCenter (l i))) ∧
      LeftInverse g Φ ∧ (ContinuousMap.id P).HomotopicRel (Φ.hom.comp g) (range Φ) := by
  have hwQ (i : ι) (s : TopCat.diskBoundary.{u} (k i)) :
      j' (α i (s, diskCenter (l i))) = χ' i (TopCat.diskBoundaryInclusion (k i) s) := by
    simpa using ConcreteCategory.congr_hom
      (Sigma.ι (fun i ↦ TopCat.diskBoundary.{u} (k i)) i ≫= hQ.w) s
  -- The comparison map `Φ : Q → P`, the retraction `g : P → Q` and the homotopy `K` on `P`.
  obtain ⟨Φ, hΦj', hΦχ'⟩ : ∃ Φ : Q ⟶ P, j' ≫ Φ = j ∧ Sigma.desc χ' ≫ Φ =
      Sigma.desc fun i ↦ _root_.TopCat.ofHom
        ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (diskCenter (l i)))) ≫ χ i :=
    ⟨hQ.desc _ _ (Sigma.hom_ext _ _ fun i ↦ by
      ext s
      simpa using handle_w_apply hP i s (diskCenter (l i))), hQ.inl_desc _ _ _,
      hQ.inr_desc _ _ _⟩
  have hΦj (x : X) : Φ (j' x) = j x := ConcreteCategory.congr_hom hΦj' x
  have hΦχ (i : ι) (x : TopCat.disk.{u} (k i)) : Φ (χ' i x) = χ i (x, diskCenter (l i)) := by
    simpa using ConcreteCategory.congr_hom hΦχ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i x)
  have hcore (i : ι) (x : TopCat.disk.{u} (k i)) :
      coreAttachmentValue (fun p ↦ j' (α i p)) (χ' i) (x, diskCenter (l i)) = χ' i x :=
    coreAttachmentValue_diskCenter (hwQ i) x
  obtain ⟨g, hgj, hgχ⟩ := exists_handleAttachment_collapse hP hwQ
  obtain ⟨K, hKj, hKχ⟩ := exists_handleAttachment_homotopy hP
  -- On the union of the attaching region and the core, `Φ` undoes the collapse of a handle.
  have hΦG (i : ι) {p : TopCat.disk.{u} (k i) × TopCat.disk.{u} (l i)}
      (hp : ‖p.1.down.1‖ = 1 ∨ p.2 = diskCenter (l i)) :
      Φ (coreAttachmentValue (fun p ↦ j' (α i p)) (χ' i) p) = χ i p := by
    obtain ⟨x, y⟩ := p
    rcases hp with hx | rfl
    · simp only [coreAttachmentValue, hx, ↓reduceDIte]
      rw [hΦj]
      exact handle_w_apply hP i _ y
    · rw [hcore, hΦχ]
  refine ⟨Φ, g.hom, hΦj', fun i ↦ ?_, ?_, fun q ↦ ?_,
    ⟨⟨⟨K, fun p ↦ ?_, fun p ↦ ?_⟩, fun t p hp ↦ ?_⟩⟩⟩
  · ext x
    exact hΦχ i x
  · -- The image of `Φ`: every point of `Q` comes from `X` or from a disk.
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      rcases exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma hQ q with
        ⟨x, rfl⟩ | ⟨i, x, rfl⟩
      · exact Or.inl ⟨x, (hΦj x).symm⟩
      · refine Or.inr (mem_iUnion.2 ⟨i, x, ?_⟩)
        simp [hΦχ]
    · rintro (⟨x, rfl⟩ | hp)
      · exact ⟨j' x, hΦj x⟩
      · obtain ⟨i, x, rfl⟩ := mem_iUnion.1 hp
        exact ⟨χ' i x, hΦχ i x⟩
  · -- `g` inverts `Φ` on the two legs of `Q`.
    have h : g.hom.comp Φ.hom = ContinuousMap.id Q := hQ.continuousMap_ext
      (fun x ↦ by simp [hΦj, hgj]) fun z ↦ by
        obtain ⟨i, x, rfl⟩ := _root_.TopCat.exists_sigma_ι_eq _ z
        simp [hΦχ, hgχ, hcore]
    exact congrArg (fun f : C(Q, Q) ↦ f q) h
  · -- At time `0` the homotopy is the identity.
    have h : (⟨fun p ↦ K (0, p), by fun_prop⟩ : C(P, P)) = ContinuousMap.id P :=
      hP.continuousMap_ext (fun x ↦ hKj 0 x) fun z ↦ by
        obtain ⟨i, x, rfl⟩ := _root_.TopCat.exists_sigma_ι_eq _ z
        simp [hKχ]
    exact congrArg (fun f : C(P, P) ↦ f p) h
  · -- At time `1` it is the core retraction followed by `Φ`.
    have h : (⟨fun p ↦ K (1, p), by fun_prop⟩ : C(P, P)) = Φ.hom.comp g.hom :=
      hP.continuousMap_ext (fun x ↦ by simp [hKj, hgj, hΦj]) fun z ↦ by
        obtain ⟨i, x, rfl⟩ := _root_.TopCat.exists_sigma_ι_eq _ z
        simp [hKχ, hgχ, hΦG i (handleCoreRetraction_mem x)]
    exact congrArg (fun f : C(P, P) ↦ f p) h
  · -- The homotopy fixes the image of `Φ`: the points of `X` and of the cores.
    obtain ⟨q, rfl⟩ := hp
    -- The goal is stated for the time-`t` slice of `K` as a bundled map.
    change K (t, Φ q) = Φ q
    rcases exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma hQ q with
      ⟨x, rfl⟩ | ⟨i, x, rfl⟩
    · rw [hΦj, hKj]
    · have hx : Sigma.desc χ' (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i x) = χ' i x := by simp
      rw [hx, hΦχ, hKχ, handleCoreHomotopy_diskCenter]

end HandleAttachment

end CategoryTheory.IsPushout
