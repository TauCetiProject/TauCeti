/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Inclusion
public import TauCeti.Topology.FiberBundle.Principal.Reduction
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.UnitSection
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic
import TauCeti.Data.Bundle
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Inclusion

/-!
# Points of a `Spinᶜ` structure adapted to a unit section

Let `s` be a `Spinᶜ` structure of rank `n + 1` on a vector bundle `E` with fibre inner products,
with principal `Spinᶜ(n + 1)`-bundle `P` and frame map `P → Fr(E)`, and let `σ` be a section of
unit vectors of `E`. The points of `P` whose frames send the last coordinate vector `e_{n+1}` of
`ℝⁿ⁺¹` to `σ` form the set `TauCeti.SpinCStructure.sectionPoints s σ`: the preimage under the frame
map of the frames adapted to `σ` (`TauCeti.OrthonormalFrameBundle.sectionFrames`).

For `E = W ⊕ ℝ` with the unit section of the trivial summand, these points are the structure-group
step of restricting `s` to a `Spinᶜ` structure on `W`, as on the boundary of a manifold: an element
`g` of `Spinᶜ(n + 1)` keeps an adapted point adapted exactly when its rotation fixes `e_{n+1}`
(`TauCeti.SpinCStructure.smul_mem_sectionPoints_iff`), that is, when `g` lies in the last-vector
stabilizer `CliffordAlgebra.realCliffordSpinCLastStabilizer n`, the image of
`Spinᶜ(n) ⊆ Spinᶜ(n + 1)` (`CliffordAlgebra.range_realCliffordSpinCInclusion`).

For a continuous section of unit vectors, the adapted points are locally trivial with fibre this
stabilizer, equivariantly (`TauCeti.SpinCStructure.exists_trivialization_sectionPoints`). Near a
point `x`, a trivialization of `P` gives a continuous local section `p`; the section `σ` read in
the frames of `p` is a continuous family `u` of unit vectors of `ℝⁿ⁺¹`; a continuous family `g` of
elements of `Spinᶜ(n + 1)` whose rotations carry `e_{n+1}` to `u`
(`CliffordAlgebra.exists_continuousOn_realCliffordSpinCGroupZero_toSpecialOrthogonal_last`)
corrects `p` to the adapted local section `p • g`; and the adapted points are then trivial near
`x` (`TauCeti.PrincipalBundle.exists_trivialization_of_continuousOn_section_mem`).

The adapted points as a principal bundle, and the frames of `W` they carry, are not constructed
here.

## Main definitions

* `TauCeti.SpinCStructure.sectionPoints s σ`: the points of `s` whose frames send the last
  coordinate vector to `σ`.

## Main results

* `TauCeti.SpinCStructure.smul_mem_sectionPoints_iff`: `Spinᶜ(n + 1)` keeps an adapted point
  adapted exactly through the last-vector stabilizer.
* `TauCeti.SpinCStructure.exists_trivialization_sectionPoints`: for a continuous unit section the
  adapted points are locally trivial with fibre the stabilizer, equivariantly.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §2 (restriction of Spin structures to hypersurfaces).
-/

public section

noncomputable section

open Bundle CliffordAlgebra MulOpposite Set
open scoped RealInnerProductSpace

namespace TauCeti.SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ} (s : SpinCStructure F E (n + 1)) (σ : ∀ x, E x)

/-- The points of a `Spinᶜ` structure of rank `n + 1` whose frames send the last coordinate vector
of `ℝⁿ⁺¹` to the section `σ`. -/
def sectionPoints : Set (TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P) :=
  s.toFrame ⁻¹'
    OrthonormalFrameBundle.sectionFrames F σ
      (WithLp.toLp 2 (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ))

variable {s σ}

/-- A point is adapted to `σ` when its frame sends the last coordinate vector to `σ`. -/
@[simp]
theorem mem_sectionPoints_iff {p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P} :
    p ∈ s.sectionPoints σ ↔
      (s.toFrame p).frame (WithLp.toLp 2 (Pi.single (Fin.last n) 1)) = σ (s.toFrame p).proj :=
  OrthonormalFrameBundle.mem_sectionFrames_iff

/-- A point `p` over `x` is adapted exactly when its frame, as a point of the total space of `E`,
sends the last coordinate vector to `σ x`. -/
private theorem mk_mem_sectionPoints_iff {x : X} {p : s.P x} :
    (⟨x, p⟩ : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P) ∈ s.sectionPoints σ ↔
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
          ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (Pi.single (Fin.last n) 1))) =
        ⟨x, σ x⟩ := by
  rw [mem_sectionPoints_iff, TotalSpace.mk_eq_mk_iff_of_eq σ (s.proj_toFrame _)]

/-- **The stabilizer of the adapted points.** An element `g` of `Spinᶜ(n + 1)` keeps a point
adapted to `σ` adapted exactly when its rotation fixes the last coordinate vector, that is, when
it lies in the last-vector stabilizer, the image of `Spinᶜ(n)`. -/
theorem smul_mem_sectionPoints_iff {p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P}
    (hp : p ∈ s.sectionPoints σ) (g : realCliffordSpinCGroupZero (n + 1)) :
    op g • p ∈ s.sectionPoints σ ↔ g ∈ realCliffordSpinCLastStabilizer n := by
  obtain ⟨x, p⟩ := p
  rw [mk_mem_sectionPoints_iff] at hp
  rw [TotalSpace.smul_mk, mk_mem_sectionPoints_iff, s.toFrame_smul_toSpecialOrthogonal, ← hp,
    TotalSpace.mk_inj, (s.toFrame ⟨x, p⟩).frame.injective.eq_iff,
    (WithLp.toLp_injective 2).eq_iff, mem_realCliffordSpinCLastStabilizer_iff]

/-! ### Local triviality -/

section Trivialization

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]

variable (s σ) in
/-- The section `σ` read in the frame of a point `p`: the coordinate vector in `ℝⁿ⁺¹` of the value
of `σ` at the base point. -/
private def coords (p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P) : Fin (n + 1) → ℝ :=
  WithLp.ofLp ((s.toFrame p).frame.symm (σ (s.toFrame p).proj))

/-- The coordinates of a continuous section in the frames of a `Spinᶜ` structure are continuous,
by `TauCeti.OrthonormalFrameBundle.continuous_frame_symm_apply`. -/
private theorem continuous_coords (hσ : Continuous fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) :
    Continuous (coords s σ) :=
  (PiLp.continuous_ofLp 2 _).comp
    ((OrthonormalFrameBundle.continuous_frame_symm_apply hσ).comp s.continuous_toFrame)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] in
/-- For a section of unit vectors, the coordinates in a frame form a unit vector. -/
private theorem realCliffordForm_coords (hσ₁ : ∀ y, ‖σ y‖ = 1)
    (p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P) :
    realCliffordForm (n + 1) 0 (coords s σ p) = 1 := by
  have h := congrArg (· ^ 2) (((s.toFrame p).frame.symm.norm_map _).trans (hσ₁ _))
  simp only [one_pow, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] at h
  rw [realCliffordForm_apply, ← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [realCliffordWeight_of_lt (by simpa using i.isLt), one_mul, sq, coords]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] in
/-- The frame of a point sends its coordinate vector of `σ` to `σ`. -/
private theorem frame_coords (p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P) :
    (s.toFrame p).frame (WithLp.toLp 2 (coords s σ p)) = σ (s.toFrame p).proj := by
  simp [coords]

variable [NeZero n]

/-- **The points adapted to a continuous unit section are locally trivial.** For a `Spinᶜ` structure
of rank `n + 1 ≥ 2` and a continuous section `σ` of unit vectors, the points whose frames send the
last coordinate vector to `σ` are locally trivial with fibre the last-vector stabilizer
`Spinᶜ(n) ⊆ Spinᶜ(n + 1)`, by trivializations equivariant for its right action. -/
theorem exists_trivialization_sectionPoints
    (hσ : Continuous fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) (hσ₁ : ∀ y, ‖σ y‖ = 1) (x : X) :
    ∃ t : Trivialization (realCliffordSpinCLastStabilizer n)
        (fun p : s.sectionPoints σ ↦
          (p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P).proj),
      x ∈ t.baseSet ∧ ∀ (g : realCliffordSpinCLastStabilizer n) (p : s.sectionPoints σ)
        (hgp : op (g : realCliffordSpinCGroupZero (n + 1)) •
          (p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P) ∈ s.sectionPoints σ),
        (p : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P).proj ∈ t.baseSet →
          t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g) := by
  let t₀ := trivializationAt (realCliffordSpinCGroupZero (n + 1)) s.P x
  have hx : x ∈ t₀.baseSet := mem_baseSet_trivializationAt _ _ x
  -- The local section of `P` given by `t₀`.
  let τ₀ : ∀ y, s.P y := fun y ↦ t₀.symm y 1
  have hτ₀ : ContinuousOn (fun y ↦ TotalSpace.mk' (realCliffordSpinCGroupZero (n + 1)) y (τ₀ y))
      t₀.baseSet :=
    t₀.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
      fun _ hy ↦ ⟨hy, mem_univ _⟩
  -- The section `σ` read in its frames, as a unit vector of `ℝⁿ⁺¹`.
  let u : X → {v : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 v = 1} := fun y ↦
    ⟨coords s σ ⟨y, τ₀ y⟩, realCliffordForm_coords hσ₁ _⟩
  have hu : ContinuousOn u t₀.baseSet := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact ((continuous_coords hσ).comp_continuousOn hτ₀).domRestrict.subtype_mk _
  -- Rotations carrying the last coordinate vector to `u`, lifted to `Spinᶜ(n + 1)`.
  obtain ⟨U, hU, hxU, g, hg, hgu⟩ :=
    exists_continuousOn_realCliffordSpinCGroupZero_toSpecialOrthogonal_last n (u x)
  let V := t₀.baseSet ∩ u ⁻¹' U
  have hV : IsOpen V := hu.isOpen_inter_preimage t₀.open_baseSet hU
  -- The corrected local section `τ₀ • g ∘ u` is adapted.
  have hτ : ContinuousOn (fun y ↦ TotalSpace.mk' (realCliffordSpinCGroupZero (n + 1)) y
      (op (g (u y)) • τ₀ y)) V :=
    ContinuousOn.totalSpaceMk_smul (f := id) (p := τ₀) (hτ₀.mono inter_subset_left)
      (hg.comp (hu.mono inter_subset_left) fun _ hy ↦ hy.2)
  have hτS (y : X) (hy : y ∈ V) :
      (⟨y, op (g (u y)) • τ₀ y⟩ : TotalSpace (realCliffordSpinCGroupZero (n + 1)) s.P) ∈
        s.sectionPoints σ := by
    rw [mk_mem_sectionPoints_iff, s.toFrame_smul_toSpecialOrthogonal, hgu (u y) hy.2,
      frame_coords, s.proj_toFrame]
  obtain ⟨t, ht, hteq⟩ := TauCeti.PrincipalBundle.exists_trivialization_of_continuousOn_section_mem
    (H := realCliffordSpinCLastStabilizer n) (fun p hp g ↦ smul_mem_sectionPoints_iff hp g) hτS
    hV hτ (b := x) ⟨hx, hxU⟩
  exact ⟨t, ht ▸ ⟨hx, hxU⟩, fun g p hgp hp ↦ hteq g p hgp (ht ▸ hp)⟩

end Trivialization

end TauCeti.SpinCStructure
