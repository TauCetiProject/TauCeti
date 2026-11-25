/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Little.OpenSet
public import TauCeti.Geometry.Manifold.VectorBundle.Holder.ContMDiffSection

/-!
# Little Hölder spaces of sections of a vector bundle

Let `V → M` be a smooth real vector bundle over a smooth manifold without boundary, and let `A`
be a finite bundle atlas, so that the Hölder space `C^{k,α}(V)` of `TauCeti.HolderSection A k α`
is defined. The **little Hölder space** `h^{k,α}(V)` (`TauCeti.HolderSection.littleHolder`) is
the closure in `C^{k,α}(V)` of the smooth sections (`TauCeti.HolderSection.smoothSections`). It
is a closed subspace, hence a Banach space when the model fibre is, and the smooth sections are
dense in it by construction. When the model fibre is complete, it is the completion of the smooth
sections in the `C^{k,α}` norm.
For `α ≤ 1` the smooth sections in `C^{k,α}(V)` are exactly the images of the smooth sections of
`V` under `TauCeti.HolderSection.ofContMDiffSection`.

For `α < 1`, every element of `h^{k,α}(V)` has, in every chart of `A`, a reading in the little
Hölder space `h^{k,α}(A.image i)` of `TauCeti.CkHolderSpaceOn.littleHolder`: its `k`-th
derivative has vanishing small-scale `α`-Hölder modulus on the chart image
(`TauCeti.HolderSection.mem_littleHolder_component_of_mem_littleHolder`). Indeed the readings of a
smooth section are `C^{k,1}`, hence little `α`-Hölder, and the little Hölder condition is closed.

## Main declarations

* `TauCeti.HolderSection.smoothSections A k α`: the elements of `C^{k,α}(V)` whose underlying
  section is smooth.
* `TauCeti.HolderSection.littleHolder A k α`: the little Hölder space `h^{k,α}(V)`, their closure.
* `TauCeti.HolderSection.isClosed_littleHolder` and
  `TauCeti.HolderSection.instCompleteSpaceLittleHolder`: it is a Banach space.
* `TauCeti.HolderSection.range_ofContMDiffSection`: for `α ≤ 1`, the smooth sections of
  `C^{k,α}(V)` are the images of the smooth sections of `V`.
* `TauCeti.HolderSection.mem_littleHolder_component_of_mem_littleHolder`: for `α < 1`, the chart
  readings of an element of `h^{k,α}(V)` have vanishing small-scale Hölder modulus.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13.
* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Birkhäuser
  (1995), Chapter 0, for little Hölder spaces as closures of smooth functions.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold NNReal ContDiff

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V) (k : ℕ) (α : ℝ≥0)

namespace HolderSection

/-- The **smooth elements** of `C^{k,α}(V)`: those whose underlying section is smooth. -/
def smoothSections : Submodule ℝ (HolderSection A k α) where
  carrier := {w | ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
    fun x ↦ TotalSpace.mk' F x (toSection w x)}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact contMDiff_zeroSection ℝ V
  add_mem' {w w'} hw hw' := by
    simpa only [Set.mem_ofPred_eq, map_add] using hw.add_section hw'
  smul_mem' c w hw := by
    simpa only [Set.mem_ofPred_eq, map_smul] using hw.const_smul_section (a := c)

/-- The **little Hölder space** `h^{k,α}(V)` of sections: the closure of the smooth sections in
`C^{k,α}(V)`. -/
def littleHolder : Submodule ℝ (HolderSection A k α) :=
  (smoothSections A k α).topologicalClosure

variable {A k α}

/-- Membership in the smooth sections of `C^{k,α}(V)`. -/
@[simp]
theorem mem_smoothSections_iff {w : HolderSection A k α} :
    w ∈ smoothSections A k α ↔
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ fun x ↦ TotalSpace.mk' F x (toSection w x) :=
  Iff.rfl

/-- The little Hölder space of sections is the closure of the smooth sections. -/
theorem littleHolder_def : littleHolder A k α = (smoothSections A k α).topologicalClosure :=
  (rfl)

/-- **Density.** The smooth sections are dense in the little Hölder space: its underlying set is
their closure. -/
theorem coe_littleHolder :
    (littleHolder A k α : Set (HolderSection A k α)) = closure (smoothSections A k α) :=
  Submodule.topologicalClosure_coe _

/-- Smooth sections lie in the little Hölder space. -/
theorem smoothSections_le_littleHolder : smoothSections A k α ≤ littleHolder A k α :=
  Submodule.le_topologicalClosure _

variable (A k α) in
/-- **The little Hölder space of sections is closed** in `C^{k,α}(V)`. -/
theorem isClosed_littleHolder : IsClosed (littleHolder A k α : Set (HolderSection A k α)) :=
  Submodule.isClosed_topologicalClosure _

/-- The little Hölder space of sections of a bundle with Banach model fibre is a Banach space. -/
instance instCompleteSpaceLittleHolder [CompleteSpace F] : CompleteSpace (littleHolder A k α) :=
  (isClosed_littleHolder A k α).completeSpace_coe

variable [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

/-- For `α ≤ 1`, the smooth sections of `C^{k,α}(V)` are the images of the smooth sections of
`V`. -/
theorem range_ofContMDiffSection (hα : α ≤ 1) :
    LinearMap.range (ofContMDiffSection A (n := ∞) (k := k) (by simp) hα) =
      smoothSections A k α := by
  ext w
  constructor
  · rintro ⟨s, rfl⟩
    rw [mem_smoothSections_iff, toSection_ofContMDiffSection]
    exact s.contMDiff
  · intro hw
    refine ⟨⟨toSection w, hw⟩, ext ?_⟩
    rw [toSection_ofContMDiffSection]
    rfl

/-- For `α ≤ 1`, the image in `C^{k,α}(V)` of a smooth section of `V` lies in the little Hölder
space. -/
theorem ofContMDiffSection_mem_littleHolder (hα : α ≤ 1) (s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯) :
    ofContMDiffSection A (by simp) hα s ∈ littleHolder A k α :=
  smoothSections_le_littleHolder <| (range_ofContMDiffSection hα).le ⟨s, rfl⟩

/-- For `α < 1`, the chart readings of a smooth element of `C^{k,α}(V)` lie in the little Hölder
spaces of the chart images: they are `C^{k,1}` there. -/
theorem mem_littleHolder_component_of_mem_smoothSections (hα : α < 1)
    {w : HolderSection A k α} (hw : w ∈ smoothSections A k α) (i : Fin A.n) :
    (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i ∈
      CkHolderSpaceOn.littleHolder k α (A.image i) F := by
  obtain ⟨g, hg⟩ := A.memHolderSection_iff.1
    (A.memHolderSection_of_contMDiff (k := k) (α := 1) (by simp) le_rfl hw) i
  refine CkHolderSpaceOn.mem_littleHolder_of_memHolder hα ?_
  rw [CkHolderSpaceOn.iteratedFDeriv_eq_of_coe_eq fun x ↦ by rw [hg, coord_toSection]]
  exact g.memHolder_iteratedFDeriv

/-- **Vanishing small-scale modulus.** For `α < 1`, every chart reading of an element of the
little Hölder space `h^{k,α}(V)` lies in the little Hölder space of the chart image: its `k`-th
derivative has `α`-Hölder difference quotients tending to zero at small scales. -/
theorem mem_littleHolder_component_of_mem_littleHolder (hα : α < 1)
    {w : HolderSection A k α} (hw : w ∈ littleHolder A k α) (i : Fin A.n) :
    (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i ∈
      CkHolderSpaceOn.littleHolder k α (A.image i) F := by
  have hcl : IsClosed {w : HolderSection A k α |
      (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i ∈
        CkHolderSpaceOn.littleHolder k α (A.image i) F} :=
    CkHolderSpaceOn.isClosed_littleHolder.preimage
      ((continuous_apply i).comp continuous_subtypeVal)
  rw [← SetLike.mem_coe, coe_littleHolder] at hw
  exact (hcl.closure_subset_iff.2 fun w hw ↦
    mem_littleHolder_component_of_mem_smoothSections hα hw i) hw

end HolderSection

end TauCeti
