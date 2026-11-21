/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TwoSidedIdeal.Annihilator
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal.Basic

/-!
# Closedness of annihilators of two-sided ideals

Closedness of left and right annihilators (and `Module.annihilator`) in `T₁` rings with separately
continuous multiplication, and preservation of annihilators under `topologicalClosure`.
-/

public section

namespace TwoSidedIdeal

section Annihilator

variable {A : Type*} [NonUnitalRing A] [TopologicalSpace A] [SeparatelyContinuousMul A]
  [T1Space A]

/-- The annihilator of a two-sided ideal of a `T₁` ring with separately continuous multiplication
is closed. -/
instance isClosed_annihilator (I : TwoSidedIdeal A) : IsClosed (I.annihilator : Set A) := by
  have hset : (I.annihilator : Set A) = ⋂ x ∈ I, (· * x) ⁻¹' {0} := by
    ext a
    simp
  rw [hset]
  exact isClosed_biInter fun x _ ↦ isClosed_singleton.preimage (continuous_mul_const x)

/-- In a `T₁` topological proper star ring, a self-adjoint ideal is essential exactly when it meets
every nonzero closed two-sided ideal. -/
theorem isEssential_iff_forall_isClosed [StarRing A] [IsProperStar A] {I : TwoSidedIdeal A}
    (hI : ∀ x ∈ I, star x ∈ I) :
    I.IsEssential ↔ ∀ J : TwoSidedIdeal A, IsClosed (J : Set A) → Disjoint I J → J = ⊥ :=
  ⟨fun h _ _ ↦ h.eq_bot_of_disjoint, fun h ↦ (annihilator_eq_bot_iff_isEssential hI).mp <|
    h _ (isClosed_annihilator I) (disjoint_annihilator hI)⟩

end Annihilator

section ClosedAnnihilator

variable {A : Type*} [NonUnitalRing A] [TopologicalSpace A]

/-- In a `T₁` space with separately continuous multiplication, the right annihilator of any
two-sided ideal is closed. -/
instance isClosed_rightAnnihilator [SeparatelyContinuousMul A] [T1Space A] (I : TwoSidedIdeal A) :
    IsClosed (I.rightAnnihilator : Set A) := by
  have hset : (I.rightAnnihilator : Set A) = ⋂ x ∈ (I : Set A), (x * ·) ⁻¹' {0} := by
    ext a
    simp [mem_rightAnnihilator]
  rw [hset]
  exact isClosed_biInter fun x _ => isClosed_singleton.preimage (continuous_const_mul x)

/-- Taking topological closure does not change the left annihilator of a two-sided ideal. -/
@[simp]
theorem annihilator_topologicalClosure [IsTopologicalRing A] [T1Space A]
    (I : TwoSidedIdeal A) :
    I.topologicalClosure.annihilator = I.annihilator :=
  le_antisymm (annihilator_le_annihilator I.le_topologicalClosure) fun a ha =>
    mem_annihilator.mpr fun _ hx =>
      closure_minimal (fun _ hy => mul_eq_zero_of_mem_annihilator ha hy)
        (isClosed_singleton.preimage (continuous_const_mul a))
        (I.mem_topologicalClosure.mp hx)

/-- Taking topological closure does not change the right annihilator of a two-sided ideal. -/
@[simp]
theorem rightAnnihilator_topologicalClosure [IsTopologicalRing A] [T1Space A]
    (I : TwoSidedIdeal A) :
    I.topologicalClosure.rightAnnihilator = I.rightAnnihilator :=
  le_antisymm (rightAnnihilator_anti I.le_topologicalClosure) fun a ha =>
    mem_rightAnnihilator.mpr fun _ hx =>
      closure_minimal (fun _ hy => mul_eq_zero_of_mem_rightAnnihilator hy ha)
        (isClosed_singleton.preimage (continuous_mul_const a))
        (I.mem_topologicalClosure.mp hx)

/-- In a `T₁` unital ring with separately continuous multiplication,
`(Module.annihilator R I).toTwoSided` is closed for any two-sided ideal `I`. -/
instance isClosed_moduleAnnihilator_toTwoSided {R : Type*} [Ring R] [TopologicalSpace R]
    [SeparatelyContinuousMul R] [T1Space R] (I : TwoSidedIdeal R) :
    IsClosed (((Module.annihilator R I).toTwoSided : TwoSidedIdeal R) : Set R) :=
  I.annihilator_eq_moduleAnnihilator_toTwoSided ▸ I.isClosed_annihilator

/-- In a `T₁` unital ring with separately continuous multiplication, `Module.annihilator R I` is
closed for any two-sided ideal `I`. -/
instance isClosed_moduleAnnihilator {R : Type*} [Ring R] [TopologicalSpace R]
    [SeparatelyContinuousMul R] [T1Space R] (I : TwoSidedIdeal R) :
    IsClosed (Module.annihilator R I : Set R) := by
  simpa only [Ideal.coe_toTwoSided] using isClosed_moduleAnnihilator_toTwoSided I

end ClosedAnnihilator

end TwoSidedIdeal
