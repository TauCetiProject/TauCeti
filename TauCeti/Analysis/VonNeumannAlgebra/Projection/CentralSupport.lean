/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
public import TauCeti.Analysis.VonNeumannAlgebra.Projection.Basic
import Mathlib.Algebra.Order.Star.Projection
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# Central support in von Neumann algebras

In the center `M ⊓ M.commutant` of a concrete von Neumann algebra `M`, the **central support**
`M.centralSupport a` of an operator `a : H →L[ℂ] H` is the smallest central projection `z`
satisfying `z * a = a` (`VonNeumannAlgebra.centralSupportProjection`,
`VonNeumannAlgebra.centralSupport`). For `a ∈ M`, we identify `M.centralSupport a` geometrically
as the orthogonal projection onto the closed span of `{x (a ξ) | x ∈ M, ξ ∈ H}`
(`VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`) and deduce the
**central-support kernel theorem**
(`VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`): for every
`y ∈ M.commutant`, `y * a = 0 ↔ y * M.centralSupport a = 0`.

## Main declarations

* `VonNeumannAlgebra.centralSupportProjection`, `VonNeumannAlgebra.centralSupport`: central support
  of an operator relative to `M`.
* `VonNeumannAlgebra.centralSupportProjection_le_iff`, `VonNeumannAlgebra.centralSupport_le_iff`:
  universal property of central support.
* `VonNeumannAlgebra.centralSupport_unitary_conj`: invariance under conjugation by unitaries in `M`.
* `VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`: geometric span formula.
* `VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`: central-support kernel
  theorem.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  §5.5 and Proposition 5.5.2.
* M. Takesaki, *Theory of Operator Algebras I*, Proposition V.1.6.
-/

public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **central support** of `a : H →L[ℂ] H` relative to `M`, bundled as a projection in the
center `M ⊓ M.commutant`: the smallest central projection `z` satisfying `z * a = a`. -/
noncomputable def centralSupportProjection (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    (M ⊓ M.commutant).Projection :=
  sInf {z : (M ⊓ M.commutant).Projection | (z : H →L[ℂ] H) * a = a}

/-- The **central support** (or central carrier) `M.centralSupport a` of `a : H →L[ℂ] H` in `M`:
the smallest star projection in the center `M ⊓ M.commutant` fixing `a` on the left. -/
noncomputable def centralSupport (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  M.centralSupportProjection a

@[simp]
theorem coe_centralSupportProjection (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    (M.centralSupportProjection a : H →L[ℂ] H) = M.centralSupport a :=
  (rfl)

theorem isStarProjection_centralSupport (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    IsStarProjection (M.centralSupport a) :=
  (M.centralSupportProjection a).isStarProjection

theorem centralSupport_mem (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a ∈ M :=
  (mem_inf.1 (M.centralSupportProjection a).coe_mem).1

theorem centralSupport_mem_commutant (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a ∈ M.commutant :=
  (mem_inf.1 (M.centralSupportProjection a).coe_mem).2

@[simp]
theorem centralSupport_mul_self (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a * a = a := by
  have hid := (M.centralSupportProjection a).isStarProjection.isIdempotentElem
  rw [← coe_centralSupportProjection,
    ContinuousLinearMap.IsIdempotentElem.mul_eq_right_iff hid,
    ← Projection.toSubmodule_closedRange, centralSupportProjection, Projection.closedRange_sInf,
    sInf_image, ClosedSubmodule.toSubmodule_iInf]
  refine le_iInf fun z => ?_
  rw [ClosedSubmodule.toSubmodule_iInf, Projection.toSubmodule_closedRange]
  exact le_iInf fun hz =>
    (ContinuousLinearMap.IsIdempotentElem.mul_eq_right_iff
      z.isStarProjection.isIdempotentElem a).1 hz

theorem mul_centralSupport_self {M : VonNeumannAlgebra H} {a : H →L[ℂ] H} (ha : a ∈ M) :
    a * M.centralSupport a = a := by
  rw [mem_commutant_iff.1 (M.centralSupport_mem_commutant a) a ha,
    M.centralSupport_mul_self a]

/-- Universal property of `M.centralSupportProjection`: a central projection `z` lies above
`M.centralSupportProjection a` if and only if `z * a = a`. -/
theorem centralSupportProjection_le_iff {M : VonNeumannAlgebra H} {a : H →L[ℂ] H}
    {z : (M ⊓ M.commutant).Projection} :
    M.centralSupportProjection a ≤ z ↔ (z : H →L[ℂ] H) * a = a :=
  ⟨fun h => (ContinuousLinearMap.IsIdempotentElem.mul_eq_right_iff
      z.isStarProjection.isIdempotentElem a).2 <|
      ((ContinuousLinearMap.IsIdempotentElem.mul_eq_right_iff
        (M.isStarProjection_centralSupport a).isIdempotentElem a).1
          (M.centralSupport_mul_self a)).trans (Projection.le_iff_range_le.1 h),
    fun hz => sInf_le hz⟩

/-- Universal property of `M.centralSupport`: for a central projection `z` of `M`,
`M.centralSupport a ≤ z ↔ z * a = a`. -/
theorem centralSupport_le_iff {M : VonNeumannAlgebra H} {a z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hzC : z ∈ M.commutant) :
    M.centralSupport a ≤ z ↔ z * a = a := by
  rw [← coe_centralSupportProjection,
    ← Projection.coe_mk z hz (mem_inf.2 ⟨hzM, hzC⟩), Projection.coe_le_coe]
  exact centralSupportProjection_le_iff

/-- Every star projection is bounded above by its central support. -/
theorem le_centralSupport {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    p ≤ M.centralSupport p :=
  (hp.le_iff_mul_eq_right (M.isStarProjection_centralSupport p)).2 (M.centralSupport_mul_self p)

/-- A central projection is equal to its own central support. -/
theorem centralSupport_eq_self_of_mem_commutant {M : VonNeumannAlgebra H} {z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hzC : z ∈ M.commutant) :
    M.centralSupport z = z :=
  le_antisymm ((centralSupport_le_iff hz hzM hzC).2 hz.isIdempotentElem.eq) (le_centralSupport hz)

@[simp]
theorem centralSupport_zero (M : VonNeumannAlgebra H) : M.centralSupport 0 = 0 :=
  le_antisymm
    ((centralSupport_le_iff (.zero _) (zero_mem M) (zero_mem M.commutant)).2 (zero_mul 0))
    (M.isStarProjection_centralSupport 0).nonneg

@[simp]
theorem centralSupport_one (M : VonNeumannAlgebra H) : M.centralSupport 1 = 1 :=
  centralSupport_eq_self_of_mem_commutant (.one _) (one_mem M) (one_mem M.commutant)

/-- Conjugating an operator by a unitary in `M` preserves its bundled central support. -/
@[simp]
theorem centralSupportProjection_unitary_conj {M : VonNeumannAlgebra H} {u a : H →L[ℂ] H}
    (huM : u ∈ M) (hu : u ∈ unitary (H →L[ℂ] H)) :
    M.centralSupportProjection (u * a * star u) = M.centralSupportProjection a := by
  unfold centralSupportProjection
  congr 1
  ext z
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  set Φ := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) ⟨u, hu⟩
  have hzu : (z : H →L[ℂ] H) * u = u * z :=
    (mem_commutant_iff.1 (mem_inf.1 z.coe_mem).2 u huM).symm
  have hz : Φ z = z := by
    rw [Unitary.conjStarAlgAut_apply, ← hzu, mul_assoc, hu.2, mul_one]
  rw [← Unitary.conjStarAlgAut_apply (S := ℂ) ⟨u, hu⟩ a]
  conv_lhs =>
    lhs
    lhs
    rw [← hz]
  rw [← map_mul Φ]
  exact Φ.injective.eq_iff

/-- Conjugating an operator by a unitary in `M` preserves its central support. -/
@[simp]
theorem centralSupport_unitary_conj {M : VonNeumannAlgebra H} {u a : H →L[ℂ] H}
    (huM : u ∈ M) (hu : u ∈ unitary (H →L[ℂ] H)) :
    M.centralSupport (u * a * star u) = M.centralSupport a :=
  congrArg Projection.val (M.centralSupportProjection_unitary_conj huM hu)

/-- **Geometric formula for the central support.** For `a ∈ M`, `M.centralSupport a` is the
orthogonal projection onto the closure of the linear span of `{x (a ξ) | x ∈ M, ξ ∈ H}`. -/
theorem centralSupport_eq_starProjection_closure_span {M : VonNeumannAlgebra H} {a : H →L[ℂ] H}
    (ha : a ∈ M) :
    M.centralSupport a =
      (Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}).topologicalClosure.starProjection
      := by
  set W : Submodule ℂ H := Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}
  set K : Submodule ℂ H := W.topologicalClosure
  -- Step 1: `W` is invariant under both `M.commutant` and `M = M.commutant.commutant`, so
  -- `K.starProjection` lies in `M ⊓ M.commutant`.
  have hW_comm : ∀ y ∈ M.commutant, W ∈ Module.End.invtSubmodule y := by
    intro y hy
    rw [Module.End.mem_invtSubmodule, Submodule.span_le]
    rintro _ ⟨x, hx, ξ, rfl⟩
    refine Submodule.subset_span ⟨x, hx, y ξ, ?_⟩
    have hcomm : y * (x * a) = (x * a) * y :=
      (mem_commutant_iff.1 hy (x * a) (mul_mem hx ha)).symm
    exact congr($hcomm ξ).symm
  have hW_M : ∀ m ∈ M, W ∈ Module.End.invtSubmodule m := by
    intro m hm
    rw [Module.End.mem_invtSubmodule, Submodule.span_le]
    rintro _ ⟨x, hx, ξ, rfl⟩
    exact Submodule.subset_span ⟨m * x, mul_mem hm hx, ξ, rfl⟩
  have hKM : K.starProjection ∈ M := by
    rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection]
    exact fun y hy => Submodule.topologicalClosure_mem_invtSubmodule (hW_comm y hy)
  have hKC : K.starProjection ∈ M.commutant := by
    rw [IsStarProjection.mem_iff isStarProjection_starProjection M.commutant,
      Submodule.range_starProjection]
    exact fun m hm => Submodule.topologicalClosure_mem_invtSubmodule
      (hW_M m (by simpa only [M.commutant_commutant] using hm))
  -- Step 2: `K.starProjection * a = a` since `a ξ = 1 (a ξ) ∈ W ≤ K`.
  have hKa : K.starProjection * a = a := by
    rw [ContinuousLinearMap.IsIdempotentElem.mul_eq_right_iff
        K.isIdempotentElem_starProjection a,
      Submodule.range_starProjection]
    rintro _ ⟨ξ, rfl⟩
    exact W.le_topologicalClosure (Submodule.subset_span ⟨1, one_mem M, ξ, rfl⟩)
  -- Step 3: Every central projection `z` with `z * a = a` contains `W`, hence `K`, in its range.
  refine le_antisymm
    ((centralSupport_le_iff isStarProjection_starProjection hKM hKC).2 hKa) ?_
  rw [← coe_centralSupportProjection]
  set z := M.centralSupportProjection a
  rw [← z.starProjection_range, Submodule.starProjection_le_starProjection_iff]
  refine W.topologicalClosure_minimal ?_
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range z.isStarProjection.isIdempotentElem)
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, ξ, rfl⟩
  have hzx : (z : H →L[ℂ] H) * x = x * z :=
    (mem_commutant_iff.1 (mem_inf.1 z.coe_mem).2 x hx).symm
  have hza : (z : H →L[ℂ] H) * a = a := M.centralSupport_mul_self a
  refine ⟨x (a ξ), ?_⟩
  calc (z : H →L[ℂ] H) (x (a ξ))
    _ = ((z : H →L[ℂ] H) * x) (a ξ) := rfl
    _ = (x * z) (a ξ) := by rw [hzx]
    _ = x (((z : H →L[ℂ] H) * a) ξ) := rfl
    _ = x (a ξ) := by rw [hza]

/-- **Central-support kernel theorem.** For `a ∈ M` and `y ∈ M.commutant`, `y * a = 0` holds if and
only if `y * M.centralSupport a = 0`. -/
theorem commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero {M : VonNeumannAlgebra H}
    {a y : H →L[ℂ] H} (ha : a ∈ M) (hy : y ∈ M.commutant) :
    y * a = 0 ↔ y * M.centralSupport a = 0 := by
  refine ⟨fun hya => ?_, fun hyc => by
    rw [← M.centralSupport_mul_self a, ← mul_assoc, hyc, zero_mul]⟩
  rw [centralSupport_eq_starProjection_closure_span ha]
  set W : Submodule ℂ H := Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}
  have hW_ker : W.topologicalClosure ≤ y.ker := by
    refine W.topologicalClosure_minimal ?_ y.isClosed_ker
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, ξ, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hyx : y * x = x * y := (mem_commutant_iff.1 hy x hx).symm
    calc y (x (a ξ))
      _ = (y * x) (a ξ) := rfl
      _ = (x * y) (a ξ) := by rw [hyx]
      _ = x ((y * a) ξ) := rfl
      _ = 0 := by rw [hya, zero_apply, map_zero]
  ext ξ
  exact hW_ker (Submodule.starProjection_apply_mem _ ξ)

end VonNeumannAlgebra
