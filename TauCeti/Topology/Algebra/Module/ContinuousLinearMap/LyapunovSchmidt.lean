/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import TauCeti.LinearAlgebra.Projection.RangeKer

/-!
# The Lyapunov–Schmidt projection

Let `L : X →L[R] Y` and `P : Y →L[R] Z` be continuous linear maps between topological modules
whose composite `A = P L` is invertible. The **Lyapunov–Schmidt projection**

`Π = id - L A⁻¹ P` (`ContinuousLinearMap.lyapunovSchmidtProj`)

is the continuous projection of `Y` onto the kernel `W` of `P` along the range of `L`, which are
topological complements (`ContinuousLinearMap.isTopCompl_range_ker_of_isInvertible_comp`,
`ContinuousLinearMap.lyapunovSchmidtProj_eq_projectionL`). It depends on `P` only through `W`
(`ContinuousLinearMap.lyapunovSchmidtProj_eq_of_ker_eq`), and it reduces the linear equation
`L f + S = 0` to an equation in `W`: the vector `f = -A⁻¹ P S` is the unique one with
`L f + S ∈ W` (`ContinuousLinearMap.apply_add_mem_ker_iff`), for it `L f + S = Π S`
(`ContinuousLinearMap.apply_neg_inverse_apply_add`), and `L f + S = 0` exactly when moreover
`Π S = 0` (`ContinuousLinearMap.apply_add_eq_zero_iff`), that is, when `S` lies in the range of `L`
(`ContinuousLinearMap.lyapunovSchmidtProj_apply_eq_zero_iff`). The algebra is
`LinearMap.id_sub_comp_comp_eq_projection`.

When `P L` is not invertible, `(P L)⁻¹ = 0` by convention and `Π` is the identity
(`ContinuousLinearMap.lyapunovSchmidtProj_of_not_isInvertible`); in particular `Π` is always
idempotent (`ContinuousLinearMap.isIdempotentElem_lyapunovSchmidtProj`).

## Main definitions

* `ContinuousLinearMap.lyapunovSchmidtProj`: the operator `id - L (P L)⁻¹ P`.

## Main results

* `ContinuousLinearMap.isTopCompl_range_ker_of_isInvertible_comp`: if `P L` is invertible, then
  `range L` and `ker P` are topological complements.
* `ContinuousLinearMap.lyapunovSchmidtProj_eq_projectionL`: for invertible `P L`, `Π` is the
  continuous projection onto `ker P` along `range L`.
* `ContinuousLinearMap.lyapunovSchmidtProj_eq_of_ker_eq`: `Π` depends on `P` only through `ker P`.
* `ContinuousLinearMap.apply_add_eq_zero_iff`: the Lyapunov–Schmidt reduction of `L f + S = 0`.

## References

* S.-N. Chow and J. K. Hale, *Methods of Bifurcation Theory*, Springer, 1982, §2.4.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {R X Y Z : Type*} [Ring R] [TopologicalSpace X] [AddCommGroup X] [Module R X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module R Y] [TopologicalSpace Z] [AddCommGroup Z]
  [Module R Z] {L : X →L[R] Y} {P : Y →L[R] Z}

section Invertible

variable (h : (P ∘L L).IsInvertible)
include h

/-- If `P L` is invertible, the range of `L` and the kernel of `P` are topological complements. -/
theorem isTopCompl_range_ker_of_isInvertible_comp : L.range.IsTopCompl P.ker := by
  have hker : ((P ∘L L).inverse ∘L P).ker = P.ker :=
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_injective h.inverse.injective)
  rw [← hker]
  exact L.isTopCompl_range_ker_of_leftInverse _ fun x => by simpa using h.inverse_apply_self x

/-- If `P L` is invertible, then `x = -(P L)⁻¹ P y` is the unique vector with `L x + y ∈ ker P`.
-/
theorem apply_add_mem_ker_iff {x : X} {y : Y} :
    L x + y ∈ P.ker ↔ x = -(P ∘L L).inverse (P y) := by
  rw [LinearMap.mem_ker, map_add, add_eq_zero_iff_eq_neg, eq_comm, ← map_neg (P ∘L L).inverse,
    eq_comm (a := x), h.inverse_apply_eq, comp_apply, coe_coe]

/-- The composite `(P L)⁻¹ P` depends on `P` only through its kernel: if `P L` and `P' L` are
invertible and `ker P = ker P'`, then `(P L)⁻¹ P = (P' L)⁻¹ P'`. -/
theorem inverse_comp_eq_of_ker_eq {Z' : Type*} [TopologicalSpace Z'] [AddCommGroup Z']
    [Module R Z'] {P' : Y →L[R] Z'} (h' : (P' ∘L L).IsInvertible) (hker : P.ker = P'.ker) :
    (P ∘L L).inverse ∘L P = (P' ∘L L).inverse ∘L P' := by
  ext y
  have hk : L (-(P ∘L L).inverse (P y)) + y ∈ P'.ker := hker ▸ (apply_add_mem_ker_iff h).2 rfl
  simpa using (apply_add_mem_ker_iff h').1 hk

end Invertible

variable [IsTopologicalAddGroup Y]

/-- The **Lyapunov–Schmidt projection** `id - L (P L)⁻¹ P` of `L : X →L[R] Y` relative to
`P : Y →L[R] Z`. When `P L` is invertible, it is the projection of `Y` onto `ker P` along
`range L` (`ContinuousLinearMap.lyapunovSchmidtProj_eq_projectionL`). -/
def lyapunovSchmidtProj (L : X →L[R] Y) (P : Y →L[R] Z) : Y →L[R] Y :=
  .id R Y - L ∘L (P ∘L L).inverse ∘L P

/-- The Lyapunov–Schmidt projection is `id - L (P L)⁻¹ P`. -/
theorem lyapunovSchmidtProj_def :
    L.lyapunovSchmidtProj P = .id R Y - L ∘L (P ∘L L).inverse ∘L P :=
  (rfl)

/-- The Lyapunov–Schmidt projection sends `y` to `y - L (P L)⁻¹ P y`. -/
theorem lyapunovSchmidtProj_apply (y : Y) :
    L.lyapunovSchmidtProj P y = y - L ((P ∘L L).inverse (P y)) := by
  simp [lyapunovSchmidtProj_def]

/-- With `f = -(P L)⁻¹ P y`, the vector `L f + y` is the Lyapunov–Schmidt projection of `y`. -/
theorem apply_neg_inverse_apply_add (y : Y) :
    L (-(P ∘L L).inverse (P y)) + y = L.lyapunovSchmidtProj P y := by
  rw [lyapunovSchmidtProj_apply, map_neg, neg_add_eq_sub]

/-- The Lyapunov–Schmidt projection fixes the kernel of `P`. -/
@[simp]
theorem lyapunovSchmidtProj_apply_of_mem_ker {y : Y} (hy : y ∈ P.ker) :
    L.lyapunovSchmidtProj P y = y := by
  rw [LinearMap.mem_ker, coe_coe] at hy
  simp [lyapunovSchmidtProj_apply, hy]

/-- The Lyapunov–Schmidt projection fixes the kernel of `P`. -/
theorem lyapunovSchmidtProj_apply_coe (y : P.ker) : L.lyapunovSchmidtProj P y = y :=
  lyapunovSchmidtProj_apply_of_mem_ker y.2

/-- If `P L` is not invertible, the Lyapunov–Schmidt projection is the identity, since
`(P L)⁻¹ = 0` by convention. -/
@[simp]
theorem lyapunovSchmidtProj_of_not_isInvertible (h : ¬(P ∘L L).IsInvertible) :
    L.lyapunovSchmidtProj P = .id R Y := by
  simp [lyapunovSchmidtProj_def, h]

section Invertible

variable (h : (P ∘L L).IsInvertible)
include h

/-- If `P L` is invertible, the Lyapunov–Schmidt projection `id - L (P L)⁻¹ P` is the continuous
projection onto the kernel of `P` along the range of `L`. -/
theorem lyapunovSchmidtProj_eq_projectionL :
    L.lyapunovSchmidtProj P =
      P.ker.projectionL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm := by
  obtain ⟨A, hA⟩ := h
  have hA' : (P : Y →ₗ[R] Z) ∘ₗ (L : X →ₗ[R] Y) = A.toLinearEquiv := by
    rw [← toLinearMap_comp, ← hA]
    rfl
  refine coe_inj.mp ?_
  rw [Submodule.toLinearMap_projectionL, ← LinearMap.id_sub_comp_comp_eq_projection _ hA']
  ext y
  simp [lyapunovSchmidtProj_apply, ← hA]

/-- If `P L` is invertible, the Lyapunov–Schmidt projection takes values in the kernel of `P`. -/
theorem lyapunovSchmidtProj_mem_ker (y : Y) : L.lyapunovSchmidtProj P y ∈ P.ker := by
  rw [lyapunovSchmidtProj_eq_projectionL h]
  exact Submodule.projectionL_apply_mem _ y

/-- If `P L` is invertible, the Lyapunov–Schmidt projection takes values in the kernel of `P`. -/
@[simp]
theorem apply_lyapunovSchmidtProj (y : Y) : P (L.lyapunovSchmidtProj P y) = 0 :=
  lyapunovSchmidtProj_mem_ker h y

/-- If `P L` is invertible, the Lyapunov–Schmidt projection vanishes on the range of `L`. -/
@[simp]
theorem lyapunovSchmidtProj_apply_apply (x : X) : L.lyapunovSchmidtProj P (L x) = 0 := by
  rw [lyapunovSchmidtProj_eq_projectionL h]
  exact Submodule.projectionL_apply_eq_zero_of_mem_right _ (LinearMap.mem_range_self _ x)

/-- If `P L` is invertible, then `P Π = 0`. -/
@[simp]
theorem comp_lyapunovSchmidtProj : P ∘L L.lyapunovSchmidtProj P = 0 :=
  ext <| apply_lyapunovSchmidtProj h

/-- If `P L` is invertible, then `Π L = 0`. -/
@[simp]
theorem lyapunovSchmidtProj_comp : L.lyapunovSchmidtProj P ∘L L = 0 :=
  ext <| lyapunovSchmidtProj_apply_apply h

/-- If `P L` is invertible, the Lyapunov–Schmidt projection of `y` vanishes exactly when `y` lies
in the range of `L`. -/
theorem lyapunovSchmidtProj_apply_eq_zero_iff {y : Y} :
    L.lyapunovSchmidtProj P y = 0 ↔ y ∈ L.range := by
  rw [lyapunovSchmidtProj_eq_projectionL h, Submodule.projectionL_apply_eq_zero_iff]

/-- If `P L` is invertible, the Lyapunov–Schmidt projection fixes `y` exactly when `y` lies in the
kernel of `P`. -/
theorem lyapunovSchmidtProj_apply_eq_self_iff {y : Y} :
    L.lyapunovSchmidtProj P y = y ↔ y ∈ P.ker := by
  rw [lyapunovSchmidtProj_eq_projectionL h, Submodule.projectionL_eq_self_iff]

/-- If `P L` is invertible, the range of the Lyapunov–Schmidt projection is the kernel of `P`. -/
@[simp]
theorem range_lyapunovSchmidtProj : (L.lyapunovSchmidtProj P).range = P.ker := by
  rw [lyapunovSchmidtProj_eq_projectionL h, Submodule.range_projectionL]

/-- If `P L` is invertible, the kernel of the Lyapunov–Schmidt projection is the range of `L`. -/
@[simp]
theorem ker_lyapunovSchmidtProj : (L.lyapunovSchmidtProj P).ker = L.range := by
  rw [lyapunovSchmidtProj_eq_projectionL h, Submodule.ker_projectionL]

/-- **Lyapunov–Schmidt reduction.** If `P L` is invertible, then `L x + y = 0` exactly when
`x = -(P L)⁻¹ P y` and the Lyapunov–Schmidt projection of `y` vanishes. -/
theorem apply_add_eq_zero_iff {x : X} {y : Y} :
    L x + y = 0 ↔ x = -(P ∘L L).inverse (P y) ∧ L.lyapunovSchmidtProj P y = 0 := by
  refine ⟨fun hxy => ?_, fun ⟨hx, hy⟩ => by rw [hx, apply_neg_inverse_apply_add, hy]⟩
  have hx := (apply_add_mem_ker_iff h).1 (hxy ▸ P.ker.zero_mem)
  exact ⟨hx, by rw [← apply_neg_inverse_apply_add, ← hx, hxy]⟩

/-- The Lyapunov–Schmidt projection depends on `P` only through its kernel: if `P L` and `P' L`
are invertible and `ker P = ker P'`, the two projections agree. -/
theorem lyapunovSchmidtProj_eq_of_ker_eq {Z' : Type*} [TopologicalSpace Z'] [AddCommGroup Z']
    [Module R Z'] {P' : Y →L[R] Z'} (h' : (P' ∘L L).IsInvertible) (hker : P.ker = P'.ker) :
    L.lyapunovSchmidtProj P = L.lyapunovSchmidtProj P' := by
  rw [lyapunovSchmidtProj_def, lyapunovSchmidtProj_def, inverse_comp_eq_of_ker_eq h h' hker]

end Invertible

/-- The Lyapunov–Schmidt projection is idempotent: for invertible `P L` it is a projection, and
otherwise it is the identity. -/
@[simp]
theorem isIdempotentElem_lyapunovSchmidtProj : IsIdempotentElem (L.lyapunovSchmidtProj P) := by
  by_cases h : (P ∘L L).IsInvertible
  · rw [lyapunovSchmidtProj_eq_projectionL h]
    exact Submodule.isIdempotentElem_projectionL _
  · rw [lyapunovSchmidtProj_of_not_isInvertible h]
    exact IsIdempotentElem.one

/-- The Lyapunov–Schmidt projection is idempotent. -/
@[simp]
theorem lyapunovSchmidtProj_comp_self :
    L.lyapunovSchmidtProj P ∘L L.lyapunovSchmidtProj P = L.lyapunovSchmidtProj P :=
  isIdempotentElem_lyapunovSchmidtProj.eq

/-- The Lyapunov–Schmidt projection is idempotent, pointwise. -/
@[simp]
theorem lyapunovSchmidtProj_apply_lyapunovSchmidtProj (y : Y) :
    L.lyapunovSchmidtProj P (L.lyapunovSchmidtProj P y) = L.lyapunovSchmidtProj P y :=
  congr($lyapunovSchmidtProj_comp_self y)

end ContinuousLinearMap
