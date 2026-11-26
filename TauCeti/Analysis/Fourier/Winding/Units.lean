/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.ContinuousMap.Units
public import TauCeti.Analysis.Fourier.Winding
import TauCeti.Topology.Algebra.Group.Connected
import TauCeti.Topology.ContinuousMap.Units

/-!
# The winding number on the units of `C(AddCircle T, ℂ)`

A unit of the ring `C(AddCircle T, ℂ)` of continuous complex functions on the circle is a
nowhere-zero function, so it has a winding number about the origin. The winding number of a
product is the sum of the winding numbers, so this is a group homomorphism
`ContinuousMap.windingNumberHom T : C(AddCircle T, ℂ)ˣ →* Multiplicative ℤ`. For `0 < T` it is
onto, since the Fourier monomial `fourier k` winds `k` times around the origin.

For `0 < T` the winding number also classifies the connected components of the unit group, whose
topology is that of uniform convergence: the identity component is exactly the kernel of
`windingNumberHom T`. A unit uniformly close to `1` keeps the winding number `0` of `1`, by the
dog-on-a-leash principle `ContinuousMap.windingNumber_eq_of_norm_sub_lt`, so the kernel is a
subgroup that is a neighbourhood of `1` and hence contains the identity component. Conversely a
unit of winding number zero has a continuous logarithm `g`
(`ContinuousMap.windingNumber_eq_zero_iff_exists_exp`), and `s ↦ exp (s g)` joins it to `1`
through units (`ContinuousMap.mem_connectedComponentOfOne_of_exp`).

Composed with the determinant, this invariant detects nontrivial components of the stable general
linear group over `C(AddCircle T, ℂ)`.

## Main definitions

* `ContinuousMap.windingNumberHom`: the winding number of a unit of `C(AddCircle T, ℂ)`, as a
  homomorphism to `Multiplicative ℤ`.

## Main results

* `ContinuousMap.windingNumberHom_of_coe_eq_fourier`: a unit equal to `fourier k` has winding
  number `k`, so `windingNumberHom T` is surjective (`ContinuousMap.windingNumberHom_surjective`).
* `ContinuousMap.ker_windingNumberHom`: the kernel of the winding number is the identity component
  of the unit group.
* `ContinuousMap.windingNumberHom_eq_one_iff_exists_exp`: a unit has winding number zero exactly
  when it is the exponential of a continuous function.
-/

public section

noncomputable section

open Topology

namespace ContinuousMap

variable (T : ℝ)

/-- The **winding number** of a unit of `C(AddCircle T, ℂ)`, a nowhere-zero function, as a
homomorphism to `Multiplicative ℤ`: the winding number of a product is the sum of the winding
numbers. -/
def windingNumberHom : C(AddCircle T, ℂ)ˣ →* Multiplicative ℤ where
  toFun u :=
    .ofAdd ((u : C(AddCircle T, ℂ)).windingNumber ((isUnit_iff_forall_ne_zero _).1 u.isUnit))
  map_one' := by
    rw [← ofAdd_zero]
    exact congrArg _ ((windingNumber_congr _ (fun _ ↦ one_ne_zero) fun _ ↦ rfl).trans
      windingNumber_one)
  map_mul' u v := by
    rw [← ofAdd_add, ← windingNumber_mul]
    exact congrArg _ (windingNumber_congr _ _ fun _ ↦ rfl)

variable {T}

/-- The value of `ContinuousMap.windingNumberHom` is the winding number of the underlying
function. -/
theorem windingNumberHom_apply (u : C(AddCircle T, ℂ)ˣ) :
    windingNumberHom T u =
      .ofAdd ((u : C(AddCircle T, ℂ)).windingNumber ((isUnit_iff_forall_ne_zero _).1 u.isUnit)) :=
  (rfl)

/-- A unit of `C(AddCircle T, ℂ)` equal to the Fourier monomial `fourier k` has winding
number `k`. -/
theorem windingNumberHom_of_coe_eq_fourier [Fact (0 < T)] {u : C(AddCircle T, ℂ)ˣ} {k : ℤ}
    (hu : (u : C(AddCircle T, ℂ)) = fourier k) : windingNumberHom T u = .ofAdd k := by
  rw [windingNumberHom_apply, ← windingNumber_fourier (T := T) k]
  exact congrArg _ (windingNumber_congr _ _ fun x ↦ by rw [hu])

variable (T) in
/-- Every integer is the winding number of a unit of `C(AddCircle T, ℂ)`, namely of the Fourier
monomial `fourier k`. -/
theorem windingNumberHom_surjective [Fact (0 < T)] :
    Function.Surjective (windingNumberHom T) := fun k ↦
  have hk : IsUnit (fourier (T := T) k.toAdd) :=
    (isUnit_iff_forall_ne_zero _).2 (TauCeti.fourier_apply_ne_zero _)
  ⟨hk.unit, windingNumberHom_of_coe_eq_fourier hk.unit_spec⟩

variable [Fact (0 < T)]

variable (T) in
/-- Units of `C(AddCircle T, ℂ)` uniformly close to `1` have winding number zero: the kernel of
the winding number is a neighbourhood of `1` in the unit group. -/
private theorem ker_windingNumberHom_mem_nhds_one :
    ((windingNumberHom T).ker : Set C(AddCircle T, ℂ)ˣ) ∈ 𝓝 1 := by
  -- The units at uniform distance less than `1` from `1` form an open neighbourhood of `1`.
  refine Filter.mem_of_superset ((Metric.isOpen_ball.preimage Units.continuous_val).mem_nhds
    (x := (1 : C(AddCircle T, ℂ)ˣ)) (Metric.mem_ball_self one_pos)) fun u hu ↦ ?_
  rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hu
  rw [SetLike.mem_coe, MonoidHom.mem_ker, windingNumberHom_apply, ← ofAdd_zero]
  refine congrArg _ ((windingNumber_eq_of_norm_sub_lt (f := 1) (fun _ ↦ one_ne_zero)
    fun x ↦ ?_).trans windingNumber_one)
  simpa using (norm_coe_le_norm ((u : C(AddCircle T, ℂ)) - 1) x).trans_lt hu

/-- A unit of `C(AddCircle T, ℂ)` has winding number zero exactly when it is the exponential of a
continuous function. -/
theorem windingNumberHom_eq_one_iff_exists_exp (u : C(AddCircle T, ℂ)ˣ) :
    windingNumberHom T u = 1 ↔
      ∃ g : C(AddCircle T, ℂ), ∀ x, (u : C(AddCircle T, ℂ)) x = Complex.exp (g x) := by
  rw [windingNumberHom_apply, ofAdd_eq_one]
  exact windingNumber_eq_zero_iff_exists_exp _ _

variable (T) in
/-- **The winding number classifies the components of the units of `C(AddCircle T, ℂ)`**: the
kernel of the winding number is the identity component of the unit group. -/
theorem ker_windingNumberHom :
    (windingNumberHom T).ker = Subgroup.connectedComponentOfOne C(AddCircle T, ℂ)ˣ := by
  refine le_antisymm (fun u hu ↦ ?_)
    (Subgroup.connectedComponentOfOne_le_of_mem_nhds_one (ker_windingNumberHom_mem_nhds_one T))
  obtain ⟨g, hg⟩ := (windingNumberHom_eq_one_iff_exists_exp u).1 hu
  exact mem_connectedComponentOfOne_of_exp hg

end ContinuousMap
