/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Basic

/-!
# Orthogonal sums of finite families of finite quadratic modules

For a finite family `A : ι → FiniteQuadraticModule`, the group `Π i, A i` carries the quadratic map

```text
q(x) = ∑ i, q_i(x_i),
```

Mathlib's `QuadraticMap.pi`, whose polar pairing is the sum of the coordinate pairings. This is
the orthogonal sum of the family; the binary case is `TauCeti.FiniteQuadraticModule.prod`.
Classification results for finite quadratic modules are stated with it, as an isometry from an
orthogonal sum of standard generators.

Since the quadratic map of `pi A` is literally `QuadraticMap.pi`, isometries between orthogonal sums
come from the general theory of quadratic maps: an orthogonal sum of coordinatewise isometries is
Mathlib's `QuadraticMap.IsometryEquiv.pi`, and over `Fin (n + 1)` splitting off the first summand
is `QuadraticMap.IsometryEquiv.consPi`.

For a constant family, the quadratic map and pairing of `pi` agree with those of
`TauCeti.FiniteQuadraticModule.coordinatePower`, which carries the additional coordinatewise API
used for codes.

## Main declarations

* `TauCeti.FiniteBilinearModule.pi`: the orthogonal sum of a finite family of finite bilinear
  modules.
* `TauCeti.FiniteBilinearModule.pi_pairing`: its pairing is the sum of the coordinate pairings.
* `TauCeti.FiniteBilinearModule.Isometry.pi`: the orthogonal sum of a family of bilinear
  isometries.
* `TauCeti.FiniteBilinearModule.isNondegenerate_pi_iff`: the orthogonal sum of finite bilinear
  modules is nondegenerate exactly when every summand is.
* `TauCeti.FiniteQuadraticModule.pi`: the orthogonal sum of a finite family of finite quadratic
  modules, built over `TauCeti.FiniteBilinearModule.pi`.
* `TauCeti.FiniteQuadraticModule.pi_toFiniteBilinearModule`: taking the polar bilinear module
  commutes with orthogonal sums.
* `TauCeti.FiniteQuadraticModule.pi_quadratic` and `TauCeti.FiniteQuadraticModule.pi_pairing`: its
  quadratic map and pairing are the sums of the coordinate ones.
* `TauCeti.FiniteQuadraticModule.isNondegenerate_pi_iff`: the orthogonal sum is nondegenerate
  exactly when every summand is.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace TauCeti

universe u v w

namespace FiniteBilinearModule

section Pi

variable {ι : Type v} [Fintype ι] (A : ι → FiniteBilinearModule.{u})

/-- **The orthogonal sum of a finite family of finite bilinear modules**: the group `Π i, A i`
with the pairing `(x, y) ↦ ∑ i, (A i).pairing (x i) (y i)`.

Reducible, exactly as `TauCeti.FiniteBilinearModule.prod` is, so that the carrier of an orthogonal
sum reduces to the product of the carriers. -/
abbrev pi : FiniteBilinearModule.{max u v} where
  carrier := ∀ i, A i
  pairing :=
    { toFun := fun x ↦
        { toFun := fun y ↦ ∑ i, (A i).pairing (x i) (y i)
          map_zero' := by simp
          map_add' := fun y z ↦ by
            simp only [Pi.add_apply, pairing_add_right, Finset.sum_add_distrib] }
      map_zero' := by
        ext y
        exact Finset.sum_eq_zero fun i _ ↦ (A i).pairing_zero_left (y i)
      map_add' := fun x y ↦ by
        ext z
        exact (Finset.sum_congr rfl fun i _ ↦ by
          rw [Pi.add_apply, pairing_add_left]).trans Finset.sum_add_distrib }
  pairing_comm x y :=
    Finset.sum_congr rfl fun i _ ↦ (A i).pairing_comm (x i) (y i)

/-- The pairing of an orthogonal sum of finite bilinear modules is the sum of the coordinate
pairings. -/
theorem pi_pairing (x y : pi A) :
    (pi A).pairing x y = ∑ i, (A i).pairing (x i) (y i) :=
  rfl

/-- **An orthogonal sum of finite bilinear modules is nondegenerate exactly when every summand
is.** -/
@[simp]
theorem isNondegenerate_pi_iff :
    (pi A).IsNondegenerate ↔ ∀ i, (A i).IsNondegenerate := by
  classical
  constructor
  · intro h i
    refine isNondegenerate_of_radical_eq_bot _ (eq_bot_iff.2 fun x hx ↦ ?_)
    rw [mem_radical_iff] at hx
    rw [AddSubgroup.mem_bot]
    -- `Pi.single i x` pairs with `y` as `x` pairs with `y i`, so it lies in the radical.
    have hsingle : (Pi.single i x : pi A) = 0 :=
      IsNondegenerate.eq_zero_of_forall_pairing_eq_zero _ h fun y ↦ by
        rw [pi_pairing, Finset.sum_eq_single i (fun j _ hj ↦ by
          rw [Pi.single_eq_of_ne hj, pairing_zero_left]) (by simp),
          Pi.single_eq_same]
        exact hx (y i)
    simpa using congr_fun hsingle i
  · intro h
    refine isNondegenerate_of_radical_eq_bot _ (eq_bot_iff.2 fun x hx ↦ ?_)
    rw [mem_radical_iff] at hx
    rw [AddSubgroup.mem_bot]
    funext i
    -- `x i` pairs with `y` as `x` pairs with `Pi.single i y`.
    refine IsNondegenerate.eq_zero_of_forall_pairing_eq_zero _ (h i) fun y ↦ ?_
    have hxy := hx (Pi.single i y)
    rwa [pi_pairing, Finset.sum_eq_single i (fun j _ hj ↦ by
      rw [Pi.single_eq_of_ne hj, pairing_zero_right]) (by simp),
      Pi.single_eq_same] at hxy

end Pi

namespace Isometry

section Pi

variable {ι : Type v} [Fintype ι]
  {A : ι → FiniteBilinearModule.{u}} {B : ι → FiniteBilinearModule.{w}}

/-- **The orthogonal sum of a family of finite bilinear module isometries.** -/
def pi (f : ∀ i, Isometry (A i) (B i)) :
    Isometry (FiniteBilinearModule.pi A) (FiniteBilinearModule.pi B) where
  toAddEquiv := AddEquiv.piCongrRight fun i ↦ (f i).toAddEquiv
  map_pairing' x y := by
    rw [pi_pairing, pi_pairing]
    exact Finset.sum_congr rfl fun i _ ↦ (f i).map_pairing (x i) (y i)

/-- An orthogonal sum of finite bilinear module isometries acts coordinatewise. -/
@[simp]
theorem pi_apply (f : ∀ i, Isometry (A i) (B i)) (x : FiniteBilinearModule.pi A) (i : ι) :
    pi f x i = f i (x i) :=
  (rfl)

end Pi

end Isometry

end FiniteBilinearModule

namespace FiniteQuadraticModule

section Pi

variable {ι : Type v} [Fintype ι] (A : ι → FiniteQuadraticModule.{u})

/-- **The orthogonal sum of a finite family of finite quadratic modules**: the group `Π i, A i`
with the quadratic map `x ↦ ∑ i, q_i(x_i)`, Mathlib's `QuadraticMap.pi`, and its polar pairing
`TauCeti.FiniteBilinearModule.pi`.

Reducible, exactly as `TauCeti.FiniteQuadraticModule.prod` is, so that the carrier of an orthogonal
sum reduces to the product of the carriers. -/
abbrev pi : FiniteQuadraticModule.{max u v} where
  toFiniteBilinearModule := FiniteBilinearModule.pi fun i ↦ (A i).toFiniteBilinearModule
  quadratic := QuadraticMap.pi fun i ↦ (A i).quadratic
  polar_eq_pairing' x y := by
    rw [FiniteBilinearModule.pi_pairing]
    simp_rw [← polar_eq_pairing]
    exact QuadraticMap.Ring.polar_pi _ x y

/-- Taking the polar bilinear module commutes with orthogonal sums. -/
@[simp]
theorem pi_toFiniteBilinearModule :
    (pi A).toFiniteBilinearModule =
      FiniteBilinearModule.pi fun i ↦ (A i).toFiniteBilinearModule :=
  rfl

/-- The quadratic map of an orthogonal sum is the sum of the coordinate quadratic maps. -/
theorem pi_quadratic (x : pi A) : (pi A).quadratic x = ∑ i, (A i).quadratic (x i) :=
  QuadraticMap.pi_apply _ x

/-- The pairing of an orthogonal sum is the sum of the coordinate pairings. -/
theorem pi_pairing (x y : pi A) :
    (pi A).toFiniteBilinearModule.pairing x y =
      ∑ i, (A i).toFiniteBilinearModule.pairing (x i) (y i) :=
  FiniteBilinearModule.pi_pairing _ x y

/-- **An orthogonal sum is nondegenerate exactly when every summand is.** -/
@[simp]
theorem isNondegenerate_pi_iff :
    (pi A).IsNondegenerate ↔ ∀ i, (A i).IsNondegenerate :=
  FiniteBilinearModule.isNondegenerate_pi_iff _

/-- An orthogonal sum has quadratic form with values in `½ℤ/ℤ` exactly when every summand
does. -/
theorem forall_quadratic_add_self_eq_zero_pi_iff :
    (∀ x : pi A, (pi A).quadratic x + (pi A).quadratic x = 0) ↔
      ∀ i (y : A i), (A i).quadratic y + (A i).quadratic y = 0 := by
  classical
  refine ⟨fun h i y ↦ ?_, fun h x ↦ ?_⟩
  · have hy := h (Pi.single i y)
    rwa [pi_quadratic, Finset.sum_eq_single i (fun j _ hj ↦ by
      rw [Pi.single_eq_of_ne hj, QuadraticMap.map_zero]) (by simp), Pi.single_eq_same] at hy
  · rw [pi_quadratic, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ h i (x i)

end Pi

end TauCeti.FiniteQuadraticModule
