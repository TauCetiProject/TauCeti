/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic

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

* `TauCeti.FiniteQuadraticModule.pi`: the orthogonal sum of a finite family.
* `TauCeti.FiniteQuadraticModule.pi_quadratic` and `TauCeti.FiniteQuadraticModule.pi_pairing`: its
  quadratic map and pairing are the sums of the coordinate ones.
* `TauCeti.FiniteQuadraticModule.isNondegenerate_pi_iff`: the orthogonal sum is nondegenerate
  exactly when every summand is.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace TauCeti.FiniteQuadraticModule

universe u v

section Pi

variable {ι : Type v} [Fintype ι] (A : ι → FiniteQuadraticModule.{u})

/-- **The orthogonal sum of a finite family of finite quadratic modules**: the group `Π i, A i`
with the quadratic map `x ↦ ∑ i, q_i(x_i)`, Mathlib's `QuadraticMap.pi`, and its polar pairing.

Reducible, exactly as `TauCeti.FiniteQuadraticModule.prod` is, so that the carrier of an orthogonal
sum reduces to the product of the carriers. -/
abbrev pi : FiniteQuadraticModule.{max u v} where
  carrier := ∀ i, A i
  pairing := LinearMap.toAddMonoidHom'.comp
    (QuadraticMap.pi fun i ↦ (A i).quadratic).polarBilin.toAddMonoidHom
  pairing_comm x y := QuadraticMap.polar_comm _ x y
  quadratic := QuadraticMap.pi fun i ↦ (A i).quadratic
  polar_eq_pairing' _ _ := rfl

/-- The quadratic map of an orthogonal sum is the sum of the coordinate quadratic maps. -/
theorem pi_quadratic (x : pi A) : (pi A).quadratic x = ∑ i, (A i).quadratic (x i) :=
  QuadraticMap.pi_apply _ x

/-- The pairing of an orthogonal sum is the sum of the coordinate pairings. -/
theorem pi_pairing (x y : pi A) :
    (pi A).toFiniteBilinearModule.pairing x y =
      ∑ i, (A i).toFiniteBilinearModule.pairing (x i) (y i) := by
  simp only [← polar_eq_pairing]
  exact QuadraticMap.Ring.polar_pi _ x y

/-- **An orthogonal sum is nondegenerate exactly when every summand is.** -/
@[simp]
theorem isNondegenerate_pi_iff :
    (pi A).IsNondegenerate ↔ ∀ i, (A i).IsNondegenerate := by
  classical
  constructor
  · intro h i
    refine FiniteBilinearModule.isNondegenerate_of_radical_eq_bot _ (eq_bot_iff.2 fun x hx ↦ ?_)
    rw [FiniteBilinearModule.mem_radical_iff] at hx
    rw [AddSubgroup.mem_bot]
    -- `Pi.single i x` pairs with `y` as `x` pairs with `y i`, so it lies in the radical.
    have hsingle : (Pi.single i x : pi A) = 0 :=
      FiniteBilinearModule.IsNondegenerate.eq_zero_of_forall_pairing_eq_zero _ h fun y ↦ by
        rw [pi_pairing, Finset.sum_eq_single i (fun j _ hj ↦ by
          rw [Pi.single_eq_of_ne hj, FiniteBilinearModule.pairing_zero_left]) (by simp),
          Pi.single_eq_same]
        exact hx (y i)
    simpa using congr_fun hsingle i
  · intro h
    refine FiniteBilinearModule.isNondegenerate_of_radical_eq_bot _ (eq_bot_iff.2 fun x hx ↦ ?_)
    rw [FiniteBilinearModule.mem_radical_iff] at hx
    rw [AddSubgroup.mem_bot]
    funext i
    -- `x i` pairs with `y` as `x` pairs with `Pi.single i y`.
    refine FiniteBilinearModule.IsNondegenerate.eq_zero_of_forall_pairing_eq_zero _ (h i)
      fun y ↦ ?_
    have hxy := hx (Pi.single i y)
    rwa [pi_pairing, Finset.sum_eq_single i (fun j _ hj ↦ by
      rw [Pi.single_eq_of_ne hj, FiniteBilinearModule.pairing_zero_right]) (by simp),
      Pi.single_eq_same] at hxy

end Pi

end TauCeti.FiniteQuadraticModule
