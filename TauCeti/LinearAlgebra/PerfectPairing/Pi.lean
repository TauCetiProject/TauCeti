/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Finite products of bilinear pairings

Given a finite family of bilinear pairings `p c : M c →ₗ[R] N c →ₗ[R] R` over a commutative
semiring, their coordinatewise sum `LinearMap.piPairing p` pairs `∀ c, M c` with `∀ c, N c` by
`∑ c, p c (x c) (y c)`.

When every `p c` is a perfect pairing, `LinearMap.piPairing p` is again a perfect pairing:
composing the coordinatewise linear equivalences `M c ≃ₗ[R] Module.Dual R (N c)` with Mathlib's
`LinearMap.lsum` exhibits the induced map into `Module.Dual R (∀ c, N c)` as a linear equivalence,
and flipping gives the dual side. No finiteness, freeness, or subtraction on the modules is needed.

## Main definitions

* `LinearMap.piPairing`: the coordinatewise sum of a finite family of bilinear pairings.

## Main results

* `LinearMap.IsPerfPair.pi`: a finite product of perfect pairings is a perfect pairing.
* `Module.IsReflexive.pi`: a finite product of reflexive modules is reflexive.
* `LinearMap.toPerfPair_piPairing`: the induced linear equivalence into the dual of the product
  factors through `LinearEquiv.piCongrRight` and `LinearMap.lsum`.
-/

public section

namespace LinearMap

variable {κ R : Type*} [Fintype κ] [CommSemiring R] {M N : κ → Type*}
  [∀ c, AddCommMonoid (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommMonoid (N c)] [∀ c, Module R (N c)]

/-- The finite product of a family of bilinear pairings `p c : M c →ₗ[R] N c →ₗ[R] R`, defined on
`(∀ c, M c)` and `(∀ c, N c)` by summing `p c (x c) (y c)` over `c`. -/
def piPairing (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R) :
    (∀ c, M c) →ₗ[R] (∀ c, N c) →ₗ[R] R :=
  ∑ c, (p c).compl₁₂ (proj c) (proj c)

theorem piPairing_apply_apply (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R)
    (x : ∀ c, M c) (y : ∀ c, N c) :
    piPairing p x y = ∑ c, p c (x c) (y c) := by
  simp [piPairing]

@[simp]
theorem flip_piPairing (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R) :
    (piPairing p).flip = piPairing fun c ↦ (p c).flip := by
  ext x y
  simp [piPairing_apply_apply]

@[simp]
theorem piPairing_single_left [DecidableEq κ] (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R)
    (c : κ) (x : M c) (y : ∀ d, N d) :
    piPairing p (Pi.single c x) y = p c x (y c) := by
  simp [piPairing_apply_apply, Pi.apply_single (fun d z ↦ p d z (y d)) (fun _ ↦ by simp)]

@[simp]
theorem piPairing_single_right [DecidableEq κ] (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R)
    (x : ∀ d, M d) (c : κ) (y : N c) :
    piPairing p x (Pi.single c y) = p c (x c) y := by
  rw [← flip_apply, flip_piPairing, piPairing_single_left, flip_apply]

/-- The linear equivalence `(∀ c, M c) ≃ₗ[R] Module.Dual R (∀ c, N c)` underlying a finite product
of perfect pairings agrees pointwise with `piPairing`. -/
private theorem piPairing_eq_toPerfPair_trans_lsum [DecidableEq κ]
    (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R) [∀ c, (p c).IsPerfPair] :
    ⇑(piPairing p) =
      ⇑((LinearEquiv.piCongrRight fun c ↦ (p c).toPerfPair).trans (lsum R N R)) := by
  ext x y
  simp [piPairing_apply_apply, lsum_apply]

/-- **A finite product of perfect pairings is a perfect pairing.** -/
instance IsPerfPair.pi (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R) [∀ c, (p c).IsPerfPair] :
    (piPairing p).IsPerfPair := by
  classical
  refine ⟨?_, ?_⟩
  · rw [piPairing_eq_toPerfPair_trans_lsum p]
    exact LinearEquiv.bijective _
  · rw [flip_piPairing, piPairing_eq_toPerfPair_trans_lsum fun c ↦ (p c).flip]
    exact LinearEquiv.bijective _

/-- The dual equivalence induced by a finite product of perfect pairings is the coordinatewise
equivalence followed by `LinearMap.lsum`. -/
theorem toPerfPair_piPairing [DecidableEq κ] (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R)
    [∀ c, (p c).IsPerfPair] :
    (piPairing p).toPerfPair =
      (LinearEquiv.piCongrRight fun c ↦ (p c).toPerfPair).trans (lsum R N R) :=
  LinearEquiv.ext (congrFun (piPairing_eq_toPerfPair_trans_lsum p))

/-- The inverse of `(piPairing p).toPerfPair` evaluates each coordinate by restricting the
functional along `LinearMap.single` and applying `(p c).toPerfPair.symm`. -/
@[simp]
theorem toPerfPair_piPairing_symm_apply [DecidableEq κ] (p : ∀ c, M c →ₗ[R] N c →ₗ[R] R)
    [∀ c, (p c).IsPerfPair] (f : Module.Dual R (∀ c, N c)) (c : κ) :
    (piPairing p).toPerfPair.symm f c = (p c).toPerfPair.symm (f.comp (single R N c)) := by
  rw [toPerfPair_piPairing]
  simp [lsum_symm_apply]

end LinearMap

/-- **A finite product of reflexive modules is reflexive.** -/
instance Module.IsReflexive.pi {κ R : Type*} [Finite κ] [CommSemiring R] {M : κ → Type*}
    [∀ c, AddCommMonoid (M c)] [∀ c, Module R (M c)] [∀ c, Module.IsReflexive R (M c)] :
    Module.IsReflexive R (∀ c, M c) :=
  let _ := Fintype.ofFinite κ
  Module.IsReflexive.of_isPerfPair (LinearMap.piPairing fun c ↦ Module.Dual.eval R (M c))
