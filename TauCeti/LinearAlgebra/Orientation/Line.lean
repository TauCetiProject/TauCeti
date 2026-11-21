/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.LinearAlgebra.Orientation
import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.LinearAlgebra.Pi.SignChange

/-!
# The orientation line of a vector space

For a module `M` over an ordered commutative ring `𝕜` and a ring `R`, the **orientation line** of
`M` with coefficients in `R` (`TauCeti.orientationLine R 𝕜 M ι`) is the `R`-module of the functions
on the orientations of `M` that change sign with the orientation: the `g` with `g (-o) = -g o`.
When `𝕜` is a linearly ordered field and the index type `ι` has the dimension of `M`, so that `M`
has exactly two opposite orientations, it is a free `R`-module of rank one, with no preferred
generator: evaluation at any orientation `o` identifies it with `R`
(`Orientation.orientationLineEquiv`, an instance of
`TauCeti.eval_bijective_of_mem_iff_apply_eq_neg`), and evaluation at `-o` is the opposite
identification. For `R = ℤ` this is the orientation group `o(M)` of `M`, whose two generators are
the two orientations. It is the fibre of the sign local system of an orientation double cover
(`TauCeti.signFiber`), for a single vector space rather than the fibres of a bundle.

The orientation lines are the coefficient-free form of choices of orientations. The integral Morse
complex, for instance, is the sum of the orientation lines of the unstable manifolds at the
critical points; choosing orientations identifies it with the free module on the critical points.

A linear isomorphism `e : M ≃ₗ[𝕜] N` transports orientations, and hence orientation lines
(`LinearEquiv.orientationLineCongr`): a function on the orientations of `M` goes to the function
on those of `N` taking the value `g o` at the image of `o`.

## Main definitions

* `TauCeti.orientationLine R 𝕜 M ι`: the functions on `Orientation 𝕜 M ι` with values in `R`
  that change sign with the orientation.
* `Orientation.orientationLineEquiv`: evaluation at an orientation, an isomorphism with `R`.
* `LinearEquiv.orientationLineCongr`: transport of orientation lines along a linear isomorphism.

## Main results

* `Orientation.orientationLineEquiv_neg`: evaluation at the opposite orientation is the opposite
  identification with `R`.
* `LinearEquiv.orientationLineCongr_apply_map`: the transported function at the transported
  orientation.
* `LinearEquiv.orientationLineCongr_symm`, `LinearEquiv.orientationLineCongr_refl` and
  `LinearEquiv.orientationLineCongr_trans`: transport along the inverse isomorphism, the identity
  and a composite.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`).
-/

public section

open Module

namespace TauCeti

section CommRing

variable (R : Type*) [Ring R] (𝕜 : Type*) [CommRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (M : Type*) [AddCommGroup M] [Module 𝕜 M] (ι : Type*)

/-- The **orientation line** of `M` with coefficients in `R`: the functions `g` on the orientations
of `M` with `g (-o) = -g o`. When `𝕜` is a linearly ordered field and `ι` has the dimension of
`M`, it is free of rank one over `R`, evaluation at either orientation being an isomorphism with
`R` (`Orientation.orientationLineEquiv`). -/
def orientationLine : Submodule R (Orientation 𝕜 M ι → R) where
  carrier := {g | Function.Odd g}
  add_mem' := Function.Odd.add
  zero_mem' := Function.Odd.zero
  smul_mem' r _ hg := hg.const_smul r

variable {R 𝕜 M ι}

/-- A function on the orientations lies in the orientation line when it changes sign with the
orientation. -/
@[simp]
theorem mem_orientationLine_iff {g : Orientation 𝕜 M ι → R} :
    g ∈ orientationLine R 𝕜 M ι ↔ ∀ o, g (-o) = -g o :=
  Iff.rfl

/-- An element of the orientation line changes sign with the orientation. -/
@[simp]
theorem orientationLine_apply_neg (g : orientationLine R 𝕜 M ι) (o : Orientation 𝕜 M ι) :
    (g : Orientation 𝕜 M ι → R) (-o) = -(g : Orientation 𝕜 M ι → R) o :=
  g.property o

end CommRing

section Field

variable {R : Type*} [Ring R] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {M : Type*} [AddCommGroup M] [Module 𝕜 M] {ι : Type*}

/-- Evaluation at an orientation is bijective on the orientation line, when `ι` has the dimension
of `M`: the orientations are `o` and `-o`. -/
private theorem orientationLine_eval_bijective [Fintype ι] (h : Fintype.card ι = finrank 𝕜 M)
    (o : Orientation 𝕜 M ι) :
    Function.Bijective fun g : orientationLine R 𝕜 M ι ↦ (g : Orientation 𝕜 M ι → R) o :=
  eval_bijective_of_mem_iff_apply_eq_neg (σ := Neg.neg) (fun o' ↦ (Module.Ray.ne_neg_self o').symm)
    (fun o' : Orientation 𝕜 M ι ↦ o'.eq_or_eq_neg_of_card_eq_finrank o h)
    fun _ ↦ mem_orientationLine_iff

/-- Two elements of the orientation line agree as soon as they agree at one orientation, when `ι`
has the dimension of `M`. -/
theorem orientationLine_ext [Fintype ι] (h : Fintype.card ι = finrank 𝕜 M)
    (o : Orientation 𝕜 M ι) {g g' : orientationLine R 𝕜 M ι}
    (hg : (g : Orientation 𝕜 M ι → R) o = (g' : Orientation 𝕜 M ι → R) o) : g = g' :=
  (orientationLine_eval_bijective h o).1 hg

end Field

end TauCeti

namespace Orientation

open TauCeti

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {M : Type*} [AddCommGroup M] [Module 𝕜 M] {ι : Type*} [Fintype ι]

variable (o : Orientation 𝕜 M ι) (R : Type*) [Ring R] (h : Fintype.card ι = finrank 𝕜 M)

/-- **Evaluation at an orientation** identifies the orientation line with the coefficients, when
`ι` has the dimension of `M`. -/
noncomputable def orientationLineEquiv : orientationLine R 𝕜 M ι ≃ₗ[R] R :=
  LinearEquiv.ofBijective ((LinearMap.proj o).comp (orientationLine R 𝕜 M ι).subtype)
    (orientationLine_eval_bijective h o)

variable {o R h}

@[simp]
theorem orientationLineEquiv_apply (g : orientationLine R 𝕜 M ι) :
    o.orientationLineEquiv R h g = (g : Orientation 𝕜 M ι → R) o :=
  (rfl)

/-- The element of the orientation line with value `r` at `o`, evaluated at `o`. -/
@[simp]
theorem orientationLineEquiv_symm_apply_self (r : R) :
    ((o.orientationLineEquiv R h).symm r : Orientation 𝕜 M ι → R) o = r :=
  (o.orientationLineEquiv R h).apply_symm_apply r

/-- The element of the orientation line with value `r` at `o`, evaluated at `-o`. -/
theorem orientationLineEquiv_symm_apply_neg (r : R) :
    ((o.orientationLineEquiv R h).symm r : Orientation 𝕜 M ι → R) (-o) = -r := by
  rw [orientationLine_apply_neg, orientationLineEquiv_symm_apply_self]

/-- **Evaluation at the opposite orientation is the opposite identification** of the orientation
line with the coefficients. -/
theorem orientationLineEquiv_neg (g : orientationLine R 𝕜 M ι) :
    (-o).orientationLineEquiv R h g = -o.orientationLineEquiv R h g :=
  orientationLine_apply_neg g o

end Orientation

namespace LinearEquiv

open TauCeti

variable {𝕜 : Type*} [CommRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {M N : Type*} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] {ι : Type*}
  (e : M ≃ₗ[𝕜] N) (R : Type*) [Ring R]

/-- **Transport of orientation lines** along a linear isomorphism `e`: a function `g` on the
orientations of `M` goes to the function on the orientations of `N` whose value at the image of
`o` under `e` is `g o`. -/
noncomputable def orientationLineCongr : orientationLine R 𝕜 M ι ≃ₗ[R] orientationLine R 𝕜 N ι where
  toFun g := ⟨fun o ↦ (g : Orientation 𝕜 M ι → R) (Orientation.map ι e.symm o), fun o ↦ by
    simp [Orientation.map_neg]⟩
  invFun g := ⟨fun o ↦ (g : Orientation 𝕜 N ι → R) (Orientation.map ι e o), fun o ↦ by
    simp [Orientation.map_neg]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv g := Subtype.ext (funext fun o ↦ by simp)
  right_inv g := Subtype.ext (funext fun o ↦ by simp)

variable {e R}

@[simp]
theorem orientationLineCongr_apply (g : orientationLine R 𝕜 M ι) (o : Orientation 𝕜 N ι) :
    (e.orientationLineCongr R g : Orientation 𝕜 N ι → R) o =
      (g : Orientation 𝕜 M ι → R) (Orientation.map ι e.symm o) :=
  (rfl)

/-- The transported function at the transported orientation is the original function at the
original orientation. -/
theorem orientationLineCongr_apply_map (g : orientationLine R 𝕜 M ι) (o : Orientation 𝕜 M ι) :
    (e.orientationLineCongr R g : Orientation 𝕜 N ι → R) (Orientation.map ι e o) =
      (g : Orientation 𝕜 M ι → R) o := by
  rw [orientationLineCongr_apply, Orientation.map_symm_map]

/-- Transport along the inverse isomorphism is the inverse transport. -/
@[simp]
theorem orientationLineCongr_symm :
    (e.orientationLineCongr R).symm = e.symm.orientationLineCongr (ι := ι) R :=
  LinearEquiv.ext fun g ↦ Subtype.ext (funext fun o ↦ by simp [orientationLineCongr])

variable (𝕜 M ι R) in
/-- Transport along the identity is the identity. -/
@[simp]
theorem orientationLineCongr_refl :
    (LinearEquiv.refl 𝕜 M).orientationLineCongr (ι := ι) R = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun g ↦ Subtype.ext (funext fun o ↦ by simp)

/-- Transport along a composite is the composite of the transports. -/
@[simp]
theorem orientationLineCongr_trans {P : Type*} [AddCommGroup P] [Module 𝕜 P] (e' : N ≃ₗ[𝕜] P) :
    (e.trans e').orientationLineCongr (ι := ι) R =
      (e.orientationLineCongr R).trans (e'.orientationLineCongr R) :=
  LinearEquiv.ext fun g ↦ Subtype.ext (funext fun o ↦ by simp [Orientation.map_trans])

end LinearEquiv
