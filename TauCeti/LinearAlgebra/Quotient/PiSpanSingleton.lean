/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination

/-!
# The quotient of `X → R` by one vector with a unit coordinate

Let `R` be a commutative ring, `X` a type with a distinguished point `x₀`, and `w : X → R` a
vector with `w x₀ = 1`. Every `u : X → R` decomposes uniquely as `u x₀ • w` plus a vector
vanishing at `x₀`, which gives a change of coordinates on the product module `X → R`: the new
coordinates of `u` are `u x - u x₀ * w x` for `x ≠ x₀` together with `u x₀`. (For finite `X` this
is the change of basis replacing the coordinate vector at `x₀` by `w`.) The resulting linear
isomorphism

`LinearEquiv.piSplitAt x₀ w hw : (X → R) ≃ₗ[R] ({x // x ≠ x₀} → R) × R`

sends `c • w` to `(0, c)`. Composing with reduction modulo an element `q` in the second factor
gives a surjective linear map onto `({x // x ≠ x₀} → R) × R ⧸ (q)` whose kernel is exactly the
span of the single vector `q • w`, hence the identification

`(X → R) ⧸ span {q • w} ≃ₗ[R] ({x // x ≠ x₀} → R) × R ⧸ (q)`.

Every vector `v` with a coordinate `v x₀` dividing all the other coordinates has the shape
`v = v x₀ • w` with `w x₀ = 1` (`exists_eq_smul_of_forall_dvd`); over a valuation ring every
vector on a finite nonempty index type has such a coordinate. This is the linear algebra behind the
structure of the abelianization of a one-relator pro-`p` group: the relator contributes the single
vector `v = q • w` to `ℤ_p^n`, and the quotient is `ℤ_p^{n-1} × ℤ_p/q`.

## Main definitions

* `TauCeti.LinearEquiv.piSplitAt`: the change of coordinates
  `(X → R) ≃ₗ[R] ({x // x ≠ x₀} → R) × R` replacing the coordinate at `x₀` by the coordinate
  along `w`.
* `TauCeti.LinearMap.piSplitAtQuot`: the composite with reduction modulo `q` in the second
  factor.
* `TauCeti.LinearEquiv.piQuotSpanSmul`: the induced isomorphism
  `(X → R) ⧸ span {q • w} ≃ₗ[R] ({x // x ≠ x₀} → R) × R ⧸ (q)`.

## Main results

* `TauCeti.LinearMap.ker_piSplitAtQuot`, `TauCeti.LinearMap.piSplitAtQuot_surjective`: the
  kernel of the reduction is the span of `q • w`, and it is surjective.
* `TauCeti.exists_eq_smul_of_forall_dvd`: a vector with a coordinate dividing all the others is a
  multiple of a vector with a `1` at that coordinate.
-/

public section

namespace TauCeti

/-- A vector with a coordinate `v x₀` dividing every coordinate is `v x₀ • w` for a vector `w`
with `w x₀ = 1`. -/
theorem exists_eq_smul_of_forall_dvd {R X : Type*} [Monoid R] {v : X → R} {x₀ : X}
    (h : ∀ x, v x₀ ∣ v x) : ∃ w : X → R, w x₀ = 1 ∧ v = v x₀ • w := by
  classical
  have h' : ∀ x, ∃ c, v x = v x₀ * c := h
  choose c hc using h'
  refine ⟨Function.update c x₀ 1, Function.update_self x₀ 1 c, funext fun x ↦ ?_⟩
  by_cases hx : x = x₀
  · subst hx
    simp
  · simp [Function.update_of_ne hx, hc x]

variable {R : Type*} [CommRing R] {X : Type*}

namespace LinearEquiv

variable (x₀ : X) (w : X → R) (hw : w x₀ = 1)

open Classical in
/-- **The change of coordinates on `X → R` replacing the coordinate at `x₀` by the coordinate
along `w`.** For `w x₀ = 1`, every `u : X → R` decomposes uniquely as `u x₀ • w` plus a vector
vanishing at `x₀`; the new coordinates of `u` are `u x - u x₀ * w x` at `x ≠ x₀` and `u x₀` along
`w`. For finite `X` this is the change of basis from the coordinate vectors to `w` together with
the coordinate vectors at `x ≠ x₀`. -/
noncomputable def piSplitAt : (X → R) ≃ₗ[R] ({x // x ≠ x₀} → R) × R where
  toFun u := (fun x ↦ u x - u x₀ * w x, u x₀)
  invFun a x := (if h : x = x₀ then 0 else a.1 ⟨x, h⟩) + a.2 * w x
  map_add' u v := by
    ext x
    · simp only [Prod.fst_add, Pi.add_apply]
      ring
    · simp only [Prod.snd_add, Pi.add_apply]
  map_smul' c u := by
    ext x
    · simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
  left_inv u := funext fun x ↦ by
    by_cases h : x = x₀
    · subst h
      simp [hw]
    · simp [h]
  right_inv a := Prod.ext (funext fun x ↦ by simp [x.2, hw]) (by simp [hw])

@[simp]
theorem piSplitAt_apply (u : X → R) :
    piSplitAt x₀ w hw u = (fun x : {x // x ≠ x₀} ↦ u x - u x₀ * w x, u x₀) :=
  (rfl)

@[simp]
theorem piSplitAt_symm_apply [DecidableEq X] (a : ({x // x ≠ x₀} → R) × R) (x : X) :
    (piSplitAt x₀ w hw).symm a x = (if h : x = x₀ then 0 else a.1 ⟨x, h⟩) + a.2 * w x := by
  by_cases h : x = x₀ <;> simp [piSplitAt, h]

/-- The change of coordinates sends a multiple of `w` to the corresponding multiple in the second
factor. -/
theorem piSplitAt_smul (c : R) : piSplitAt x₀ w hw (c • w) = (0, c) := by
  ext x <;> simp [hw]

/-- The change of coordinates fixes the coordinate vectors at `x ≠ x₀`. -/
theorem piSplitAt_single_of_ne [DecidableEq X] {x : X} (hx : x ≠ x₀) :
    piSplitAt x₀ w hw (Pi.single x 1) = (Pi.single ⟨x, hx⟩ 1, 0) := by
  ext y
  · simp [Pi.single_apply, Subtype.ext_iff, hx.symm]
  · simp [hx.symm]

/-- The change of coordinates sends the coordinate vector at `x₀` to `(-w, 1)`: it is `w` minus
the vector `w - e_{x₀}` supported away from `x₀`. -/
theorem piSplitAt_single_self [DecidableEq X] :
    piSplitAt x₀ w hw (Pi.single x₀ 1) = (fun x : {x // x ≠ x₀} ↦ -w x, 1) := by
  ext y
  · simp [Pi.single_eq_of_ne y.2]
  · simp

end LinearEquiv

namespace LinearMap

variable (x₀ : X) (w : X → R) (hw : w x₀ = 1) (q : R)

/-- The change of coordinates `LinearEquiv.piSplitAt` followed by reduction modulo `q` on the
coordinate along `w`. Its kernel is the span of `q • w` (`ker_piSplitAtQuot`), and it is
surjective (`piSplitAtQuot_surjective`). -/
noncomputable def piSplitAtQuot : (X → R) →ₗ[R] ({x // x ≠ x₀} → R) × (R ⧸ Ideal.span {q}) :=
  (LinearMap.id.prodMap (Ideal.span {q}).mkQ) ∘ₗ (LinearEquiv.piSplitAt x₀ w hw).toLinearMap

@[simp]
theorem piSplitAtQuot_apply (u : X → R) :
    piSplitAtQuot x₀ w hw q u =
      (fun x : {x // x ≠ x₀} ↦ u x - u x₀ * w x,
        (Submodule.Quotient.mk (u x₀) : R ⧸ Ideal.span {q})) :=
  (rfl)

/-- The reduction composed with the inverse change of coordinates is reduction modulo `q` on the
second coordinate. -/
theorem piSplitAtQuot_piSplitAt_symm (a : {x // x ≠ x₀} → R) (b : R) :
    piSplitAtQuot x₀ w hw q ((LinearEquiv.piSplitAt x₀ w hw).symm (a, b)) =
      (a, Submodule.Quotient.mk b) := by
  simp [piSplitAtQuot]

/-- The change of coordinates followed by reduction modulo `q` is surjective. -/
theorem piSplitAtQuot_surjective : Function.Surjective (piSplitAtQuot x₀ w hw q) := by
  rintro ⟨a, b⟩
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact ⟨(LinearEquiv.piSplitAt x₀ w hw).symm (a, c), piSplitAtQuot_piSplitAt_symm x₀ w hw q a c⟩

/-- The reduction fixes the coordinate vectors at `x ≠ x₀`. -/
theorem piSplitAtQuot_single_of_ne [DecidableEq X] {x : X} (hx : x ≠ x₀) :
    piSplitAtQuot x₀ w hw q (Pi.single x 1) = (Pi.single ⟨x, hx⟩ 1, 0) := by
  simp [piSplitAtQuot, LinearEquiv.piSplitAt_single_of_ne x₀ w hw hx]

/-- The reduction sends the coordinate vector at `x₀` to `(-w, 1)`. -/
theorem piSplitAtQuot_single_self [DecidableEq X] :
    piSplitAtQuot x₀ w hw q (Pi.single x₀ 1) =
      (fun x : {x // x ≠ x₀} ↦ -w x, Submodule.Quotient.mk 1) := by
  simp [piSplitAtQuot, LinearEquiv.piSplitAt_single_self x₀ w hw]

/-- **The kernel of the reduction is the span of `q • w`.** -/
theorem ker_piSplitAtQuot : LinearMap.ker (piSplitAtQuot x₀ w hw q) = Submodule.span R {q • w} := by
  ext u
  rw [LinearMap.mem_ker, piSplitAtQuot_apply, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_span_singleton', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h, a, ha⟩
    refine ⟨a, funext fun x ↦ ?_⟩
    by_cases hx : x = x₀
    · subst hx
      simp [hw, ha]
    · have hx' := congr_fun h ⟨x, hx⟩
      rw [Pi.zero_apply, ← ha] at hx'
      simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination (-1 : R) * hx'
  · rintro ⟨a, rfl⟩
    refine ⟨funext fun x ↦ ?_, a, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hw, Pi.zero_apply]
      ring
    · simp [hw]

end LinearMap

namespace LinearEquiv

variable (x₀ : X) (w : X → R) (hw : w x₀ = 1) (q : R)

/-- **The quotient of `X → R` by one vector.** For `w x₀ = 1`, the quotient of `X → R` by the
span of `q • w` is `({x // x ≠ x₀} → R) × R ⧸ (q)`, through the change of coordinates
`LinearEquiv.piSplitAt`. -/
noncomputable def piQuotSpanSmul :
    ((X → R) ⧸ Submodule.span R {q • w}) ≃ₗ[R] ({x // x ≠ x₀} → R) × (R ⧸ Ideal.span {q}) :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.ker_piSplitAtQuot x₀ w hw q).symm).trans
    ((LinearMap.piSplitAtQuot x₀ w hw q).quotKerEquivOfSurjective
      (LinearMap.piSplitAtQuot_surjective x₀ w hw q))

@[simp]
theorem piQuotSpanSmul_mk (u : X → R) :
    piQuotSpanSmul x₀ w hw q (Submodule.Quotient.mk u) = LinearMap.piSplitAtQuot x₀ w hw q u := by
  simp [piQuotSpanSmul]

end LinearEquiv

end TauCeti
