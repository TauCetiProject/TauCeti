/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Coordinatewise submodules of `L^p` products

For a family of submodules `s i` of `E i`, the vectors of the `L^p` product `PiLp p E` whose
coordinates lie in the `s i` form a submodule `Submodule.piLp p s`: the product submodule
`Submodule.pi univ s` transported through the identification `PiLp p E ≃ ∀ i, E i`.

## Main declarations

* `Submodule.piLp p s`: the vectors of `PiLp p E` whose coordinates lie in the submodules `s i`,
  with its coordinate projections `Submodule.piLpProj`.
* `Submodule.piLpEquiv p s`: `Submodule.piLp p s` is the product of the `s i`.
* `Submodule.dense_piLp_iff`: `Submodule.piLp p s` is dense if and only if every `s i` is.
-/

public section

open Set WithLp

variable {R ι : Type*} {E : ι → Type*} (p : ENNReal)

namespace Submodule

variable [Semiring R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

/-- The vectors of the `L^p` product whose coordinates lie in the submodules `s i`:
`Submodule.pi univ s` transported to `PiLp p E`. It is the domain of `LinearPMap.piLpMap`. -/
def piLp (s : ∀ i, Submodule R (E i)) : Submodule R (PiLp p E) :=
  (Submodule.pi univ s).comap (WithLp.linearEquiv p R (∀ i, E i)).toLinearMap

variable {p} {s : ∀ i, Submodule R (E i)}

/-- A vector lies in `Submodule.piLp p s` exactly when each coordinate `x i` lies in `s i`. -/
@[simp]
theorem mem_piLp {x : PiLp p E} : x ∈ piLp p s ↔ ∀ i, x i ∈ s i := by
  simp [piLp, Submodule.mem_pi]

/-- A family of vectors `x i ∈ s i` gives a vector of `Submodule.piLp p s`. -/
theorem toLp_mem_piLp (x : ∀ i, s i) : toLp p (fun i ↦ (x i : E i)) ∈ piLp p s :=
  mem_piLp.mpr fun i ↦ (x i).property

/-- A vector of `s i` placed in the `i`-th coordinate, with `0` elsewhere, lies in
`Submodule.piLp p s`. -/
theorem single_mem_piLp [DecidableEq ι] {i : ι} {x : E i} (hx : x ∈ s i) :
    PiLp.single p i x ∈ piLp p s :=
  mem_piLp.mpr fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simp [Pi.single_eq_of_ne hj]

variable (p s) in
/-- The `i`-th coordinate of a vector of `Submodule.piLp p s`, as a vector of `s i`. -/
def piLpProj (i : ι) : piLp p s →ₗ[R] s i :=
  ((LinearMap.proj i).comp ((WithLp.linearEquiv p R (∀ i, E i)).toLinearMap.comp
    (piLp p s).subtype)).codRestrict (s i) fun x ↦ mem_piLp.mp x.property i

/-- `Submodule.piLpProj p s i` reads off the `i`-th coordinate. -/
@[simp]
theorem coe_piLpProj (i : ι) (x : piLp p s) :
    (piLpProj p s i x : E i) = (x : PiLp p E) i :=
  (rfl)

variable (p s) in
/-- `Submodule.piLp p s` is the product of the submodules `s i`. -/
def piLpEquiv : piLp p s ≃ₗ[R] ∀ i, s i where
  toFun x i := piLpProj p s i x
  invFun x := ⟨toLp p fun i ↦ (x i : E i), toLp_mem_piLp x⟩
  map_add' x y := by funext i; simp
  map_smul' c x := by funext i; simp
  left_inv x := Subtype.ext (PiLp.ext fun i ↦ by simp)
  right_inv x := funext fun i ↦ Subtype.ext (by simp)

/-- The `i`-th component of `Submodule.piLpEquiv p s x` is the `i`-th coordinate of `x`. -/
@[simp]
theorem piLpEquiv_apply (x : piLp p s) (i : ι) :
    piLpEquiv p s x i = piLpProj p s i x :=
  (rfl)

/-- `(Submodule.piLpEquiv p s).symm` assembles a family of vectors into a vector of
`PiLp p E`. -/
@[simp]
theorem coe_piLpEquiv_symm_apply (x : ∀ i, s i) :
    ((piLpEquiv p s).symm x : PiLp p E) = toLp p fun i ↦ (x i : E i) :=
  (rfl)

variable [∀ i, TopologicalSpace (E i)]

/-- `Submodule.piLp p s` is dense if and only if every `s i` is dense. -/
theorem dense_piLp_iff :
    Dense (piLp p s : Set (PiLp p E)) ↔ ∀ i, Dense (s i : Set (E i)) := by
  have hdom : (piLp p s : Set (PiLp p E)) =
      PiLp.homeomorph p E ⁻¹' univ.pi fun i ↦ (s i : Set (E i)) := by
    ext x
    simp [← Homeomorph.coe_toEquiv]
  rw [hdom, (PiLp.homeomorph p E).isOpenQuotientMap.dense_preimage_iff]
  refine ⟨fun h i ↦ ?_, fun h ↦ dense_pi univ fun i _ ↦ h i⟩
  -- Every `s i` contains `0`, so `s i` is the image of the product under the `i`-th evaluation.
  rw [← eval_image_univ_pi (t := fun i ↦ (s i : Set (E i))) ⟨0, fun i _ ↦ (s i).zero_mem⟩]
  exact (Function.surjective_eval i).denseRange.dense_image (continuous_apply i) h

end Submodule
