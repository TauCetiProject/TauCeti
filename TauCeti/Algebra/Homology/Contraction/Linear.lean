/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Special contractions of modules with a differential

A *special contraction* of a module `M` with an endomorphism `dM` onto a module `N` with an
endomorphism `dN` consists of linear maps `incl : N → M` and `proj : M → N` commuting with the
endomorphisms, a homotopy `h : M → M` with

`proj ∘ incl = 1`,   `dM h + h dM = 1 - incl ∘ proj`,

and the three side conditions `h ∘ incl = 0`, `proj ∘ h = 0`, `h ∘ h = 0`.  When `dM` and `dN`
square to zero this is the classical strong deformation retract of differential modules.  The
square of `dN` is in any case the compression of the square of `dM` to the retract
(`LinearSpecialContraction.dN_comp_dN`), so once `dM` squares to zero a separate requirement
that `dN` square to zero would be redundant; nothing in the data forces `dM` itself to square to
zero.

`TauCeti.SpecialContraction` packages the same notion degreewise, for cochain complexes in a
preadditive category.  The present total-module form is the one homological perturbation theory
operates on: the perturbation series inverts an endomorphism of the *total* module, and the bar
constructions it is applied to are modules with an internal grading, not degreewise objects.  The
orientation of the contracting equation, with `1 - incl ∘ proj` on the right, is the one fixed by
`TauCeti.Contraction`; the identity contraction `LinearSpecialContraction.refl` therefore has zero
homotopy.

## Main definitions

* `TauCeti.LinearSpecialContraction`: a special contraction of `(M, dM)` onto `(N, dN)`.
* `TauCeti.LinearSpecialContraction.refl`: the identity contraction.

## Main results

* `TauCeti.LinearSpecialContraction.dN_comp_dN`: the square of `dN` is `proj ∘ dM ∘ dM ∘ incl`;
  in particular `dN` squares to zero when `dM` does.
* `TauCeti.LinearSpecialContraction.isHomogeneous_dN`: `dN` has the degree of `dM` when the
  inclusion and projection have degree zero.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
-/

public section

universe uR uM uN uP

namespace TauCeti

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A **special contraction** of `(M, dM)` onto `(N, dN)`: maps `incl`, `proj` commuting with
the endomorphisms, with `proj ∘ incl = 1`, and a homotopy `h` with `dM h + h dM = 1 - incl ∘ proj`
satisfying the side conditions `h ∘ incl = 0`, `proj ∘ h = 0` and `h ∘ h = 0`.  When `dM` squares
to zero (so `dN` does too, by `dN_comp_dN_eq_zero`) this is a strong deformation retract of
differential modules; for general endomorphisms it is the analogous contraction data. -/
@[ext]
structure LinearSpecialContraction (dM : Module.End R M) (dN : Module.End R N) where
  /-- the inclusion of the retract -/
  incl : N →ₗ[R] M
  /-- the projection onto the retract -/
  proj : M →ₗ[R] N
  /-- the contracting homotopy -/
  homotopy : Module.End R M
  /-- the inclusion commutes with the endomorphisms -/
  dM_comp_incl : dM ∘ₗ incl = incl ∘ₗ dN
  /-- the projection commutes with the endomorphisms -/
  proj_comp_dM : proj ∘ₗ dM = dN ∘ₗ proj
  /-- the projection retracts the inclusion -/
  proj_comp_incl : proj ∘ₗ incl = LinearMap.id
  /-- `dM h + h dM` is the complementary idempotent `1 - incl ∘ proj` -/
  dM_comp_homotopy_add_homotopy_comp_dM :
    dM ∘ₗ homotopy + homotopy ∘ₗ dM = LinearMap.id - incl ∘ₗ proj
  /-- the homotopy annihilates the inclusion -/
  homotopy_comp_incl : homotopy ∘ₗ incl = 0
  /-- the projection annihilates the homotopy -/
  proj_comp_homotopy : proj ∘ₗ homotopy = 0
  /-- the homotopy squares to zero -/
  homotopy_comp_homotopy : homotopy ∘ₗ homotopy = 0

namespace LinearSpecialContraction

attribute [simp] dM_comp_incl proj_comp_dM proj_comp_incl homotopy_comp_incl proj_comp_homotopy
  homotopy_comp_homotopy

variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {P : Type uP} [AddCommMonoid P] [Module R P]

/-- The idempotent `incl ∘ proj` of a special contraction is the complement of `dM h + h dM`. -/
theorem incl_comp_proj : c.incl ∘ₗ c.proj = LinearMap.id - (dM ∘ₗ c.homotopy + c.homotopy ∘ₗ dM) :=
  by rw [c.dM_comp_homotopy_add_homotopy_comp_dM, sub_sub_cancel]

/-! ### Reassociated forms

The defining equations, stated with an arbitrary further factor on the right, so that they can
rewrite inside right-associated compositions. -/

@[simp]
theorem proj_comp_incl_assoc (f : P →ₗ[R] N) : c.proj ∘ₗ c.incl ∘ₗ f = f := by
  rw [← LinearMap.comp_assoc, c.proj_comp_incl, LinearMap.id_comp]

@[simp]
theorem homotopy_comp_incl_assoc (f : P →ₗ[R] N) : c.homotopy ∘ₗ c.incl ∘ₗ f = 0 := by
  rw [← LinearMap.comp_assoc, c.homotopy_comp_incl, LinearMap.zero_comp]

@[simp]
theorem proj_comp_homotopy_assoc (f : P →ₗ[R] M) : c.proj ∘ₗ c.homotopy ∘ₗ f = 0 := by
  rw [← LinearMap.comp_assoc, c.proj_comp_homotopy, LinearMap.zero_comp]

@[simp]
theorem homotopy_comp_homotopy_assoc (f : P →ₗ[R] M) : c.homotopy ∘ₗ c.homotopy ∘ₗ f = 0 := by
  rw [← LinearMap.comp_assoc, c.homotopy_comp_homotopy, LinearMap.zero_comp]

@[simp]
theorem dM_comp_incl_assoc (f : P →ₗ[R] N) : dM ∘ₗ c.incl ∘ₗ f = c.incl ∘ₗ dN ∘ₗ f := by
  rw [← LinearMap.comp_assoc, c.dM_comp_incl, LinearMap.comp_assoc]

@[simp]
theorem proj_comp_dM_assoc (f : P →ₗ[R] M) : c.proj ∘ₗ dM ∘ₗ f = dN ∘ₗ c.proj ∘ₗ f := by
  rw [← LinearMap.comp_assoc, c.proj_comp_dM, LinearMap.comp_assoc]

theorem incl_comp_proj_assoc (f : P →ₗ[R] M) :
    c.incl ∘ₗ c.proj ∘ₗ f = f - dM ∘ₗ c.homotopy ∘ₗ f - c.homotopy ∘ₗ dM ∘ₗ f := by
  rw [← LinearMap.comp_assoc, c.incl_comp_proj, LinearMap.sub_comp, LinearMap.id_comp,
    LinearMap.add_comp, LinearMap.comp_assoc, LinearMap.comp_assoc, sub_add_eq_sub_sub]

/-! ### Pointwise forms

The defining equations evaluated on elements. -/

@[simp]
theorem proj_incl_apply (y : N) : c.proj (c.incl y) = y :=
  LinearMap.congr_fun c.proj_comp_incl y

@[simp]
theorem homotopy_incl_apply (y : N) : c.homotopy (c.incl y) = 0 :=
  LinearMap.congr_fun c.homotopy_comp_incl y

@[simp]
theorem proj_homotopy_apply (x : M) : c.proj (c.homotopy x) = 0 :=
  LinearMap.congr_fun c.proj_comp_homotopy x

@[simp]
theorem homotopy_homotopy_apply (x : M) : c.homotopy (c.homotopy x) = 0 :=
  LinearMap.congr_fun c.homotopy_comp_homotopy x

@[simp]
theorem dM_incl_apply (y : N) : dM (c.incl y) = c.incl (dN y) :=
  LinearMap.congr_fun c.dM_comp_incl y

@[simp]
theorem proj_dM_apply (x : M) : c.proj (dM x) = dN (c.proj x) :=
  LinearMap.congr_fun c.proj_comp_dM x

theorem incl_proj_apply (x : M) :
    c.incl (c.proj x) = x - dM (c.homotopy x) - c.homotopy (dM x) := by
  rw [← LinearMap.comp_apply, c.incl_comp_proj]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, sub_add_eq_sub_sub]

/-! ### The square of the differential of the retract -/

/-- The square of `dN` is the compression `proj ∘ dM² ∘ incl` of the square of `dM` to the
retract. -/
theorem dN_comp_dN : dN ∘ₗ dN = c.proj ∘ₗ dM ∘ₗ dM ∘ₗ c.incl := by
  rw [c.dM_comp_incl, c.dM_comp_incl_assoc, c.proj_comp_incl_assoc]

include c in
/-- If `dM` squares to zero, so does the endomorphism of the retract. -/
theorem dN_comp_dN_eq_zero (h : dM ∘ₗ dM = 0) : dN ∘ₗ dN = 0 := by
  rw [c.dN_comp_dN, ← LinearMap.comp_assoc c.incl dM dM, h, LinearMap.zero_comp,
    LinearMap.comp_zero]

/-- The endomorphism of the retract has the degree of `dM` when the inclusion and projection have
degree zero, since it is the compression `proj ∘ dM ∘ incl`. -/
theorem isHomogeneous_dN {ι σM σN : Type*} [AddMonoid ι] [SetLike σM M] [SetLike σN N]
    {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} (hdM : LinearMap.IsHomogeneous dM 𝒜 𝒜 q)
    (hincl : LinearMap.IsHomogeneous c.incl ℬ 𝒜 0)
    (hproj : LinearMap.IsHomogeneous c.proj 𝒜 ℬ 0) :
    LinearMap.IsHomogeneous dN ℬ ℬ q := by
  have h : dN = c.proj ∘ₗ dM ∘ₗ c.incl := by
    rw [← LinearMap.comp_assoc, c.proj_comp_dM, LinearMap.comp_assoc, c.proj_comp_incl,
      LinearMap.comp_id]
  rw [h]
  simpa only [zero_add, add_zero] using hproj.comp (hdM.comp hincl)

/-- Every module with an endomorphism is a special contraction of itself, with zero homotopy.
This pins the orientation of the contracting equation: it has `1 - incl ∘ proj` on the right. -/
def refl (dM : Module.End R M) : LinearSpecialContraction dM dM where
  incl := LinearMap.id
  proj := LinearMap.id
  homotopy := 0
  dM_comp_incl := by simp
  proj_comp_dM := by simp
  proj_comp_incl := by simp
  dM_comp_homotopy_add_homotopy_comp_dM := by simp
  homotopy_comp_incl := by simp
  proj_comp_homotopy := by simp
  homotopy_comp_homotopy := by simp

/-- The identity contraction has the identity as inclusion. -/
@[simp] theorem refl_incl (dM : Module.End R M) : (refl dM).incl = LinearMap.id := (rfl)

/-- The identity contraction has the identity as projection. -/
@[simp] theorem refl_proj (dM : Module.End R M) : (refl dM).proj = LinearMap.id := (rfl)

/-- The identity contraction has zero homotopy. -/
@[simp] theorem refl_homotopy (dM : Module.End R M) : (refl dM).homotopy = 0 := (rfl)

end LinearSpecialContraction

end TauCeti
