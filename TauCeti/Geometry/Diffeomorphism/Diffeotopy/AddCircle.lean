/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Calculus.Deriv.AddCircle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Interpolating circle diffeomorphisms to the identity

An orientation-preserving diffeomorphism `φ` of the circle `AddCircle T` is presented by a lift
`F : ℝ → ℝ` with `F (x + T) = F x + T` and `F' > 0`. For a weight `w ∈ [0, 1]` the map
`x ↦ x + w (F x - x)` is again such a lift: its derivative `(1 - w) + w F'` is positive. So the
lifts interpolate between the identity and `F` through circle diffeomorphisms. This file makes the
interpolation smooth in all variables at once, including the inverses, and uses it to extend `φ`
across a product collar `ℝ × AddCircle T`: equal to `φ` on one side of the collar and to the
identity on the other. This is the step that extends a prescribed boundary-circle diffeomorphism
of a surface into a collar of that boundary circle.

The general construction is `AddCircle.prodDiffeomorphOfLift`. Let `L : ℝ × ℝ → ℝ` be a `C^n`
family of lifts, `L (s, x + T) = L (s, x) + T`, with positive derivative in `x`, and let
`κ : N → ℝ` be a `C^n` function on a manifold `N`, possibly with boundary or corners. Then
`(a, [x]) ↦ (a, [L (κ a, x)])` is a `C^n` diffeomorphism of `N × AddCircle T`. The forward map is
smooth because the quotient map `ℝ → AddCircle T` is a local diffeomorphism. For the inverse, the
map `(s, x) ↦ (s, L (s, x))` of the plane is a bijection whose derivative is invertible everywhere,
so it is an open map, hence a homeomorphism, and its inverse is `C^n` by the inverse function
theorem; the inverse is again a family of lifts and descends to the circle.

## Main definitions

* `AddCircle.prodDiffeomorphOfLift`: the level-preserving diffeomorphism
  `(a, [x]) ↦ (a, [L (κ a, x)])` of `N × AddCircle T`.
* `AddCircle.diffeotopyOfLift`: the diffeotopy of `AddCircle T` which at time `t` is the circle
  map with lift `x ↦ x + sin (π t / 2) ^ 2 (F x - x)`, from the identity to the map with lift `F`.
* `AddCircle.collarDiffeomorphOfLift`: the level-preserving diffeomorphism of `ℝ × AddCircle T`
  which is `(r, [x]) ↦ (r, [x + smoothTransition (1 - r) (F x - x)])`.

## Main results

* `AddCircle.diffeotopyOfLift_final_apply_coe`: every orientation-preserving `C^n` diffeomorphism
  of the circle, `n ≠ 0`, presented by a lift, is the final map of a diffeotopy.
* `AddCircle.collarDiffeomorphOfLift_apply_coe_of_nonpos` and
  `AddCircle.collarDiffeomorphOfLift_apply_of_one_le`: the collar diffeomorphism is
  `(r, θ) ↦ (r, φ θ)` for `r ≤ 0` and the identity for `r ≥ 1`; similarly for its inverse
  (`AddCircle.collarDiffeomorphOfLift_symm_apply_coe_of_nonpos`,
  `AddCircle.collarDiffeomorphOfLift_symm_apply_of_one_le`).

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §§1–2, for
  diffeotopies and their extension across collars.
-/

public section

noncomputable section

open Set Function unitInterval
open scoped Manifold ContDiff

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)] {n : ℕ∞ω} {L : ℝ × ℝ → ℝ}

/-! ### Families of lifts on the plane -/

section Plane

variable (hL : ContDiff ℝ n L) (hn : n ≠ 0) (hper : ∀ s x, L (s, x + T) = L (s, x) + T)
  (hpos : ∀ s x, 0 < deriv (fun y ↦ L (s, y)) x)

include hL hn in
/-- The derivative of a slice `y ↦ L (s, y)` is the partial derivative of `L` in its second
variable. -/
private theorem hasDerivAt_slice (s x : ℝ) :
    HasDerivAt (fun y ↦ L (s, y)) (fderiv ℝ L (s, x) (0, 1)) x :=
  ((hL.differentiable hn) (s, x)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_const x s).prodMk (hasDerivAt_id x))

include hL hn hper hpos in
/-- The map `(s, x) ↦ (s, L (s, x))` is a bijection of the plane: each slice is a lift with
positive derivative, hence a bijection of `ℝ`. -/
private theorem bijective_plane : Bijective fun p : ℝ × ℝ ↦ (p.1, L p) := by
  have h (s : ℝ) := exists_lift_inverse
    (fun x ↦ (hasDerivAt_slice hL hn s x).differentiableAt.hasDerivAt) (hper s) (hpos s)
  refine ⟨fun ⟨s, x⟩ ⟨s', x'⟩ hpq ↦ ?_, fun ⟨s, y⟩ ↦ ?_⟩
  · obtain ⟨rfl, hx⟩ := Prod.ext_iff.1 hpq
    obtain ⟨G, hl, -⟩ := h s
    exact Prod.ext rfl (hl.injective hx)
  · obtain ⟨G, -, hr, -⟩ := h s
    exact ⟨(s, G y), Prod.ext rfl (hr y)⟩

/-- The derivative of `(s, x) ↦ (s, L (s, x))`. -/
private def planeDeriv (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ L p)

include hL hn hpos in
private theorem injective_planeDeriv (p : ℝ × ℝ) : Injective (planeDeriv (L := L) p) := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨u, v⟩ h ↦ ?_
  obtain ⟨rfl, h⟩ : u = 0 ∧ fderiv ℝ L p (u, v) = 0 := by simpa [planeDeriv] using h
  -- The second component is `v` times the positive partial derivative in the second variable.
  have hd : 0 < fderiv ℝ L p (0, 1) := (hasDerivAt_slice hL hn p.1 p.2).deriv ▸ hpos p.1 p.2
  have hv : fderiv ℝ L p (0, v) = v * fderiv ℝ L p (0, 1) := by
    simpa using map_smul (fderiv ℝ L p) v ((0 : ℝ), (1 : ℝ))
  rw [hv, mul_eq_zero] at h
  exact Prod.ext rfl (h.resolve_right hd.ne')

/-- The derivative of `(s, x) ↦ (s, L (s, x))`, as a linear equivalence. -/
private def planeDerivEquiv (p : ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.ofInjectiveEndo (planeDeriv (L := L) p : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ)
    (injective_planeDeriv hL hn hpos p)).toContinuousLinearEquiv

private theorem coe_planeDerivEquiv (p : ℝ × ℝ) :
    (planeDerivEquiv hL hn hpos p : ℝ × ℝ →L[ℝ] ℝ × ℝ) = planeDeriv (L := L) p :=
  DFunLike.coe_injective (by simp [planeDerivEquiv])

include hL hn in
private theorem hasStrictFDerivAt_plane (p : ℝ × ℝ) :
    HasStrictFDerivAt (fun p : ℝ × ℝ ↦ (p.1, L p))
      (planeDerivEquiv hL hn hpos p : ℝ × ℝ →L[ℝ] ℝ × ℝ) p := by
  have hd : HasFDerivAt (fun p : ℝ × ℝ ↦ (p.1, L p)) (planeDeriv p) p :=
    hasFDerivAt_fst.prodMk ((hL.differentiable hn) p).hasFDerivAt
  have hs := ((contDiff_fst.prodMk hL).contDiffAt (x := p)).hasStrictFDerivAt hn
  rwa [hd.fderiv, ← coe_planeDerivEquiv hL hn hpos] at hs

/-- The map `(s, x) ↦ (s, L (s, x))` as a homeomorphism of the plane: a continuous bijection which
is open by the inverse function theorem. -/
private def planeHomeomorph : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  (Equiv.ofBijective _ (bijective_plane hL hn hper hpos)).toHomeomorphOfContinuousOpen
    (continuous_fst.prodMk hL.continuous)
    (isOpenMap_of_hasStrictFDerivAt_equiv (hasStrictFDerivAt_plane hL hn hpos))

private theorem planeHomeomorph_apply (p : ℝ × ℝ) :
    planeHomeomorph hL hn hper hpos p = (p.1, L p) := (rfl)

/-- The inverse family of lifts: `L (s, invLift s y) = y`. -/
private def invLift (q : ℝ × ℝ) : ℝ := ((planeHomeomorph hL hn hper hpos).symm q).2

private theorem fst_planeHomeomorph_symm (q : ℝ × ℝ) :
    ((planeHomeomorph hL hn hper hpos).symm q).1 = q.1 := by
  have h := congrArg Prod.fst ((planeHomeomorph hL hn hper hpos).apply_symm_apply q)
  rwa [planeHomeomorph_apply] at h

private theorem apply_invLift (s y : ℝ) : L (s, invLift hL hn hper hpos (s, y)) = y := by
  have h := congrArg Prod.snd ((planeHomeomorph hL hn hper hpos).apply_symm_apply (s, y))
  have e : (planeHomeomorph hL hn hper hpos).symm (s, y) = (s, invLift hL hn hper hpos (s, y)) :=
    Prod.ext (fst_planeHomeomorph_symm hL hn hper hpos (s, y)) rfl
  rwa [planeHomeomorph_apply, e] at h

private theorem invLift_apply (s x : ℝ) : invLift hL hn hper hpos (s, L (s, x)) = x := by
  have h := (planeHomeomorph hL hn hper hpos).symm_apply_apply (s, x)
  rw [planeHomeomorph_apply] at h
  exact congrArg Prod.snd h

private theorem invLift_add_period (s y : ℝ) :
    invLift hL hn hper hpos (s, y + T) = invLift hL hn hper hpos (s, y) + T := by
  conv_lhs => rw [← apply_invLift hL hn hper hpos s y, ← hper]
  exact invLift_apply hL hn hper hpos s _

private theorem contDiff_invLift : ContDiff ℝ n (invLift hL hn hper hpos) :=
  contDiff_snd.comp ((planeHomeomorph hL hn hper hpos).contDiff_symm
    (fun p ↦ (hasStrictFDerivAt_plane hL hn hpos p).hasFDerivAt)
    (contDiff_fst.prodMk hL))

end Plane

/-! ### Families of circle diffeomorphisms -/

section Family

variable {N : Type*}

/-- Descend a family `M (a, ·)` of lifts to a level-preserving map of `N × AddCircle T`. -/
private def descend (M : N × ℝ → ℝ) (hM : ∀ a x, M (a, x + T) = M (a, x) + T) :
    N × AddCircle T → N × AddCircle T :=
  fun p ↦ (p.1, Periodic.lift (f := fun x : ℝ ↦ (M (p.1, x) : AddCircle T))
    (fun x ↦ by simp only [hM, coe_add_period]) p.2)

omit [Fact (0 < T)] in
private theorem descend_coe (M : N × ℝ → ℝ) (hM : ∀ a x, M (a, x + T) = M (a, x) + T) (a : N)
    (x : ℝ) : descend M hM (a, (x : AddCircle T)) = (a, (M (a, x) : AddCircle T)) := (rfl)

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

private theorem contMDiff_descend {M : N × ℝ → ℝ} (hM : ∀ a x, M (a, x + T) = M (a, x) + T)
    (hM' : ContMDiff (I'.prod 𝓘(ℝ)) 𝓘(ℝ) n M) :
    ContMDiff (I'.prod 𝓘(ℝ)) (I'.prod 𝓘(ℝ)) n (descend M hM) := by
  rw [← (isLocalDiffeomorph_coe T n).contMDiff_comp_prodMap_iff QuotientAddGroup.mk_surjective
    le_rfl]
  exact contMDiff_fst.prodMk ((contMDiff_coe T n).comp hM')

variable (hL : ContDiff ℝ n L) (hn : n ≠ 0) (hper : ∀ s x, L (s, x + T) = L (s, x) + T)
  (hpos : ∀ s x, 0 < deriv (fun y ↦ L (s, y)) x) (κ : N → ℝ) (hκ : ContMDiff I' 𝓘(ℝ) n κ)

/-- **A smooth family of circle diffeomorphisms.** For a `C^n` family `L` of lifts,
`L (s, x + T) = L (s, x) + T`, with positive derivative in `x`, and a `C^n` function `κ` on a
manifold `N`, the map `(a, [x]) ↦ (a, [L (κ a, x)])` is a level-preserving `C^n` diffeomorphism
of `N × AddCircle T`. Its slice at `a` is the orientation-preserving circle diffeomorphism with
lift `L (κ a, ·)`. -/
def prodDiffeomorphOfLift :
    (N × AddCircle T) ≃ₘ^n⟮I'.prod 𝓘(ℝ), I'.prod 𝓘(ℝ)⟯ N × AddCircle T where
  toFun := descend (fun p ↦ L (κ p.1, p.2)) fun _ _ ↦ hper _ _
  invFun := descend (fun p ↦ invLift hL hn hper hpos (κ p.1, p.2))
    fun _ _ ↦ invLift_add_period hL hn hper hpos _ _
  left_inv := fun ⟨a, θ⟩ ↦ by
    induction θ using QuotientAddGroup.induction_on with
    | H x => rw [descend_coe, descend_coe, invLift_apply]
  right_inv := fun ⟨a, θ⟩ ↦ by
    induction θ using QuotientAddGroup.induction_on with
    | H y => rw [descend_coe, descend_coe, apply_invLift hL hn hper hpos]
  contMDiff_toFun := contMDiff_descend (M := fun p ↦ L (κ p.1, p.2)) (fun _ _ ↦ hper _ _)
    (hL.contMDiff.comp ((hκ.comp contMDiff_fst).prodMk_space contMDiff_snd))
  contMDiff_invFun := contMDiff_descend (M := fun p ↦ invLift hL hn hper hpos (κ p.1, p.2))
    (fun _ _ ↦ invLift_add_period hL hn hper hpos _ _)
    ((contDiff_invLift hL hn hper hpos).contMDiff.comp
      ((hκ.comp contMDiff_fst).prodMk_space contMDiff_snd))

@[simp]
theorem prodDiffeomorphOfLift_apply_coe (a : N) (x : ℝ) :
    prodDiffeomorphOfLift hL hn hper hpos κ hκ (a, (x : AddCircle T)) =
      (a, (L (κ a, x) : AddCircle T)) := (rfl)

@[simp]
theorem fst_prodDiffeomorphOfLift (p : N × AddCircle T) :
    (prodDiffeomorphOfLift hL hn hper hpos κ hκ p).1 = p.1 := (rfl)

@[simp]
theorem fst_prodDiffeomorphOfLift_symm (p : N × AddCircle T) :
    ((prodDiffeomorphOfLift hL hn hper hpos κ hκ).symm p).1 = p.1 := (rfl)

/-- The inverse of `prodDiffeomorphOfLift` undoes the lift `L (κ a, ·)` on the slice at `a`. -/
@[simp]
theorem prodDiffeomorphOfLift_symm_apply_coe (a : N) (x : ℝ) :
    (prodDiffeomorphOfLift hL hn hper hpos κ hκ).symm (a, (L (κ a, x) : AddCircle T)) =
      (a, (x : AddCircle T)) := by
  rw [← prodDiffeomorphOfLift_apply_coe hL hn hper hpos κ hκ a x, Diffeomorph.symm_apply_apply]

end Family

/-! ### Interpolating a lift to the identity -/

section Interpolation

variable {F : ℝ → ℝ} {w : ℝ → ℝ}

/-- The lifts `x ↦ x + w s * (F x - x)` interpolating between the identity and `F`. -/
private def interpolate (w F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := p.2 + w p.1 * (F p.2 - p.2)

private theorem contDiff_interpolate (hw : ContDiff ℝ n w) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (interpolate w F) :=
  contDiff_snd.add ((hw.comp contDiff_fst).mul ((hF.comp contDiff_snd).sub contDiff_snd))

omit [Fact (0 < T)] in
private theorem interpolate_add_period (hper : ∀ x, F (x + T) = F x + T) (s x : ℝ) :
    interpolate w F (s, x + T) = interpolate w F (s, x) + T := by
  simp only [interpolate, hper]
  ring

/-- For a weight in `[0, 1]`, the interpolating lifts have positive derivative
`(1 - w s) + w s * F'`. -/
private theorem deriv_interpolate_pos (hw : ∀ s, w s ∈ Icc 0 1) (hF : ContDiff ℝ n F)
    (hn : n ≠ 0) (hpos : ∀ x, 0 < deriv F x) (s x : ℝ) :
    0 < deriv (fun y ↦ interpolate w F (s, y)) x := by
  have hd : HasDerivAt (fun y ↦ interpolate w F (s, y)) (1 + w s * (deriv F x - 1)) x :=
    (hasDerivAt_id x).add
      ((((hF.differentiable hn) x).hasDerivAt.sub (hasDerivAt_id x)).const_mul (w s))
  rw [hd.deriv]
  obtain ⟨hw₀, hw₁⟩ := hw s
  rcases hw₁.eq_or_lt with h | h
  · rw [h]
    linarith [hpos x]
  · nlinarith [mul_nonneg hw₀ (hpos x).le]

/-- The weight `sin (π t / 2) ^ 2`, rising analytically from `0` at `t = 0` to `1` at `t = 1`. -/
private def sinSqWeight (t : ℝ) : ℝ := Real.sin (Real.pi * t / 2) ^ 2

private theorem sinSqWeight_mem (t : ℝ) : sinSqWeight t ∈ Icc 0 1 :=
  ⟨sq_nonneg _, Real.sin_sq_le_one _⟩

private theorem contDiff_sinSqWeight : ContDiff ℝ n sinSqWeight :=
  (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2

variable (hF : ContDiff ℝ n F) (hn : n ≠ 0) (hper : ∀ x, F (x + T) = F x + T)
  (hpos : ∀ x, 0 < deriv F x)

/-- **Orientation-preserving circle diffeomorphisms are diffeotopic to the identity.** For a `C^n`
lift `F`, `n ≠ 0`, with `F (x + T) = F x + T` and `F' > 0`, the diffeotopy of `AddCircle T` which at
time `t` is the circle diffeomorphism with lift `x ↦ x + sin (π t / 2) ^ 2 (F x - x)`. It starts at
the identity and ends at the diffeomorphism with lift `F`. -/
def diffeotopyOfLift : TauCeti.Diffeotopy 𝓘(ℝ) n (AddCircle T) where
  toDiffeomorph := prodDiffeomorphOfLift (L := interpolate sinSqWeight F)
    (contDiff_interpolate contDiff_sinSqWeight hF) hn (fun _ ↦ interpolate_add_period hper _)
    (deriv_interpolate_pos sinSqWeight_mem hF hn hpos) (fun t : I ↦ (t : ℝ))
    contMDiff_subtypeVal_Icc
  fst_apply := fst_prodDiffeomorphOfLift _ _ _ _ _ _
  snd_apply_zero' θ := by
    induction θ using QuotientAddGroup.induction_on with
    | H x => simp [interpolate, sinSqWeight]

/-- At time `t` the diffeotopy `diffeotopyOfLift` is the circle map with lift
`x ↦ x + sin (π t / 2) ^ 2 (F x - x)`. -/
@[simp]
theorem diffeotopyOfLift_apply_coe (t : I) (x : ℝ) :
    diffeotopyOfLift hF hn hper hpos (t, (x : AddCircle T)) =
      ((x + Real.sin (Real.pi * t / 2) ^ 2 * (F x - x) : ℝ) : AddCircle T) := (rfl)

/-- The diffeotopy `diffeotopyOfLift` ends at the circle diffeomorphism with lift `F`. -/
theorem diffeotopyOfLift_final_apply_coe (x : ℝ) :
    (diffeotopyOfLift hF hn hper hpos).final x = (F x : AddCircle T) := by
  rw [TauCeti.Diffeotopy.final_apply, diffeotopyOfLift_apply_coe, Set.Icc.coe_one, mul_one,
    Real.sin_pi_div_two, one_pow, one_mul, add_sub_cancel]

end Interpolation

/-! ### Extension across a product collar -/

section Collar

variable {F : ℝ → ℝ} {n : ℕ∞} (hF : ContDiff ℝ n F) (hn : n ≠ 0)
  (hper : ∀ x, F (x + T) = F x + T) (hpos : ∀ x, 0 < deriv F x)

/-- **Extension of a circle diffeomorphism across a product collar.** For a `C^n` lift `F`,
`n ≠ 0`, with `F (x + T) = F x + T` and `F' > 0`, the level-preserving `C^n` diffeomorphism
`(r, [x]) ↦ (r, [x + smoothTransition (1 - r) (F x - x)])` of `ℝ × AddCircle T`. It is the circle
diffeomorphism with lift `F` for `r ≤ 0` and the identity for `r ≥ 1`. -/
def collarDiffeomorphOfLift :
    (ℝ × AddCircle T) ≃ₘ^n⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ).prod 𝓘(ℝ)⟯ ℝ × AddCircle T :=
  prodDiffeomorphOfLift (L := interpolate Real.smoothTransition F)
    (contDiff_interpolate Real.smoothTransition.contDiff hF) (by exact_mod_cast hn)
    (fun _ ↦ interpolate_add_period hper _)
    (deriv_interpolate_pos (fun s ↦ ⟨Real.smoothTransition.nonneg s,
      Real.smoothTransition.le_one s⟩) hF (by exact_mod_cast hn) hpos)
    (fun r ↦ 1 - r) (contDiff_const.sub contDiff_id).contMDiff

@[simp]
theorem collarDiffeomorphOfLift_apply_coe (r x : ℝ) :
    collarDiffeomorphOfLift hF hn hper hpos (r, (x : AddCircle T)) =
      (r, ((x + Real.smoothTransition (1 - r) * (F x - x) : ℝ) : AddCircle T)) := (rfl)

@[simp]
theorem fst_collarDiffeomorphOfLift (p : ℝ × AddCircle T) :
    (collarDiffeomorphOfLift hF hn hper hpos p).1 = p.1 := (rfl)

@[simp]
theorem fst_collarDiffeomorphOfLift_symm (p : ℝ × AddCircle T) :
    ((collarDiffeomorphOfLift hF hn hper hpos).symm p).1 = p.1 := (rfl)

/-- On the side `r ≤ 0` of the collar, `collarDiffeomorphOfLift` is the circle diffeomorphism with
lift `F`. -/
theorem collarDiffeomorphOfLift_apply_coe_of_nonpos {r : ℝ} (hr : r ≤ 0) (x : ℝ) :
    collarDiffeomorphOfLift hF hn hper hpos (r, (x : AddCircle T)) = (r, (F x : AddCircle T)) := by
  rw [collarDiffeomorphOfLift_apply_coe, Real.smoothTransition.one_of_one_le (by linarith),
    one_mul, add_sub_cancel]

/-- On the side `r ≥ 1` of the collar, `collarDiffeomorphOfLift` is the identity. -/
theorem collarDiffeomorphOfLift_apply_of_one_le {r : ℝ} (hr : 1 ≤ r) (θ : AddCircle T) :
    collarDiffeomorphOfLift hF hn hper hpos (r, θ) = (r, θ) := by
  induction θ using QuotientAddGroup.induction_on with
  | H x => rw [collarDiffeomorphOfLift_apply_coe,
      Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul, add_zero]

/-- On the side `r ≤ 0` of the collar, the inverse of `collarDiffeomorphOfLift` undoes `F`. -/
theorem collarDiffeomorphOfLift_symm_apply_coe_of_nonpos {r : ℝ} (hr : r ≤ 0) (x : ℝ) :
    (collarDiffeomorphOfLift hF hn hper hpos).symm (r, (F x : AddCircle T)) =
      (r, (x : AddCircle T)) := by
  rw [← collarDiffeomorphOfLift_apply_coe_of_nonpos hF hn hper hpos hr x,
    Diffeomorph.symm_apply_apply]

/-- On the side `r ≥ 1` of the collar, the inverse of `collarDiffeomorphOfLift` is the
identity. -/
theorem collarDiffeomorphOfLift_symm_apply_of_one_le {r : ℝ} (hr : 1 ≤ r) (θ : AddCircle T) :
    (collarDiffeomorphOfLift hF hn hper hpos).symm (r, θ) = (r, θ) := by
  conv_lhs => rw [← collarDiffeomorphOfLift_apply_of_one_le hF hn hper hpos hr θ]
  exact Diffeomorph.symm_apply_apply _ _

end Collar

end AddCircle
