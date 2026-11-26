/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Analysis.Complex.RootsOfUnity.Circle
public import TauCeti.Topology.Homotopy.HomotopyGroup.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
public import TauCeti.Topology.PathComponent
import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Inner

/-!
# The exact homotopy sequence of the power maps of the circle

For `n ≠ 0` the power map `z ↦ zⁿ` of the unit circle `Circle` (`Circle.powCover`) is an
`n`-fold covering (`Circle.isQuotientCoveringMap_npow`), hence a Serre fibration
(`Circle.mem_serreFibrations_powCover`). Its fibre `F` over a point `b` is the set of `n`-th roots
of `b`, and the low end of its exact homotopy sequence is

`0 = π₁(F) → π₁(S¹, e) → π₁(S¹, b) → π₀(F) → π₀(S¹) = *`.

This file computes it. The middle map is multiplication by `n` on `π₁(S¹) ≅ ℤ`
(`Circle.fundamentalGroupMulEquiv_map_pow`). The fibre is discrete, so its path components are
its points, and they are the points `e · e^{2πij/n}` for `j ∈ ℤ/n`, given a point `e` of the fibre
(`Circle.powCoverFiberEquiv`). In these coordinates the boundary map `π₁(S¹, b) → π₀(F)` is the
reduction modulo `n` of the degree (`Circle.fibrationBoundary_powCover`): a loop of degree `k`
lifts, from `e`, to a path ending at `e · e^{2πik/n}`, since `t ↦ e · exp(i(θ t - θ 0)/n)` lifts
it for every continuous angle `θ` of the loop. Hence the kernel of the boundary map is `nℤ`
(`Circle.fibrationBoundary_powCover_eq_const_iff`), which by exactness is the image of the middle
map (`Circle.mem_range_homotopyGroupMap_powCover_iff`).

For the double cover `z ↦ z²` and the base point `1`, the fibre is `{1, -1}`, the class of the
loop `t ↦ e^{2πit}` is sent to the component of `-1`, the end point of its lift `t ↦ e^{πit}`
(`Circle.pi0EquivZerothHomotopy_fibrationBoundary_sq_expLoop`), and the kernel of the boundary
map is `2ℤ`: the integers whose lift closes up.

## Main definitions

* `Circle.powCover n`: the map `z ↦ zⁿ` of the circle, as a morphism of `TopCat`.
* `Circle.powCoverFiberEquiv e`: `ℤ/n ≃ π₀(F)`, `j ↦ [e · e^{2πij/n}]`.

## Main results

* `Circle.fibrationBoundary_powCover`: the boundary map is reduction modulo `n` of the degree.
* `Circle.fibrationBoundary_powCover_eq_const_iff`: its kernel is `nℤ`.
* `Circle.mem_range_homotopyGroupMap_powCover_iff`: the image of `π₁(S¹, e) → π₁(S¹, b)` is
  `nℤ`.
* `Circle.pi0EquivZerothHomotopy_fibrationBoundary_sq_expLoop`: for the double cover, the
  generator of `π₁(S¹, 1)` is sent to the component of `-1`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.41 and
  Section 1.3.
-/

public section

noncomputable section

open CategoryTheory Real unitInterval
open scoped Topology

namespace Circle

variable {n : ℕ}

variable (n) in
/-- The power map `z ↦ zⁿ` of the circle, as a morphism of `TopCat`. For `n ≠ 0` it is the
`n`-fold covering of the circle (`Circle.isQuotientCoveringMap_npow`). -/
def powCover : TopCat.of Circle ⟶ TopCat.of Circle :=
  TopCat.ofHom ⟨(· ^ n), continuous_pow n⟩

variable (n) in
@[simp]
theorem hom_powCover : (powCover n).hom = ⟨(· ^ n), continuous_pow n⟩ :=
  (rfl)

/-- For `n ≠ 0`, the power map `z ↦ zⁿ` of the circle is a Serre fibration. -/
theorem mem_serreFibrations_powCover [NeZero n] : TauCeti.TopCat.serreFibrations (powCover n) :=
  IsCoveringMap.mem_serreFibrations (isQuotientCoveringMap_npow n).isCoveringMap

variable {b : Circle}

/-- A point of the fibre of `z ↦ zⁿ` over `b` is an `n`-th root of `b`. -/
theorem coe_fiber_pow (e : (powCover n).fiber b) : (e : Circle) ^ n = b := by
  simpa using e.property

variable [NeZero n]

/-- Rotating a point of the fibre of `z ↦ zⁿ` by an `n`-th root of unity `e^{2πij/n}` stays in
the fibre. -/
theorem mul_toCircle_mem_preimage_powCover (e : (powCover n).fiber b) (j : ZMod n) :
    (e : Circle) * ZMod.toCircle j ∈ powCover n ⁻¹' {b} := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hom_powCover, ContinuousMap.coe_mk, mul_pow,
    ZMod.toCircle_pow_eq_one, mul_one]
  exact coe_fiber_pow e

/-- For `n ≠ 0`, the fibres of `z ↦ zⁿ` are discrete, as fibres of a covering map. -/
instance : DiscreteTopology ((powCover n).fiber b) := by
  have hcov := (isQuotientCoveringMap_npow n).isCoveringMap
  exact (hcov b).discreteTopology_fiber

variable (b) in
/-- **The path components of the fibre of `z ↦ zⁿ`.** Given a point `e` of the fibre over `b`, the
path components of the fibre are the points `e · e^{2πij/n}`, `j ∈ ℤ/n`: the class of `j` is sent
to the component of `e · ZMod.toCircle j`. -/
def powCoverFiberEquiv (e : (powCover n).fiber b) : ZMod n ≃ π_ 0 ((powCover n).fiber b) e :=
  .ofBijective (fun j ↦ HomotopyGroup.pi0EquivZerothHomotopy.symm
      (.mk ⟨e * ZMod.toCircle j, mul_toCircle_mem_preimage_powCover e j⟩)) <| by
    constructor
    · intro j k h
      have h := ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
        (HomotopyGroup.pi0EquivZerothHomotopy.symm.injective h)
      exact ZMod.injective_toCircle (mul_left_cancel (congrArg Subtype.val h))
    · intro c
      obtain ⟨w, hw⟩ := ZerothHomotopy.mk_surjective (HomotopyGroup.pi0EquivZerothHomotopy c)
      obtain ⟨j, hj⟩ := ZMod.exists_toCircle_eq_of_pow_eq_one (n := n)
        (ζ := (e : Circle)⁻¹ * w) (by rw [mul_pow, inv_pow, coe_fiber_pow, coe_fiber_pow,
          inv_mul_cancel])
      refine ⟨j, HomotopyGroup.pi0EquivZerothHomotopy.symm_apply_eq.2 (Eq.trans ?_ hw)⟩
      congr 1
      exact Subtype.ext (by simp [hj])

@[simp]
theorem pi0EquivZerothHomotopy_powCoverFiberEquiv (e : (powCover n).fiber b) (j : ZMod n) :
    HomotopyGroup.pi0EquivZerothHomotopy (powCoverFiberEquiv b e j) =
      .mk ⟨e * ZMod.toCircle j, mul_toCircle_mem_preimage_powCover e j⟩ :=
  HomotopyGroup.pi0EquivZerothHomotopy.apply_symm_apply (ZerothHomotopy.mk
    (⟨e * ZMod.toCircle j, mul_toCircle_mem_preimage_powCover e j⟩ : (powCover n).fiber b))

/-- The class of `0` is the component of the base point `e`. -/
@[simp]
theorem powCoverFiberEquiv_zero (e : (powCover n).fiber b) :
    powCoverFiberEquiv b e 0 = ⟦GenLoop.const⟧ := by
  refine HomotopyGroup.pi0EquivZerothHomotopy.injective ?_
  rw [pi0EquivZerothHomotopy_powCoverFiberEquiv, HomotopyGroup.pi0EquivZerothHomotopy_mk]
  congr 1
  exact Subtype.ext (by simp)

/-- **The boundary map of `z ↦ zⁿ` on path components.** The class of a loop `γ` at `b` is sent to
the component of `e · e^{2πik/n}`, where `k` is the degree of `γ`: if `θ` is a continuous angle of
`γ`, then `t ↦ e · exp(i(θ t - θ 0)/n)` lifts `γ` from `e`. -/
private theorem pi0EquivZerothHomotopy_fibrationBoundary_powCover_fromPath
    (e : (powCover n).fiber b) (γ : Path b b) :
    HomotopyGroup.pi0EquivZerothHomotopy (TauCeti.TopCat.fibrationBoundary
        mem_serreFibrations_powCover e ((homotopyGroupEquivFundamentalGroupOfUnique
          (Option (Fin 0))).symm (FundamentalGroup.fromPath (.mk γ)))) =
      .mk ⟨e * ZMod.toCircle (degree γ : ZMod n),
        mul_toCircle_mem_preimage_powCover e _⟩ := by
  rw [TauCeti.TopCat.fibrationBoundary_eq_fiberMonodromy, Equiv.apply_symm_apply]
  obtain ⟨r, hr⟩ := exp_surjective b
  obtain ⟨θ, hθ, hθ0⟩ := isCoveringMap_exp.exists_path_lifts γ.toContinuousMap r
    (γ.source.trans hr.symm)
  have hθγ (t : I) : exp (θ t) = γ t := congrFun hθ t
  let Γ : C(I, Circle) := ⟨fun t ↦ e * exp ((θ t - θ 0) / n), by fun_prop⟩
  have hΓ : (powCover n : Circle → Circle) ∘ Γ = γ := by
    funext t
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    simp only [Function.comp_apply, hom_powCover, ContinuousMap.coe_mk, Γ, hθ0]
    rw [mul_pow, ← exp_natCast_mul, mul_div_cancel₀ _ hn, exp_sub, hθγ, hr, coe_fiber_pow,
      mul_div_cancel]
  refine TauCeti.HasHomotopyLiftingProperty.fiberMonodromy_mk _ γ hΓ (z := e) (by simp [Γ])
    (w := ⟨_, mul_toCircle_mem_preimage_powCover e (degree γ)⟩) ?_
  simp only [Γ, ContinuousMap.coe_mk, ZMod.toCircle_intCast_eq_circleExp,
    sub_eq_degree_mul γ θ.continuous hθγ]
  congr 2
  ring

/-- **The boundary map of `z ↦ zⁿ` is reduction modulo `n`.** Read through the degree
`π₁(S¹, b) ≅ ℤ` and the identification `ℤ/n ≃ π₀(F)` of `Circle.powCoverFiberEquiv`, the boundary
map `π₁(S¹, b) → π₀(F)` of the exact homotopy sequence of `z ↦ zⁿ` sends a class of degree `k` to
the class of `k` modulo `n`. -/
theorem fibrationBoundary_powCover (e : (powCover n).fiber b) (g : FundamentalGroup Circle b) :
    TauCeti.TopCat.fibrationBoundary mem_serreFibrations_powCover e
        ((homotopyGroupEquivFundamentalGroupOfUnique (Option (Fin 0))).symm g) =
      powCoverFiberEquiv b e ((fundamentalGroupMulEquiv b g).toAdd : ZMod n) := by
  obtain ⟨g⟩ := g
  induction g using Path.Homotopic.Quotient.ind with | mk γ => ?_
  refine HomotopyGroup.pi0EquivZerothHomotopy.injective ?_
  rw [pi0EquivZerothHomotopy_powCoverFiberEquiv]
  exact (pi0EquivZerothHomotopy_fibrationBoundary_powCover_fromPath e γ).trans
    (by rw [fundamentalGroupMulEquiv_fromPath, toAdd_ofAdd])

/-- **The kernel of the boundary map of `z ↦ zⁿ` is `nℤ`.** A class of `π₁(S¹, b)` is sent to the
component of the base point exactly when its degree is divisible by `n`. -/
theorem fibrationBoundary_powCover_eq_const_iff (e : (powCover n).fiber b)
    (g : FundamentalGroup Circle b) :
    TauCeti.TopCat.fibrationBoundary mem_serreFibrations_powCover e
        ((homotopyGroupEquivFundamentalGroupOfUnique (Option (Fin 0))).symm g) =
      ⟦GenLoop.const⟧ ↔ (n : ℤ) ∣ (fundamentalGroupMulEquiv b g).toAdd := by
  rw [fibrationBoundary_powCover, ← powCoverFiberEquiv_zero,
    (powCoverFiberEquiv b e).apply_eq_iff_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The image of `π₁(S¹, e) → π₁(S¹, b)` under `z ↦ zⁿ` is `nℤ`.** By exactness of the homotopy
sequence at `π₁(S¹, b)`, a class comes from the total space exactly when its boundary is trivial,
that is, when its degree is divisible by `n`. -/
theorem mem_range_homotopyGroupMap_powCover_iff (e : (powCover n).fiber b)
    (a : HomotopyGroup (Option (Fin 0)) (TopCat.of Circle) b) :
    a ∈ Set.range (HomotopyGroup.map (powCover n).hom (Set.mem_singleton_iff.1 e.property)) ↔
      (n : ℤ) ∣ (fundamentalGroupMulEquiv b
        (homotopyGroupEquivFundamentalGroupOfUnique (Option (Fin 0)) a)).toAdd := by
  rw [TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq
    mem_serreFibrations_powCover, ← fibrationBoundary_powCover_eq_const_iff e,
    Equiv.symm_apply_apply]

/-- **The double cover of the circle sends the generator to `-1`.** For `z ↦ z²` and the base
point `1`, whose fibre is `{1, -1}`, the boundary map sends the class of the loop
`t ↦ e^{2πit}` to the component of `-1`, the end point of its lift `t ↦ e^{πit}` from `1`. -/
theorem pi0EquivZerothHomotopy_fibrationBoundary_sq_expLoop :
    HomotopyGroup.pi0EquivZerothHomotopy (TauCeti.TopCat.fibrationBoundary
        (mem_serreFibrations_powCover (n := 2)) ⟨1, by simp⟩
        ((homotopyGroupEquivFundamentalGroupOfUnique (Option (Fin 0))).symm
          (FundamentalGroup.fromPath (.mk expLoop)))) =
      .mk ⟨-1, by simp⟩ := by
  rw [fibrationBoundary_powCover, pi0EquivZerothHomotopy_powCoverFiberEquiv,
    fundamentalGroupMulEquiv_expLoop, toAdd_ofAdd]
  have h : ZMod.toCircle ((1 : ℤ) : ZMod 2) = -1 := by
    rw [ZMod.toCircle_intCast_eq_circleExp]
    convert exp_pi using 2
    push_cast
    ring
  congr 1
  exact Subtype.ext (by simpa using h)

end Circle
