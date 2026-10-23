/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Growth
public import TauCeti.Analysis.Complex.Fuchsian.MeromorphicDescent

/-!
# Meromorphic functions on the compactified quotient of a Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` be discrete, and let `F` be a function on the compactified quotient
`Subgroup.CompactifiedQuotient Γ`, whose pullback to the upper half-plane is
`f z = F (ofQuotient ⟦z⟧)`. This file decides when `F` is meromorphic, and computes its orders, in
terms of `f` alone, at both kinds of points of the compactified quotient.

At the orbit of `z ∈ ℍ` the compactified quotient is the coarse quotient `Γ \ ℍ`, so meromorphic
descent applies: `F` is meromorphic at the orbit of `z` exactly when `f` is meromorphic at `z`,
and `ord_z f = m * ord_[z] F` for the order `m` of the stabilizer of `z`.

At an adjoined cusp, read in the q-coordinate chart of any normalized cusp datum `D` representing
it, `F` is the cusp extension `TauCeti.Subgroup.CuspDatum.cuspExtension D f` on a punctured disc
around `q = 0` (`Subgroup.CompactifiedQuotient.comp_cuspChart_symm_eventuallyEq`). Hence `F` is
meromorphic at the cusp exactly when the cusp extension is meromorphic at `0`, with the same
order. The q-expansion criteria for invariant functions holomorphic sufficiently high turn
exponential growth of rate `2πk / w` in the scaling coordinate into meromorphy at the cusp with
a pole of order at
most `k`, and exponential decay of rate `2πn / w` into a zero of order at least `n`.

## Main declarations

* `Subgroup.CompactifiedQuotient.meromorphicAt_ofQuotient_mk_iff` and
  `Subgroup.CompactifiedQuotient.meromorphicOrderAt_comp_ofQuotient_mk`: meromorphy and the
  order formula at the orbit of a point of the upper half-plane.
* `Subgroup.CompactifiedQuotient.meromorphicAt_ofCusp_iff` and
  `Subgroup.CompactifiedQuotient.meromorphicOrderAt_ofCusp`: meromorphy and order at a cusp, in
  the q-coordinate of any cusp datum representing it.
* `Subgroup.CompactifiedQuotient.neg_le_meromorphicOrderAt_ofCusp` and
  `Subgroup.CompactifiedQuotient.natCast_le_meromorphicOrderAt_ofCusp`: growth bounds the pole
  order and decay bounds the zero order at a cusp.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.4–2.5.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §19.
-/

public noncomputable section

open Asymptotics Filter IsManifold MulAction Set TauCeti TauCeti.Subgroup.CuspDatum Topology
  UpperHalfPlane
open scoped Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

/-! ### Points of the coarse quotient -/

section Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Γ.CompactifiedQuotient → E}

/-- A function on the compactified quotient is meromorphic at a point of the coarse quotient
exactly when its restriction to the coarse quotient is. -/
theorem meromorphicAt_ofQuotient_iff {p : orbitRel.Quotient Γ ℍ} :
    RiemannSurface.MeromorphicAt F (ofQuotient p) ↔
      RiemannSurface.MeromorphicAt (F ∘ ofQuotient) p := by
  have h : F ∘ (ofQuotientChart (chartAt ℂ p)).symm = (F ∘ ofQuotient) ∘ (chartAt ℂ p).symm :=
    funext fun u ↦ congrArg F (ofQuotientChart_symm_apply _ u)
  rw [RiemannSurface.meromorphicAt_def, RiemannSurface.meromorphicAt_def, chartAt_ofQuotient,
    ofQuotientChart_ofQuotient, h]

/-- The order of a function on the compactified quotient at a point of the coarse quotient is the
order of its restriction to the coarse quotient. -/
theorem meromorphicOrderAt_ofQuotient (F : Γ.CompactifiedQuotient → E)
    (p : orbitRel.Quotient Γ ℍ) :
    RiemannSurface.meromorphicOrderAt F (ofQuotient p) =
      RiemannSurface.meromorphicOrderAt (F ∘ ofQuotient) p := by
  have h : F ∘ (ofQuotientChart (chartAt ℂ p)).symm = (F ∘ ofQuotient) ∘ (chartAt ℂ p).symm :=
    funext fun u ↦ congrArg F (ofQuotientChart_symm_apply _ u)
  rw [RiemannSurface.meromorphicOrderAt_def, RiemannSurface.meromorphicOrderAt_def,
    chartAt_ofQuotient, ofQuotientChart_ofQuotient, h]

variable [CompleteSpace E]

/-- **Meromorphy at the orbit of a point of the upper half-plane.** A function on the compactified
quotient is meromorphic at the orbit of `z` exactly when its pullback to the upper half-plane is
meromorphic at `z`, including at elliptic points. -/
theorem meromorphicAt_ofQuotient_mk_iff {z : ℍ} :
    RiemannSurface.MeromorphicAt F (ofQuotient (Quotient.mk _ z)) ↔
      RiemannSurface.MeromorphicAt (F ∘ ofQuotient ∘ Quotient.mk _) z := by
  rw [meromorphicAt_ofQuotient_iff, ← Γ.meromorphicAt_comp_quotientMk_iff, Function.comp_assoc]

/-- **The elliptic order formula on the compactified quotient.** Pulling a function on the
compactified quotient back to the upper half-plane multiplies its order at the orbit of `z` by
the order `m` of the stabilizer of `z`: `ord_z (F ∘ π) = m * ord_[z] F`. -/
theorem meromorphicOrderAt_comp_ofQuotient_mk (F : Γ.CompactifiedQuotient → E) (z : ℍ) :
    RiemannSurface.meromorphicOrderAt (F ∘ ofQuotient ∘ Quotient.mk (orbitRel Γ ℍ)) z =
      Nat.card (stabilizer Γ z) *
        RiemannSurface.meromorphicOrderAt F (ofQuotient (Quotient.mk _ z)) := by
  rw [meromorphicOrderAt_ofQuotient, ← Function.comp_assoc]
  exact Γ.meromorphicOrderAt_comp_quotientMk (F ∘ ofQuotient) z

end Interior

/-! ### Cusps -/

variable {F : Γ.CompactifiedQuotient → ℂ} {f : ℍ → ℂ}

omit [DiscreteTopology Γ] in
/-- The pullback of a function on the compactified quotient is invariant under `Γ`. -/
private theorem apply_smul_of_forall_eq (hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z) (g : Γ)
    (z : ℍ) : f (g • z) = f z := by
  rw [← hF, ← hF]
  exact congrArg (fun p ↦ F (ofQuotient p)) (Quotient.sound (orbitRel_apply.mpr (mem_orbit z g)))

/-- **A function on the compactified quotient read in a cusp chart.** If `f` is the pullback of
`F` to the upper half-plane, then near `q = 0`, away from `0`, the representative of `F` in the
cusp chart of the cusp datum `D` is the cusp extension of `f` at `D`. -/
theorem comp_cuspChart_symm_eventuallyEq (D : Γ.CuspDatum) {A : ℝ} (hA : D.width ≤ A)
    (hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z) :
    F ∘ (cuspChart D hA).symm =ᶠ[𝓝[≠] 0] cuspExtension D f := by
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 (cuspRadius_pos D A)),
    self_mem_nhdsWithin] with q hq hq0
  rw [Function.comp_apply, cuspChart_symm_of_ne_zero D hA (by rwa [cuspChart_target]) hq0, hF,
    cuspExtension_def, UpperHalfPlane.cuspFunction,
    Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0, Function.comp_apply]

/-- **Meromorphy at a cusp.** A function on the compactified quotient is meromorphic at the cusp
orbit of a cusp datum `D` exactly when the cusp extension at `D` of its pullback `f` to the upper
half-plane is meromorphic at `q = 0`. Any cusp datum representing the cusp orbit may be used. -/
theorem meromorphicAt_ofCusp_iff (D : Γ.CuspDatum)
    (hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z) :
    RiemannSurface.MeromorphicAt F (ofCusp D.cuspOrbit) ↔ MeromorphicAt (cuspExtension D f) 0 := by
  rw [RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas
    (subset_maximalAtlas (cuspChart_mem_atlas D le_rfl)) (ofCusp_mem_cuspChart_source D le_rfl),
    cuspChart_ofCusp]
  exact MeromorphicAt.meromorphicAt_congr (comp_cuspChart_symm_eventuallyEq D le_rfl hF)

/-- **The order at a cusp.** The order of a function on the compactified quotient at the cusp
orbit of a cusp datum `D` is the order at `q = 0` of the cusp extension at `D` of its pullback `f`
to the upper half-plane. Any cusp datum representing the cusp orbit may be used. -/
theorem meromorphicOrderAt_ofCusp (D : Γ.CuspDatum)
    (hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z) :
    RiemannSurface.meromorphicOrderAt F (ofCusp D.cuspOrbit) =
      meromorphicOrderAt (cuspExtension D f) 0 := by
  rw [RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas
    (subset_maximalAtlas (cuspChart_mem_atlas D le_rfl)) (ofCusp_mem_cuspChart_source D le_rfl),
    cuspChart_ofCusp]
  exact meromorphicOrderAt_congr (comp_cuspChart_symm_eventuallyEq D le_rfl hF)

section Growth

variable (hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z)
include hF

/-- **Meromorphic extension across a cusp.** If the pullback `f` of a function on the compactified
quotient is holomorphic at sufficiently large normalized heights and grows at most like
`exp (2πky / w)` in the scaling coordinate of a cusp datum of width `w`, then the function is
meromorphic at that cusp. -/
theorem meromorphicAt_ofCusp_of_isBigO (D : Γ.CuspDatum) (k : ℤ)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * k * z.im / D.width)) :
    RiemannSurface.MeromorphicAt F (ofCusp D.cuspOrbit) :=
  (meromorphicAt_ofCusp_iff D hF).2 <| meromorphicAt_cuspExtension_zero D k f
    (fun g ↦ apply_smul_of_forall_eq hF g) hhol hbound

/-- **Growth bounds the pole order at a cusp.** If the pullback `f` of a function on the
compactified quotient is holomorphic sufficiently high and grows at most like `exp (2πky / w)`
in the scaling coordinate of a cusp datum of width `w`, then the order of the function at that
cusp is at
least `-k`. -/
theorem neg_le_meromorphicOrderAt_ofCusp (D : Γ.CuspDatum) (k : ℤ)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * k * z.im / D.width)) :
    ((-k : ℤ) : WithTop ℤ) ≤ RiemannSurface.meromorphicOrderAt F (ofCusp D.cuspOrbit) := by
  rw [meromorphicOrderAt_ofCusp D hF]
  exact neg_le_meromorphicOrderAt_cuspExtension D k f (fun g ↦ apply_smul_of_forall_eq hF g)
    hhol hbound

/-- **Decay bounds the zero order at a cusp.** If the pullback `f` of a function on the
compactified quotient is holomorphic sufficiently high and decays at least like
`exp (-2πny / w)` in the scaling coordinate of a cusp datum of width `w`, then the function
vanishes to order at least `n` at that
cusp. -/
theorem natCast_le_meromorphicOrderAt_ofCusp (D : Γ.CuspDatum) (n : ℕ)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hdecay : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * n * z.im / D.width)) :
    ((n : ℤ) : WithTop ℤ) ≤ RiemannSurface.meromorphicOrderAt F (ofCusp D.cuspOrbit) := by
  rw [meromorphicOrderAt_ofCusp D hF]
  exact natCast_le_meromorphicOrderAt_cuspExtension D n f (fun g ↦ apply_smul_of_forall_eq hF g)
    hhol hdecay

end Growth

end Subgroup.CompactifiedQuotient
