/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.ComplexStructure
public import TauCeti.Analysis.PDE.Vortex.Index
public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension
public import TauCeti.Geometry.Symplectic.Complex.Module.DetLine
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The complex orientation of the deformation determinant of a plane vortex

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` is realized as a bounded operator

`TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`,

with `a` the `L∞` class of `x`. It is complex linear for the complex structure
`J (y₀, y₁, y₂, y₃) = (-y₁, y₀, -y₃, y₂)` of variations and the complex structure `J'` of the target
(`TauCeti.Vortex.sobolevGaugeFixedOperator_sobolevVariationAlmostComplexStructure`). This file
uses that to orient its determinant line `det (ker L_x) ⊗ (det (coker L_x))^*` complexly, and
identifies this orientation with the complex orientation of the tangent space of the divisor space
`Sym^m ℂ`.

* `J'` acts on `L²(ℂ; ℝ⁴)` pointwise, as an almost complex structure
  (`TauCeti.Vortex.lpTargetAlmostComplexStructure`), and the realization intertwines `J` and `J'`
  (`TauCeti.Vortex.isComplexLinearMap_sobolevGaugeFixedOperator`); both are in
  `TauCeti.Analysis.PDE.Vortex.Gauge.ComplexStructure`. Packaged as a complex-linear map
  (`TauCeti.IsComplexLinearMap.toComplexLinearMap`), its determinant line carries the complex
  orientation of the determinant lines of complex-linear Fredholm operators
  (`TauCeti.IsComplexLinearMap.IsComplexPositiveDetLine`).
* At a plane vortex `x` lying in `A_m^k` for every `k`, with zero divisor `D`, the kernel of the
  realization is identified with the space `D → ℂ` of principal parts, the tangent space of
  `Sym^m ℂ` at `D`: an element `y` of the kernel is taken to the smooth classical solution with
  the same values (`TauCeti.Vortex.kerSobolevGaugeFixedOperatorEquiv`), and then to the principal
  parts of `δα / α` at the zeros of `α` (`TauCeti.Vortex.sobolevKernelPrincipalPartEquiv`). Every
  element of the kernel has the values of such a classical solution
  (`TauCeti.Vortex.exists_gaugeFixedKernel_ae_eq_values`), and the isomorphism reads off the
  principal parts of that solution
  (`TauCeti.Vortex.sobolevKernelPrincipalPartEquiv_apply_of_ae_eq`). This identification is
  complex linear: it sends `J y` to `i` times the principal parts of `y`
  (`TauCeti.Vortex.sobolevKernelPrincipalPartEquiv_sobolevGaugeFixedKernelAlmostComplexStructure`).
* The realization is onto at a vortex, so its determinant line is the real determinant line of its
  kernel (`LinearMap.detLineEquivOfSurjective`). Under this identification and the principal-part
  isomorphism, an element of the determinant line of `L_x` is complex positive exactly when the
  corresponding element of the real determinant line of `D → ℂ` is complex positive
  (`TauCeti.Vortex.isComplexPositiveDetLine_sobolevGaugeFixedOperator_iff`).

So the complex orientation of the deformation determinant of a plane vortex, the orientation
entering the comparison of determinant lines in the gluing of vortices into large-parameter
Seiberg–Witten solutions, is the complex orientation of the vortex moduli space `Sym^m ℂ`
transported by the principal-part identification of its tangent spaces.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section A.2.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### The principal parts of the kernel at a plane vortex -/

section Vortex

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {D : Multiset ℂ} {ν : ℂ → ℂ}

/-- **The principal parts of the kernel of the realization.** Let `x` be a continuous field lying
in the affine field space `A_m^k` for every `k`, whose section satisfies the holomorphicity rows
`∂bar_a α = 0` and has zero divisor `D`, and let `a` be its `L∞` class. An element `y` of the
kernel of the realization `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` has the values of a smooth square-integrable
classical solution of `L_x y = 0`, and this isomorphism sends `y` to the principal parts of
`δα / α` of that solution at the zeros of `α` (`sobolevKernelPrincipalPartEquiv_apply_of_ae_eq`).
Here `∂bar ν = (b₂ - i b₁) / 2`. The space `D → ℂ` of principal parts is the tangent space of the
divisor space `Sym^m ℂ` at `D`. -/
def sobolevKernelPrincipalPartEquiv (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] (Multiset.ToType D → ℂ) :=
  (kerSobolevGaugeFixedOperatorEquiv (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem i n)
    hax).trans
    (principalPartEquiv (contDiff_of_forall_mem_framedFieldSpace hx hmem) hhol
      (tendsto_normSq_of_forall_mem_framedFieldSpace hx hmem) hD hν hνeq)

/-- `sobolevKernelPrincipalPartEquiv` is `principalPartEquiv` of a classical kernel element with
the same values. -/
private theorem sobolevKernelPrincipalPartEquiv_eq_of_ae_eq (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : (sobolevGaugeFixedOperator a).ker) (u : gaugeFixedKernel x)
    (h : (u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
      fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value ((y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) j) z :
        EuclideanSpace ℝ (Fin 4))) :
    sobolevKernelPrincipalPartEquiv hx hmem hhol hax hD hν hνeq y =
      principalPartEquiv (contDiff_of_forall_mem_framedFieldSpace hx hmem) hhol
        (tendsto_normSq_of_forall_mem_framedFieldSpace hx hmem) hD hν hνeq u := by
  have hu :
      kerSobolevGaugeFixedOperatorEquiv (contDiff_of_forall_mem_framedFieldSpace hx hmem)
        (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem i n)
        hax y = u :=
    (kerSobolevGaugeFixedOperatorEquiv_eq_iff (contDiff_of_forall_mem_framedFieldSpace hx hmem)
      (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem i n)
      hax y u).2 fun j ↦
      ae_restrict_of_ae (h.symm.mono fun z hz ↦ by simpa using congrArg (· j) hz)
  rw [sobolevKernelPrincipalPartEquiv, LinearEquiv.trans_apply, hu]

/-- **Every element of the kernel of the realization has the values of a classical solution.** Let
`x` be a continuous field lying in the affine field space `A_m^k` for every `k`, and let `a` be its
`L∞` class. Every element `y` of the kernel of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` agrees almost
everywhere with a smooth square-integrable classical solution `u` of `L_x u = 0`, which is the input
of `sobolevKernelPrincipalPartEquiv_apply_of_ae_eq`. -/
theorem exists_gaugeFixedKernel_ae_eq_values (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hax : a =ᵐ[μ⊤] x)
    (y : (sobolevGaugeFixedOperator a).ker) :
    ∃ u : gaugeFixedKernel x, (u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
      fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value ((y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) j) z :
        EuclideanSpace ℝ (Fin 4)) := by
  refine ⟨kerSobolevGaugeFixedOperatorEquiv (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem i n)
    hax y, ?_⟩
  have hae (j : Fin 4) :=
    kerSobolevGaugeFixedOperatorEquiv_apply_ae (contDiff_of_forall_mem_framedFieldSpace hx hmem)
      (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem i n)
      hax y j
  simp only [Opens.coe_top, Measure.restrict_univ] at hae
  filter_upwards [ae_all_iff.2 hae] with z hz
  ext j
  exact (hz j).symm

/-- **`sobolevKernelPrincipalPartEquiv` reads off the principal parts of the classical solution**:
if a classical kernel element `u` agrees almost everywhere with the values of `y`, then
`sobolevKernelPrincipalPartEquiv` sends `y` to the principal parts of `δα / α` of `u` at the points
of `D`. -/
theorem sobolevKernelPrincipalPartEquiv_apply_of_ae_eq (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : (sobolevGaugeFixedOperator a).ker) (u : gaugeFixedKernel x)
    (h : (u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
      fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value ((y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) j) z :
        EuclideanSpace ℝ (Fin 4)))
    (i : Multiset.ToType D) :
    sobolevKernelPrincipalPartEquiv hx hmem hhol hax hD hν hνeq y i =
      principalPart x ν u i.1 i.2 := by
  rw [sobolevKernelPrincipalPartEquiv_eq_of_ae_eq hx hmem hhol hax hD hν hνeq y u h,
    principalPartEquiv_apply]

/-- **The principal-part identification of the kernel is complex linear**: it sends `J y` to `i`
times the principal parts of `y`, where `J` is the complex structure of the kernel of the
realization (`sobolevGaugeFixedKernelAlmostComplexStructure`). -/
theorem sobolevKernelPrincipalPartEquiv_sobolevGaugeFixedKernelAlmostComplexStructure
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : (sobolevGaugeFixedOperator a).ker) :
    sobolevKernelPrincipalPartEquiv hx hmem hhol hax hD hν hνeq
        (sobolevGaugeFixedKernelAlmostComplexStructure a y) =
      I • sobolevKernelPrincipalPartEquiv hx hmem hhol hax hD hν hνeq y := by
  obtain ⟨u, hu⟩ := exists_gaugeFixedKernel_ae_eq_values hx hmem hax y
  have hJu : (gaugeFixedKernelAlmostComplexStructure x u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
      fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value
        ((sobolevGaugeFixedKernelAlmostComplexStructure a y :
          Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) j) z : EuclideanSpace ℝ (Fin 4)) := by
    have h₁ : (gaugeFixedKernelAlmostComplexStructure x u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
        fun z ↦ variationComplexStructure ((u : ℂ → EuclideanSpace ℝ (Fin 4)) z) :=
      Filter.EventuallyEq.of_eq (funext (coe_gaugeFixedKernelAlmostComplexStructure_apply x u))
    have h₂ : (fun z ↦ variationComplexStructure ((u : ℂ → EuclideanSpace ℝ (Fin 4)) z)) =ᵐ[volume]
        fun z ↦ variationComplexStructure (WithLp.toLp 2 fun j ↦
          W1p.value ((y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) j) z) :=
      hu.mono fun z hz ↦ congrArg variationComplexStructure hz
    rw [coe_sobolevGaugeFixedKernelAlmostComplexStructure_apply]
    exact (h₁.trans h₂).trans ((values_sobolevVariationAlmostComplexStructure_ae
      (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)).filter_mono
        (ae_mono (Measure.restrict_coe_opens_top _).ge)).symm
  have e₁ := sobolevKernelPrincipalPartEquiv_eq_of_ae_eq hx hmem hhol hax hD hν hνeq
    (sobolevGaugeFixedKernelAlmostComplexStructure a y) (gaugeFixedKernelAlmostComplexStructure x u)
    hJu
  have e₂ := sobolevKernelPrincipalPartEquiv_eq_of_ae_eq hx hmem hhol hax hD hν hνeq y u hu
  refine e₁.trans (Eq.trans ?_ (congrArg (I • ·) e₂).symm)
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_decomposition_of_gaugeFixedOperator_eq_zero (μ := volume)
    ((contDiff_of_forall_mem_framedFieldSpace hx hmem).of_le (by simp)) hhol hν hνeq
    (fun _ ↦ mem_gaugeFixedKernel.1) u u.property
  funext i
  rw [principalPartEquiv_apply, Pi.smul_apply, principalPartEquiv_apply, smul_eq_mul,
    ← principalPart_variationComplexStructure hD hν.continuous hG hH hGH i.snd.isLt]
  congr 1
  exact funext (coe_gaugeFixedKernelAlmostComplexStructure_apply x u)

/-! ### The complex orientation of the determinant line at a plane vortex -/

/-- **The complex orientation of the deformation determinant of a plane vortex is the complex
orientation of `Sym^m ℂ`.** Let `x` be a continuous plane vortex lying in the affine field space
`A_m^k` for every `k`, with `L∞` class `a` and zero divisor `D`. The realization
`L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is complex linear and onto, so its determinant line is the real
determinant line of its kernel (`LinearMap.detLineEquivOfSurjective`), which the principal-part
isomorphism `sobolevKernelPrincipalPartEquiv` identifies with the real determinant line of the
tangent space `D → ℂ` of `Sym^m ℂ` at `D`. An element of the determinant line of `L_x` lies in the
complex orientation of the complex-linear operator `L_x` exactly when its image lies in the
complex orientation of `D → ℂ`. -/
theorem isComplexPositiveDetLine_sobolevGaugeFixedOperator_iff (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (z : (sobolevGaugeFixedOperator a :
      (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤).detLine) :
    (isComplexLinearMap_sobolevGaugeFixedOperator a).IsComplexPositiveDetLine z ↔
      IsComplexPositive (LinearEquiv.detLineCongr
        (sobolevKernelPrincipalPartEquiv hx hmem (fun w ↦ by simp [hsol w]) hax hD hν hνeq)
        (LinearMap.detLineEquivOfSurjective
          (sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace hx hmem hsol hax)
          z)) := by
  refine (isComplexLinearMap_sobolevGaugeFixedOperator a)
    |>.isComplexPositiveDetLine_iff_of_surjective _ _ (fun v w hw ↦ ?_) z
  have hJ : w = sobolevGaugeFixedKernelAlmostComplexStructure a v :=
    Subtype.ext (hw.trans (coe_sobolevGaugeFixedKernelAlmostComplexStructure_apply a v).symm)
  exact (congrArg _ hJ).trans
    (sobolevKernelPrincipalPartEquiv_sobolevGaugeFixedKernelAlmostComplexStructure hx hmem _ hax hD
      hν hνeq v)

end Vortex

end TauCeti.Vortex
