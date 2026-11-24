/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Coupling
public import TauCeti.Analysis.PDE.Vortex.Reduced.Continuity
public import TauCeti.Analysis.Polynomial.SymmetricPower
public import Mathlib.Topology.CompactOpen
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The moduli space of framed plane vortices is homeomorphic to `Sym ℂ m`

The smooth framed degree-`m` plane vortices of coupling `c > 0`
(`TauCeti.Vortex.framedVortexSubMulAction c m`) modulo the smooth framed gauge group are in
bijection with `Sym ℂ m` through their zero divisors (`TauCeti.Vortex.framedVortexModuliEquiv`),
by Taubes's existence and uniqueness theorems. This file shows that this bijection is a
homeomorphism when the vortices carry the topology of locally uniform convergence and the moduli
space the quotient topology.

The field space `ℂ → ℝ⁴` carries the product topology, that of pointwise convergence, so the
orbit space of `framedVortexSubMulAction c m` inherits the quotient of that topology. Smooth
vortices are continuous fields, and the natural topology on continuous fields is the compact-open
topology of `C(ℂ, ℝ⁴)`, which on the locally compact plane is the topology of locally uniform
convergence (`ContinuousMap.tendsto_iff_tendstoLocallyUniformly`). The framed vortices form the
subspace `TauCeti.Vortex.framedVortices c m` of `C(ℂ, ℝ⁴)`, identified with the sub-action by
`TauCeti.Vortex.framedVortexEquiv`. The smooth framed gauge group acts on it, and its orbit space
carries the quotient topology.

* **The divisor is continuous.** If vortices converge locally uniformly, their sections do, and by
  Hurwitz's theorem their zero divisors converge in `Sym ℂ m`
  (`TauCeti.Vortex.tendsto_of_tendstoLocallyUniformly`). Hence the divisor is continuous on
  `framedVortices c m` (`TauCeti.Vortex.continuous_framedVortexDivisor`), at every coupling, and it
  descends to the orbit space.
* **The inverse is continuous.** For a monic polynomial `P` of degree `m ≥ 1`, Taubes's vortex with
  zero divisor `P` is the field reconstructed from the amplitude `u₀ + w_P` and the section `P`,
  where `u₀` is the background amplitude of `P` and `w_P` the solution of the reduced equation
  (`TauCeti.Vortex.equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue`). When
  the coefficients of `P` converge, these fields converge uniformly on the plane
  (`TauCeti.Vortex.tendstoUniformly_amplitudeField_backgroundAmplitude_add`,
  `TauCeti.Vortex.tendstoUniformly_reducedSolution`,
  `TauCeti.Vortex.tendstoUniformly_fderiv_reducedSolution`). Reading a divisor through the
  elementary symmetric chart `Sym.coeffHomeomorph`, which is a homeomorphism `Sym ℂ m ≃ₜ ℂᵐ`
  sending `D` to the lower coefficients of `∏_{a ∈ D} (X - a)`, collisions of zeros included, this
  is a continuous section of the divisor at coupling one. The dilation by `c^(1/2)`, which is
  continuous for the compact-open topology, carries it to every coupling `c > 0`.

Together these give the homeomorphism `TauCeti.Vortex.framedVortexModuliHomeomorph` between the
orbit space of `framedVortices c m` and `Sym ℂ m`, and so, through `Sym.coeffHomeomorph`, with
`ℂᵐ`. Equivalently, the divisor is a quotient map from the space of framed vortices onto `Sym ℂ m`
(`TauCeti.Vortex.isQuotientMap_framedVortexDivisor`), whose fibres are the gauge orbits.

## Main definitions

* `TauCeti.Vortex.framedVortices c m`: the smooth framed degree-`m` vortices of coupling `c`, as a
  subspace of `C(ℂ, ℝ⁴)`.
* `TauCeti.Vortex.framedVortexEquiv c m`: its identification with
  `TauCeti.Vortex.framedVortexSubMulAction c m`, which is equivariant for the smooth framed gauge
  group (`TauCeti.Vortex.framedVortexEquiv_smul`).
* `TauCeti.Vortex.framedVortexOrbitEquiv c m`: the induced identification of the orbit spaces of
  `TauCeti.Vortex.framedVortexSubMulAction c m` and `framedVortices c m`.
* `TauCeti.Vortex.framedVortexModuliHomeomorph hc m`: the homeomorphism from the orbit space of
  `framedVortices c m` onto `Sym ℂ m`, sending the orbit of a vortex to its zero divisor. Through
  `TauCeti.Vortex.framedVortexOrbitEquiv` it is the bijection
  `TauCeti.Vortex.framedVortexModuliEquiv` (`framedVortexModuliHomeomorph_framedVortexOrbitEquiv`).

## Main results

* `TauCeti.Vortex.continuous_framedVortexDivisor`: the zero divisor is continuous on
  `framedVortices c m`.
* `TauCeti.Vortex.isQuotientMap_framedVortexDivisor`: for `c > 0` it is a quotient map onto
  `Sym ℂ m`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

open Complex Filter Topology Polynomial TauCeti.Polynomial

namespace TauCeti.Vortex

variable {c : ℝ} {m : ℕ}

/-! ### Framed vortices as continuous fields -/

variable (c m) in
/-- **The framed vortices as continuous fields.** The smooth framed degree-`m` vortices of
coupling `c`, the members of `TauCeti.Vortex.framedVortexSubMulAction c m`, as a subset of the
continuous fields `C(ℂ, ℝ⁴)`. With the subspace topology, which is that of locally uniform
convergence, this is the space whose quotient by gauge is identified with `Sym ℂ m`. -/
def framedVortices : Set C(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  {x | ⇑x ∈ framedVortexSubMulAction c m}

@[simp]
theorem mem_framedVortices {x : C(ℂ, EuclideanSpace ℝ (Fin 4))} :
    x ∈ framedVortices c m ↔ ⇑x ∈ framedVortexSubMulAction c m :=
  Iff.rfl

variable (c m) in
/-- A smooth framed vortex, regarded as a continuous field. -/
def framedVortexEquiv : framedVortexSubMulAction c m ≃ framedVortices c m where
  toFun x := ⟨⟨x, (mem_framedVortexSubMulAction.1 x.property).1.continuous⟩, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_framedVortexEquiv (x : framedVortexSubMulAction c m) :
    ⇑(framedVortexEquiv c m x : C(ℂ, EuclideanSpace ℝ (Fin 4))) = x :=
  (rfl)

@[simp]
theorem coe_framedVortexEquiv_symm (x : framedVortices c m) :
    ((framedVortexEquiv c m).symm x : ℂ → EuclideanSpace ℝ (Fin 4)) = ⇑(x : C(ℂ, _)) :=
  (rfl)

/-- The smooth framed gauge group acts on the framed vortices regarded as continuous fields, by
the action on fields. -/
instance : MulAction framedGaugeGroup (framedVortices c m) :=
  (framedVortexEquiv c m).symm.mulAction framedGaugeGroup

/-- The inverse of `TauCeti.Vortex.framedVortexEquiv` is equivariant. -/
@[simp]
theorem framedVortexEquiv_symm_smul (u : framedGaugeGroup) (x : framedVortices c m) :
    (framedVortexEquiv c m).symm (u • x) = u • (framedVortexEquiv c m).symm x := by
  rw [Equiv.smul_def, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- `TauCeti.Vortex.framedVortexEquiv` is equivariant. -/
@[simp]
theorem framedVortexEquiv_smul (u : framedGaugeGroup) (x : framedVortexSubMulAction c m) :
    framedVortexEquiv c m (u • x) = u • framedVortexEquiv c m x := by
  rw [← Equiv.eq_symm_apply, framedVortexEquiv_symm_smul, Equiv.symm_apply_apply]

/-- A gauge acts on a framed vortex regarded as a continuous field by the action on fields. -/
@[simp]
theorem coe_smul_framedVortices (u : framedGaugeGroup) (x : framedVortices c m) :
    ⇑((u • x : framedVortices c m) : C(ℂ, EuclideanSpace ℝ (Fin 4))) = u • ⇑(x : C(ℂ, _)) := by
  rw [← coe_framedVortexEquiv_symm, framedVortexEquiv_symm_smul, SubMulAction.val_smul,
    coe_framedVortexEquiv_symm]

/-! ### Continuity of the divisor -/

/-- **The divisor is continuous for locally uniform convergence.** At every coupling, the zero
divisor of a framed vortex depends continuously on the vortex in the compact-open topology. -/
theorem continuous_framedVortexDivisor :
    Continuous fun x : framedVortices c m ↦
      framedVortexDivisor ((framedVortexEquiv c m).symm x) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  have h := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1
    (continuous_subtypeVal.continuousAt (x := x₀))
  exact tendsto_of_tendstoLocallyUniformly (y := fun (x : framedVortices c m) ↦ ⇑(x : C(ℂ, _)))
    (isZeroMultiplicity_sectionValue_framedVortexDivisor ((framedVortexEquiv c m).symm x₀))
    (.of_forall fun x ↦
      isZeroMultiplicity_sectionValue_framedVortexDivisor ((framedVortexEquiv c m).symm x)) h

/-! ### A continuous section at coupling one -/

/-- The vortex field of the monic polynomial with lower coefficients `a`: the field reconstructed
from the amplitude `u₀ + w`, `u₀` the background amplitude and `w` the reduced solution. -/
private def coeffVortex (a : Fin m → ℂ) : ℂ → EuclideanSpace ℝ (Fin 4) :=
  amplitudeField (fun z ↦ backgroundAmplitude (monicOfCoeff a).eval z +
    reducedSolution (monicOfCoeff a) z) (monicOfCoeff a).eval

private theorem coeffVortex_mem (hm : 0 < m) (a : Fin m → ℂ) :
    coeffVortex a ∈ framedVortexSubMulAction 1 m := by
  obtain ⟨hsol, hfr⟩ := equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue
    (monic_monicOfCoeff a) (by rw [natDegree_monicOfCoeff]; exact hm)
  rw [natDegree_monicOfCoeff] at hfr
  refine mem_framedVortexSubMulAction.2 ⟨contDiff_amplitudeField (n := ⊤)
    ((contDiff_backgroundAmplitude
      (((monicOfCoeff a).differentiable.contDiff).restrict_scalars ℝ)).add
        (contDiff_reducedSolution _))
    (((monicOfCoeff a).differentiable.contDiff).restrict_scalars ℝ), ?_, hfr⟩
  simpa [coupledEquation_one, coeffVortex] using hsol

private theorem framedVortexDivisor_coeffVortex (hm : 0 < m) (a : Fin m → ℂ) :
    framedVortexDivisor (⟨coeffVortex a, coeffVortex_mem hm a⟩ : framedVortexSubMulAction 1 m) =
      (Sym.coeffEquiv ℂ m).symm a := by
  rw [framedVortexDivisor_eq_iff]
  have hu : Continuous fun z ↦ backgroundAmplitude (monicOfCoeff a).eval z +
      reducedSolution (monicOfCoeff a) z :=
    ((contDiff_backgroundAmplitude
      (((monicOfCoeff a).differentiable.contDiff (n := 1)).restrict_scalars ℝ)).continuous).add
      (contDiff_reducedSolution _).continuous
  have h := isZeroMultiplicity_sectionValue_amplitudeField_prod_sub hu
    (((Sym.coeffEquiv ℂ m).symm a : Sym ℂ m) : Multiset ℂ)
  have he : (fun w ↦ ((((Sym.coeffEquiv ℂ m).symm a : Sym ℂ m) : Multiset ℂ).map (w - ·)).prod) =
      (monicOfCoeff a).eval :=
    funext fun w ↦ by rw [← Sym.eval_toMonic, Sym.toMonic_coeffEquiv_symm]
  rwa [he] at h

/-- **Continuity of Taubes's vortices in the coefficients.** For `m ≥ 1`, the vortex of the monic
polynomial with lower coefficients `a` depends continuously on `a` in the compact-open topology. -/
private theorem continuous_coeffVortex (hm : 0 < m) :
    Continuous fun a : Fin m → ℂ ↦ (framedVortexEquiv 1 m ⟨coeffVortex a, coeffVortex_mem hm a⟩ :
      C(ℂ, EuclideanSpace ℝ (Fin 4))) := by
  refine continuous_iff_continuousAt.2 fun a₀ ↦ ?_
  refine ContinuousMap.tendsto_iff_tendstoLocallyUniformly.2
    (TendstoUniformly.tendstoLocallyUniformly ?_)
  have hdeg : ∀ᶠ a in 𝓝 a₀, (monicOfCoeff a).natDegree ≤ (monicOfCoeff a₀).natDegree :=
    .of_forall fun a ↦ by rw [natDegree_monicOfCoeff, natDegree_monicOfCoeff]
  have hcoeff (k : ℕ) :=
    (continuous_coeff_monicOfCoeff (R := ℂ) (n := m) k).continuousAt (x := a₀)
  have hpos : 0 < (monicOfCoeff a₀).natDegree := by rwa [natDegree_monicOfCoeff]
  -- The limiting reduced solution is bounded, since it tends to zero at infinity.
  obtain ⟨M, hM⟩ := (⟨⟨_, (contDiff_reducedSolution (monicOfCoeff a₀)).continuous⟩,
    tendsto_reducedSolution_cocompact _⟩ :
      ZeroAtInftyContinuousMap ℂ ℝ).isBounded_range.exists_norm_le
  exact tendstoUniformly_amplitudeField_backgroundAmplitude_add hdeg hcoeff
    (fun a ↦ (contDiff_reducedSolution _).differentiable (by simp))
    ((contDiff_reducedSolution _).differentiable (by simp))
    (fun z ↦ (Real.le_norm_self _).trans (hM _ ⟨z, rfl⟩))
    (tendstoUniformly_reducedSolution hpos hdeg hcoeff)
    (tendstoUniformly_fderiv_reducedSolution hpos hdeg hcoeff)

/-! ### Dilation is continuous -/

/-- The linear part of the dilation of a field by `t`: the connection coordinates are multiplied by
`t` and the section coordinates are kept. -/
private def dilateCoord (t : ℝ) : C(EuclideanSpace ℝ (Fin 4), EuclideanSpace ℝ (Fin 4)) :=
  ⟨fun v ↦ !₂[t * v 0, t * v 1, v 2, v 3], by fun_prop⟩

/-- **The dilation of fields is continuous** for the compact-open topology: the dilation
`TauCeti.Vortex.dilateField t x` of a continuous field `x` is `dilateCoord t ∘ x ∘ (t • ·)`. -/
private theorem continuous_dilateCoord_comp (t : ℝ) :
    Continuous fun x : C(ℂ, EuclideanSpace ℝ (Fin 4)) ↦
      (dilateCoord t).comp (x.comp ⟨(t • ·), continuous_const_smul t⟩) :=
  (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)

/-! ### The homeomorphism -/

/-- **A continuous section of the divisor.** For `c > 0` and `m ≥ 1` there is a continuous map
from `Sym ℂ m` to the framed vortices of coupling `c` assigning to every divisor a vortex with that
divisor. -/
private theorem exists_continuous_framedVortexDivisor_eq (hc : 0 < c) (hm : 0 < m) :
    ∃ s : Sym ℂ m → framedVortices c m, Continuous s ∧
      ∀ D, framedVortexDivisor ((framedVortexEquiv c m).symm (s D)) = D := by
  have hc' : (√c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hc).ne'
  let a : Sym ℂ m → Fin m → ℂ := fun D ↦ Sym.coeffHomeomorph ℂ m (D.map ((√c : ℂ) * ·))
  have ha : Continuous a :=
    (Sym.coeffHomeomorph ℂ m).continuous.comp (Sym.continuous_map (by fun_prop))
  refine ⟨fun D ↦ framedVortexEquiv c m ((framedVortexNormalize hc m).symm
    ⟨coeffVortex (a D), coeffVortex_mem hm _⟩), ?_, fun D ↦ ?_⟩
  · refine continuous_induced_rng.2 (((continuous_dilateCoord_comp √c).comp
      ((continuous_coeffVortex hm).comp ha)).congr fun D ↦ ?_)
    ext1 z
    simp [dilateCoord]
  · rw [Equiv.symm_apply_apply, framedVortexDivisor_framedVortexNormalize_symm,
      framedVortexDivisor_coeffVortex hm]
    simp only [a, Sym.coeffHomeomorph_apply, Equiv.symm_apply_apply, Sym.map_map]
    convert Sym.map_id D using 2
    simp [hc']

variable (c m) in
/-- The orbit spaces of the smooth framed gauge group on `framedVortexSubMulAction c m` and on
`framedVortices c m` are identified by the equivariant `TauCeti.Vortex.framedVortexEquiv`
(`TauCeti.MulAction.orbitRelQuotientCongr`). -/
def framedVortexOrbitEquiv :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction c m) ≃
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortices c m) :=
  MulAction.orbitRelQuotientCongr (MulEquiv.refl _) (framedVortexEquiv c m) framedVortexEquiv_smul

/-- The orbit of a framed vortex goes to the orbit of the same vortex regarded as a continuous
field. -/
@[simp]
theorem framedVortexOrbitEquiv_mk (x : framedVortexSubMulAction c m) :
    framedVortexOrbitEquiv c m (Quotient.mk'' x) = Quotient.mk'' (framedVortexEquiv c m x) :=
  MulAction.orbitRelQuotientCongr_mk _ _ _ x

/-- The orbit of a framed vortex regarded as a continuous field goes back to the orbit of the same
vortex in `framedVortexSubMulAction c m`. -/
@[simp]
theorem framedVortexOrbitEquiv_symm_mk (x : framedVortices c m) :
    (framedVortexOrbitEquiv c m).symm (Quotient.mk'' x) =
      Quotient.mk'' ((framedVortexEquiv c m).symm x) :=
  MulAction.orbitRelQuotientCongr_symm_mk _ _ _ x

/-- The divisor bijection `TauCeti.Vortex.framedVortexModuliEquiv`, read through
`TauCeti.Vortex.framedVortexOrbitEquiv`, sends the orbit of a framed vortex to its divisor. -/
private theorem framedVortexModuliEquiv_framedVortexOrbitEquiv_symm_mk (hc : 0 < c)
    (x : framedVortices c m) :
    framedVortexModuliEquiv hc m ((framedVortexOrbitEquiv c m).symm (Quotient.mk'' x)) =
      framedVortexDivisor ((framedVortexEquiv c m).symm x) := by
  rw [framedVortexOrbitEquiv_symm_mk, framedVortexModuliEquiv_mk]

/-- **The moduli space of framed plane vortices is homeomorphic to `Sym ℂ m`** (Taubes). For
`c > 0`, the zero divisor identifies the orbit space of the smooth framed gauge group on the smooth
framed degree-`m` vortices of coupling `c`, with the topology of locally uniform convergence, with
`Sym ℂ m`, collisions of zeros included. -/
def framedVortexModuliHomeomorph (hc : 0 < c) (m : ℕ) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortices c m) ≃ₜ Sym ℂ m where
  toEquiv := (framedVortexOrbitEquiv c m).symm.trans (framedVortexModuliEquiv hc m)
  continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.2 <|
    continuous_framedVortexDivisor.congr fun x ↦
      (framedVortexModuliEquiv_framedVortexOrbitEquiv_symm_mk hc x).symm
  continuous_invFun := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact continuous_of_const fun _ _ ↦ congrArg _ (Subsingleton.elim _ _)
    obtain ⟨s, hs, hsD⟩ := exists_continuous_framedVortexDivisor_eq hc hm
    -- The section `s` is a right inverse of the divisor, hence it picks the inverse's orbits.
    refine (continuous_quot_mk.comp hs).congr fun D ↦ (((framedVortexOrbitEquiv c m).symm.trans
      (framedVortexModuliEquiv hc m)).symm_apply_eq.2 ?_).symm
    exact ((framedVortexModuliEquiv_framedVortexOrbitEquiv_symm_mk hc (s D)).trans (hsD D)).symm

/-- The orbit of a framed vortex goes to its divisor. -/
@[simp]
theorem framedVortexModuliHomeomorph_mk (hc : 0 < c) (x : framedVortices c m) :
    framedVortexModuliHomeomorph hc m (Quotient.mk'' x) =
      framedVortexDivisor ((framedVortexEquiv c m).symm x) :=
  framedVortexModuliEquiv_framedVortexOrbitEquiv_symm_mk hc x

/-- The homeomorphism `TauCeti.Vortex.framedVortexModuliHomeomorph` extends the bijection
`TauCeti.Vortex.framedVortexModuliEquiv` on the orbit space of `framedVortexSubMulAction c m`. -/
@[simp]
theorem framedVortexModuliHomeomorph_framedVortexOrbitEquiv (hc : 0 < c)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction c m)) :
    framedVortexModuliHomeomorph hc m (framedVortexOrbitEquiv c m q) =
      framedVortexModuliEquiv hc m q :=
  congrArg (framedVortexModuliEquiv hc m) ((framedVortexOrbitEquiv c m).symm_apply_apply q)

/-- **The divisor is a quotient map.** For `c > 0`, `Sym ℂ m` carries the quotient topology of the
zero divisor on the framed vortices of coupling `c`, with the topology of locally uniform
convergence. -/
theorem isQuotientMap_framedVortexDivisor (hc : 0 < c) :
    Topology.IsQuotientMap
      fun x : framedVortices c m ↦ framedVortexDivisor ((framedVortexEquiv c m).symm x) := by
  convert (framedVortexModuliHomeomorph hc m).isQuotientMap.comp isQuotientMap_quotient_mk' using 1
  exact funext fun x ↦ (framedVortexModuliHomeomorph_mk hc x).symm

end TauCeti.Vortex
