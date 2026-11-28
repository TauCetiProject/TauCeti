/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.MaxCompact
public import TauCeti.LinearAlgebra.Matrix.PrincipalMinorProd
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.DiscreteSeries.DoubledParameter
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.Matrix
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary

/-!
# Flensted-Jensen's function `c_λ`, the formal degree and the kernel `e_λ`

Let `ε : ι → ℤˣ` be signs, `G = U(ε)` the unitary group of the hermitian form of `diag(ε)`
(`U(p, q)`) and `K = U(p) × U(q)` its maximal compact subgroup (`TauCeti.Fock.maxCompact ε`), with
its Haar probability measure `dk`. For a doubled Harish-Chandra parameter `l = 2λ`, write
`Λ = λ + ρ - 2ρ_c` for its lowest `K`-type and `m_w` for the product of principal minors of
weight `w` (`Matrix.principalMinorProd`). Following Flensted-Jensen, the coefficient of the lowest
`K`-type of the discrete series of parameter `λ` is the explicit integral

`Ξ_l(a, z) = (∫_K m_Λ(a k) · conj m_Λ(k) / m_{-(λ+ρ)}(k* z k) dk) / ‖m_Λ‖²_K`,
`c_λ(g) = Ξ_l(a_g, a_g⁻¹ g)`,

where `‖m_w‖²_K = ∫_K |m_w(k)|² dk` and `a_g` is the block diagonal part of `g` for the signs `ε`
(`Matrix.blockDiagPart`), which is invertible for `g ∈ G`
(`TauCeti.Fock.det_blockDiagPart_ne_zero`). This file defines `Ξ_l`
(`TauCeti.DiscreteSeries.flenstedJensenIntegral`), `c_λ` as a function of a complex matrix
(`TauCeti.DiscreteSeries.flenstedJensen`), the formal degree `deg_λ = (∫_G |c_λ|²)⁻¹` for a Haar
measure on `G` (`TauCeti.DiscreteSeries.formalDegree`) and the kernel `e_λ = deg_λ · conj c_λ`
(`TauCeti.DiscreteSeries.kernel`). The normalisation is the one of `c_λ(1) = 1`
(`TauCeti.DiscreteSeries.flenstedJensen_one`): `m_Λ` is continuous on `K` and `1` at `1`, so
`‖m_Λ‖²_K > 0` (`TauCeti.DiscreteSeries.principalMinorProdNormSq_pos`), and the integrand of
`Ξ_l(1, 1)` is `|m_Λ(k)|²`.

The definitions make sense for every `l`; the analytic properties of `c_λ` (its independence of
the splitting `g = a_g · a_g⁻¹ g`, its decay, square integrability and Schur orthogonality) need a
gap between the entries of `l` of different signs (`TauCeti.DiscreteSeries.HasGap`). When `c_λ` is
not square integrable the integral defining `deg_λ` is `0`, and so is `deg_λ`, the value
`1 / ∞` of the formal degree of a function that is not square integrable.

## Main definitions

* `TauCeti.DiscreteSeries.principalMinorProdNormSq ε w`: `‖m_w‖²_K`.
* `TauCeti.DiscreteSeries.flenstedJensenIntegral ε l a z`: `Ξ_l(a, z)`.
* `TauCeti.DiscreteSeries.flenstedJensen ε l g`: Flensted-Jensen's function `c_λ(g)`.
* `TauCeti.DiscreteSeries.formalDegree ε l μ`: `deg_λ` for the Haar measure `μ` on `G`.
* `TauCeti.DiscreteSeries.kernel ε l μ g`: `e_λ(g) = deg_λ · conj c_λ(g)`.

## Main results

* `TauCeti.DiscreteSeries.continuous_principalMinorProd_maxCompact`: `m_w` is continuous on `K`.
* `TauCeti.DiscreteSeries.principalMinorProdNormSq_pos`: `‖m_w‖²_K > 0`.
* `TauCeti.DiscreteSeries.flenstedJensen_one`: `c_λ(1) = 1`.
* `TauCeti.DiscreteSeries.formalDegree_nonneg`: `deg_λ ≥ 0`.

## References

* M. Flensted-Jensen, *Discrete series for semisimple symmetric spaces*, Ann. of Math. 111 (1980),
  253–311.
* B. Sun, *Matrix coefficients of cohomologically induced representations*, Compositio Math. 143
  (2007).
* The shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>
  (Apache 2.0): the definitions follow `New.HCParam.flenstedJensen`, `New.HCParam.dsCoeff`,
  `New.HCParam.formalDegree` and `New.HCParam.dsKernel` in
  `src/Lib/DiscreteSeries/FlenstedJensen/Defs.lean`, and `c_λ(1) = 1` follows `New.dsCoeff_one` in
  `src/Lib/DiscreteSeries/FlenstedJensen/PsiKTypes.lean`.
-/

public section

open MeasureTheory Matrix TauCeti.Fock
open scoped ComplexConjugate

namespace TauCeti.DiscreteSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℤˣ)
  [MeasurableSpace (maxCompact ε)] [BorelSpace (maxCompact ε)]

/-- The squared `L²` norm `‖m_w‖²_K = ∫_K |m_w(k)|² dk` on the maximal compact subgroup `K` of the
product of principal minors of weight `w`, for the Haar probability measure of `K`. -/
noncomputable def principalMinorProdNormSq (w : ι → ℤ) : ℝ :=
  ∫ k : maxCompact ε, ‖((k : GL ι ℂ) : Matrix ι ι ℂ).principalMinorProd w‖ ^ 2
    ∂haarProb (maxCompact ε)

theorem principalMinorProdNormSq_def (w : ι → ℤ) :
    principalMinorProdNormSq ε w =
      ∫ k : maxCompact ε, ‖((k : GL ι ℂ) : Matrix ι ι ℂ).principalMinorProd w‖ ^ 2
        ∂haarProb (maxCompact ε) :=
  (rfl)

/-- **Flensted-Jensen's integral** `Ξ_l(a, z)` of the doubled parameter `l = 2λ`:
`(∫_K m_Λ(a k) · conj m_Λ(k) / m_{-(λ+ρ)}(k* z k) dk) / ‖m_Λ‖²_K`, where `Λ` is the lowest `K`-type
of `l` for the signs `ε`, `ρ` is taken for the order of `l`, and `dk` is the Haar probability
measure of `K`. -/
noncomputable def flenstedJensenIntegral (l : ι → ℤ) (a z : Matrix ι ι ℂ) : ℂ :=
  (∫ k : maxCompact ε,
      (a * ((k : GL ι ℂ) : Matrix ι ι ℂ)).principalMinorProd (lowestKType ε l) *
        conj (((k : GL ι ℂ) : Matrix ι ι ℂ).principalMinorProd (lowestKType ε l)) /
        (star ((k : GL ι ℂ) : Matrix ι ι ℂ) * z * ((k : GL ι ℂ) : Matrix ι ι ℂ)).principalMinorProd
          (-paramAddRho l) ∂haarProb (maxCompact ε)) /
    principalMinorProdNormSq ε (lowestKType ε l)

theorem flenstedJensenIntegral_def (l : ι → ℤ) (a z : Matrix ι ι ℂ) :
    flenstedJensenIntegral ε l a z =
      (∫ k : maxCompact ε,
          (a * ((k : GL ι ℂ) : Matrix ι ι ℂ)).principalMinorProd (lowestKType ε l) *
            conj (((k : GL ι ℂ) : Matrix ι ι ℂ).principalMinorProd (lowestKType ε l)) /
            (star ((k : GL ι ℂ) : Matrix ι ι ℂ) * z *
              ((k : GL ι ℂ) : Matrix ι ι ℂ)).principalMinorProd (-paramAddRho l)
          ∂haarProb (maxCompact ε)) /
        principalMinorProdNormSq ε (lowestKType ε l) :=
  (rfl)

/-- **Flensted-Jensen's function** `c_λ(g) = Ξ_l(a_g, a_g⁻¹ g)` of the doubled parameter
`l = 2λ`, where `a_g` is the block diagonal part of `g` for the signs `ε`, invertible on the
unitary group `U(ε)` (`TauCeti.Fock.det_blockDiagPart_ne_zero`). Flensted-Jensen's integral formula
identifies it, for a parameter with a gap, with the coefficient of the lowest `K`-type of the
discrete series of parameter `λ`. -/
noncomputable def flenstedJensen (l : ι → ℤ) (g : Matrix ι ι ℂ) : ℂ :=
  flenstedJensenIntegral ε l (g.blockDiagPart ε) ((g.blockDiagPart ε)⁻¹ * g)

theorem flenstedJensen_def (l : ι → ℤ) (g : Matrix ι ι ℂ) :
    flenstedJensen ε l g =
      flenstedJensenIntegral ε l (g.blockDiagPart ε) ((g.blockDiagPart ε)⁻¹ * g) :=
  (rfl)

/-- **The formal degree** `deg_λ = (∫_G |c_λ|² dμ)⁻¹` of Flensted-Jensen's function for a measure
`μ` on `G = U(ε)`, normally a Haar measure. It is `0` when `c_λ` is not square integrable. -/
noncomputable def formalDegree (l : ι → ℤ) [MeasurableSpace (unitaryGroup ε)]
    (μ : Measure (unitaryGroup ε)) : ℝ :=
  (∫ g : unitaryGroup ε, ‖flenstedJensen ε l ((g : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ 2 ∂μ)⁻¹

theorem formalDegree_def (l : ι → ℤ) [MeasurableSpace (unitaryGroup ε)]
    (μ : Measure (unitaryGroup ε)) :
    formalDegree ε l μ =
      (∫ g : unitaryGroup ε, ‖flenstedJensen ε l ((g : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ 2 ∂μ)⁻¹ :=
  (rfl)

theorem formalDegree_nonneg (l : ι → ℤ) [MeasurableSpace (unitaryGroup ε)]
    (μ : Measure (unitaryGroup ε)) : 0 ≤ formalDegree ε l μ :=
  inv_nonneg.2 (integral_nonneg fun _ ↦ by positivity)

/-- **The kernel** `e_λ = deg_λ · conj c_λ` of the doubled parameter `l = 2λ`, for the formal
degree taken with respect to the measure `μ` on `U(ε)`: the kernel attached to the discrete series
of parameter `λ` through its lowest `K`-type coefficient `c_λ`. -/
noncomputable def kernel (l : ι → ℤ) [MeasurableSpace (unitaryGroup ε)]
    (μ : Measure (unitaryGroup ε)) (g : Matrix ι ι ℂ) : ℂ :=
  formalDegree ε l μ * conj (flenstedJensen ε l g)

theorem kernel_apply (l : ι → ℤ) [MeasurableSpace (unitaryGroup ε)]
    (μ : Measure (unitaryGroup ε)) (g : Matrix ι ι ℂ) :
    kernel ε l μ g = formalDegree ε l μ * conj (flenstedJensen ε l g) :=
  (rfl)

omit [MeasurableSpace (maxCompact ε)] [BorelSpace (maxCompact ε)] in
/-- A product of principal minors is continuous on the maximal compact subgroup. -/
theorem continuous_principalMinorProd_maxCompact (w : ι → ℤ) :
    Continuous fun k : maxCompact ε ↦ ((k : GL ι ℂ) : Matrix ι ι ℂ).principalMinorProd w := by
  have hval : Continuous fun k : maxCompact ε ↦ ((k : GL ι ℂ) : Matrix ι ι ℂ) :=
    Units.continuous_val.comp continuous_subtypeVal
  simp only [principalMinorProd_def, principalMinor_def]
  refine continuous_finsetProd _ fun t _ ↦ (hval.matrix_submatrix _ _).matrix_det.div ?_
    fun k ↦ ?_
  · split_ifs
    · exact hval.matrix_det
    · exact continuous_const
  · split_ifs
    · exact GeneralLinearGroup.det_ne_zero _
    · exact one_ne_zero

/-- `‖m_w‖²_K > 0`: the continuous function `m_w` is `1` at `1`. -/
theorem principalMinorProdNormSq_pos (w : ι → ℤ) : 0 < principalMinorProdNormSq ε w := by
  have hc : Continuous fun k : maxCompact ε ↦
      ‖((k : GL ι ℂ) : Matrix ι ι ℂ).principalMinorProd w‖ ^ 2 :=
    (continuous_principalMinorProd_maxCompact ε w).norm.pow 2
  rw [principalMinorProdNormSq_def, integral_pos_iff_support_of_nonneg (fun _ ↦ by positivity)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact hc.isOpen_support.measure_pos _ ⟨1, by simp⟩

/-- **Normalisation of Flensted-Jensen's function**: `c_λ(1) = 1`. -/
theorem flenstedJensen_one (l : ι → ℤ) : flenstedJensen ε l 1 = 1 := by
  have hk (k : maxCompact ε) : star ((k : GL ι ℂ) : Matrix ι ι ℂ) * 1 * ((k : GL ι ℂ) :
      Matrix ι ι ℂ) = 1 := by
    rw [Matrix.mul_one, ← mem_unitaryGroup_iff']
    exact mem_unitarySubgroup_GL_iff_mem_unitaryGroup.1 (mem_maxCompact_iff.1 k.property).2
  rw [flenstedJensen_def, blockDiagPart_one, inv_one, Matrix.mul_one, flenstedJensenIntegral_def]
  simp only [Matrix.one_mul, hk, principalMinorProd_one, div_one, Complex.mul_conj',
    ← Complex.ofReal_pow]
  rw [integral_complex_ofReal, ← principalMinorProdNormSq_def]
  exact div_self (by exact_mod_cast (principalMinorProdNormSq_pos ε _).ne')

end TauCeti.DiscreteSeries
