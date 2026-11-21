/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Augmentation
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Complex orientations of bijective augmented maps

Let `f : M → N` and `g : M → V` be complex-linear, with `V` finite-dimensional, and suppose the
augmented map `f.prod g : M → N × V` is bijective. Then `g` maps the kernel of `f` complex-linearly
and isomorphically onto `V`, and the determinant line of the underlying real map of `f` is
identified with `det V` (`LinearMap.detLineEquivOfBijectiveProd`). This file shows that the
identification respects complex orientations: it sends the complex orientation of the determinant
line of `f` (`LinearMap.IsComplexPositiveDetLine`) to the complex orientation of `V`
(`TauCeti.IsComplexPositive`).

For a Cauchy–Riemann operator `f` augmented by the evaluation `g` of its sections at finitely many
points, the sign comparing an orientation of `det f` with the complex orientation of the fibres
at the points is the sign with which a curve through these points is counted. When the operator
and the evaluation are complex-linear and the orientation of `det f` is the complex one, this sign
is `+1`.

## Main results

* `LinearMap.IsComplexPositiveDetLine.isComplexPositive_detLineEquivOfBijectiveProd`: the
  identification `det f ≃ det V` of a bijective complex-linear augmented map preserves complex
  positivity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 3.2 and Appendix A.2.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential
  Geom. **44** (1996), 818–893.
-/

public section

noncomputable section

open Module TensorProduct TauCeti

namespace LinearMap

variable {M N V : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  {f : M →ₗ[ℂ] N} {g : M →ₗ[ℂ] V} [FiniteDimensional ℝ V]

/-- **Complex-linear augmented maps preserve complex orientations.** If `f` and `g` are
complex-linear and the real augmented map `f.prod g` is bijective, then
`LinearMap.detLineEquivOfBijectiveProd` sends complex positive elements of the determinant line of
`f` to complex positive elements of `det V`. -/
theorem IsComplexPositiveDetLine.isComplexPositive_detLineEquivOfBijectiveProd
    (h : Function.Bijective ((f.restrictScalars ℝ).prod (g.restrictScalars ℝ)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    IsComplexPositive
      ((f.restrictScalars ℝ).detLineEquivOfBijectiveProd (g.restrictScalars ℝ) h z) := by
  -- `f` is onto and `g` restricts to a complex-linear isomorphism `e : ker f ≃ V`.
  -- The complex augmented map `f.prod g` has the same underlying function as the real one.
  have hC : Function.Bijective (f.prod g) := h
  have hg : Function.Bijective (g.domRestrict (ker f)) := bijective_domRestrict_of_bijective_prod hC
  let e : ker f ≃ₗ[ℂ] V := LinearEquiv.ofBijective _ hg
  -- A complex basis `b` of `ker f`; the cokernel of `f` is zero.
  have : FiniteDimensional ℝ (ker f) :=
    Module.Finite.of_injective ((g.domRestrict (ker f)).restrictScalars ℝ) hg.1
  have : FiniteDimensional ℂ (ker f) := Module.Finite.of_restrictScalars_finite ℝ ℂ (ker f)
  let b := Module.finBasis ℂ (ker f)
  have hn : finrank ℝ (ker f) = 2 * finrank ℂ (ker f) := finrank_real_eq_two_mul_finrank_complex
  have := subsingleton_quotient_range_of_surjective_prod hC.2
  have h₀ : finrank ℝ (N ⧸ range f) = 2 * 0 := finrank_zero_of_subsingleton
  -- The explicit complex positive element `z₀ = (b₀ ∧ I • b₀ ∧ ⋯) ⊗ φ₀` of the determinant line,
  -- with `φ₀` taking the value `1` on the empty exterior product of the zero cokernel.
  let φ₀ : Dual ℝ (TauCeti.detLine ℝ (N ⧸ range f)) := (detLineEquivOfFinrankEqZero h₀ :
    TauCeti.detLine ℝ (N ⧸ range f) →ₗ[ℝ] ℝ)
  have hφ₀ : IsComplexPositiveDual φ₀ :=
    (isComplexPositive_ιMulti_complexToRealFamily (Basis.empty (N ⧸ range f) : Basis (Fin 0) ℂ _)
      h₀).isComplexPositiveDual_iff.mpr (by simp [φ₀])
  let z₀ := f.detLineRestrictScalarsEquiv.symm
    (exteriorPower.ιMulti ℝ _ (complexToRealFamily ⇑b ∘ Fin.cast hn) ⊗ₜ φ₀)
  have hz₀ : f.IsComplexPositiveDetLine z₀ := by
    rw [isComplexPositiveDetLine_iff, LinearEquiv.apply_symm_apply]
    exact (isComplexPositive_ιMulti_complexToRealFamily b hn).isComplexPositiveTMulDual_tmul hφ₀
  obtain ⟨c, hc, rfl⟩ := hz₀.exists_pos_smul_eq hz
  rw [map_smul]
  refine IsComplexPositive.smul ((isComplexPositive_iff (b.map e)).mpr ⟨1, one_pos, ?_⟩) hc
  -- Compute the image of `z₀` by `LinearMap.coe_detLineEquivOfBijectiveProd_tmul`.
  have h₀' : finrank ℝ (N ⧸ range (f.restrictScalars ℝ)) = 0 :=
    (f.cokerRestrictScalarsEquiv ℝ).finrank_eq.trans h₀
  dsimp only [z₀]
  rw [detLineRestrictScalarsEquiv_symm_tmul, LinearEquiv.detLineCongr_ιMulti,
    coe_detLineEquivOfBijectiveProd_tmul _ _ h _ _ (Fin.elim0 ∘ Fin.cast h₀'),
    LinearMap.comp_apply]
  simp only [φ₀, LinearEquiv.coe_coe, LinearEquiv.detLineCongr_ιMulti,
    detLineEquivOfFinrankEqZero_ιMulti, one_smul, Basis.coe_map]
  rw [← LinearEquiv.coe_coe e, complexToRealFamily_comp, ← TauCeti.ExteriorAlgebra.ιMulti_comp_cast
    ((f.kerRestrictScalarsEquiv ℝ).finrank_eq.symm.trans hn)]
  congr 1
  funext i
  simp only [e, Function.comp_apply, domRestrict_apply, coe_kerRestrictScalarsEquiv_apply,
    coe_restrictScalars, LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply, Fin.cast_cast]

end LinearMap
