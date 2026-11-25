/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The canonical bundle of the projective line is `𝒪(-2)`

Let `𝕜` be a complete nontrivially normed field and `ℙ¹ = ℙ 𝕜 (Fin 2 → 𝕜)` the projective line,
with its two affine charts: the chart `0` has the coordinate `w = v₁ / v₀` and the chart `1` the
coordinate `z = v₀ / v₁`. This file identifies the canonical bundle `K_ℙ¹`
(`TauCeti.CanonicalBundle`, the bundle of top-degree forms) with the line bundle `𝒪(-2)`
(`Projectivization.twistCore (-2)`), as analytic line bundles. For `𝕜 = ℂ` this is the holomorphic
isomorphism `K_ℂℙ¹ ≃ 𝒪(-2)`.

**Transition functions.** On the overlap of the two charts `z = 1 / w`, so `dz = -w⁻² dw`. More
precisely, the derivative of the change from the chart `i` to the chart `j ≠ i` is multiplication
by `-(v j / v i)⁻²` (`Projectivization.hasFDerivAt_affineChart_symm_trans`), and the Jacobian
determinant of `tangentCoordChange` is `εᵢ εⱼ (v j / v i)⁻²`
(`Projectivization.det_tangentCoordChange_fin_two`). Here `εᵢ = eulerFormSign i` is `1` for the
chart `0` and `-1` for the chart `1`. Since the transitions of the canonical bundle are these
Jacobian determinants (`TauCeti.CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul`), and
those of `𝒪(-2)` are `(v j / v i)⁻²` (`Projectivization.twistTransition`), the two cocycles agree
up to the coboundary of the locally constant signs `εᵢ`.

**The isomorphism.** The fibre map `Projectivization.twistEquivCanonicalBundle x` sends a vector
of `𝒪(-2)` at `x` with coordinate `c` in the frame of the preferred chart `i` at `x` to the form
`c εᵢ dzᵢ`, where `dzᵢ` is the coordinate form of that chart
(`TauCeti.CanonicalBundle.coordForm`). Thus the frame of the chart `0` goes to `dw` and the frame of
the chart `1` goes to `-dz`. Read in the trivializations of any chart `i₀`, the isomorphism is
multiplication by the constant `εᵢ₀` (`Projectivization.trivializationAt_twistEquivCanonicalBundle`
and `Projectivization.trivializationAt_twistEquivCanonicalBundle_symm`), so the maps of total spaces
in both directions are analytic (`Projectivization.contMDiff_twistEquivCanonicalBundle`,
`Projectivization.contMDiff_twistEquivCanonicalBundle_symm`), and together they form an analytic
diffeomorphism of total spaces over `ℙ¹` (`Projectivization.twistDiffeomorphCanonicalBundle`). In
homogeneous coordinates the isomorphism is multiplication by the Euler form `v₀ dv₁ - v₁ dv₀`,
which is homogeneous of degree `2` and reads `dw` in the chart `0` and `-dz` in the chart `1`.

Combined with Serre duality, `H¹(ℂℙ¹, 𝒪(k))` is dual to `H⁰(ℂℙ¹, K ⊗ 𝒪(-k)) = H⁰(ℂℙ¹, 𝒪(-2-k))`,
which vanishes for `k ≥ -1` (`Projectivization.holomorphicTwistSections_eq_bot`). This is the
vanishing that makes the lines of `ℂPⁿ`, whose normal bundles are sums of `𝒪(1)`, regular
holomorphic spheres.

## Main declarations

* `Projectivization.eulerFormSign`: the sign `εᵢ` of the Euler form in the chart `i`.
* `Projectivization.det_tangentCoordChange_fin_two`: the Jacobian determinants of the coordinate
  changes of `ℙ¹`, `dz = -w⁻² dw`.
* `Projectivization.twistEquivCanonicalBundle`: the fibrewise isomorphism `𝒪(-2) ≃ K_ℙ¹`.
* `Projectivization.contMDiff_twistEquivCanonicalBundle` and
  `Projectivization.contMDiff_twistEquivCanonicalBundle_symm`: it is analytic in both directions.
* `Projectivization.twistDiffeomorphCanonicalBundle`: the analytic diffeomorphism of total spaces.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1, §1
  (the canonical bundle of `ℙⁿ` is `𝒪(-n-1)`, through the Euler form).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.4.
-/

public noncomputable section

open Bundle Set TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization Topology

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### The coordinate changes of the projective line -/

section Transition

/-- The sign of the Euler form `v₀ dv₁ - v₁ dv₀` in the affine charts of the projective line: it
reads `dw` in the chart `0`, with coordinate `w = v₁ / v₀`, and `-dz` in the chart `1`, with
coordinate `z = v₀ / v₁`. -/
def eulerFormSign (i : Fin 2) : 𝕜 :=
  if i = 0 then 1 else -1

@[simp]
theorem eulerFormSign_zero : eulerFormSign (𝕜 := 𝕜) 0 = 1 :=
  ite_eq_left rfl

@[simp]
theorem eulerFormSign_one : eulerFormSign (𝕜 := 𝕜) 1 = -1 :=
  ite_eq_right Fin.zero_ne_one.symm

@[simp]
theorem eulerFormSign_mul_self (i : Fin 2) : eulerFormSign (𝕜 := 𝕜) i * eulerFormSign i = 1 := by
  fin_cases i <;> simp

/-- The Euler form has opposite signs in the two charts. -/
theorem eulerFormSign_mul_of_ne {i j : Fin 2} (h : i ≠ j) :
    eulerFormSign (𝕜 := 𝕜) i * eulerFormSign j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- The change between the two affine charts of the projective line is `z ↦ 1 / z`. -/
theorem affineChart_symm_trans_eq_inv_of_ne {i j : Fin 2} (h : i ≠ j) :
    ⇑((affineChart (K := 𝕜) i).symm.trans (affineChart j)) = fun z _ ↦ (z 0)⁻¹ := by
  funext z k
  rw [affineChart_symm_trans_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.insertNth]

/-- **`dz = -w⁻² dw`.** The derivative of the change from the affine chart `i` to the affine chart
`j` of the projective line, at a point `z` of the chart `i` with homogeneous coordinates
`v = Fin.insertNth i 1 z`, is multiplication by `εᵢ εⱼ (v j)⁻²`: the identity for `i = j`, and
`-(z 0)⁻²` for `i ≠ j`. -/
theorem hasFDerivAt_affineChart_symm_trans (i j : Fin 2) {z : Fin 1 → 𝕜}
    (hz : Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j ≠ 0) :
    HasFDerivAt ((affineChart (K := 𝕜) i).symm.trans (affineChart j))
      ((eulerFormSign i * eulerFormSign j * Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j ^ (-2 : ℤ)) •
        ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜)) z := by
  rcases eq_or_ne i j with rfl | h
  · have hid : ⇑((affineChart (K := 𝕜) i).symm.trans (affineChart i)) = id := by
      funext z k
      rw [affineChart_symm_trans_apply]
      simp
    rw [hid, Fin.insertNth_apply_same, eulerFormSign_mul_self]
    simpa using hasFDerivAt_id (𝕜 := 𝕜) z
  · -- In the chart `i`, the homogeneous coordinate `j ≠ i` is the affine coordinate.
    have hj : Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j = z 0 := by
      fin_cases i <;> fin_cases j <;> simp_all [Fin.insertNth]
    rw [hj] at hz ⊢
    rw [affineChart_symm_trans_eq_inv_of_ne h, eulerFormSign_mul_of_ne h]
    have h0 := (hasDerivAt_inv hz).hasFDerivAt.comp z (hasFDerivAt_apply (𝕜 := 𝕜) 0 z)
    refine hasFDerivAt_pi'' fun k ↦ h0.congr_fderiv ?_
    ext v
    fin_cases k
    simpa [zpow_neg] using mul_comm _ _

/-- **The Jacobian determinants of the projective line.** The determinant of the derivative of the
change from the coordinates of the chart at `x₁` to those of the chart at `x₀`, at a point `x` of
both charts, is `εᵢ₀ εᵢ₁ (v i₀ / v i₁)⁻²`, where `i₀` and `i₁` are the indices of the two charts and
`[v] = x`. Up to the signs, this is the transition function of `𝒪(-2)` from the chart `i₀` to the
chart `i₁`. -/
theorem det_tangentCoordChange_fin_two {x₀ x₁ x : ℙ 𝕜 (Fin 2 → 𝕜)}
    (hx₀ : x ∈ (chartAt (Fin 1 → 𝕜) x₀).source) (hx₁ : x ∈ (chartAt (Fin 1 → 𝕜) x₁).source) :
    LinearMap.det (tangentCoordChange 𝓘(𝕜, Fin 1 → 𝕜) x₁ x₀ x :
        (Fin 1 → 𝕜) →ₗ[𝕜] Fin 1 → 𝕜) =
      eulerFormSign ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₀) *
        eulerFormSign ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₁) *
        twistTransition (-2) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₀)
          ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₁) x := by
  set i₀ := (twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₀
  set i₁ := (twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₁
  have h₀ : x ∈ affineOpen i₀ := by
    simpa [chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt (-2) x₀] using hx₀
  have h₁ : x ∈ affineOpen i₁ := by
    simpa [chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt (-2) x₁] using hx₁
  have hz : Fin.insertNth (α := fun _ ↦ 𝕜) i₁ 1 (affineChart i₁ x) i₀ ≠ 0 := by
    rw [← rep_div_rep_eq_insertNth_affineChart i₀ h₁]
    exact div_ne_zero ((mem_affineOpen_iff i₀ x).1 h₀) ((mem_affineOpen_iff i₁ x).1 h₁)
  have hd := (hasFDerivAt_affineChart_symm_trans i₁ i₀ hz).fderiv
  rw [PartialEquiv.coe_trans] at hd
  -- With the trivial model, `tangentCoordChange` is the derivative of the change of affine charts.
  have hchart : tangentCoordChange 𝓘(𝕜, Fin 1 → 𝕜) x₁ x₀ x =
      fderiv 𝕜 (affineChart i₀ ∘ (affineChart i₁).symm) (affineChart i₁ x) := by
    simp [chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt (-2) x₀,
      chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt (-2) x₁, i₀, i₁]
  rw [hchart, hd, ← rep_div_rep_eq_insertNth_affineChart i₀ h₁, twistTransition_def]
  simp [LinearMap.det_smul, mul_comm]

end Transition

/-! ### The isomorphism `𝒪(-2) ≃ K_ℙ¹` -/

section Equiv

variable [CompleteSpace 𝕜]

/-- The standard basis of the model space `Fin 1 → 𝕜` of the affine charts of the projective line,
indexed by `Fin (finrank 𝕜 (Fin 1 → 𝕜))` as the canonical bundle requires. Its coordinate form
in a chart (`TauCeti.CanonicalBundle.coordForm`) is the differential `dw` of the affine
coordinate `w` of that chart. -/
def projectiveLineChartBasis : Module.Basis (Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))) 𝕜 (Fin 1 → 𝕜) :=
  (Pi.basisFun 𝕜 (Fin 1)).reindex (finCongr (Module.finrank_fin_fun 𝕜).symm)

/-- **The fibres of `𝒪(-2)` and of the canonical bundle of the projective line.** At `x`, with
preferred chart `i`, a vector of `𝒪(-2)` with coordinate `c` in the frame of the chart `i` goes to
the form `c εᵢ dwᵢ`, where `dwᵢ` is the coordinate form of the chart `i`: the frame of the chart `0`
goes to `dw` and the frame of the chart `1` to `-dz`. The inverse reads the coefficient of a form in
the frame `dwᵢ` and multiplies it by `εᵢ`. -/
def twistEquivCanonicalBundle (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber x ≃ₗ[𝕜]
      CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜)) x :=
  -- The fibre of a vector bundle core is its model fibre `𝕜`, by definition.
  (LinearEquiv.refl 𝕜 𝕜 : (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber x ≃ₗ[𝕜] 𝕜).trans
  { LinearMap.toSpanSingleton 𝕜 (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜)) x)
      (eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x) •
        CanonicalBundle.coordForm 𝓘(𝕜, Fin 1 → 𝕜) x projectiveLineChartBasis x) with
    invFun α := eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x) *
      (trivializationAt ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
        (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) x ⟨x, α⟩).2
          projectiveLineChartBasis
    left_inv c := by
      have hlin := ((trivializationAt ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
        (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) x).linear 𝕜
          (mem_baseSet_trivializationAt _ _ x)).map_smul
            (c * eulerFormSign ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x))
            (CanonicalBundle.coordForm 𝓘(𝕜, Fin 1 → 𝕜) x projectiveLineChartBasis x)
      simp only [LinearMap.toFun_eq_coe, LinearMap.toSpanSingleton_apply]
      rw [smul_smul, hlin,
        CanonicalBundle.trivializationAt_apply_snd_coordForm (mem_chart_source _ x),
        ContinuousAlternatingMap.smul_apply, Module.Basis.continuousDet_apply,
        Module.Basis.det_self, smul_eq_mul, mul_one, mul_left_comm, eulerFormSign_mul_self,
        mul_one]
    right_inv α := by
      simp only [LinearMap.toFun_eq_coe, LinearMap.toSpanSingleton_apply]
      rw [smul_smul, mul_right_comm, eulerFormSign_mul_self, one_mul]
      exact (CanonicalBundle.eq_smul_coordForm (mem_chart_source _ x) α).symm }

theorem twistEquivCanonicalBundle_apply (x : ℙ 𝕜 (Fin 2 → 𝕜)) (c : 𝕜) :
    twistEquivCanonicalBundle x c =
      c • eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x) •
        CanonicalBundle.coordForm 𝓘(𝕜, Fin 1 → 𝕜) x projectiveLineChartBasis x :=
  (rfl)

theorem twistEquivCanonicalBundle_symm_apply (x : ℙ 𝕜 (Fin 2 → 𝕜))
    (α : CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜)) x) :
    ((twistEquivCanonicalBundle x).symm α : 𝕜) =
      eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x) *
        (trivializationAt ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
          (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) x ⟨x, α⟩).2
            projectiveLineChartBasis :=
  (rfl)

/-- **The isomorphism in the trivializations of a chart.** Read in the trivializations of the chart
`i₀` at `x₀`, the isomorphism `𝒪(-2) ≃ K_ℙ¹` sends the coordinate `c'` of a vector of `𝒪(-2)` to
`εᵢ₀ c'` times the determinant form, the coordinate of `dwᵢ₀`. -/
theorem trivializationAt_twistEquivCanonicalBundle (x₀ : ℙ 𝕜 (Fin 2 → 𝕜))
    {x : ℙ 𝕜 (Fin 2 → 𝕜)} (hx : x ∈ (chartAt (Fin 1 → 𝕜) x₀).source) (c : 𝕜) :
    (trivializationAt ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
        (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) x₀
        ⟨x, twistEquivCanonicalBundle x c⟩).2 =
      (eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₀) *
        (trivializationAt 𝕜 (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber x₀ ⟨x, c⟩).2) •
          projectiveLineChartBasis.continuousDet := by
  have hb : x ∈ (trivializationAt ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
      (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) x₀).baseSet := by
    simpa using hx
  have hlin := ((trivializationAt ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
    (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) x₀).linear 𝕜 hb).map_smul
  -- `dwₓ = det (tangentCoordChange) dwₓ₀`, and the determinant is the transition of `𝒪(-2)` up to
  -- the signs of the Euler form.
  rw [twistEquivCanonicalBundle_apply,
    CanonicalBundle.coordForm_eq_det_smul_coordForm (mem_chart_source _ x) hx,
    det_tangentCoordChange_fin_two (mem_chart_source _ x) hx, smul_smul, smul_smul, hlin,
    CanonicalBundle.trivializationAt_apply_snd_coordForm hx, VectorBundleCore.trivializationAt,
    ← VectorBundleCore.localTrivAt_def, VectorBundleCore.localTriv_apply,
    twistCore_coordChange_apply]
  congr 1
  linear_combination (c * eulerFormSign ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₀) *
    twistTransition (-2) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x)
      ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₀) x) *
    eulerFormSign_mul_self (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x)

/-- **The inverse isomorphism in the trivializations of a chart.** Read in the trivializations of
the chart `i₀` at `x₀`, the inverse isomorphism `K_ℙ¹ ≃ 𝒪(-2)` sends a form to `εᵢ₀` times its
coefficient in the frame `dwᵢ₀`. -/
theorem trivializationAt_twistEquivCanonicalBundle_symm (x₀ : ℙ 𝕜 (Fin 2 → 𝕜))
    {x : ℙ 𝕜 (Fin 2 → 𝕜)} (hx : x ∈ (chartAt (Fin 1 → 𝕜) x₀).source)
    (α : CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜)) x) :
    (trivializationAt 𝕜 (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber x₀
        ⟨x, (twistEquivCanonicalBundle x).symm α⟩).2 =
      eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt x₀) *
        (trivializationAt ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
          (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) x₀ ⟨x, α⟩).2
            projectiveLineChartBasis := by
  have h := congrArg (fun β ↦ β projectiveLineChartBasis)
    (trivializationAt_twistEquivCanonicalBundle x₀ hx ((twistEquivCanonicalBundle x).symm α))
  simp only [LinearEquiv.apply_symm_apply, ContinuousAlternatingMap.smul_apply,
    Module.Basis.continuousDet_apply, Module.Basis.det_self, smul_eq_mul, mul_one] at h
  rw [h, ← mul_assoc, eulerFormSign_mul_self, one_mul]

/-- **The isomorphism `𝒪(-2) ≃ K_ℙ¹` is analytic.** The map of total spaces from `𝒪(-2)` to the
canonical bundle of the projective line is analytic; for `𝕜 = ℂ` it is holomorphic. -/
theorem contMDiff_twistEquivCanonicalBundle :
    ContMDiff (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜))
      (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, (Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)) ω
      (fun p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber ↦
        (⟨p.proj, twistEquivCanonicalBundle p.proj p.snd⟩ :
          TotalSpace ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
            (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))))) := by
  intro p₀
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  -- Near `p₀` the fibre coordinate is a constant multiple of the coordinate of `𝒪(-2)`.
  have hO := ((contMDiffAt_totalSpace_iff (n := ω) (IB := 𝓘(𝕜, Fin 1 → 𝕜))
    (IM := 𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜))).1 (contMDiffAt_id (x := p₀))).2
  have hsrc : ∀ᶠ p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber in 𝓝 p₀,
      p.proj ∈ (chartAt (Fin 1 → 𝕜) p₀.proj).source :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((chartAt (Fin 1 → 𝕜) p₀.proj).open_source.mem_nhds (mem_chart_source _ _))
  refine ((ContinuousLinearMap.toSpanSingleton 𝕜
    (eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt p₀.proj) •
      projectiveLineChartBasis.continuousDet)).contMDiff.contMDiffAt.comp p₀
        hO).congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with p hp
  rw [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_smul, mul_comm]
  exact trivializationAt_twistEquivCanonicalBundle _ hp p.snd

/-- **The inverse isomorphism `K_ℙ¹ ≃ 𝒪(-2)` is analytic.** The map of total spaces from the
canonical bundle of the projective line to `𝒪(-2)` is analytic; for `𝕜 = ℂ` it is holomorphic. -/
theorem contMDiff_twistEquivCanonicalBundle_symm :
    ContMDiff
      (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, (Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜))
      (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜)) ω
      (fun q : TotalSpace ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
          (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) ↦
        (⟨q.proj, (twistEquivCanonicalBundle q.proj).symm q.snd⟩ :
          TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber)) := by
  intro q₀
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  -- Near `q₀` the fibre coordinate is a constant multiple of the value of the form on the basis.
  have hK := ((contMDiffAt_totalSpace_iff (n := ω) (IB := 𝓘(𝕜, Fin 1 → 𝕜))
    (IM := 𝓘(𝕜, Fin 1 → 𝕜).prod
      𝓘(𝕜, (Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜))).1
        (contMDiffAt_id (x := q₀))).2
  have hsrc : ∀ᶠ q : TotalSpace ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
      (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) in 𝓝 q₀,
      q.proj ∈ (chartAt (Fin 1 → 𝕜) q₀.proj).source :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((chartAt (Fin 1 → 𝕜) q₀.proj).open_source.mem_nhds (mem_chart_source _ _))
  refine ((eulerFormSign (𝕜 := 𝕜) ((twistCore (𝕜 := 𝕜) (n := 1) (-2)).indexAt q₀.proj) •
    ContinuousAlternatingMap.apply 𝕜 (Fin 1 → 𝕜) 𝕜
      projectiveLineChartBasis).contMDiff.contMDiffAt.comp q₀ hK).congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with q hq
  rw [Function.comp_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.apply_apply,
    smul_eq_mul]
  exact trivializationAt_twistEquivCanonicalBundle_symm _ hq q.snd

/-- **The canonical bundle of the projective line is `𝒪(-2)`.** The fibrewise isomorphisms
`Projectivization.twistEquivCanonicalBundle` form an analytic diffeomorphism from the total space
of `𝒪(-2)` to that of the canonical bundle of `ℙ¹`, covering the identity of `ℙ¹`. For `𝕜 = ℂ` it
is the holomorphic isomorphism `𝒪(-2) ≃ K_ℂℙ¹`. -/
def twistDiffeomorphCanonicalBundle :
    TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber ≃ₘ^ω⟮𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜),
      𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, (Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)⟯
      TotalSpace ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
        (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜))) where
  toFun p := ⟨p.proj, twistEquivCanonicalBundle p.proj p.snd⟩
  invFun q := ⟨q.proj, (twistEquivCanonicalBundle q.proj).symm q.snd⟩
  left_inv p := by simp
  right_inv q := by simp
  contMDiff_toFun := contMDiff_twistEquivCanonicalBundle
  contMDiff_invFun := contMDiff_twistEquivCanonicalBundle_symm

@[simp]
theorem twistDiffeomorphCanonicalBundle_apply
    (p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := 1) (-2)).Fiber) :
    twistDiffeomorphCanonicalBundle (𝕜 := 𝕜) p = ⟨p.proj, twistEquivCanonicalBundle p.proj p.snd⟩ :=
  (rfl)

@[simp]
theorem twistDiffeomorphCanonicalBundle_symm_apply
    (q : TotalSpace ((Fin 1 → 𝕜) [⋀^Fin (Module.finrank 𝕜 (Fin 1 → 𝕜))]→L[𝕜] 𝕜)
      (CanonicalBundle 𝓘(𝕜, Fin 1 → 𝕜) (ℙ 𝕜 (Fin 2 → 𝕜)))) :
    (twistDiffeomorphCanonicalBundle (𝕜 := 𝕜)).symm q =
      ⟨q.proj, (twistEquivCanonicalBundle q.proj).symm q.snd⟩ :=
  (rfl)

end Equiv

end Projectivization
