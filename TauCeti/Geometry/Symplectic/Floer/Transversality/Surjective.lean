/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm
public import TauCeti.Geometry.Symplectic.Floer.Transversality.WeakCokernel
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.LinearAlgebra.Submodule.Quotient
import TauCeti.Topology.Algebra.Order.Floor

/-!
# The universal linearized Floer operator on the cylinder is onto

Let `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` be the Sobolev realization of the linearized Floer
operator along a map `u` of the cylinder into a finite-dimensional symplectic vector space `V`
(`TauCeti.SymplecticForm.floerSobolevOperator`), for Floer data `(J, K_s, K_t)`. Varying the
Hamiltonian `K_s` by `δK` changes the Floer operator by `-X_{δK}(u)`. The **universal operator**
adds these variations to `D_u`, `(ξ, δK) ↦ D_u ξ - X_{δK}(u)`. This file proves that it is onto
`L²` as soon as `D_u` has closed range of finite codimension, as a Fredholm operator does, even
when `δK` is restricted to smooth compactly supported variations supported in a set `W` that is a
neighbourhood of the graph of `u` over an arbitrary nonempty open subset `U` of the open strip
`ℝ × (0, 1)`, a fundamental domain of the cylinder: every element of `L²` is `D_u ξ` plus a finite
linear combination of such variation terms, the Hamiltonian variations
`TauCeti.SymplecticForm.hamiltonianVariations`
(`TauCeti.SymplecticForm.range_floerSobolevOperator_sup_span_hamiltonianVariations_eq_top`).
Since the range of `D_u` has finite codimension, finitely many Hamiltonian variations already
suffice
(`exists_finset_subset_hamiltonianVariations_range_floerSobolevOperator_sup_span_eq_top`, in the
namespace `TauCeti.SymplecticForm`).
This is the surjectivity of the universal operator on which the Sard–Smale construction of regular
Floer data rests, for the free Hamiltonian directions of an inhomogeneous core.

The proof is the standard one (McDuff–Salamon, Proposition 3.2.1). The statements and the closing
argument follow the Morse analogue
`TauCeti.range_trajectoryOperator_sup_span_metricVariations_eq_top` in
`TauCeti.Analysis.Calculus.Morse.MorseSmale.MetricVariation`.

* **Closed range.** The range of `D_u` is closed and of finite codimension, so every subspace
  containing it is closed (`Submodule.isClosed_mono_of_finiteDimensional_quotient`).
  The sum of the range of `D_u` and the span of the variation terms is therefore all of `L²` as
  soon as its orthogonal complement is trivial.
* **The variation terms.** A variation `δK` that is `C¹`, of compact support and supported over
  `U` changes the Floer operator by `-X_{δK}(u)`
  (`TauCeti.SymplecticForm.floerOperator_add_const_mul_left_of_tsupport_subset`), and not at all
  off `U` (`TauCeti.SymplecticForm.floerOperator_add_sub_eq_zero`), so its variation term is
  continuous with compact support, and lies in every `Lᵖ` of the strip
  (`TauCeti.SymplecticForm.memLp_floerOperator_add_sub`).
* **Weak cokernel elements.** Let `h ∈ L²` be orthogonal to the range of `D_u` and to every
  variation term, and let `η = ⟪h, ·⟫` be the covector field it defines. A smooth map `ξ` with
  compact support in the open strip `ℝ × (0, 1)` periodizes to a test section of the cylinder
  (`TauCeti.CylinderSobolev.comp_fract_mem_testSection`) that agrees with `ξ` on the open strip,
  which carries the strip measure
  (`TauCeti.StripSobolev.stripMeasure_eq_restrict_univ_prod_Ioo`). So `η` annihilates
  `D_u ξ` for every such `ξ`, and every variation term supported in `W` over `U`: it is a weak
  cokernel element of the universal operator on the open strip. Such elements vanish
  (`ae_eq_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub` in the namespace
  `TauCeti.SymplecticForm`), so `h = 0`.

The closed range of finite codimension is a hypothesis. It holds whenever `D_u` is Fredholm: for
compatible Floer data cylindrical near the ends and nondegenerate asymptotic orbits by
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`, and along a
map asymptotic to nondegenerate orbits for the data `(J_t, 0, H_t)` of a Floer trajectory by
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_compatible`. In the latter case, for
`J` and `u` of class `C²`, the surjectivity is
`range_floerSobolevOperator_sup_span_hamiltonianVariations_eq_top_of_compatible`, in the namespace
`TauCeti.SymplecticForm`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 (the universal operator is onto).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev StripSobolev

section VariationTerm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}
  {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {δK : ℝ × ℝ → V → ℝ}
  {U : Set (ℝ × ℝ)}

/-- **The variation terms are square integrable.** Let `δK` be a `C¹` variation of `K_s`, of
compact support and supported over an open set `U` of the cylinder, over which `K_s` is
differentiable along the graph of `u` and `u` is continuous. Then the change
`z ↦ F(J, K_s + δK, K_t)(u)(z) - F(J, K_s, K_t)(u)(z)` of the Floer operator, which is
`-X_{δK}(u)`, is continuous with compact support, and lies in every `Lᵖ` of the strip. -/
theorem memLp_floerOperator_add_sub (hU : IsOpen U)
    (hKs : ∀ z ∈ U, DifferentiableAt ℝ (Ks z) (u z)) (hu : ContinuousOn u U)
    (hδK : ContDiff ℝ 1 (uncurry δK)) (hδKc : HasCompactSupport (uncurry δK))
    (hδKU : tsupport (uncurry δK) ⊆ U ×ˢ univ) (p : ℝ≥0∞) :
    MemLp (fun z ↦ ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
      ω.floerOperator J Ks Kt u z) p stripMeasure := by
  set f := fun z ↦ ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
    ω.floerOperator J Ks Kt u z
  -- The variation is supported over the compact set `C ⊆ U` of the domain.
  set C := Prod.fst '' tsupport (uncurry δK)
  have hC : IsCompact C := hδKc.isCompact.image continuous_fst
  have hCU : C ⊆ U := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hδKU hw).1
  have hoff (z : ℝ × ℝ) (hz : z ∉ C) : f z = 0 :=
    ω.floerOperator_add_sub_eq_zero J Ks Kt δK u fun y ↦
      image_eq_zero_of_notMem_tsupport (f := uncurry δK) fun h ↦ hz ⟨(z, y), h, rfl⟩
  -- The variation term is `-X_{δK}(u)`.
  have hon (z : ℝ × ℝ) : f z = -ω.hamiltonianVectorField (δK z) (u z) := by
    have h := ω.floerOperator_add_const_mul_left_of_tsupport_subset J Ks Kt u hKs hδK hδKU z 1
    simp only [one_mul, one_smul] at h
    simp only [f, h, sub_sub_cancel_left]
  have hX : Continuous fun w : (ℝ × ℝ) × V ↦ ω.hamiltonianVectorField (δK w.1) w.2 :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hδK)).continuous
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun z ↦ by
    by_cases hz : z ∈ U
    · exact ((hX.comp_continuousOn (continuousOn_id.prodMk hu)).neg.congr
        fun z _ ↦ hon z).continuousAt
        (hU.mem_nhds hz)
    · exact continuousAt_const.congr (Filter.eventually_of_mem
        ((isOpen_compl_iff.2 hC.isClosed).mem_nhds fun h ↦ hz (hCU h)) fun w hw ↦ (hoff w hw).symm)
  exact hcont.memLp_of_hasCompactSupport (HasCompactSupport.intro hC hoff)

variable (ω J Ks Kt u) in
/-- The **Hamiltonian variations** of the Floer operator in `W ⊆ (ℝ × ℝ) × V`: the classes in
`L²(ℝ × S¹, V)` of the changes `F(J, K_s + δK, K_t)(u) - F(J, K_s, K_t)(u)` of the Floer operator,
for smooth variations `δK` of `K_s` of compact support, supported in `W`. Where `K_s` is
differentiable along `u`, the change is `-X_{δK}(u)`, the direction in which varying `K_s` moves
the Floer equation at `u`. -/
def hamiltonianVariations (W : Set ((ℝ × ℝ) × V)) : Set (Lp V 2 stripMeasure) :=
  {g | ∃ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) ∧ HasCompactSupport (uncurry δK) ∧
    tsupport (uncurry δK) ⊆ W ∧
    g =ᵐ[stripMeasure] fun z ↦ ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
      ω.floerOperator J Ks Kt u z}

/-- Membership in the Hamiltonian variations. -/
theorem mem_hamiltonianVariations {W : Set ((ℝ × ℝ) × V)} {g : Lp V 2 stripMeasure} :
    g ∈ ω.hamiltonianVariations J Ks Kt u W ↔ ∃ δK : ℝ × ℝ → V → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) ∧ HasCompactSupport (uncurry δK) ∧
        tsupport (uncurry δK) ⊆ W ∧
        g =ᵐ[stripMeasure] fun z ↦ ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
          ω.floerOperator J Ks Kt u z :=
  Iff.rfl

/-- Hamiltonian variations supported in a smaller set are Hamiltonian variations supported in a
larger one. -/
theorem hamiltonianVariations_mono {W W' : Set ((ℝ × ℝ) × V)} (h : W ⊆ W') :
    ω.hamiltonianVariations J Ks Kt u W ⊆ ω.hamiltonianVariations J Ks Kt u W' :=
  fun _ ⟨δK, h₁, h₂, h₃, h₄⟩ ↦ ⟨δK, h₁, h₂, h₃.trans h, h₄⟩

end VariationTerm

/-- Integrals over the strip are integrals over the open strip `ℝ × (0, 1)`. -/
private theorem integral_stripMeasure (f : ℝ × ℝ → ℝ) :
    ∫ z, f z ∂stripMeasure = ∫ z in univ ×ˢ Ioo (0 : ℝ) 1, f z := by
  rw [stripMeasure_eq_restrict_univ_prod_Ioo]

section Surjective

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}
  {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)}
  {W : Set ((ℝ × ℝ) × V)}

/-- **Cokernel elements are weak cokernel elements on the open strip.** An element `h` of
`L²(ℝ × S¹, V)` orthogonal to the range of the Sobolev realization of `D_u` annihilates `D_u ξ`,
`∫ ⟪h, D_u ξ⟫ = 0`, for every `C²` map `ξ` with compact support in the open strip `ℝ × (0, 1)`. -/
private theorem integral_inner_floerLinearization_eq_zero
    (hM : MemLp (ω.floerJetCoeff J Ks Kt u) ∞ stripMeasure) {h : Lp V 2 stripMeasure}
    (hh : ∀ x, ⟪h, ω.floerSobolevOperator J Ks Kt u x⟫_ℝ = 0) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ univ ×ˢ Ioo (0 : ℝ) 1) :
    ∫ z, ⟪h z, ω.floerLinearization J Ks Kt u ξ z⟫_ℝ = 0 := by
  set ξp : testSection V := ⟨_, comp_fract_mem_testSection hξ hξc hξS⟩
  have h0 := hh ⟨jetLp 2 (testSection V) ξp, jetLp_mem_jetClosure ξp⟩
  rw [MeasureTheory.L2.inner_def] at h0
  have hΩ : ∀ᵐ z ∂stripMeasure, z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
    rw [stripMeasure_eq_restrict_univ_prod_Ioo]
    exact ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioo)
  -- On the open strip the periodization agrees with `ξ` near every point.
  rw [integral_congr_ae (g := fun z ↦ ⟪h z, ω.floerLinearization J Ks Kt u ξ z⟫_ℝ)
    (by
      filter_upwards [floerSobolevOperator_jetLp_ae_eq ω hM ξp, hΩ] with z hz hzΩ
      rw [hz, ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u
        (apply_fract_snd_eventuallyEq_self hzΩ.2)]),
    integral_stripMeasure] at h0
  -- Off the open strip `D_u ξ` vanishes.
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
    rw [ω.floerLinearization_of_notMem_tsupport J Ks Kt u fun h ↦ hz (hξS h), inner_zero_right]]
    at h0

/-- **Orthogonality to the Hamiltonian variations.** An element `h` of `L²(ℝ × S¹, V)` orthogonal to
every Hamiltonian variation in `W` annihilates the change of the Floer operator under each such
variation `δK` supported over an open subset `U` of the open strip `ℝ × (0, 1)`, integrated over
the plane. -/
private theorem integral_inner_floerOperator_add_sub_eq_zero (hU : IsOpen U)
    (hUΩ : U ⊆ univ ×ˢ Ioo (0 : ℝ) 1)
    (hKs : ∀ z ∈ U, DifferentiableAt ℝ (Ks z) (u z)) (hu : ContinuousOn u U)
    {h : Lp V 2 stripMeasure} (hh : ∀ g ∈ ω.hamiltonianVariations J Ks Kt u W, ⟪h, g⟫_ℝ = 0)
    {δK : ℝ × ℝ → V → ℝ} (h₁ : ContDiff ℝ (⊤ : ℕ∞) (uncurry δK))
    (h₂ : HasCompactSupport (uncurry δK)) (h₃ : tsupport (uncurry δK) ⊆ W ∩ U ×ˢ univ) :
    ∫ z, ⟪h z, ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
      ω.floerOperator J Ks Kt u z⟫_ℝ = 0 := by
  have hmem := memLp_floerOperator_add_sub (ω := ω) (J := J) (Ks := Ks) (Kt := Kt) (δK := δK) hU
    hKs hu (h₁.of_le (WithTop.coe_le_coe.2 le_top)) h₂ (h₃.trans inter_subset_right) 2
  have h0 := hh _ (mem_hamiltonianVariations.2
    ⟨δK, h₁, h₂, h₃.trans inter_subset_left, hmem.coeFn_toLp⟩)
  -- Off `U`, hence off the open strip, the variation does not change the Floer operator.
  rwa [MeasureTheory.L2.inner_def, integral_congr_ae (hmem.coeFn_toLp.mono fun z hz ↦ by
    rw [hz]), integral_stripMeasure, setIntegral_eq_integral_of_forall_compl_eq_zero
    fun z hz ↦ by
      beta_reduce
      rw [ω.floerOperator_add_sub_eq_zero J Ks Kt δK u fun y ↦ image_eq_zero_of_notMem_tsupport
        (f := uncurry δK) (x := (z, y)) fun hy ↦ hz (hUΩ (h₃ hy).2.1), inner_zero_right]] at h0

/-- **The universal linearized Floer operator on the cylinder is onto.** Let `V` be a
finite-dimensional real inner product space with a symplectic form `ω`, and let the Floer data
`(J, K_s, K_t)` and the map `u` be regular over the open strip `ℝ × (0, 1)`: `J` is `C²` and the
Hamiltonians `K_s`, `K_t` are `C³` near the graph of `u`, `u` is `C²`, and `J(z, u z)² = -1`.
Suppose that the coefficients of the linearized operator are essentially bounded on the cylinder
and that its Sobolev realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` has closed range of
finite codimension, as a Fredholm operator does. Let `U` be a nonempty open subset of the open
strip, and `W` a neighbourhood of the graph of `u` over `U`. Then every element of `L²` is `D_u ξ`
plus a finite linear combination of Hamiltonian variations in `W`
(`TauCeti.SymplecticForm.hamiltonianVariations`), the variation terms
`F(J, K_s + δK, K_t)(u) - F(J, K_s, K_t)(u)` for smooth variations `δK` of `K_s` of compact
support supported in `W`. -/
theorem range_floerSobolevOperator_sup_span_hamiltonianVariations_eq_top
    (hJ : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 2 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 3 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerJetCoeff J Ks Kt u) ∞ stripMeasure)
    (hDc : IsClosed ((ω.floerSobolevOperator J Ks Kt u).range : Set (Lp V 2 stripMeasure)))
    (hDf : (ω.floerSobolevOperator J Ks Kt u).range.CoFG) (hU : IsOpen U) (hUne : U.Nonempty)
    (hUΩ : U ⊆ univ ×ˢ Ioo (0 : ℝ) 1) (hW : ∀ z ∈ U, W ∈ 𝓝 (z, u z)) :
    (ω.floerSobolevOperator J Ks Kt u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariations J Ks Kt u W) = ⊤ := by
  set Ω : Set (ℝ × ℝ) := univ ×ˢ Ioo (0 : ℝ) 1
  set D := ω.floerSobolevOperator J Ks Kt u
  set T := ω.hamiltonianVariations J Ks Kt u W
  -- The sum contains the closed range of `D_u`, of finite codimension, so it is closed, and it is
  -- everything once its orthogonal complement is trivial.
  have hSc : IsClosed ((D.range ⊔ Submodule.span ℝ T : Submodule ℝ _) :
      Set (Lp V 2 stripMeasure)) := by
    have : FiniteDimensional ℝ (Lp V 2 stripMeasure ⧸ D.range) := hDf
    exact Submodule.isClosed_mono_of_finiteDimensional_quotient hDc le_sup_left
  rw [← hSc.submodule_topologicalClosure_eq, ← Submodule.orthogonal_orthogonal_eq_closure,
    Submodule.orthogonal_eq_top_iff, Submodule.eq_bot_iff]
  intro h hh
  -- The covector field `η = ⟪h, ·⟫` is a weak cokernel element of the universal operator.
  set η : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ innerSL ℝ (h z)
  have hΩo : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have hη : MemLpLoc 2 Ω η := MemLp.memLpLoc (by
    rw [← stripMeasure_eq_restrict_univ_prod_Ioo]
    exact (innerSL ℝ).comp_memLp' (Lp.memLp h))
  have hDη (ξ : ℝ × ℝ → V) (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξc : HasCompactSupport ξ)
      (hξΩ : tsupport ξ ⊆ Ω) : ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0 := by
    simpa only [η, innerSL_apply_apply] using integral_inner_floerLinearization_eq_zero hM
      (fun x ↦ Submodule.inner_left_of_mem_orthogonal
        (Submodule.mem_sup_left (LinearMap.mem_range.2 ⟨x, rfl⟩)) hh)
      (hξ.of_le (WithTop.coe_le_coe.2 le_top)) hξc hξΩ
  have hKη (δK : ℝ × ℝ → V → ℝ) (h₁ : ContDiff ℝ (⊤ : ℕ∞) (uncurry δK))
      (h₂ : HasCompactSupport (uncurry δK)) (h₃ : tsupport (uncurry δK) ⊆ W ∩ U ×ˢ univ) :
      ∫ z, η z (ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
        ω.floerOperator J Ks Kt u z) = 0 := by
    simpa only [η, innerSL_apply_apply] using integral_inner_floerOperator_add_sub_eq_zero
      (ω := ω) (J := J) (Ks := Ks) (Kt := Kt) hU hUΩ
      (fun z hz ↦ ((hKs z (hUΩ hz)).differentiableAt (by norm_num)).comp (u z)
        ((differentiableAt_const z).prodMk differentiableAt_id))
      (fun z hz ↦ (hu z (hUΩ hz)).continuousAt.continuousWithinAt)
      (fun g hg ↦ Submodule.inner_left_of_mem_orthogonal
        (Submodule.mem_sup_right (Submodule.subset_span hg)) hh) h₁ h₂ h₃
  have h0 := ae_eq_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub hΩo
    (isPreconnected_univ.prod isPreconnected_Ioo) hJ hJJ hKs hKt hu ENNReal.one_lt_two hη hDη hU
    hUne hUΩ (fun z hz ↦ inter_mem (hW z hz) ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩))
    hKη
  -- So `h` vanishes almost everywhere on the open strip, which carries the strip measure.
  have hae : ∀ᵐ z ∂stripMeasure, η z = 0 := by
    rw [stripMeasure_eq_restrict_univ_prod_Ioo]
    exact h0
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae] with z hz
  rw [Pi.zero_apply, ← norm_eq_zero, ← innerSL_apply_norm ℝ]
  exact (congrArg norm hz).trans norm_zero

/-- **Finitely many Hamiltonian variations make the linearized Floer operator onto.** Under the
hypotheses of
`TauCeti.SymplecticForm.range_floerSobolevOperator_sup_span_hamiltonianVariations_eq_top`,
finitely many Hamiltonian variations in `W` already span `L²(ℝ × S¹, V)` together with the range
of the Sobolev realization `D_u`, which has finite codimension. -/
theorem exists_finset_subset_hamiltonianVariations_range_floerSobolevOperator_sup_span_eq_top
    (hJ : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 2 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 3 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ univ ×ˢ Ioo (0 : ℝ) 1, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerJetCoeff J Ks Kt u) ∞ stripMeasure)
    (hDc : IsClosed ((ω.floerSobolevOperator J Ks Kt u).range : Set (Lp V 2 stripMeasure)))
    (hDf : (ω.floerSobolevOperator J Ks Kt u).range.CoFG) (hU : IsOpen U) (hUne : U.Nonempty)
    (hUΩ : U ⊆ univ ×ˢ Ioo (0 : ℝ) 1) (hW : ∀ z ∈ U, W ∈ 𝓝 (z, u z)) :
    ∃ t : Finset (Lp V 2 stripMeasure), (t : Set _) ⊆ ω.hamiltonianVariations J Ks Kt u W ∧
      (ω.floerSobolevOperator J Ks Kt u).range ⊔ Submodule.span ℝ t = ⊤ :=
  have := hDf
  Submodule.exists_finset_subset_sup_span_eq_top
    (range_floerSobolevOperator_sup_span_hamiltonianVariations_eq_top hJ hJJ hKs hKt hu hM hDc hDf
      hU hUne hUΩ hW)

end Surjective

section Compatible

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {U : Set (ℝ × ℝ)}

/-- **The universal linearized Floer operator along a Floer trajectory is onto.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let
`J_t(y)` be a `C²` family of `ω`-compatible almost complex structures, and let `H` be a
one-periodic, jointly `C³` time-dependent Hamiltonian whose suspended vector field is globally
Lipschitz, with one-periodic orbits `x₋` and `x₊` whose initial points are nondegenerate fixed
points of the time-one map. Let `u` be a `C²` map whose loops converge uniformly to `x₋` at `-∞`
and to `x₊` at `+∞`, with slice defect `∂t u - X_{H_t}(u)` tending uniformly to zero at both
ends. For the Floer data `(J_t, 0, H_t)`, a nonempty open subset `U` of the open strip
`ℝ × (0, 1)` and a neighbourhood `W` of the graph of `u` over `U`, every element of
`L²(ℝ × S¹, F)` is `D_u ξ` plus a finite linear combination of the variation terms of smooth
variations `δK` of `K_s = 0`, of compact support and supported in `W`. -/
theorem range_floerSobolevOperator_sup_span_hamiltonianVariations_eq_top_of_compatible
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    {J : ℝ → F → AlmostComplexStructure F}
    (hJ : ContDiff ℝ 2 fun p : ℝ × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJc : ∀ t y, ω.Compatible (J t y)) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {u : ℝ × ℝ → F} (hu : ContDiff ℝ 2 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ univ ×ˢ Ioo (0 : ℝ) 1)
    {W : Set ((ℝ × ℝ) × F)} (hW : ∀ z ∈ U, W ∈ 𝓝 (z, u z)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariations
        (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2) u
        W) = ⊤ := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hJ₁ : ContDiff ℝ 1 fun p : ℝ × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap :=
    hJ.of_le (by norm_num)
  have hg : ContDiff ℝ ⊤ fun p : (ℝ × ℝ) × F ↦ (p.1.2, p.2) := contDiff_fst.snd.prodMk contDiff_snd
  -- The realization of the linearized operator is Fredholm.
  have hD := ω.isFredholm_floerSobolevOperator_of_compatible hω hJ₁ hJc hX hH hHper hxm hxmper hndm
    hxp hxpper hndp (hu.of_le (by norm_num)) huxm hδm huxp hδp
  exact range_floerSobolevOperator_sup_span_hamiltonianVariations_eq_top
    (fun _ _ ↦ (hJ.comp (hg.of_le le_top)).contDiffAt) (fun _ _ ↦ by ext v; simp)
    (fun _ _ ↦ contDiffAt_const) (fun _ _ ↦ (hH.comp (hg.of_le le_top)).contDiffAt)
    (fun _ _ ↦ hu.contDiffAt)
    (ω.memLp_floerJetCoeff (hH.of_le (by norm_num)) hJ₁ (hu.of_le (by norm_num)) huxm huxp hδm
      hδp)
    hD.isClosed_range hD.finite_coker hU hUne hUΩ hW

end Compatible

end TauCeti.SymplecticForm
