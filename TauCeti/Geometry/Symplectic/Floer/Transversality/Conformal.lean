/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Transversality.WeakCokernel
import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# Variations of the data and the cokernel of the linearized Floer operator on `W^{1,2}`

Let `U ⊆ ℝ × ℝ` be a connected open set with a conformal weight `ρ`, such as the pair of pants
`ℂ ∖ {0, 1}` with its cylindrical weight, and let `D_u : W^{1,2}_0(U, V) → L²(U, V)` be the
realization `TauCeti.SymplecticForm.floerConformalSobolevOperator` of the linearized Floer operator
along a map `u`, for Floer data `(J, K_s, K_t)` on `U`. The universal linearized operator adds to
`D_u` the directions in which the Floer operator moves when the perturbation `K_s` varies. A
smooth compactly supported variation `δK` moves it by `-X_{δK}(u)`, the Hamiltonian vector field of
`δK` along `u` (`TauCeti.SymplecticForm.floerOperator_add_const_mul_left`). This file proves that
these directions, for variations supported near the graph of `u` over any nonempty open subset of
`U`, detect the whole cokernel of `D_u`: on an inhomogeneous core of a punctured domain, where the
Hamiltonian perturbation is free, the universal operator has dense range, and it is onto as soon as
`D_u` is Fredholm.

* `TauCeti.SymplecticForm.hamiltonianVariationsOn ω U u W` is the set of `L²` classes on `U` of the
  fields `-X_{δK}(u)` for smooth `δK` with compact support in `W ⊆ (ℝ × ℝ) × V`. Every such field is
  in `Lᵖ` on `U` when `u` is continuous on `U`
  (`TauCeti.SymplecticForm.memLp_hamiltonianVectorField_comp`), so each variation `δK` has its
  class in the set (`TauCeti.SymplecticForm.toLp_mem_hamiltonianVariationsOn`).
* **Cokernel detection.** An element `h ∈ L²(U, V)` orthogonal to the range of `D_u` and to these
  variations, for `W` a neighbourhood of the graph of `u` over a nonempty open set `O ⊆ U`, is zero
  (`TauCeti.SymplecticForm.eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator`). The
  covector field `η = ⟪h, ·⟫` on `U` is a weak cokernel element of the universal operator: by
  Green's formula on the jets of test sections it annihilates `D_u ξ` for every test section `ξ`
  (`TauCeti.SymplecticForm.setIntegral_inner_floerLinearization_eq_zero_of_mem_orthogonal_range`),
  and it annihilates the change `F(K_s + δK) - F(K_s) = -X_{δK}(u)` of the Floer operator. Weak
  cokernel elements of the universal operator vanish
  (`ae_eq_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub`, in the namespace
  `TauCeti.SymplecticForm`): they are regular, they vanish on `O` because the variations realize
  every field there, and
  unique continuation spreads the vanishing over the connected set `U`. No hypothesis is placed
  on `u` over `O`: in particular `u` may be constant there.
* **Regularity.** When the data are regular enough along `u`, an element of `L²(U, V)` orthogonal
  to the range of `D_u` is represented on `U` by a `C²` covector field annihilated by the formal
  adjoint `D_u^*`
  (`exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero`, in the namespace
  `TauCeti.SymplecticForm`).
* **Density.** Equivalently, the range of `D_u` and the span of the variations are dense in
  `L²(U, V)`
  (`topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top`,
  in the namespace `TauCeti.SymplecticForm`).
* **Surjectivity.** When the range of `D_u` is closed and of finite codimension, for instance when
  `D_u` is Fredholm, the sum is closed, so the range of `D_u` and the
  variations span `L²(U, V)`
  (`range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top`), and finitely many
  variations suffice (`exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`, both in
  the namespace `TauCeti.SymplecticForm`). This is the surjectivity of the total linearization of
  a finite-dimensional family of perturbations `K_s + ∑ cᵢ δKᵢ`, the input of the Sard–Smale
  argument for regular moduli spaces.

On a sphere component of a Floer configuration the almost complex structure is frozen, a target
structure `J(x)` independent of the domain point, and there are no free Hamiltonian directions:
transversality uses variations `Y` of `J` alone. Along the line `J + τ Y` the Floer operator moves
by `Y(u)(∂ₜu - X_{K_t}(u))` (`TauCeti.SymplecticForm.hasDerivAt_floerOperator_add_smul`). The same
statements hold for these directions, at injective points of `u`.

* `TauCeti.SymplecticForm.almostComplexVariationsOn ω U u J Kt n W` is the set of `L²` classes on
  `U` of the fields `Y(u)(∂ₜu - X_{K_t}(u))` for compactly supported `Cⁿ` fields `Y` with support in
  `W ⊆ V` and `Y x` in the compatible tangent space of `J x`. Such a field is in `L²` on `U` when
  the preimage of the support of `Y` under `u` lies in a compact subset of `U`
  (`TauCeti.SymplecticForm.memLp_almostComplexVariation_of_preimage_subset`), and then its class is
  in the set (`TauCeti.SymplecticForm.toLp_mem_almostComplexVariationsOn`).
* **Cokernel detection.** Let `O ⊆ U` be a nonempty open set of injective points of `u` at which
  `J` is tamed by `ω` and `∂ₜu - X_{K_t}` does not vanish, and `W` a neighbourhood of `u(O)`. An
  element of `L²(U, V)` orthogonal to the range of `D_u` and to the almost complex variations
  supported in `W` is zero
  (`eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator_of_almostComplex`, in the
  namespace `TauCeti.SymplecticForm`). This is the weak vanishing theorem for frozen structures
  (`ae_eq_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator`), applied to the
  variations supported near a single injective point `z₀ ∈ O`: there a neighbourhood of `u z₀` has
  preimage under `u` inside a compact neighbourhood of `z₀` in `O`, so these variations are
  compactly supported along `u` and lie in `L²(U, V)` with no integrability hypothesis on
  `∂ₜu - X_{K_t}`.
* **Density and surjectivity.** The range of `D_u` and the span of these variations are dense in
  `L²(U, V)`, by
`topologicalClosure_range_floerConformalSobolevOperator_sup_span_almostComplexVariationsOn_eq_top`;
  they span it when the range of `D_u` is closed and of finite codimension
  (`range_floerConformalSobolevOperator_sup_span_almostComplexVariationsOn_eq_top`), and then
  finitely many variations suffice
  (`exists_finset_subset_almostComplexVariationsOn_range_sup_span_eq_top`), all in the namespace
  `TauCeti.SymplecticForm`.

That the injective points of a simple curve form a dense open set is not proved here: the set `O`
is a hypothesis.

The target is a finite-dimensional real inner product space `V` with a symplectic form `ω`; the
inner product identifies `L²(U, V)` with its dual, and need not be related to `ω`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1, Lemma 3.2.2 and Section 8.1, on the
  surjectivity of the universal linearized operator, on variations of the almost complex structure
  at injective points and on Hamiltonian perturbations.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

noncomputable section

open MeasureTheory Set Function Filter Topology TauCeti.ConformalSobolev
open scoped ENNReal InnerProductSpace

namespace TauCeti.SymplecticForm

section Variations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations along a map are in `Lᵖ`.** For a `C¹` family `δK` of Hamiltonians
with compact support in `(ℝ × ℝ) × V`, and a map `u` continuous on a measurable set `U`, the field
`z ↦ X_{δK z}(u z)` along `u` is in `Lᵖ` on `U` for every `p`: it is continuous on `U`, bounded,
and vanishes outside the compact projection of the support of `δK`. -/
theorem memLp_hamiltonianVectorField_comp (ω : SymplecticForm V) {δK : ℝ × ℝ → V → ℝ}
    (hδK : ContDiff ℝ 1 (uncurry δK)) (hc : HasCompactSupport (uncurry δK))
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {u : ℝ × ℝ → V} (hu : ContinuousOn u U)
    (p : ℝ≥0∞) :
    MemLp (fun z ↦ ω.hamiltonianVectorField (δK z) (u z)) p (volume.restrict U) := by
  set X := uncurry fun z ↦ ω.hamiltonianVectorField (δK z)
  have hX : Continuous X := ω.continuous_uncurry_hamiltonianVectorField hδK
  obtain ⟨C, hC⟩ := hX.bounded_above_of_compact_support (hc.mono' fun w hw ↦ by
    by_contra h
    exact hw (ω.hamiltonianVectorField_eq_zero_of_notMem_tsupport_uncurry h))
  -- The field is bounded, and vanishes outside the compact projection of the support of `δK`.
  have hP : IsCompact (Prod.fst '' tsupport (uncurry δK)) := hc.isCompact.image continuous_fst
  have hmeas : AEStronglyMeasurable (fun z ↦ X (z, u z)) (volume.restrict U) :=
    (hX.comp_continuousOn (continuousOn_id.prodMk hu)).aestronglyMeasurable hU
  refine MemLp.mono_exponent_of_measure_support_ne_top
    (memLp_top_of_bound hmeas C (ae_of_all _ fun z ↦ hC (z, u z)))
    (s := Prod.fst '' tsupport (uncurry δK))
    (fun z hz ↦ ω.hamiltonianVectorField_eq_zero_of_notMem_tsupport_uncurry fun hzy ↦
      hz ⟨(z, u z), hzy, rfl⟩)
    (ne_top_of_le_ne_top hP.measure_lt_top.ne (Measure.restrict_apply_le _ _)) le_top

variable (ω : SymplecticForm V) (U : Set (ℝ × ℝ)) (u : ℝ × ℝ → V) (W : Set ((ℝ × ℝ) × V))

/-- The **Hamiltonian variations** of the Floer operator along `u` on `U`, for perturbations
supported in `W ⊆ (ℝ × ℝ) × V`: the `L²` classes on `U` of the fields `-X_{δK}(u)` for smooth
families `δK` of Hamiltonians with compact support in `W`. The field `-X_{δK}(u)` is the change
of the Floer operator when `δK` is added to the `ds` component of the perturbation
(`TauCeti.SymplecticForm.floerOperator_add_const_mul_left`). -/
def hamiltonianVariationsOn : Set (Lp V 2 (volume.restrict U)) :=
  {g | ∃ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) ∧
    HasCompactSupport (uncurry δK) ∧ tsupport (uncurry δK) ⊆ W ∧
      (g : ℝ × ℝ → V) =ᵐ[volume.restrict U] fun z ↦ -ω.hamiltonianVectorField (δK z) (u z)}

variable {ω U u W}

/-- Membership in the Hamiltonian variations. -/
theorem mem_hamiltonianVariationsOn_iff {g : Lp V 2 (volume.restrict U)} :
    g ∈ ω.hamiltonianVariationsOn U u W ↔ ∃ δK : ℝ × ℝ → V → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) ∧ HasCompactSupport (uncurry δK) ∧
        tsupport (uncurry δK) ⊆ W ∧
          (g : ℝ × ℝ → V) =ᵐ[volume.restrict U] fun z ↦ -ω.hamiltonianVectorField (δK z) (u z) :=
  Iff.rfl

/-- The Hamiltonian variations grow with the set `W` in which the variations are supported. -/
theorem hamiltonianVariationsOn_mono {W' : Set ((ℝ × ℝ) × V)} (hW : W ⊆ W') :
    ω.hamiltonianVariationsOn U u W ⊆ ω.hamiltonianVariationsOn U u W' :=
  fun _ ⟨δK, hδK, hc, hs, hg⟩ ↦ ⟨δK, hδK, hc, hs.trans hW, hg⟩

/-- **Every variation gives a Hamiltonian variation.** For a smooth family `δK` with compact
support in `W`, the `L²` class of `-X_{δK}(u)` on `U` is a Hamiltonian variation. The field is in
`L²` on `U` when `u` is continuous on `U`
(`TauCeti.SymplecticForm.memLp_hamiltonianVectorField_comp`). -/
theorem toLp_mem_hamiltonianVariationsOn {δK : ℝ × ℝ → V → ℝ}
    (hδK : ContDiff ℝ (⊤ : ℕ∞) (uncurry δK)) (hc : HasCompactSupport (uncurry δK))
    (hW : tsupport (uncurry δK) ⊆ W)
    (hX : MemLp (fun z ↦ -ω.hamiltonianVectorField (δK z) (u z)) 2 (volume.restrict U)) :
    hX.toLp _ ∈ ω.hamiltonianVariationsOn U u W :=
  ⟨δK, hδK, hc, hW, hX.coeFn_toLp⟩

end Variations

section AlmostComplexVariations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The **almost complex variations** of the Floer operator along `u` on `U`, for a frozen almost
complex structure `J`, a time component `K_t` of the perturbation, and variations of class `Cⁿ`
supported in `W ⊆ V`: the `L²` classes on `U` of the fields `Y(u)(∂ₜu - X_{K_t}(u))` for compactly
supported `Cⁿ` fields `Y` of endomorphisms with support in `W` and `Y x` in the compatible tangent
space of `J x`. The field `Y(u)(∂ₜu - X_{K_t}(u))` is the derivative of the Floer operator along
the line of structures `J + τ Y` (`TauCeti.SymplecticForm.hasDerivAt_floerOperator_add_smul`). -/
def almostComplexVariationsOn (ω : SymplecticForm V) (U : Set (ℝ × ℝ)) (u : ℝ × ℝ → V)
    (J : V → AlmostComplexStructure V) (Kt : ℝ × ℝ → V → ℝ) (n : ℕ∞) (W : Set V) :
    Set (Lp V 2 (volume.restrict U)) :=
  {g | ∃ Y : V → V →L[ℝ] V, ContDiff ℝ n Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
    (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) ∧
      (g : ℝ × ℝ → V) =ᵐ[volume.restrict U]
        fun z ↦ Y (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))}

variable {ω : SymplecticForm V} {U : Set (ℝ × ℝ)} {u : ℝ × ℝ → V}
  {J : V → AlmostComplexStructure V} {Kt : ℝ × ℝ → V → ℝ} {n : ℕ∞} {W : Set V}

/-- Membership in the almost complex variations. -/
theorem mem_almostComplexVariationsOn_iff {g : Lp V 2 (volume.restrict U)} :
    g ∈ ω.almostComplexVariationsOn U u J Kt n W ↔ ∃ Y : V → V →L[ℝ] V,
      ContDiff ℝ n Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
        (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) ∧
          (g : ℝ × ℝ → V) =ᵐ[volume.restrict U] fun z ↦
            Y (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) :=
  Iff.rfl

/-- The almost complex variations grow with the set `W` in which the variations are supported. -/
theorem almostComplexVariationsOn_mono {W' : Set V} (hW : W ⊆ W') :
    ω.almostComplexVariationsOn U u J Kt n W ⊆ ω.almostComplexVariationsOn U u J Kt n W' :=
  fun _ ⟨Y, hY, hc, hs, hm, hg⟩ ↦ ⟨Y, hY, hc, hs.trans hW, hm, hg⟩

/-- **Every variation gives an almost complex variation.** For a compactly supported `Cⁿ` field
`Y` of compatible variations of `J` with support in `W`, the `L²` class of `Y(u)(∂ₜu - X_{K_t}(u))`
on `U`, when this field is in `L²` on `U`, is an almost complex variation. The field is in `L²`
on `U` when the preimage of the support of `Y` under `u` lies in a compact subset of `U`
(`TauCeti.SymplecticForm.memLp_almostComplexVariation_of_preimage_subset`). -/
theorem toLp_mem_almostComplexVariationsOn {Y : V → V →L[ℝ] V} (hY : ContDiff ℝ n Y)
    (hc : HasCompactSupport Y) (hW : tsupport Y ⊆ W)
    (hm : ∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x))
    (hX : MemLp (fun z ↦ Y (u z)
      (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))) 2
        (volume.restrict U)) :
    hX.toLp _ ∈ ω.almostComplexVariationsOn U u J Kt n W :=
  ⟨Y, hY, hc, hW, hm, hX.coeFn_toLp⟩

/-- A variation `Y(u)(∂ₜu - X_{K_t}(u))` is in `L²` on an open set `U` on which `u` is `C¹` and
`K_t` is `C²` along the graph of `u`, when the continuous field `Y` is supported in a set whose
preimage under `u` lies in a compact subset `N` of `U`: the field is continuous on `U` and vanishes
on `U` off `N`. -/
theorem memLp_almostComplexVariation_of_preimage_subset (hU : IsOpen U)
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z)
    {Y : V → V →L[ℝ] V} (hY : Continuous Y) {N : Set (ℝ × ℝ)} (hN : IsCompact N) (hNU : N ⊆ U)
    (hYN : u ⁻¹' tsupport Y ⊆ N) :
    MemLp (fun z ↦ Y (u z)
      (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))) 2
        (volume.restrict U) := by
  set f : ℝ × ℝ → V := fun z ↦ Y (u z)
    (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))
  have hf : ContinuousOn f U := fun z hz ↦ by
    have hX := (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKt z hz)).continuousAt.comp
      (x := z) (continuousAt_id.prodMk (hu z hz).continuousAt)
    exact ((hY.continuousAt.comp (hu z hz).continuousAt).clm_apply
      ((((hu z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).sub
        hX)).continuousWithinAt
  -- Off `N` the point `u z` lies outside the support of `Y`.
  have h0 (z : ℝ × ℝ) (hz : z ∉ N) : f z = 0 := by
    simp only [f, image_eq_zero_of_notMem_tsupport fun h ↦ hz (hYN h), zero_apply]
  obtain ⟨C, hC⟩ := hN.exists_bound_of_continuousOn (hf.mono hNU)
  refine MemLp.mono_exponent_of_measure_support_ne_top
    (memLp_top_of_bound (hf.aestronglyMeasurable hU.measurableSet) (max C 0)
      (ae_of_all _ fun z ↦ ?_)) (s := N) h0
    (ne_top_of_le_ne_top hN.measure_lt_top.ne (Measure.restrict_apply_le _ _)) le_top
  by_cases hz : z ∈ N
  · exact (hC z hz).trans (le_max_left _ _)
  · rw [h0 z hz, norm_zero]
    exact le_max_right _ _

end AlmostComplexVariations

section Cokernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {U : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
  {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- The covector field `⟪h, ·⟫` on `U` of an element `h` of `L²(U, V)`, extended by zero. -/
private abbrev innerField (U : Set (ℝ × ℝ)) (h : Lp V 2 (volume.restrict U)) :
    ℝ × ℝ → V →L[ℝ] ℝ :=
  U.indicator fun z ↦ innerSL ℝ (h z)

omit [FiniteDimensional ℝ V] in
/-- Integrating a field `X` against `⟪h, ·⟫` is integrating `⟪h, X⟫` over `U`. -/
private theorem integral_innerField_apply (hU : MeasurableSet U) (h : Lp V 2 (volume.restrict U))
    (X : ℝ × ℝ → V) : ∫ z, innerField U h z (X z) = ∫ z in U, ⟪h z, X z⟫_ℝ := by
  rw [← integral_indicator hU]
  congr 1 with z
  by_cases hz : z ∈ U <;> simp [hz]

omit [FiniteDimensional ℝ V] in
/-- The covector field `⟪h, ·⟫` of `h ∈ L²(U, V)` is locally `L²` on `U`. -/
private theorem memLpLoc_innerField (hU : MeasurableSet U) (h : Lp V 2 (volume.restrict U)) :
    MemLpLoc 2 U (innerField U h) :=
  ((Lp.memLp h).memLpLoc.clm_comp (innerSL ℝ)).congr_ae
    (indicator_ae_eq_restrict hU.nullMeasurableSet).symm

/-- **Elements orthogonal to the range are weak cokernel elements.** When the coefficient field of
the linearized operator on conformal jets is essentially bounded on `U`, an element `h ∈ L²(U, V)`
orthogonal to the range of the realization `D_u : W^{1,2}_0(U, V) → L²(U, V)` annihilates `D_u ξ`
for every test section `ξ` on `U`: `∫_U ⟪h, D_u ξ⟫ = 0`. -/
theorem setIntegral_inner_floerLinearization_eq_zero_of_mem_orthogonal_range
    (hρ : IsWeight U ρ)
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    {h : Lp V 2 (volume.restrict U)}
    (hD : h ∈ (ω.floerConformalSobolevOperator U ρ J Ks Kt u).rangeᗮ) {ξ : ℝ × ℝ → V}
    (hξ : ξ ∈ testSection V U) :
    ∫ z in U, ⟪h z, ω.floerLinearization J Ks Kt u ξ z⟫_ℝ = 0 := by
  have h0 := (Submodule.mem_orthogonal' _ _).1 hD _ (LinearMap.mem_range_self _
    ⟨(memLp_jet hρ hξ).toLp (jet ρ ξ), jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule hρ hξ)⟩)
  rw [MeasureTheory.L2.inner_def] at h0
  rw [← h0]
  exact integral_congr_ae ((floerConformalSobolevOperator_toLp_jet_ae_eq ω hρ hM hξ).mono
    fun z hz ↦ congrArg (fun v ↦ ⟪h z, v⟫_ℝ) hz.symm)

/-- **Elements orthogonal to the range are regular.** Let `J` be `C³` with `J(z, u z)² = -1` and the
Hamiltonians `K_s`, `K_t` be `C⁴` at the points `(z, u z)` of the graph of a map `u` which is `C³`
on `U`, and let the coefficient field of the linearized operator on conformal jets be essentially
bounded on `U`. Every element `h ∈ L²(U, V)` orthogonal to the range of the realization
`D_u : W^{1,2}_0(U, V) → L²(U, V)` is represented on `U` by a covector field `η` which is `C²` on
`U`: `⟪h, ·⟫ = η` almost everywhere on `U`, and `η` is annihilated by the formal adjoint,
`D_u^* η = 0` on `U`. -/
theorem exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero (hρ : IsWeight U ρ)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ U, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 3 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    {h : Lp V 2 (volume.restrict U)}
    (hD : h ∈ (ω.floerConformalSobolevOperator U ρ J Ks Kt u).rangeᗮ) :
    ∃ η : ℝ × ℝ → V →L[ℝ] ℝ, ContDiffOn ℝ 2 η U ∧
      (fun z ↦ innerSL ℝ (h z)) =ᵐ[volume.restrict U] η ∧
      ∀ z ∈ U, ω.floerLinearizationAdjoint J Ks Kt u η z = 0 := by
  have hUo := hρ.isOpen
  have hUm := hUo.measurableSet
  -- The weak annihilation of `D_u`, from the orthogonality to its range.
  have hweak (ξ : ℝ × ℝ → V) (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξc : HasCompactSupport ξ)
      (hξU : tsupport ξ ⊆ U) : ∫ z, innerField U h z (ω.floerLinearization J Ks Kt u ξ z) = 0 := by
    rw [integral_innerField_apply hUm]
    exact setIntegral_inner_floerLinearization_eq_zero_of_mem_orthogonal_range hρ hM hD
      (mem_testSection_iff.2 ⟨hξ.of_le (WithTop.coe_le_coe.2 le_top), hξc, hξU⟩)
  obtain ⟨η, hηc, hηae⟩ :=
    exists_contDiffOn_ae_eq_of_forall_integral_apply_floerLinearization_eq_zero (ω := ω) hUo
    (k := 2) (fun z hz ↦ (hJ z hz).of_le (by norm_num)) (fun z hz ↦ (hKs z hz).of_le (by norm_num))
    (fun z hz ↦ (hKt z hz).of_le (by norm_num)) (fun z hz ↦ (hu z hz).of_le (by norm_num)) hJJ
    ENNReal.one_lt_two (memLpLoc_innerField hUm h) hweak
  refine ⟨η, hηc, ((indicator_ae_eq_restrict hUm.nullMeasurableSet).symm.trans
    (ae_restrict_of_ae hηae)), ?_⟩
  have hη1 (z : ℝ × ℝ) (hz : z ∈ U) : ContDiffAt ℝ 1 η z :=
    (hηc.contDiffAt (hUo.mem_nhds hz)).of_le one_le_two
  have hJ1 (z : ℝ × ℝ) (hz : z ∈ U) : ContDiffAt ℝ 1 (uncurry J) (z, u z) :=
    (hJ z hz).of_le (by norm_num)
  have hKs2 (z : ℝ × ℝ) (hz : z ∈ U) : ContDiffAt ℝ 2 (uncurry Ks) (z, u z) :=
    (hKs z hz).of_le (by norm_num)
  have hKt2 (z : ℝ × ℝ) (hz : z ∈ U) : ContDiffAt ℝ 2 (uncurry Kt) (z, u z) :=
    (hKt z hz).of_le (by norm_num)
  have hu1 (z : ℝ × ℝ) (hz : z ∈ U) : ContDiffAt ℝ 1 u z := (hu z hz).of_le (by norm_num)
  -- Each component `z ↦ (D^* η)(z) v` vanishes against every test function on `U`, by Green's
  -- formula, and it is continuous on `U`.
  have hv (v : V) : EqOn (fun z ↦ ω.floerLinearizationAdjoint J Ks Kt u η z v) 0 U := by
    have hcv : ContinuousOn (fun z ↦ ω.floerLinearizationAdjoint J Ks Kt u η z v) U :=
      fun z hz ↦ ((continuousAt_floerLinearizationAdjoint (hJ1 z hz) (hKs2 z hz) (hKt2 z hz)
        (hu1 z hz) (hη1 z hz)).clm_apply continuousAt_const).continuousWithinAt
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hUo hcv continuousOn_const
    refine (ae_restrict_iff' hUm).2 (hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hcv.locallyIntegrableOn hUm) fun g hg hgc hgU ↦ ?_)
    set ξ : ℝ × ℝ → V := fun z ↦ g z • v
    have hξ : ContDiff ℝ (⊤ : ℕ∞) ξ := hg.smul contDiff_const
    have hξU : tsupport ξ ⊆ U := (tsupport_smul_subset_left g _).trans hgU
    have hsub : tsupport η ∩ tsupport ξ ⊆ U := inter_subset_right.trans hξU
    have hgreen := ω.integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply
      (J := J) (Ks := Ks) (Kt := Kt) (u := u) (η := η) (ξ := ξ) (fun z hz ↦ hJ1 z (hsub hz))
      (fun z hz ↦ hKs2 z (hsub hz)) (fun z hz ↦ hKt2 z (hsub hz)) (fun z hz ↦ hu1 z (hsub hz))
      (fun z hz ↦ hη1 z (hsub hz)) (fun z _ ↦ (hξ.of_le (by simp)).contDiffAt)
      (hgc.smul_right.isCompact.inter_left (isClosed_tsupport η))
    calc ∫ z, g z • ω.floerLinearizationAdjoint J Ks Kt u η z v
        = ∫ z, ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z) := by
          simp only [ξ, map_smul, smul_eq_mul]
      _ = ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) := hgreen.symm
      _ = ∫ z, innerField U h z (ω.floerLinearization J Ks Kt u ξ z) :=
          integral_congr_ae (hηae.mono fun z hz ↦ by simp only [hz])
      _ = 0 := hweak ξ hξ hgc.smul_right hξU
  intro z hz
  ext v
  exact hv v hz

/-- **Hamiltonian variations detect the cokernel of the linearized Floer operator on
`W^{1,2}`.** Let `U` be a connected open set with a conformal weight `ρ`, let `J` be `C²` with
`J(z, u z)² = -1` and the Hamiltonians `K_s`, `K_t` be `C³` near the graph of a map `u` which is
`C²` on `U`, and let the coefficient field of the linearized operator on conformal jets be
essentially bounded on `U`, so that `D_u : W^{1,2}_0(U, V) → L²(U, V)` realizes the linearized
Floer operator. Let `W` be a neighbourhood of the graph of `u` over a nonempty open set `O ⊆ U`. An
element `h ∈ L²(U, V)` orthogonal to the range of `D_u` and to the Hamiltonian variations supported
in `W` is zero. -/
theorem eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator (hρ : IsWeight U ρ)
    (hUc : IsPreconnected U) (hJ : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ U, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) {h : Lp V 2 (volume.restrict U)}
    (hD : h ∈ (ω.floerConformalSobolevOperator U ρ J Ks Kt u).rangeᗮ)
    (hvar : h ∈ (Submodule.span ℝ (ω.hamiltonianVariationsOn U u W))ᗮ) : h = 0 := by
  have hUm := hρ.isOpen.measurableSet
  have huc : ContinuousOn u U := fun z hz ↦ (hu z hz).continuousAt.continuousWithinAt
  have hη := ae_eq_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub
    (ω := ω) hρ.isOpen hUc hJ hJJ hKs hKt hu (by norm_num) (memLpLoc_innerField hUm h)
    (fun ξ hξ hξc hξU ↦ ?_) hO hOne hOU hW (fun δK hδK hc hδKW ↦ ?_)
  · -- `⟪h z, ·⟫ = 0` almost everywhere on `U`, hence `h = 0`.
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [hη, ae_restrict_mem hUm] with z hz hzU
    have hn := congrArg norm hz
    rw [innerField, indicator_of_mem hzU, innerSL_apply_norm] at hn
    simpa using hn
  · -- Orthogonality to the range of `D_u`, on the jet of the test section `ξ`.
    rw [integral_innerField_apply hUm]
    exact setIntegral_inner_floerLinearization_eq_zero_of_mem_orthogonal_range hρ hM hD
      (mem_testSection_iff.2 ⟨hξ.of_le (WithTop.coe_le_coe.2 le_top), hξc, hξU⟩)
  · -- Orthogonality to the variation `δK`, whose change of the Floer operator is `-X_{δK}(u)`.
    have hX : MemLp (fun z ↦ -ω.hamiltonianVectorField (δK z) (u z)) 2 (volume.restrict U) :=
      (ω.memLp_hamiltonianVectorField_comp (hδK.of_le (WithTop.coe_le_coe.2 le_top)) hc hUm huc
        2).neg
    have hmem := toLp_mem_hamiltonianVariationsOn hδK hc hδKW hX
    have h0 := (Submodule.mem_orthogonal' _ _).1 hvar _ (Submodule.subset_span hmem)
    rw [MeasureTheory.L2.inner_def] at h0
    rw [integral_innerField_apply hUm, ← h0]
    refine integral_congr_ae ?_
    filter_upwards [hX.coeFn_toLp, ae_restrict_mem hUm] with z hz hzU
    have hF := ω.floerOperator_add_const_mul_left J Ks Kt δK u z
      (((hKs z hzU).differentiableAt (by norm_num)).comp _
        ((differentiableAt_const _).prodMk differentiableAt_id))
      ((hδK.differentiable (by simp) (z, u z)).comp _
        ((differentiableAt_const _).prodMk differentiableAt_id)) 1
    simp only [one_mul, one_smul] at hF
    rw [hz, hF, sub_sub_cancel_left]

/-- **The universal linearized operator has dense range.** Under the hypotheses of
`TauCeti.SymplecticForm.eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator`, the range
of `D_u : W^{1,2}_0(U, V) → L²(U, V)` and the Hamiltonian variations supported in `W` together span
a dense subspace of `L²(U, V)`. -/
theorem
    topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
    (hρ : IsWeight U ρ) (hUc : IsPreconnected U)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ U, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator U ρ J Ks Kt u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn U u W)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, ← Submodule.inf_orthogonal, eq_bot_iff]
  exact fun h hh ↦ eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator hρ hUc hJ hJJ
    hKs hKt hu hM hO hOne hOU hW hh.1 hh.2

/-- **The universal linearized operator is onto.** Under the hypotheses of
`TauCeti.SymplecticForm.eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator`, if
the range of `D_u : W^{1,2}_0(U, V) → L²(U, V)` is closed and of finite codimension, as when `D_u`
is Fredholm, then this range and the Hamiltonian variations supported in `W` span `L²(U, V)`. -/
theorem range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
    (hρ : IsWeight U ρ) (hUc : IsPreconnected U)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ U, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z))
    (hcl : IsClosed
      ((ω.floerConformalSobolevOperator U ρ J Ks Kt u).range : Set (Lp V 2 (volume.restrict U))))
    (hco : (ω.floerConformalSobolevOperator U ρ J Ks Kt u).range.CoFG) :
    (ω.floerConformalSobolevOperator U ρ J Ks Kt u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn U u W) = ⊤ := by
  -- `CoFG` is the finiteness of the quotient; put it in scope as an instance.
  have : Module.Finite ℝ (_ ⧸ (ω.floerConformalSobolevOperator U ρ J Ks Kt u).range) := hco
  -- The sum contains the closed range, of finite codimension, so it is closed.
  have hK := Submodule.isClosed_mono_of_finiteDimensional_quotient hcl
    (le_sup_left (b := Submodule.span ℝ (ω.hamiltonianVariationsOn U u W)))
  rw [← hK.submodule_topologicalClosure_eq]
  exact
    topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
      hρ hUc hJ hJJ hKs hKt hu hM hO hOne hOU hW

/-- **Finitely many Hamiltonian variations make the linearized operator onto.** Under the
hypotheses of
`TauCeti.SymplecticForm.eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator`, if
the range of `D_u : W^{1,2}_0(U, V) → L²(U, V)` is closed and of finite codimension, as when `D_u`
is Fredholm, then finitely many Hamiltonian variations supported in `W` span `L²(U, V)` together
with the range of `D_u`. -/
theorem exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top
    (hρ : IsWeight U ρ) (hUc : IsPreconnected U)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ U, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z))
    (hcl : IsClosed
      ((ω.floerConformalSobolevOperator U ρ J Ks Kt u).range : Set (Lp V 2 (volume.restrict U))))
    (hco : (ω.floerConformalSobolevOperator U ρ J Ks Kt u).range.CoFG) :
    ∃ t : Finset (Lp V 2 (volume.restrict U)), (t : Set _) ⊆ ω.hamiltonianVariationsOn U u W ∧
      (ω.floerConformalSobolevOperator U ρ J Ks Kt u).range ⊔ Submodule.span ℝ t = ⊤ := by
  -- `CoFG` is the finiteness of the quotient; put it in scope as an instance.
  have : Module.Finite ℝ (_ ⧸ (ω.floerConformalSobolevOperator U ρ J Ks Kt u).range) := hco
  exact Submodule.exists_finset_subset_sup_span_eq_top
    (range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top hρ hUc hJ hJJ hKs
      hKt hu hM hO hOne hOU hW hcl hco)

end Cokernel

section AlmostComplexCokernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {U : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
  {J : V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {n : ℕ∞}

/-- **Variations of a frozen almost complex structure detect the cokernel of the linearized Floer
operator on `W^{1,2}`.** Let `U` be a connected open set with a conformal weight `ρ`, let `J` be a
frozen `Cⁿ` family of complex structures preserving `ω`, with `2 ≤ n`, and let the Hamiltonians
`K_s`, `K_t` be `C³` near the graph of a map `u` which is `C²` on `U`. Let the coefficient field of
the linearized operator on conformal jets be essentially bounded on `U`, so that
`D_u : W^{1,2}_0(U, V) → L²(U, V)` realizes the linearized Floer operator. Suppose that on a
nonempty open set `O ⊆ U` every point `z` is an injective point of `u`, with `J` tamed by `ω` at
`u z` and `∂ₜu - X_{K_t} ≠ 0` at `z`, and let `W` be a neighbourhood of `u(O)`. An element
`h ∈ L²(U, V)` orthogonal to the range of `D_u` and to the almost complex variations of class `Cⁿ`
supported in `W` is zero. -/
theorem eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator_of_almostComplex
    (hρ : IsWeight U ρ) (hUc : IsPreconnected U)
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) (hn : 2 ≤ n)
    (hJω : ∀ x, ω.Invariant (J x)) (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u) ∞
        (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    (hJ₀ : ∀ z ∈ O, ω.Tames (J (u z))) (hinj : ∀ z ∈ O, (𝓝 (u z)).comap u ≤ 𝓝 z)
    (hξ₀ : ∀ z ∈ O, fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) ≠ 0)
    {W : Set V} (hW : ∀ z ∈ O, W ∈ 𝓝 (u z)) {h : Lp V 2 (volume.restrict U)}
    (hD : h ∈ (ω.floerConformalSobolevOperator U ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).rangeᗮ)
    (hvar : h ∈ (Submodule.span ℝ (ω.almostComplexVariationsOn U u J Kt n W))ᗮ) : h = 0 := by
  have hUo := hρ.isOpen
  have hUm := hUo.measurableSet
  have huc : ContinuousOn u U := fun z hz ↦ (hu z hz).continuousAt.continuousWithinAt
  -- Localize at an injective point `z₀ ∈ O`: a compact neighbourhood `N ⊆ O` of `z₀`, and an open
  -- neighbourhood `W' ⊆ W` of `u z₀` whose preimage under `u` lies in `N`. The variations supported
  -- in `W'` are then supported in `N` along `u`, hence in `L²` on `U`.
  obtain ⟨z₀, hz₀⟩ := hOne
  obtain ⟨N, hN, hz₀N, hNO⟩ := exists_compact_subset hO hz₀
  obtain ⟨W'', hW'', hW''N⟩ :=
    Filter.mem_comap.1 (hinj z₀ hz₀ (mem_interior_iff_mem_nhds.1 hz₀N))
  have hW'o : IsOpen (interior (W ∩ W'')) := isOpen_interior
  have hW'N : u ⁻¹' interior (W ∩ W'') ⊆ N := fun z hz ↦ hW''N (interior_subset hz).2
  have hO' : IsOpen (O ∩ u ⁻¹' interior (W ∩ W'')) :=
    (huc.mono hOU).isOpen_inter_preimage hO hW'o
  have hη := ae_eq_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator (ω := ω)
    hJ hn hJω hUo hUc hKs hKt hu (by norm_num) (memLpLoc_innerField hUm h)
    (fun ξ hξ hξc hξU ↦ ?_) hO'
    ⟨z₀, hz₀, mem_interior_iff_mem_nhds.2 (Filter.inter_mem (hW z₀ hz₀) hW'')⟩
    (inter_subset_left.trans hOU) (fun z hz ↦ hJ₀ z hz.1) (fun z hz ↦ hinj z hz.1)
    (fun z hz ↦ hξ₀ z hz.1) (fun z hz ↦ hW'o.mem_nhds hz.2) (fun Y hY hc hYW hm ↦ ?_)
  · -- `⟪h z, ·⟫ = 0` almost everywhere on `U`, hence `h = 0`.
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [hη, ae_restrict_mem hUm] with z hz hzU
    have hn := congrArg norm hz
    rw [innerField, indicator_of_mem hzU, innerSL_apply_norm] at hn
    simpa using hn
  · -- Orthogonality to the range of `D_u`, on the jet of the test section `ξ`.
    rw [integral_innerField_apply hUm]
    exact setIntegral_inner_floerLinearization_eq_zero_of_mem_orthogonal_range hρ hM hD
      (mem_testSection_iff.2 ⟨hξ.of_le (WithTop.coe_le_coe.2 le_top), hξc, hξU⟩)
  · -- Orthogonality to the variation `Y`, whose derivative of the Floer operator is
    -- `Y(u)(∂ₜu - X_{K_t}(u))`.
    have hX := memLp_almostComplexVariation_of_preimage_subset (ω := ω) hUo
      (fun z hz ↦ (hKt z hz).of_le (by norm_num)) (fun z hz ↦ (hu z hz).of_le (by norm_num))
      hY.continuous hN (hNO.trans hOU) ((preimage_mono hYW).trans hW'N)
    have hmem := toLp_mem_almostComplexVariationsOn hY hc
      (hYW.trans (interior_subset.trans inter_subset_left)) hm hX
    have h0 := (Submodule.mem_orthogonal' _ _).1 hvar _ (Submodule.subset_span hmem)
    rw [MeasureTheory.L2.inner_def] at h0
    simp only [(hasDerivAt_floerOperator_add_smul ω _ (fun _ ↦ Y) Ks Kt u _ 0).deriv]
    rw [integral_innerField_apply hUm, ← h0]
    refine integral_congr_ae ?_
    filter_upwards [hX.coeFn_toLp] with z hz
    rw [hz]

/-- **Variations of a frozen almost complex structure give the linearized operator dense range.**
Under the hypotheses of
`eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator_of_almostComplex`,
the range of `D_u : W^{1,2}_0(U, V) → L²(U, V)` and the almost complex variations supported in `W`
together span a dense subspace of `L²(U, V)`. -/
theorem
    topologicalClosure_range_floerConformalSobolevOperator_sup_span_almostComplexVariationsOn_eq_top
    (hρ : IsWeight U ρ) (hUc : IsPreconnected U)
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) (hn : 2 ≤ n)
    (hJω : ∀ x, ω.Invariant (J x)) (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u) ∞
        (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    (hJ₀ : ∀ z ∈ O, ω.Tames (J (u z))) (hinj : ∀ z ∈ O, (𝓝 (u z)).comap u ≤ 𝓝 z)
    (hξ₀ : ∀ z ∈ O, fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) ≠ 0)
    {W : Set V} (hW : ∀ z ∈ O, W ∈ 𝓝 (u z)) :
    ((ω.floerConformalSobolevOperator U ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range ⊔
        Submodule.span ℝ (ω.almostComplexVariationsOn U u J Kt n W)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, ← Submodule.inf_orthogonal, eq_bot_iff]
  exact fun h hh ↦ eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator_of_almostComplex
    hρ hUc hJ hn hJω hKs hKt hu hM hO hOne hOU hJ₀ hinj hξ₀ hW hh.1 hh.2

/-- **Variations of a frozen almost complex structure make the linearized operator onto.** Under
the hypotheses of
`eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator_of_almostComplex`,
if the range of `D_u : W^{1,2}_0(U, V) → L²(U, V)` is closed and of finite codimension, as when
`D_u` is Fredholm, then this range and the almost complex variations supported in `W` span
`L²(U, V)`. -/
theorem range_floerConformalSobolevOperator_sup_span_almostComplexVariationsOn_eq_top
    (hρ : IsWeight U ρ) (hUc : IsPreconnected U)
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) (hn : 2 ≤ n)
    (hJω : ∀ x, ω.Invariant (J x)) (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u) ∞
        (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    (hJ₀ : ∀ z ∈ O, ω.Tames (J (u z))) (hinj : ∀ z ∈ O, (𝓝 (u z)).comap u ≤ 𝓝 z)
    (hξ₀ : ∀ z ∈ O, fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) ≠ 0)
    {W : Set V} (hW : ∀ z ∈ O, W ∈ 𝓝 (u z))
    (hcl : IsClosed ((ω.floerConformalSobolevOperator U ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range :
        Set (Lp V 2 (volume.restrict U))))
    (hco : (ω.floerConformalSobolevOperator U ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range.CoFG) :
    (ω.floerConformalSobolevOperator U ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range ⊔
        Submodule.span ℝ (ω.almostComplexVariationsOn U u J Kt n W) = ⊤ := by
  -- `CoFG` is the finiteness of the quotient; put it in scope as an instance.
  have : Module.Finite ℝ (_ ⧸ (ω.floerConformalSobolevOperator U ρ
    (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range) := hco
  -- The sum contains the closed range, of finite codimension, so it is closed.
  have hK := Submodule.isClosed_mono_of_finiteDimensional_quotient hcl
    (le_sup_left (b := Submodule.span ℝ (ω.almostComplexVariationsOn U u J Kt n W)))
  rw [← hK.submodule_topologicalClosure_eq]
  exact
    topologicalClosure_range_floerConformalSobolevOperator_sup_span_almostComplexVariationsOn_eq_top
      hρ hUc hJ hn hJω hKs hKt hu hM hO hOne hOU hJ₀ hinj hξ₀ hW

/-- **Finitely many variations of a frozen almost complex structure make the linearized operator
onto.** Under the hypotheses of
`eq_zero_of_mem_orthogonal_range_floerConformalSobolevOperator_of_almostComplex`,
if the range of `D_u : W^{1,2}_0(U, V) → L²(U, V)` is closed and of finite codimension, as when
`D_u` is Fredholm, then finitely many almost complex variations supported in `W` span `L²(U, V)`
together with the range of `D_u`. -/
theorem exists_finset_subset_almostComplexVariationsOn_range_sup_span_eq_top
    (hρ : IsWeight U ρ) (hUc : IsPreconnected U)
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) (hn : 2 ≤ n)
    (hJω : ∀ x, ω.Invariant (J x)) (hKs : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u) ∞
        (volume.restrict U))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOU : O ⊆ U)
    (hJ₀ : ∀ z ∈ O, ω.Tames (J (u z))) (hinj : ∀ z ∈ O, (𝓝 (u z)).comap u ≤ 𝓝 z)
    (hξ₀ : ∀ z ∈ O, fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) ≠ 0)
    {W : Set V} (hW : ∀ z ∈ O, W ∈ 𝓝 (u z))
    (hcl : IsClosed ((ω.floerConformalSobolevOperator U ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range :
        Set (Lp V 2 (volume.restrict U))))
    (hco : (ω.floerConformalSobolevOperator U ρ
      (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range.CoFG) :
    ∃ t : Finset (Lp V 2 (volume.restrict U)),
      (t : Set _) ⊆ ω.almostComplexVariationsOn U u J Kt n W ∧
        (ω.floerConformalSobolevOperator U ρ
          (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range ⊔
            Submodule.span ℝ t = ⊤ := by
  -- `CoFG` is the finiteness of the quotient; put it in scope as an instance.
  have : Module.Finite ℝ (_ ⧸ (ω.floerConformalSobolevOperator U ρ
    (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) Ks Kt u).range) := hco
  exact Submodule.exists_finset_subset_sup_span_eq_top
    (range_floerConformalSobolevOperator_sup_span_almostComplexVariationsOn_eq_top hρ hUc hJ hn
      hJω hKs hKt hu hM hO hOne hOU hJ₀ hinj hξ₀ hW hcl hco)

end AlmostComplexCokernel

end TauCeti.SymplecticForm
