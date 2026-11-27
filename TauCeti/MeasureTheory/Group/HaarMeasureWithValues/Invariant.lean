/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution
public import TauCeti.RepresentationTheory.LinearCharacter.Eigenspace
public import TauCeti.Topology.LocallyConstant.CompactSupport.Ideal
import TauCeti.RepresentationTheory.Dual

/-!
# Invariant and eigen functionals on test functions

Let `G` be a Hausdorff topological group and `A` a commutative ring, and let `G` act on the test
functions `C_c^∞(G, A)`, the locally constant functions with compact support, by left translation
`(g • f)(x) = f(g⁻¹ x)` (`TauCeti.compactlySupportedRep`). A linear functional `Λ` on `C_c^∞(G, A)`
which is invariant under the contragredient action, `Λ(g • f) = Λ(f)`, is integration against an
`A`-valued Haar measure: the volumes `μ_Λ(K) = Λ(1_K)` of compact open sets are finitely additive
and left invariant (`TauCeti.HaarMeasureWithValues.ofInvariant`), and `Λ` is the integral against
`μ_Λ` (`TauCeti.HaarMeasureWithValues.integral_ofInvariant`), because test functions are finite
sums of indicators. If `G` has a compact open subgroup `U₀` of invertible pro-order in `A`, every
`A`-valued Haar measure is its volume of `U₀` times the normalised one, so the invariant functionals
are the multiples of the normalised Haar integral
(`TauCeti.dual_invariants_compactlySupportedRep`); over a field they form a line.

A character `χ : G →* Aˣ` with locally constant values moves eigenfunctionals to invariant ones.
The `χ`-eigenspace of the contragredient consists of the `λ` with `λ(g • f) = χ(g)⁻¹ λ(f)`, and
since `g • (χ f) = χ(g)⁻¹ χ (g • f)`, the functional `f ↦ λ(χ f)` is then invariant. Hence the
`χ`-eigenspace is the line spanned by `f ↦ ∫ χ⁻¹ f dμ`
(`TauCeti.dual_charEigenspace_compactlySupportedRep`). For the multiplicative group of a
nonarchimedean local field these are Tate's eigendistributions on `C_c^∞(F^×)`, spanned by
`ω(x) d^×x`.

## Main definitions

* `TauCeti.HaarMeasureWithValues.ofInvariant`: the `A`-valued Haar measure `K ↦ Λ(1_K)` of an
  invariant functional `Λ`.

## Main results

* `TauCeti.HaarMeasureWithValues.integral_ofInvariant`: an invariant functional is the integral
  against its Haar measure.
* `TauCeti.dual_invariants_compactlySupportedRep`: the invariant functionals are the multiples of
  the normalised Haar integral.
* `TauCeti.finrank_dual_invariants_compactlySupportedRep`: over a field they form a line.
* `TauCeti.dual_charEigenspace_compactlySupportedRep`,
  `TauCeti.finrank_dual_charEigenspace_compactlySupportedRep`: the eigenfunctionals of a character
  with locally constant values are the multiples of `f ↦ ∫ χ⁻¹ f dμ`, a line over a field.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §3.1, for Haar measures on locally profinite
  groups.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, Birkhäuser, 2003, §3, for the eigendistributions on `C_c^∞(F^×)`.
-/

public section

noncomputable section

open LocallyConstant TopologicalSpace Module

namespace TauCeti

variable {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G]

section ContinuousConstSMul

variable [ContinuousConstSMul G G] [T2Space G]

namespace HaarMeasureWithValues

/-- The `A`-valued Haar measure of a translation-invariant functional `Λ` on `C_c^∞(G, A)`: the
volume of a compact open set `K` is `Λ(1_K)`. -/
def ofInvariant {Λ : Dual A (compactlySupported A G A)}
    (hΛ : Λ ∈ (compactlySupportedRep A G G A).dual.invariants) : HaarMeasureWithValues A G where
  toFun K := Λ ⟨compactOpenIndicator K 1, compactOpenIndicator_mem_compactlySupported K 1⟩
  map_bot' := by
    rw [← map_zero Λ]
    congr 1
    ext
    simp
  map_sup' K L hKL := by
    rw [← map_add]
    congr 1
    ext
    simp [Set.indicator_union_of_disjoint hKL]
  map_smul' g K := by
    rw [← compactlySupportedRep_apply_compactOpenIndicator,
      Representation.apply_of_mem_invariants_dual hΛ]

@[simp]
theorem ofInvariant_apply {Λ : Dual A (compactlySupported A G A)}
    (hΛ : Λ ∈ (compactlySupportedRep A G G A).dual.invariants) (K : CompactOpens G) :
    ofInvariant hΛ K =
      Λ ⟨compactOpenIndicator K 1, compactOpenIndicator_mem_compactlySupported K 1⟩ :=
  (rfl)

/-- **Invariant functionals are Haar integrals.** A functional on `C_c^∞(G, A)` invariant under
left translation is the integral against the `A`-valued Haar measure `K ↦ Λ(1_K)`. -/
theorem integral_ofInvariant {Λ : Dual A (compactlySupported A G A)}
    (hΛ : Λ ∈ (compactlySupportedRep A G G A).dual.invariants) :
    (ofInvariant hΛ).integral = Λ := by
  refine (eq_integral_of_apply_compactOpenIndicator _ Λ fun K m ↦ ?_).symm
  have hK : (⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ :
      compactlySupported A G A) =
      m • ⟨compactOpenIndicator K 1, compactOpenIndicator_mem_compactlySupported K 1⟩ := by
    ext
    simp [← compactOpenIndicator_smul]
  rw [hK, map_smul, ofInvariant_apply, smul_eq_mul, smul_eq_mul, mul_comm]

end HaarMeasureWithValues

end ContinuousConstSMul

variable [IsTopologicalGroup G] [T2Space G] {U₀ : OpenSubgroup G} (hU₀ : IsCompact (U₀ : Set G))
  (h : HasUnitProOrder A U₀)

/-- **Invariant functionals on test functions are multiples of the Haar integral.** If `U₀` is a
compact open subgroup of invertible pro-order in `A`, the functionals on `C_c^∞(G, A)` invariant
under left translation are the multiples of the integral against the Haar measure normalised by
`μ(U₀) = 1`. -/
theorem dual_invariants_compactlySupportedRep :
    (compactlySupportedRep A G G A).dual.invariants =
      A ∙ (HaarMeasureWithValues.normalized A U₀ hU₀ h).integral := by
  set μ := HaarMeasureWithValues.normalized A U₀ hU₀ h
  refine le_antisymm (fun Λ hΛ ↦ Submodule.mem_span_singleton.2 ?_) ?_
  · -- `Λ` integrates against `μ_Λ = μ_Λ(U₀) • μ`.
    refine ⟨HaarMeasureWithValues.ofInvariant hΛ (U₀.toCompactOpens hU₀),
      Eq.trans ?_ (HaarMeasureWithValues.integral_ofInvariant hΛ)⟩
    refine HaarMeasureWithValues.eq_integral_of_apply_compactOpenIndicator
      (HaarMeasureWithValues.ofInvariant hΛ) _ fun K m ↦ ?_
    rw [LinearMap.smul_apply, HaarMeasureWithValues.integral_compactOpenIndicator,
      (HaarMeasureWithValues.ofInvariant hΛ).apply_eq_normalized_mul hU₀ h K, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    ring
  · rw [Submodule.span_singleton_le_iff_mem, Representation.mem_invariants_dual_iff]
    exact fun g f ↦ HaarMeasureWithValues.integral_compactlySupportedRep _ g f

/-- The normalised Haar integral is nonzero: it gives the indicator of `U₀` the value `1`. -/
private theorem integral_normalized_ne_zero [Nontrivial A] :
    ((HaarMeasureWithValues.normalized A U₀ hU₀ h).integral : Dual A (compactlySupported A G A)) ≠
      0 := fun h0 ↦ by
  have := LinearMap.congr_fun h0
    ⟨compactOpenIndicator (U₀.toCompactOpens hU₀) 1,
      compactOpenIndicator_mem_compactlySupported _ 1⟩
  rw [HaarMeasureWithValues.integral_compactOpenIndicator,
    HaarMeasureWithValues.normalized_apply_self, LinearMap.zero_apply, smul_eq_mul,
    mul_one] at this
  exact one_ne_zero this

include hU₀ in
/-- Over a field `k` in which a compact open subgroup has invertible pro-order, the functionals on
`C_c^∞(G, k)` invariant under left translation form a line. -/
theorem finrank_dual_invariants_compactlySupportedRep {k : Type*} [Field k]
    (h : HasUnitProOrder k U₀) :
    finrank k (compactlySupportedRep k G G k).dual.invariants = 1 := by
  rw [dual_invariants_compactlySupportedRep hU₀ h]
  exact finrank_span_singleton (integral_normalized_ne_zero hU₀ h)

/-! ### Eigenfunctionals of a character -/

section Character

omit [T2Space G] in
/-- Translating the product of a test function with the values of a character `χ`:
`g • (χ f) = χ(g)⁻¹ χ (g • f)`. -/
private theorem compactlySupportedRep_mulLeft (χ : G →* Aˣ) (hχ : IsLocallyConstant χ) (g : G)
    (f : compactlySupported A G A) :
    compactlySupportedRep A G G A g
        (compactlySupported.mulLeft ((⟨χ, hχ⟩ : LocallyConstant G Aˣ).map (↑)) f) =
      ((χ g)⁻¹ : Aˣ) • compactlySupported.mulLeft ((⟨χ, hχ⟩ : LocallyConstant G Aˣ).map (↑))
        (compactlySupportedRep A G G A g f) := by
  ext x
  simp [Units.smul_def, mul_assoc]

/-- **Eigenfunctionals of a character are multiples of a twisted Haar integral.** Let `χ : G →* Aˣ`
have locally constant values, and let `U₀` be a compact open subgroup of invertible pro-order in
`A`. The functionals `λ` on `C_c^∞(G, A)` in the `χ`-eigenspace of the contragredient, that is with
`λ(g • f) = χ(g)⁻¹ λ(f)`, are the multiples of `f ↦ ∫ χ⁻¹ f dμ` for the Haar measure `μ` normalised
by `μ(U₀) = 1`. -/
theorem dual_charEigenspace_compactlySupportedRep (χ : G →* Aˣ) (hχ : IsLocallyConstant χ) :
    (compactlySupportedRep A G G A).dual.charEigenspace χ =
      A ∙ ((HaarMeasureWithValues.normalized A U₀ hU₀ h).integral ∘ₗ
        compactlySupported.mulLeft
          ((⟨χ, hχ⟩ : LocallyConstant G Aˣ).map fun u ↦ ((u⁻¹ : Aˣ) : A))) := by
  set ρ := compactlySupportedRep A G G A
  set I : Dual A (compactlySupported A G A) :=
    (HaarMeasureWithValues.normalized A U₀ hU₀ h).integral
  set φ := (⟨χ, hχ⟩ : LocallyConstant G Aˣ).map ((↑) : Aˣ → A)
  set ψ := (⟨χ, hχ⟩ : LocallyConstant G Aˣ).map fun u ↦ ((u⁻¹ : Aˣ) : A)
  -- `ψ` is the function of the character `χ⁻¹`, and `φ ψ = 1`.
  have hχ' : IsLocallyConstant ⇑χ⁻¹ := hχ.comp fun u : Aˣ ↦ u⁻¹
  have hψ : ψ = (⟨⇑χ⁻¹, hχ'⟩ : LocallyConstant G Aˣ).map ((↑) : Aˣ → A) := rfl
  have hφψ (f : compactlySupported A G A) :
      compactlySupported.mulLeft φ (compactlySupported.mulLeft ψ f) = f := by
    ext x
    simp [φ, ψ, ← mul_assoc]
  refine le_antisymm (fun ℓ hℓ ↦ Submodule.mem_span_singleton.2 ?_) ?_
  · -- `f ↦ ℓ (χ f)` is invariant, hence a multiple of `I`.
    have hinv : ℓ ∘ₗ compactlySupported.mulLeft φ ∈ ρ.dual.invariants := by
      refine Representation.mem_invariants_dual_iff.2 fun g f ↦ ?_
      have hg := inv_smul_eq_iff.1 (compactlySupportedRep_mulLeft χ hχ g f).symm
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hg, Units.smul_def, map_smul,
        (Representation.mem_charEigenspace_dual_iff _ χ).1 hℓ, smul_eq_mul, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      ((dual_invariants_compactlySupportedRep hU₀ h).le hinv)
    refine ⟨c, LinearMap.ext fun f ↦ ?_⟩
    rw [LinearMap.smul_apply, LinearMap.comp_apply, ← LinearMap.smul_apply, hc,
      LinearMap.comp_apply, hφψ]
  · rw [Submodule.span_singleton_le_iff_mem, Representation.mem_charEigenspace_dual_iff]
    intro g f
    have hg := compactlySupportedRep_mulLeft χ⁻¹ hχ' g f
    rw [← hψ] at hg
    rw [LinearMap.comp_apply, LinearMap.comp_apply, inv_smul_eq_iff.1 hg.symm, Units.smul_def,
      map_smul, HaarMeasureWithValues.integral_compactlySupportedRep, MonoidHom.inv_apply,
      smul_eq_mul]

include hU₀ in
/-- Over a field `k` in which a compact open subgroup has invertible pro-order, the
eigenfunctionals of a character with locally constant values form a line. -/
theorem finrank_dual_charEigenspace_compactlySupportedRep {k : Type*} [Field k]
    (h : HasUnitProOrder k U₀) (χ : G →* kˣ) (hχ : IsLocallyConstant χ) :
    finrank k ((compactlySupportedRep k G G k).dual.charEigenspace χ) = 1 := by
  rw [dual_charEigenspace_compactlySupportedRep hU₀ h χ hχ]
  refine finrank_span_singleton fun h0 ↦ integral_normalized_ne_zero hU₀ h ?_
  refine LinearMap.ext fun f ↦ ?_
  have hf := LinearMap.congr_fun h0
    (compactlySupported.mulLeft ((⟨χ, hχ⟩ : LocallyConstant G kˣ).map (↑)) f)
  rw [LinearMap.comp_apply] at hf
  convert hf using 2
  ext x
  simp [← mul_assoc]

end Character

end TauCeti
