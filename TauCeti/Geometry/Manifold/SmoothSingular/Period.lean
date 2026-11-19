/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Stokes
public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DeRham.Circle

/-!
# Periods of closed forms on integral smooth singular homology

A closed `C¹` `p`-form `φ` on a `C²` manifold `M`, with values in a real normed space `F`, can be
integrated over the smooth singular `p`-chains of `M` with **integer** coefficients: the chain
`∑ nᵢ σᵢ` integrates to `∑ nᵢ ∫_{σᵢ} φ` (`TauCeti.intIntegrationCochain`). By Stokes' theorem
the integral of `φ` over a boundary `∂c` is the integral of `dφ = 0` over `c`
(`TauCeti.d_comp_intIntegrationCochain`), so it descends to a homomorphism

`TauCeti.smoothHomologyPeriodHom φ : H_p^sm(M; ℤ) →+ F`

from the integral smooth singular homology of `M`, the **periods** of `φ`. Exact forms have
vanishing periods (`TauCeti.smoothHomologyPeriodHom_mextDeriv`), and the periods are natural under
smooth maps: those of a pullback `f^* ψ` are those of `ψ` on the pushforward classes
(`TauCeti.smoothHomologyPeriodHom_homologyMap`). For smooth real forms they therefore only depend
on the de Rham class, and give the **pairing of de Rham cohomology with integral smooth singular
homology** (`TauCeti.deRhamCohomology.smoothHomologyPeriod`), a linear map

`H^p_dR(M) →ₗ[ℝ] (H_p^sm(M; ℤ) →+ ℝ)`,

natural in smooth maps (`TauCeti.deRhamCohomology.smoothHomologyPeriod_map`). The pairing is not
trivial: the angular form `dθ` of the circle has period `2π` on the class of the loop
`t ↦ exp (2π i t)`, read as a smooth singular `1`-cycle
(`TauCeti.deRhamCohomology.smoothHomologyPeriod_mk_circleAngularClosedForm_circleLoopClass`).

The real-coefficient counterpart is `TauCeti.integrationCochain` together with
`TauCeti.deRhamCohomology.integration`, which sends a de Rham class to a class in smooth singular
cohomology with real coefficients. Integer coefficients are what is needed to pair a closed form
with integral homology classes, such as the area `ω(A)` of a class `A ∈ H₂(M; ℤ)` of a symplectic
manifold `(M, ω)`. Through the comparison of smooth and ordinary singular homology this becomes a
homomorphism on `H_p(M; ℤ)`; that comparison is not used here.

## Main definitions

* `TauCeti.intIntegrationCochain φ`: integration of `φ` over smooth singular chains with integer
  coefficients.
* `TauCeti.smoothHomologyPeriodHom φ hφ hdφ`: the periods of a closed `C¹` form on
  `H_p^sm(M; ℤ)`.
* `TauCeti.deRhamCohomology.smoothHomologyPeriod`: the periods of de Rham classes, a linear map
  `H^p_dR(M) →ₗ[ℝ] (H_p^sm(M; ℤ) →+ ℝ)`.

## Main results

* `TauCeti.d_comp_intIntegrationCochain`: Stokes' theorem for integral smooth chains.
* `TauCeti.smoothHomologyPeriodHom_homologyπ`: the period on the class of a cycle is the integral
  over the cycle.
* `TauCeti.smoothHomologyPeriodHom_mextDeriv`: exact forms have vanishing periods.
* `TauCeti.smoothHomologyPeriodHom_homologyMap`: naturality under smooth maps.
* `TauCeti.deRhamCohomology.smoothHomologyPeriod_mk`,
  `TauCeti.deRhamCohomology.smoothHomologyPeriod_map`: the class-level pairing and its
  naturality.
* `TauCeti.deRhamCohomology.smoothHomologyPeriod_mk_circleAngularClosedForm_circleLoopClass`: the
  period of `dθ` on the standard loop of the circle is `2π`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18 (integration over smooth
  chains, Stokes' theorem for chains and the de Rham homomorphism).
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-! ### Integration over integral smooth singular chains -/

section Cochain

/-- Integration of a `p`-form over smooth singular `p`-chains with integer coefficients: the chain
`∑ nᵢ σᵢ` is sent to `∑ nᵢ ∫_{σᵢ} φ`. -/
def intIntegrationCochain (φ : RoughForm I M F p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p ⟶
      ModuleCat.of ℤ F :=
  ModuleCat.ofHom ((Finsupp.linearCombination ℤ (fun σ : SmoothSimplex I M p ↦ σ.integral φ)).comp
    (SSet.chainsLinearEquivFinsupp _ ℤ p).toLinearMap)

/-- On canonical simplicial chains, integration is the finite sum of the integrals over the
simplices, weighted by their integer coefficients. -/
theorem intIntegrationCochain_apply (φ : RoughForm I M F p)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    (intIntegrationCochain φ).hom c =
      ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c).sum
        fun σ n ↦ n • SmoothSimplex.integral σ φ :=
  Finsupp.linearCombination_apply ℤ _

/-- The integration cochain takes a simplex with coefficient `n` to `n` times its integral. -/
@[simp]
theorem intIntegrationCochain_ιChainComplex (φ : RoughForm I M F p) (σ : SmoothSimplex I M p)
    (n : ℤ) :
    (intIntegrationCochain φ).hom (((smoothSingularSubcomplex I M : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) σ).hom n) = n • σ.integral φ := by
  rw [intIntegrationCochain_apply, SSet.chainsLinearEquivFinsupp_ιChainComplex,
    Finsupp.sum_single_index (by simp)]

/-- Integrating the zero form gives the zero cochain. -/
@[simp]
theorem intIntegrationCochain_zero : intIntegrationCochain (0 : RoughForm I M F p) = 0 := by
  ext c
  simp [intIntegrationCochain_apply (I := I)]

/-- Integration over integral chains is homogeneous in the form. -/
theorem intIntegrationCochain_smul (a : ℝ) (φ : RoughForm I M F p) :
    intIntegrationCochain (a • φ) = a • intIntegrationCochain φ := by
  ext c
  simp only [intIntegrationCochain_apply (I := I), SmoothSimplex.integral_smul, ModuleCat.hom_smul,
    LinearMap.smul_apply, Finsupp.smul_sum, smul_comm a]

/-- Integration over integral chains is additive on continuous forms. -/
theorem intIntegrationCochain_add [IsManifold I 1 M] {φ ψ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    intIntegrationCochain (φ + ψ) = intIntegrationCochain φ + intIntegrationCochain ψ := by
  ext c
  simp only [intIntegrationCochain_apply (I := I), SmoothSimplex.integral_add _ hφ hψ, smul_add,
    Finsupp.sum_add, ModuleCat.hom_add, LinearMap.add_apply]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]

/-- Integration over integral chains is natural for the chain map induced by a smooth map:
integrating `ψ` over the pushforward of a chain is integrating the pullback of `ψ`. -/
@[reassoc]
theorem intIntegrationCochain_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    (ψ : RoughForm J N F p) :
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)).f p ≫
      intIntegrationCochain ψ = intIntegrationCochain (mpullback I J f ψ) := by
  ext c
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, intIntegrationCochain_apply,
    intIntegrationCochain_apply, SSet.chainsLinearEquivFinsupp_chainComplexMap_f,
    Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
  simp only [SmoothSimplex.integral_smoothSingularSubcomplexMap_app hf]

variable [IsManifold I 2 M]

/-- **Stokes' theorem for integral smooth singular chains.** For a `C¹` form `φ`, integrating
`φ` over the boundary of a smooth singular chain with integer coefficients is integrating `dφ`
over the chain. -/
@[reassoc]
theorem d_comp_intIntegrationCochain {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (p + 1) p ≫
      intIntegrationCochain φ = intIntegrationCochain (mextDeriv φ) := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rw [intIntegrationCochain_ιChainComplex, one_smul, SmoothSimplex.integral_mextDeriv σ hφ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [intIntegrationCochain_ιChainComplex, one_smul, ← Int.cast_smul_eq_zsmul ℝ]
  simp

/-- The integration cochain of a closed `C¹` form over integral chains is a cocycle. -/
theorem d_comp_intIntegrationCochain_eq_zero {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (p + 1) p ≫
      intIntegrationCochain φ = 0 := by
  rw [d_comp_intIntegrationCochain hφ, hdφ, intIntegrationCochain_zero]

end Cochain

/-! ### Periods on integral smooth singular homology -/

section Period

variable [IsManifold I 2 M]

/-- The **periods** of a closed `C¹` `p`-form `φ` on the integral smooth singular homology of `M`:
the integral of `φ` over integral smooth singular `p`-cycles, which only depends on their homology
classes by Stokes' theorem. -/
def smoothHomologyPeriodHom (φ : RoughForm I M F p) (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p →+ F :=
  (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyι p ≫
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).descOpcycles
      (intIntegrationCochain φ) (p + 1) (ChainComplex.prev ℕ p)
      (d_comp_intIntegrationCochain_eq_zero hφ hdφ)).hom.toAddMonoidHom

/-- The period on the homology class of a cycle `∑ nᵢ σᵢ` is `∑ nᵢ ∫_{σᵢ} φ`. -/
@[simp]
theorem smoothHomologyPeriodHom_homologyπ {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles p) :
    smoothHomologyPeriodHom φ hφ hdφ
        ((((smoothSingularSubcomplex I M : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).homologyπ p).hom z) =
      (intIntegrationCochain φ).hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).iCycles p).hom z) := by
  have h : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ p ≫
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyι p ≫
        ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).descOpcycles
          (intIntegrationCochain φ) (p + 1) (ChainComplex.prev ℕ p)
          (d_comp_intIntegrationCochain_eq_zero hφ hdφ) =
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles p ≫
        intIntegrationCochain φ := by
    rw [HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles]
  exact ConcreteCategory.congr_hom h z

omit [NormedSpace ℝ F] [IsManifold I 2 M] in
/-- Two homomorphisms out of the integral smooth singular homology agree once they agree on the
classes of cycles. -/
private theorem addMonoidHom_ext_homologyπ {f g :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p →+ F}
    (h : ∀ z, f ((((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).homologyπ p).hom z) =
      g ((((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).homologyπ p).hom z)) : f = g := by
  ext c
  obtain ⟨z, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p c
  exact h z

/-- **Exact forms have vanishing periods.** For a `C¹` form `θ`, the periods of `dθ` on integral
smooth singular homology vanish. -/
theorem smoothHomologyPeriodHom_mextDeriv {θ : RoughForm I M F p} (hθ : IsSmoothForm I 1 θ)
    (h₁ : IsSmoothForm I 1 (mextDeriv θ)) (h₂ : mextDeriv (mextDeriv θ) = 0) :
    smoothHomologyPeriodHom (mextDeriv θ) h₁ h₂ = 0 := by
  refine addMonoidHom_ext_homologyπ fun z ↦ ?_
  -- the integral of `dθ` over a cycle is the integral of `θ` over its boundary, which is zero
  rw [smoothHomologyPeriodHom_homologyπ, AddMonoidHom.zero_apply,
    ← d_comp_intIntegrationCochain hθ]
  simp

/-- The periods only depend on the closed form, not on the proofs of its regularity and
closedness. -/
theorem smoothHomologyPeriodHom_congr {φ ψ : RoughForm I M F p} (h : φ = ψ)
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) (hψ : IsSmoothForm I 1 ψ)
    (hdψ : mextDeriv ψ = 0) :
    smoothHomologyPeriodHom φ hφ hdφ = smoothHomologyPeriodHom ψ hψ hdψ := by
  subst h
  rfl

/-- The periods are additive in the closed form. -/
theorem smoothHomologyPeriodHom_add {φ ψ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (hψ : IsSmoothForm I 1 ψ) (hdψ : mextDeriv ψ = 0)
    (hφψ : IsSmoothForm I 1 (φ + ψ)) (hdφψ : mextDeriv (φ + ψ) = 0) :
    smoothHomologyPeriodHom (φ + ψ) hφψ hdφψ =
      smoothHomologyPeriodHom φ hφ hdφ + smoothHomologyPeriodHom ψ hψ hdψ := by
  refine addMonoidHom_ext_homologyπ fun z ↦ ?_
  rw [AddMonoidHom.add_apply, smoothHomologyPeriodHom_homologyπ, smoothHomologyPeriodHom_homologyπ,
    smoothHomologyPeriodHom_homologyπ,
    intIntegrationCochain_add (hφ.of_le (by simp)) (hψ.of_le (by simp)), ModuleCat.hom_add,
    LinearMap.add_apply]

/-- The periods are homogeneous in the closed form. -/
theorem smoothHomologyPeriodHom_smul (a : ℝ) {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (haφ : IsSmoothForm I 1 (a • φ)) (hdaφ : mextDeriv (a • φ) = 0) :
    smoothHomologyPeriodHom (a • φ) haφ hdaφ = a • smoothHomologyPeriodHom φ hφ hdφ := by
  refine addMonoidHom_ext_homologyπ fun z ↦ ?_
  rw [AddMonoidHom.smul_apply, smoothHomologyPeriodHom_homologyπ,
    smoothHomologyPeriodHom_homologyπ, intIntegrationCochain_smul, ModuleCat.hom_smul,
    LinearMap.smul_apply]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 2 N]

/-- **Naturality of the periods.** For a smooth map `f : M → N` and a closed `C¹` form `ψ` on `N`,
the period of `ψ` on the pushforward `f_* c` of a class `c ∈ H_p^sm(M; ℤ)` is the period of the
pullback `f^* ψ` on `c`. -/
theorem smoothHomologyPeriodHom_homologyMap {f : M → N} (hf : ContMDiff I J ∞ f)
    {ψ : RoughForm J N F p} (hψ : IsSmoothForm J 1 ψ) (hdψ : mextDeriv ψ = 0)
    (hfψ : IsSmoothForm I 1 (mpullback I J f ψ)) (hdfψ : mextDeriv (mpullback I J f ψ) = 0)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p) :
    smoothHomologyPeriodHom ψ hψ hdψ
        ((SSet.homologyMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ) p).hom c) =
      smoothHomologyPeriodHom (mpullback I J f ψ) hfψ hdfψ c := by
  obtain ⟨z, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p c
  have hz := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)) p) z
  have h : HomologicalComplex.cyclesMap
      (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)) p ≫
        ((smoothSingularSubcomplex J N : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles p ≫
          intIntegrationCochain ψ =
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles p ≫
        intIntegrationCochain (mpullback I J f ψ) := by
    rw [HomologicalComplex.cyclesMap_i_assoc, intIntegrationCochain_naturality]
  simp only [ConcreteCategory.comp_apply] at hz
  rw [SSet.homologyMap, hz, smoothHomologyPeriodHom_homologyπ, smoothHomologyPeriodHom_homologyπ]
  exact ConcreteCategory.congr_hom h z

end Period

/-! ### The pairing of de Rham cohomology with integral smooth singular homology -/

namespace deRhamCohomology

variable [IsManifold I 2 M]

/-- The periods on integral smooth singular homology of closed smooth real forms, as a linear
map. -/
private def smoothHomologyPeriodClosedForms : closedForms I M p →ₗ[ℝ]
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p →+ ℝ where
  toFun φ := smoothHomologyPeriodHom (φ.1 : RoughForm I M ℝ p) (φ.1.isSmoothForm.of_le (by simp))
    ((mem_closedForms I _).mp φ.2)
  map_add' φ ψ := smoothHomologyPeriodHom_add _ _ _ _ _ _
  map_smul' a φ := smoothHomologyPeriodHom_smul a _ _ _ _

/-- Exact forms have vanishing periods on integral smooth singular homology. -/
private theorem ker_mk_le_ker_smoothHomologyPeriodClosedForms :
    LinearMap.ker (mk I (M := M) p) ≤
      LinearMap.ker (smoothHomologyPeriodClosedForms (I := I) (M := M) (p := p)) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker]
  cases p with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ
    have hφ' : φ = 0 := Subtype.ext hφ
    subst hφ'
    exact map_zero _
  | succ p =>
    rw [exactForms_succ, LinearMap.mem_range] at hφ
    obtain ⟨θ, hθ⟩ := hφ
    have h : (φ.1 : RoughForm I M ℝ (p + 1)) = mextDeriv (θ : RoughForm I M ℝ p) := by
      rw [← hθ, mextDerivₗ_apply]
    have hθ₁ : IsSmoothForm I 1 (θ : RoughForm I M ℝ p) := θ.isSmoothForm.of_le (by simp)
    have hφ₁ : IsSmoothForm I 1 (φ.1 : RoughForm I M ℝ (p + 1)) := φ.1.isSmoothForm.of_le (by simp)
    have hdφ : mextDeriv (φ.1 : RoughForm I M ℝ (p + 1)) = 0 := (mem_closedForms I _).mp φ.2
    exact (smoothHomologyPeriodHom_congr h hφ₁ hdφ (h ▸ hφ₁) (h ▸ hdφ)).trans
      (smoothHomologyPeriodHom_mextDeriv hθ₁ _ _)

/-- The **pairing of de Rham cohomology with integral smooth singular homology**: the periods
`smoothHomologyPeriodHom` of any closed form representing a de Rham class, as a linear map from
`H^p_dR(M)` to the homomorphisms `H_p^sm(M; ℤ) → ℝ`. -/
def smoothHomologyPeriod :
    deRhamCohomology I M p →ₗ[ℝ]
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p →+ ℝ :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M p)
    (M₂ := deRhamCohomology I M p)
    (M₃ := ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p →+ ℝ)
    (f := mk I (M := M) p) (mk_surjective I p)
    ⟨smoothHomologyPeriodClosedForms, ker_mk_le_ker_smoothHomologyPeriodClosedForms⟩

/-- The periods of the class of a closed form are those of the form. -/
@[simp]
theorem smoothHomologyPeriod_mk (φ : closedForms I M p) :
    smoothHomologyPeriod (mk I p φ) =
      smoothHomologyPeriodHom (φ.1 : RoughForm I M ℝ p) (φ.1.isSmoothForm.of_le (by simp))
        ((mem_closedForms I _).mp φ.2) :=
  LinearMap.equivOfSurjective_apply _ _

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 2 N]

/-- **Naturality of the pairing.** For a smooth map `f : M → N`, the pairing of the pullback
`f^* c` of a de Rham class `c` of `N` with a class `z ∈ H_p^sm(M; ℤ)` is the pairing of `c` with
the pushforward `f_* z`. -/
theorem smoothHomologyPeriod_map {f : M → N} (hf : ContMDiff I J ∞ f)
    (c : deRhamCohomology J N p)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p) :
    smoothHomologyPeriod (map f hf p c) z =
      smoothHomologyPeriod c
        ((SSet.homologyMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ) p).hom z) := by
  obtain ⟨ψ, rfl⟩ := mk_surjective J p c
  have hfψ : IsSmoothForm I 1 ((closedForms.mpullback f hf p ψ).1 : RoughForm I M ℝ p) :=
    (closedForms.mpullback f hf p ψ).1.isSmoothForm.of_le (by simp)
  have hdfψ := (mem_closedForms I _).mp (closedForms.mpullback f hf p ψ).2
  simp only [closedForms.coe_mpullback, SmoothForm.coe_mpullback] at hfψ hdfψ
  rw [map_mk, smoothHomologyPeriod_mk, smoothHomologyPeriod_mk,
    smoothHomologyPeriodHom_homologyMap hf _ _ hfψ hdfψ]
  exact DFunLike.congr_fun (smoothHomologyPeriodHom_congr (by simp) _ _ _ _) z

end deRhamCohomology

/-! ### The angular form of the circle -/

section Circle

/-- The standard loop `t ↦ exp (2π i t)` of the circle is smooth. -/
private theorem contMDiff_circleExp_two_pi_mul :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ fun t : ℝ ↦ Circle.exp (2 * Real.pi * t) :=
  contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff

/-- The standard loop `t ↦ exp (2π i t)` of the circle, as a smooth singular `1`-simplex. -/
def circleLoopSimplex : SmoothSimplex (𝓡 1) Circle 1 :=
  SmoothSimplex.ofCurve contMDiff_circleExp_two_pi_mul

/-- The standard loop of the circle is an integral smooth singular `1`-cycle: its two faces are
the same vertex `1`. -/
theorem d_ιChainComplex_circleLoopSimplex :
    (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom
      (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) circleLoopSimplex).hom 1) = 0 := by
  rw [← ConcreteCategory.comp_apply, SSet.ιChainComplex_d]
  simp [Fin.sum_univ_two, circleLoopSimplex]

/-- The homology class in `H₁^sm(S¹; ℤ)` of the standard loop `t ↦ exp (2π i t)`. -/
def circleLoopClass :
    ((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology 1 :=
  (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ 1).hom
    (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).moduleCatCyclesMk _ 0 (ChainComplex.next_nat_succ 0)
        d_ιChainComplex_circleLoopSimplex)

/-- **The period of `dθ` on the standard loop of the circle is `2π`.** In particular the pairing
of de Rham cohomology with integral smooth singular homology is nonzero on the circle. -/
theorem deRhamCohomology.smoothHomologyPeriod_mk_circleAngularClosedForm_circleLoopClass :
    deRhamCohomology.smoothHomologyPeriod (deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm)
      circleLoopClass = 2 * Real.pi := by
  rw [circleLoopClass, deRhamCohomology.smoothHomologyPeriod_mk, smoothHomologyPeriodHom_homologyπ,
    HomologicalComplex.iCycles_moduleCatCyclesMk, intIntegrationCochain_ιChainComplex, one_smul,
    coe_circleAngularClosedForm, circleLoopSimplex, SmoothSimplex.integral_ofCurve]
  have h := pathIntegral_comp_mul_add (isSmoothForm_circleAngularForm.of_le (by simp))
    (contMDiff_circleExp (m := 1)) (2 * Real.pi) 0 0 1
  simp only [add_zero, mul_zero, mul_one] at h
  rw [h, pathIntegral_circleAngularForm_circleExp, sub_zero]

end Circle

end TauCeti
