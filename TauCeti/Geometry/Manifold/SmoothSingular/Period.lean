/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Stokes
public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Algebra.Homology.Kronecker

/-!
# Periods of closed forms on integral smooth singular homology

A closed `C¹` `p`-form `φ` on a `C²` manifold `M`, with values in a real normed space `F`, can be
integrated over the smooth singular `p`-chains of `M` with coefficients in any ring `R` acting on
`F` (`TauCeti.integrationCochain`); with **integer** coefficients the chain `∑ nᵢ σᵢ` integrates
to `∑ nᵢ ∫_{σᵢ} φ`. By Stokes' theorem the integral of `φ` over a boundary `∂c` is the integral of
`dφ = 0` over `c` (`TauCeti.d_comp_integrationCochain`), so it descends to an `R`-linear map

`TauCeti.smoothHomologyPeriodHom φ : H_p^sm(M; R) →ₗ[R] F`

from the smooth singular homology of `M`, the **periods** of `φ`. Exact forms have vanishing
periods (`TauCeti.smoothHomologyPeriodHom_mextDeriv`), and the periods are natural under smooth
maps: those of a pullback `f^* ψ` are those of `ψ` on the pushforward classes
(`TauCeti.smoothHomologyPeriodHom_homologyMap`). For smooth real forms they therefore only depend
on the de Rham class, and with integer coefficients give the **pairing of de Rham cohomology with
integral smooth singular homology** (`TauCeti.deRhamCohomology.smoothHomologyPeriod`), a linear map

`H^p_dR(M) →ₗ[ℝ] (H_p^sm(M; ℤ) →+ ℝ)`,

natural in smooth maps (`TauCeti.deRhamCohomology.smoothHomologyPeriod_map`). The periods are the
Kronecker evaluation (`TauCeti.ChainComplex.kronecker`) of the class of the cocycle
`TauCeti.integrationCochain φ`. That the pairing is not trivial, the angular form of the circle
having period `2π` on the standard loop, is shown in
`TauCeti.Geometry.Manifold.SmoothSingular.Circle`.

The real-coefficient cochain-level counterpart is `TauCeti.deRhamCohomology.integration`, which
sends a de Rham class to a class in smooth singular cohomology with real coefficients. Integer
coefficients are what is needed to pair a closed form with integral homology classes, such as the
area `ω(A)` of a class `A ∈ H₂(M; ℤ)` of a symplectic manifold `(M, ω)`. Through the comparison of
smooth and ordinary singular homology this becomes a homomorphism on `H_p(M; ℤ)`; that comparison
is not used here.

## Main definitions

* `TauCeti.smoothHomologyPeriodHom φ`: the periods of a closed `C¹` form on `H_p^sm(M; R)`,
  and `0` for other forms.
* `TauCeti.deRhamCohomology.smoothHomologyPeriod`: the periods of de Rham classes, a linear map
  `H^p_dR(M) →ₗ[ℝ] (H_p^sm(M; ℤ) →+ ℝ)`.

## Main results

* `TauCeti.smoothHomologyPeriodHom_homologyπ`: the period on the class of a cycle is the integral
  over the cycle.
* `TauCeti.smoothHomologyPeriodHom_mextDeriv`,
  `TauCeti.smoothHomologyPeriodHom_eq_zero_of_mem_exactForms`: exact forms have vanishing periods.
* `TauCeti.smoothHomologyPeriodHom_homologyMap`: naturality under smooth maps, from the
  naturality of the class of the integration cocycle
  (`TauCeti.homologyMap_homologyClassOfComp_integrationCochain`).
* `TauCeti.deRhamCohomology.smoothHomologyPeriod_mk`,
  `TauCeti.deRhamCohomology.smoothHomologyPeriod_map`: the class-level pairing and its
  naturality.

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

/-! ### Periods on smooth singular homology -/

section Period

variable [IsManifold I 2 M] {R : Type} [Ring R] [Module R F]

/-- Stokes' theorem for the integration cochain of a closed form, with the source degree of the
differential written as the successor of `p` in the shape of the dual cochain complex, as
`TauCeti.ChainComplex.homologyClassOfComp` takes it. -/
theorem d_next_comp_integrationCochain_eq_zero {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).d
      ((ComplexShape.up ℕ).next p) p ≫ integrationCochain φ = 0 := by
  rw [CochainComplex.next ℕ p]
  exact d_comp_integrationCochain_eq_zero hφ hdφ

open Classical in
/-- The **periods** of a closed `C¹` `p`-form `φ` on the smooth singular homology of `M` with
coefficients in `R`: the integral of `φ` over smooth singular `p`-cycles, which only depends on
their homology classes by Stokes' theorem. It is the Kronecker evaluation of the class of the
cocycle `TauCeti.integrationCochain φ`, and `0` when `φ` is not a closed `C¹` form. -/
def smoothHomologyPeriodHom (φ : RoughForm I M F p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).homology p →ₗ[R] F :=
  if h : IsSmoothForm I 1 φ ∧ mextDeriv φ = 0 then
    (ChainComplex.kronecker ℤ
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R))
      (ModuleCat.of R F) p (ChainComplex.homologyClassOfComp ℤ (ModuleCat.of R F)
        (integrationCochain φ) (d_next_comp_integrationCochain_eq_zero h.1 h.2) (𝟙 _))).hom
  else 0

/-- The periods of a closed `C¹` form are the Kronecker evaluation of the class of its
integration cocycle. -/
theorem smoothHomologyPeriodHom_of_isSmoothForm {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    smoothHomologyPeriodHom (R := R) φ =
      (ChainComplex.kronecker ℤ
        ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R))
        (ModuleCat.of R F) p (ChainComplex.homologyClassOfComp ℤ (ModuleCat.of R F)
          (integrationCochain φ) (d_next_comp_integrationCochain_eq_zero hφ hdφ) (𝟙 _))).hom :=
  dite_eq_left ⟨hφ, hdφ⟩

/-- The period on the homology class of a cycle `∑ nᵢ σᵢ` is `∑ nᵢ ∫_{σᵢ} φ`. -/
@[simp]
theorem smoothHomologyPeriodHom_homologyπ {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).cycles p) :
    smoothHomologyPeriodHom φ
        ((((smoothSingularSubcomplex I M : SSet).chainComplex
          (ModuleCat.of R R)).homologyπ p).hom z) =
      (integrationCochain φ).hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex
          (ModuleCat.of R R)).iCycles p).hom z) := by
  rw [smoothHomologyPeriodHom_of_isSmoothForm hφ hdφ]
  exact ConcreteCategory.congr_hom
    (ChainComplex.homologyπ_kronecker_homologyClassOfComp _ _ (𝟙 _)) z

/-- The periods of a `p`-form which is not a closed `C¹` form are `0` by convention. -/
theorem smoothHomologyPeriodHom_undef {φ : RoughForm I M F p}
    (h : ¬(IsSmoothForm I 1 φ ∧ mextDeriv φ = 0)) :
    smoothHomologyPeriodHom (R := R) φ = 0 :=
  dite_eq_right h

/-- **Exact forms have vanishing periods.** For a `C¹` form `θ`, the periods of `dθ` on smooth
singular homology vanish. -/
theorem smoothHomologyPeriodHom_mextDeriv {θ : RoughForm I M F p} (hθ : IsSmoothForm I 1 θ) :
    smoothHomologyPeriodHom (R := R) (mextDeriv θ) = 0 := by
  by_cases h : IsSmoothForm I 1 (mextDeriv θ) ∧ mextDeriv (mextDeriv θ) = 0
  swap
  · exact smoothHomologyPeriodHom_undef h
  refine HomologicalComplex.moduleCat_linearMap_ext_homologyπ fun z ↦ ?_
  -- the integral of `dθ` over a cycle is the integral of `θ` over its boundary, which is zero
  rw [smoothHomologyPeriodHom_homologyπ h.1 h.2, LinearMap.zero_apply,
    ← d_comp_integrationCochain hθ]
  simp

/-- **Exact smooth real forms have vanishing periods.** -/
theorem smoothHomologyPeriodHom_eq_zero_of_mem_exactForms [Module R ℝ] {φ : SmoothForm I M ℝ p}
    (hφ : φ ∈ exactForms I M p) : smoothHomologyPeriodHom (R := R) (φ : RoughForm I M ℝ p) = 0 := by
  cases p with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ
    subst hφ
    refine HomologicalComplex.moduleCat_linearMap_ext_homologyπ fun z ↦ ?_
    rw [smoothHomologyPeriodHom_homologyπ ((0 : SmoothForm I M ℝ 0).isSmoothForm.of_le (by simp))
      (by simp)]
    simp
  | succ p =>
    rw [exactForms_succ, LinearMap.mem_range] at hφ
    obtain ⟨θ, rfl⟩ := hφ
    rw [mextDerivₗ_apply, smoothHomologyPeriodHom_mextDeriv (θ.isSmoothForm.of_le (by simp))]

/-- The periods are additive in the closed form. -/
theorem smoothHomologyPeriodHom_add {φ ψ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (hψ : IsSmoothForm I 1 ψ) (hdψ : mextDeriv ψ = 0) :
    smoothHomologyPeriodHom (R := R) (φ + ψ) =
      smoothHomologyPeriodHom φ + smoothHomologyPeriodHom ψ := by
  have hdφψ : mextDeriv (φ + ψ) = 0 := by rw [hφ.mextDeriv_add hψ, hdφ, hdψ, add_zero]
  refine HomologicalComplex.moduleCat_linearMap_ext_homologyπ fun z ↦ ?_
  simp [smoothHomologyPeriodHom_homologyπ (hφ.add hψ) hdφψ,
    smoothHomologyPeriodHom_homologyπ hφ hdφ, smoothHomologyPeriodHom_homologyπ hψ hdψ,
    integrationCochain_add (hφ.of_le (by simp)) (hψ.of_le (by simp))]

/-- The periods are homogeneous in the closed form. -/
theorem smoothHomologyPeriodHom_smul [SMulCommClass R ℝ F] (a : ℝ) {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    smoothHomologyPeriodHom (R := R) (a • φ) = a • smoothHomologyPeriodHom φ := by
  refine HomologicalComplex.moduleCat_linearMap_ext_homologyπ fun z ↦ ?_
  simp [smoothHomologyPeriodHom_homologyπ (hφ.smul a) (by simp [hdφ]),
    smoothHomologyPeriodHom_homologyπ hφ hdφ]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 2 N]

/-- The pullback along a smooth map `f : M → N` of the class of the integration cocycle of a
closed `C¹` form `ψ` on `N` is the class of the integration cocycle of `f^* ψ`. -/
theorem homologyMap_homologyClassOfComp_integrationCochain {f : M → N} (hf : ContMDiff I J ∞ f)
    {ψ : RoughForm J N F p} (hψ : IsSmoothForm J 1 ψ) (hdψ : mextDeriv ψ = 0) :
    HomologicalComplex.homologyMap
      (K := ((smoothSingularSubcomplex J N : SSet).chainComplex
        (ModuleCat.of R R)).linearYonedaObj ℤ (ModuleCat.of R F))
      (L := ((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of R R)).linearYonedaObj ℤ (ModuleCat.of R F))
      ((ChainComplex.linearYonedaFunctor ℤ (ModuleCat.of R F)).map
        (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of R R)).op) p
      (ChainComplex.homologyClassOfComp ℤ (ModuleCat.of R F)
          (integrationCochain ψ) (d_next_comp_integrationCochain_eq_zero hψ hdψ) (𝟙 _)) =
      ChainComplex.homologyClassOfComp ℤ (ModuleCat.of R F) (integrationCochain (mpullback I J f ψ))
        (d_next_comp_integrationCochain_eq_zero (hψ.mpullback (hf.of_le (by simp)))
          (hψ.mextDeriv_mpullback_eq_zero hdψ (hf.of_le (by simp)))) (𝟙 _) := by
  rw [ChainComplex.homologyClassOfComp_eq _ _ _ _ (ChainComplex.iCycles_cocycleOfComp _
      (d_next_comp_integrationCochain_eq_zero hψ hdψ) _),
    ChainComplex.homologyMap_linearYonedaFunctor_map_homologyπ_apply]
  refine (ChainComplex.homologyClassOfComp_eq (integrationCochain (mpullback I J f ψ)) _ (𝟙 _) _
    ?_).symm
  rw [ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply,
    ChainComplex.iCycles_cocycleOfComp, ← integrationCochain_naturality hf, Category.assoc]

/-- **Naturality of the periods.** For a smooth map `f : M → N` and a closed `C¹` form `ψ` on `N`,
the period of `ψ` on the pushforward `f_* c` of a class `c ∈ H_p^sm(M; R)` is the period of the
pullback `f^* ψ` on `c`. -/
theorem smoothHomologyPeriodHom_homologyMap {f : M → N} (hf : ContMDiff I J ∞ f)
    {ψ : RoughForm J N F p} (hψ : IsSmoothForm J 1 ψ) (hdψ : mextDeriv ψ = 0)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).homology p) :
    smoothHomologyPeriodHom ψ
        ((SSet.homologyMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of R R) p).hom c) =
      smoothHomologyPeriodHom (mpullback I J f ψ) c := by
  have hfψ : IsSmoothForm I 1 (mpullback I J f ψ) := hψ.mpullback (hf.of_le (by simp))
  have hdfψ : mextDeriv (mpullback I J f ψ) = 0 :=
    hψ.mextDeriv_mpullback_eq_zero hdψ (hf.of_le (by simp))
  have h := ConcreteCategory.congr_hom (ChainComplex.kronecker_naturality
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of R R)) p
    (ChainComplex.homologyClassOfComp ℤ (ModuleCat.of R F) (integrationCochain ψ)
      (d_next_comp_integrationCochain_eq_zero hψ hdψ) (𝟙 _))) c
  rw [homologyMap_homologyClassOfComp_integrationCochain hf hψ hdψ] at h
  rw [smoothHomologyPeriodHom_of_isSmoothForm hψ hdψ,
    smoothHomologyPeriodHom_of_isSmoothForm hfψ hdfψ]
  exact h.symm

end Period

/-! ### The pairing of de Rham cohomology with integral smooth singular homology -/

namespace deRhamCohomology

variable [IsManifold I 2 M]

/-- The periods on integral smooth singular homology of closed smooth real forms, as a linear
map. -/
private def smoothHomologyPeriodClosedForms : closedForms I M p →ₗ[ℝ]
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p →+ ℝ where
  toFun φ := (smoothHomologyPeriodHom (φ.val : RoughForm I M ℝ p)).toAddMonoidHom
  map_add' φ ψ := congrArg LinearMap.toAddMonoidHom (smoothHomologyPeriodHom_add
    (φ.val.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp φ.property)
    (ψ.val.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp ψ.property))
  map_smul' a φ := congrArg LinearMap.toAddMonoidHom (smoothHomologyPeriodHom_smul a
    (φ.val.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp φ.property))

/-- The periods of closed smooth real forms evaluate to the periods of the underlying form. -/
private theorem smoothHomologyPeriodClosedForms_apply (φ : closedForms I M p) :
    smoothHomologyPeriodClosedForms φ =
      (smoothHomologyPeriodHom (φ.val : RoughForm I M ℝ p)).toAddMonoidHom :=
  (rfl)

/-- Exact forms have vanishing periods on integral smooth singular homology. -/
private theorem ker_mk_le_ker_smoothHomologyPeriodClosedForms :
    LinearMap.ker (mk I (M := M) p) ≤
      LinearMap.ker (smoothHomologyPeriodClosedForms (I := I) (M := M) (p := p)) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  refine AddMonoidHom.ext fun z ↦ ?_
  simp [smoothHomologyPeriodClosedForms_apply, smoothHomologyPeriodHom_eq_zero_of_mem_exactForms hφ]

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
      (smoothHomologyPeriodHom (φ.val : RoughForm I M ℝ p)).toAddMonoidHom :=
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
  simp [smoothHomologyPeriodHom_homologyMap hf (ψ.val.isSmoothForm.of_le (by simp))
    ((mem_closedForms J _).mp ψ.property)]

end deRhamCohomology

end TauCeti
