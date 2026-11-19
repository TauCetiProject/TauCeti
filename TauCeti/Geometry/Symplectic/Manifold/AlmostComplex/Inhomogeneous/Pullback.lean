/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Chart
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Pulling back inhomogeneous terms along diffeomorphisms of the target

Let `g : M → N` be a `Cʳ` diffeomorphism, where `M` and `N` may be modelled on different spaces,
and `A` a jointly `Cⁿ` section, over `P × N`, of the bundle of linear maps from the tangent spaces
of `P` to those of `N`, with `n + 1 ≤ r`. Its pullback `(p, x) ↦ (dg_x)⁻¹ ∘ A(p, g x)` is again a
jointly `Cⁿ` section, now over `P × M`
(`TauCeti.DomainDependentHomSection.pullback`). Regularity is read on total spaces: the
pulled-back section moves a vector tangent to `P` at `p` to `A(p, g x)` of it, tangent to `N`
at `g x`, and then applies the tangent map of `g⁻¹`, which is `Cⁿ` since `n + 1 ≤ r`.

For an inhomogeneous term `ν` for a structure `j` on `P` and a domain-dependent structure `J` on
`N`, the pullback is an inhomogeneous term `g^* ν` for `j` and the pulled-back structure `g^* J`
(`TauCeti.InhomogeneousTerm.pullback`): complex antilinearity is transported because `dg`
intertwines `g^* J` with `J`. Read in a chart `φ` of `P` and the chart `g ≫ ψ` of `M`, the term
`g^* ν` is `ν` read in `φ` and `ψ` (`TauCeti.InhomogeneousTerm.chartTerm_pullback_trans`).

## Main declarations

* `TauCeti.DomainDependentHomSection.pullback`: the pulled-back Hom section, with
  `TauCeti.DomainDependentHomSection.mfderiv_tangentHom_pullback_apply`.
* `TauCeti.InhomogeneousTerm.pullback`: the pulled-back inhomogeneous term, whose underlying
  Hom section is the pulled-back Hom section (`TauCeti.InhomogeneousTerm.val_pullback`).
* `TauCeti.InhomogeneousTerm.chartTerm_pullback`,
  `TauCeti.InhomogeneousTerm.chartTerm_pullback_trans`: transport in charts.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (inhomogeneous Cauchy--Riemann equations).
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M E' H' N EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
  {n r : ℕ∞}

namespace DomainDependentHomSection

/-- The field `(p, x) ↦ (dg_x)⁻¹ ∘ A(p, g x)` underlying the pullback of a Hom section. -/
private def pullbackField (g : M ≃ₘ^r⟮I, I'⟯ N) (A : DomainDependentHomSection I' N IP P n)
    (q : P × M) : TangentSpace IP q.1 →L[ℝ] TangentSpace I q.2 :=
  (mfderiv I I' g q.2).inverse ∘L A.tangentHom (q.1, g q.2)

/-- The field `(p, x) ↦ (dg_x)⁻¹ ∘ A(p, g x)` is a jointly `Cⁿ` Hom section when `n + 1 ≤ r`. -/
private theorem contMDiff_pullbackField (g : M ≃ₘ^r⟮I, I'⟯ N)
    (A : DomainDependentHomSection I' N IP P n) (hnr : n + 1 ≤ r) :
    ContMDiff (IP.prod I) ((IP.prod I).prod 𝓘(ℝ, EP →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (EP →L[ℝ] E)
        (E := fun q : P × M ↦ horizontalTangentBundle I M IP P q →L[ℝ]
          verticalTangentBundle I M IP P q) q (pullbackField g A q)) := by
  refine (TauCeti.contMDiff_hom_bundle_iff (E₁ := horizontalTangentBundle I M IP P)
    (E₂ := verticalTangentBundle I M IP P) (pullbackField g A)).2 ?_
  have hr : (r : ℕ∞ω) ≠ 0 := ENat.coe_ne_zero_of_add_one_le hnr
  have hnr' : (n : ℕ∞ω) + 1 ≤ r := by exact_mod_cast hnr
  have hg : ContMDiff I I' n g := g.contMDiff.of_le (le_trans le_self_add hnr')
  -- Move a horizontal vector at `(p, x)` to `(p, g x)`.
  have hS : ContMDiff ((IP.prod I).prod 𝓘(ℝ, EP)) ((IP.prod I').prod 𝓘(ℝ, EP)) n
      (fun p : TotalSpace EP (horizontalTangentBundle I M IP P) ↦
        (⟨(p.proj.1, g p.proj.2), p.2⟩ : TotalSpace EP (horizontalTangentBundle I' N IP P))) := by
    refine (Bundle.Pullback.contMDiff_iff
      (ContMDiffMap.fst : C^∞⟮IP.prod I', P × N; IP, P⟯) contMDiff_fst).2 ⟨?_, ?_⟩
    · exact (contMDiff_fst.comp (contMDiff_proj _)).prodMk
        (hg.comp (contMDiff_snd.comp (contMDiff_proj _)))
    · exact Bundle.Pullback.contMDiff_lift
        (ContMDiffMap.fst : C^∞⟮IP.prod I, P × M; IP, P⟯) contMDiff_fst
  -- Apply `A` there, as a vector tangent to `N` at `g x`.
  have hA := (TauCeti.contMDiff_hom_bundle_iff (E₁ := horizontalTangentBundle I' N IP P)
    (E₂ := verticalTangentBundle I' N IP P) A.tangentHom).1 A.contMDiff_tangentHom
  have hT := (Bundle.Pullback.contMDiff_lift
    (ContMDiffMap.snd : C^∞⟮IP.prod I', P × N; I', N⟯) contMDiff_snd).comp (hA.comp hS)
  have hti := g.symm.contMDiff.contMDiff_tangentMap (m := (n : ℕ∞ω)) hnr'
  refine (Bundle.Pullback.contMDiff_iff
    (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) contMDiff_snd).2
      ⟨contMDiff_proj _, (hti.comp hT).congr fun p ↦ ?_⟩
  exact (g.tangentMap_symm_mk hr p.proj.2 _).symm

/-- The pullback of a Hom section along a `Cʳ` diffeomorphism `g : M → N` of the targets with
`n + 1 ≤ r`: at `(p, x)` it is `(dg_x)⁻¹ ∘ A(p, g x)`. -/
def pullback (g : M ≃ₘ^r⟮I, I'⟯ N) (A : DomainDependentHomSection I' N IP P n)
    (hnr : n + 1 ≤ r) : DomainDependentHomSection I M IP P n :=
  ⟨pullbackField g A, contMDiff_pullbackField g A hnr⟩

variable (g : M ≃ₘ^r⟮I, I'⟯ N) (A : DomainDependentHomSection I' N IP P n) (hnr : n + 1 ≤ r)

/-- The pulled-back section at `(p, x)` is `(dg_x)⁻¹ ∘ A(p, g x)`. -/
theorem tangentHom_pullback (q : P × M) :
    (A.pullback g hnr).tangentHom q =
      (mfderiv I I' g q.2).inverse ∘L A.tangentHom (q.1, g q.2) := by
  ext v
  rw [tangentHom_apply]
  -- The pulled-back section is the field `pullbackField` by definition.
  rfl

/-- The differential of `g` carries the pulled-back section to the original one. -/
@[simp]
theorem mfderiv_tangentHom_pullback_apply (q : P × M) (v : TangentSpace IP q.1) :
    mfderiv I I' g q.2 ((A.pullback g hnr).tangentHom q v) = A.tangentHom (q.1, g q.2) v := by
  rw [tangentHom_pullback, ContinuousLinearMap.comp_apply]
  exact (g.isInvertible_mfderiv (ENat.coe_ne_zero_of_add_one_le hnr)).self_apply_inverse _

end DomainDependentHomSection

namespace InhomogeneousTerm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I' N IP P n}

/-- The pullback `g^* ν` of an inhomogeneous term for `(j, J)` along a `Cʳ` diffeomorphism
`g : M → N` of the targets with `n + 1 ≤ r`, an inhomogeneous term for `(j, g^* J)`: at
`(p, x)` it is `(dg_x)⁻¹ ∘ ν(p, g x)`. -/
def pullback (ν : InhomogeneousTerm j J) (g : M ≃ₘ^r⟮I, I'⟯ N) (hnr : n + 1 ≤ r) :
    InhomogeneousTerm j (J.pullback g hnr) :=
  ⟨ν.val.pullback g hnr, (mem_inhomogeneousTerms _ _ _).2 fun q ↦ by
    apply isComplexAntilinear_of_apply
    intro v
    have hinj := (g.isInvertible_mfderiv (x := q.2)
      (ENat.coe_ne_zero_of_add_one_le hnr)).bijective.injective
    have key (w : TangentSpace IP q.1) : (ν.val.pullback g hnr).tangentHom q (j q.1 w) =
        -(J.pullback g hnr).tangentEndomorphism q ((ν.val.pullback g hnr).tangentHom q w) := by
      apply hinj
      rw [map_neg, ContMDiffAlmostComplexStructureFamily.mfderiv_pullback_apply,
        DomainDependentHomSection.mfderiv_tangentHom_pullback_apply,
        DomainDependentHomSection.mfderiv_tangentHom_pullback_apply, ν.tangentHom_apply_j]
    have h := key v
    erw [DomainDependentHomSection.tangentHom_apply, DomainDependentHomSection.tangentHom_apply,
      ContMDiffAlmostComplexStructureFamily.tangentEndomorphism_apply] at h
    simp only [ContinuousLinearMap.coe_coe]
    erw [ContMDiffAlmostComplexStructure.horizontalEndomorphism_apply]
    exact h⟩

/-- The underlying Hom section of the pulled-back term is the pullback of the Hom section. -/
@[simp]
theorem val_pullback (ν : InhomogeneousTerm j J) (g : M ≃ₘ^r⟮I, I'⟯ N) (hnr : n + 1 ≤ r) :
    (ν.pullback g hnr).val = ν.val.pullback g hnr :=
  (rfl)

omit [FiniteDimensional ℝ EP] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Two terms are equal when their readings in the tangent spaces agree. -/
private theorem ext_tangentHom {J' : ContMDiffAlmostComplexStructureFamily I M IP P n}
    {ν₁ ν₂ : InhomogeneousTerm j J'}
    (h : ∀ q v, ν₁.val.tangentHom q v = ν₂.val.tangentHom q v) : ν₁ = ν₂ :=
  InhomogeneousTerm.ext fun q v ↦ (DomainDependentHomSection.tangentHom_apply _ q v).symm.trans
    ((h q v).trans (DomainDependentHomSection.tangentHom_apply _ q v))

/-- The pullback of the zero term is zero. -/
@[simp]
theorem pullback_zero (g : M ≃ₘ^r⟮I, I'⟯ N) (hnr : n + 1 ≤ r) :
    (0 : InhomogeneousTerm j J).pullback g hnr = 0 :=
  ext_tangentHom fun q v ↦ by simp [DomainDependentHomSection.tangentHom_pullback]

variable (ν : InhomogeneousTerm j J) (g : M ≃ₘ^r⟮I, I'⟯ N) (hnr : n + 1 ≤ r)

/-- The differential of `g` carries the pulled-back term to the original one (`simp` proves it
from `TauCeti.InhomogeneousTerm.val_pullback`). -/
theorem mfderiv_tangentHom_pullback_apply (q : P × M) (v : TangentSpace IP q.1) :
    mfderiv I I' g q.2 ((ν.pullback g hnr).val.tangentHom q v) = ν.val.tangentHom (q.1, g q.2) v :=
  DomainDependentHomSection.mfderiv_tangentHom_pullback_apply g ν.val hnr q v

/-- **Transport in charts.** Let `χ` be a chart of `M` and `ψ` a chart of `N` with
`χ = ψ ∘ g` and `χ⁻¹ = g⁻¹ ∘ ψ⁻¹`, such as `g ≫ ψ`. Read in a chart `φ` of the domain and in
`χ`, the pulled-back term `g^* ν` is `ν` read in `φ` and `ψ`. -/
theorem chartTerm_pullback {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : OpenPartialHomeomorph P ℂ) {χ : OpenPartialHomeomorph M G}
    {ψ : OpenPartialHomeomorph N G} (hχ : ⇑χ = ψ ∘ g) (hχs : ⇑χ.symm = g.symm ∘ ψ.symm) :
    (ν.pullback g hnr).chartTerm φ χ = ν.chartTerm φ ψ := by
  have hr : (r : ℕ∞ω) ≠ 0 := ENat.coe_ne_zero_of_add_one_le hnr
  funext z v
  set y := g.symm (ψ.symm v) with hy_def
  have hy : g y = ψ.symm v := g.apply_symm_apply _
  rw [chartTerm_apply, chartTerm_apply, hχs, Function.comp_apply, ← hy_def, hχ,
    mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, ← hy]
  -- Where `ψ` is not differentiable, neither is `ψ ∘ g`, and both sides vanish.
  by_cases hψ : MDifferentiableAt I' 𝓘(ℝ, G) ψ (g y)
  swap
  · have hψg : ¬MDifferentiableAt I 𝓘(ℝ, G) (ψ ∘ g) y := by
      rwa [g.mdifferentiableAt_comp_diffeomorph_iff hr]
    rw [mfderiv_zero_of_not_mdifferentiableAt hψ, mfderiv_zero_of_not_mdifferentiableAt hψg]
    rfl
  have h := ν.mfderiv_tangentHom_pullback_apply g hnr (φ.symm z, y)
    (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ))
  rw [mfderiv_comp_apply y hψ (g.mdifferentiable hr y)]
  -- `h` is stated at the base point `(φ.symm z, y).2`, which is `y` by definition.
  erw [h]

/-- **Transport in charts.** Read in a chart `φ` of the domain and the chart `g ≫ ψ` of `M`, the
pulled-back term `g^* ν` is `ν` read in `φ` and `ψ`. -/
@[simp]
theorem chartTerm_pullback_trans {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : OpenPartialHomeomorph P ℂ) (ψ : OpenPartialHomeomorph N G) :
    (ν.pullback g hnr).chartTerm φ (g.toHomeomorph.toOpenPartialHomeomorph.trans ψ) =
      ν.chartTerm φ ψ :=
  ν.chartTerm_pullback g hnr φ rfl rfl

end InhomogeneousTerm

end TauCeti
