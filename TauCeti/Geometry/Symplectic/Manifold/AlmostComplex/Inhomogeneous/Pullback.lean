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
  `TauCeti.DomainDependentHomSection.mfderiv_tangentHom_pullback_apply`; it is the only section
  that `dg` carries to `A` (`TauCeti.DomainDependentHomSection.eq_pullback_iff`). Its identity
  and composition laws are `TauCeti.DomainDependentHomSection.pullback_refl` and
  `TauCeti.DomainDependentHomSection.pullback_trans`.
* `TauCeti.InhomogeneousTerm.pullback`: the pulled-back inhomogeneous term, whose underlying
  Hom section is the pulled-back Hom section (`TauCeti.InhomogeneousTerm.val_pullback`), with
  the characterisation `TauCeti.InhomogeneousTerm.eq_pullback_iff`. The identity and composition
  laws `TauCeti.InhomogeneousTerm.pullback_refl` and `TauCeti.InhomogeneousTerm.pullback_trans`
  use `ofEq` to identify the pulled-back target structures.
* `TauCeti.InhomogeneousTerm.mvfderiv_val_tangentHom_pullback`: the pointwise transport of values
  in charts of the targets, from which `TauCeti.InhomogeneousTerm.chartTerm_pullback`,
  `TauCeti.InhomogeneousTerm.chartTerm_pullback_trans`: transport in charts;
  `TauCeti.InhomogeneousTerm.chartTermExtend_pullback` and
  `TauCeti.InhomogeneousTerm.chartTermExtend_pullback_trans` in the extended charts of domains
  with boundary or corners.

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
        (⟨(p.proj.1, g p.proj.2), p.snd⟩ : TotalSpace EP (horizontalTangentBundle I' N IP P))) := by
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

/-- **Characterisation of the pullback.** `g^* A` is the only Hom section that the differentials
of `g` carry to `A`. -/
theorem eq_pullback_iff {B : DomainDependentHomSection I M IP P n} :
    B = A.pullback g hnr ↔ ∀ (q : P × M) (v : TangentSpace IP q.1),
      mfderiv I I' g q.2 (B.tangentHom q v) = A.tangentHom (q.1, g q.2) v := by
  refine ⟨fun hB q v ↦ hB ▸ mfderiv_tangentHom_pullback_apply g A hnr q v, fun hB ↦ ?_⟩
  have h (q : P × M) (v : TangentSpace IP q.1) :
      B.tangentHom q v = (A.pullback g hnr).tangentHom q v := by
    rw [tangentHom_pullback, ContinuousLinearMap.comp_apply, ← hB,
      (g.isInvertible_mfderiv (ENat.coe_ne_zero_of_add_one_le hnr)).inverse_apply_self]
  ext q v
  exact (tangentHom_apply B q v).symm.trans ((h q v).trans (tangentHom_apply _ q v))

/-- Pullback of a Hom section along the identity is the original section. -/
@[simp]
theorem pullback_refl (A : DomainDependentHomSection I M IP P n) (hnr : n + 1 ≤ r) :
    A.pullback (Diffeomorph.refl I M r) hnr = A := by
  refine ((eq_pullback_iff (Diffeomorph.refl I M r) A hnr).2 fun q v ↦ ?_).symm
  simp only [Diffeomorph.coe_refl, mfderiv_id]
  -- Reducing the identity base map also exposes the identity linear-map application.
  rfl

section Composition

variable {E'' H'' Q : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace Q] [ChartedSpace H'' Q] [IsManifold I'' ∞ Q]

/-- Pullback of a Hom section along a composite is the iterated pullback. -/
theorem pullback_trans (h : M ≃ₘ^r⟮I, I'⟯ N) (g : N ≃ₘ^r⟮I', I''⟯ Q)
    (A : DomainDependentHomSection I'' Q IP P n) (hnr : n + 1 ≤ r) :
    A.pullback (h.trans g) hnr = (A.pullback g hnr).pullback h hnr := by
  refine ((eq_pullback_iff (h.trans g) A hnr).2 fun q v ↦ ?_).symm
  have hchain (w : TangentSpace I q.2) :
      mfderiv I I'' (h.trans g) q.2 w =
        mfderiv I' I'' g (h q.2) (mfderiv I I' h q.2 w) :=
    mfderiv_comp_apply q.2
      (g.mdifferentiable (ENat.coe_ne_zero_of_add_one_le hnr) (h q.2))
      (h.mdifferentiable (ENat.coe_ne_zero_of_add_one_le hnr) q.2) w
  refine (hchain _).trans ((congrArg
    (fun w ↦ mfderiv I' I'' g (h q.2) w)
    (mfderiv_tangentHom_pullback_apply h (A.pullback g hnr) hnr q v)).trans ?_)
  exact (mfderiv_tangentHom_pullback_apply g A hnr (q.1, h q.2) v).trans
    (congrArg (fun y ↦ A.tangentHom (q.1, y) v)
      (congrFun (Diffeomorph.coe_trans h g) q.2).symm)

end Composition

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
  ⟨ν.val.pullback g hnr, (mem_inhomogeneousTerms_iff_tangentHom _ _ _).2 fun q w ↦ by
    apply (g.isInvertible_mfderiv (x := q.2)
      (ENat.coe_ne_zero_of_add_one_le hnr)).bijective.injective
    rw [map_neg, ContMDiffAlmostComplexStructureFamily.mfderiv_pullback_apply,
      DomainDependentHomSection.mfderiv_tangentHom_pullback_apply,
      DomainDependentHomSection.mfderiv_tangentHom_pullback_apply, ν.tangentHom_apply_j]⟩

/-- The underlying Hom section of the pulled-back term is the pullback of the Hom section. -/
@[simp]
theorem val_pullback (ν : InhomogeneousTerm j J) (g : M ≃ₘ^r⟮I, I'⟯ N) (hnr : n + 1 ≤ r) :
    (ν.pullback g hnr).val = ν.val.pullback g hnr :=
  (rfl)

/-- Pullback along the identity preserves a term after identifying its target structure. -/
@[simp]
theorem pullback_refl (ν : InhomogeneousTerm j J) (hnr : n + 1 ≤ r) :
    ν.pullback (Diffeomorph.refl I' N r) hnr =
      ν.ofEq rfl (ContMDiffAlmostComplexStructureFamily.pullback_refl J hnr).symm := by
  apply Subtype.ext
  simp only [ofEq_val, val_pullback, DomainDependentHomSection.pullback_refl]

section Composition

variable {E'' H'' Q : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace Q] [ChartedSpace H'' Q] [IsManifold I'' ∞ Q]

/-- Pullback along a composite agrees with iterated pullback after identifying target structures. -/
theorem pullback_trans (h : M ≃ₘ^r⟮I, I'⟯ N) (g : N ≃ₘ^r⟮I', I''⟯ Q)
    {K : ContMDiffAlmostComplexStructureFamily I'' Q IP P n}
    (ν : InhomogeneousTerm j K) (hnr : n + 1 ≤ r) :
    (ν.pullback (h.trans g) hnr).ofEq rfl
      (ContMDiffAlmostComplexStructureFamily.pullback_trans h g K hnr) =
        (ν.pullback g hnr).pullback h hnr := by
  apply Subtype.ext
  simp only [ofEq_val, val_pullback, DomainDependentHomSection.pullback_trans]

end Composition

variable (ν : InhomogeneousTerm j J) (g : M ≃ₘ^r⟮I, I'⟯ N) (hnr : n + 1 ≤ r)

/-- **Characterisation of the pullback.** `g^* ν` is the only inhomogeneous term for
`(j, g^* J)` that the differentials of `g` carry to `ν`. -/
theorem eq_pullback_iff {μ : InhomogeneousTerm j (J.pullback g hnr)} :
    μ = ν.pullback g hnr ↔ ∀ (q : P × M) (v : TangentSpace IP q.1),
      mfderiv I I' g q.2 (μ.val.tangentHom q v) = ν.val.tangentHom (q.1, g q.2) v := by
  rw [← Subtype.coe_inj, val_pullback, DomainDependentHomSection.eq_pullback_iff]

/-- The pullback of the zero term is zero. -/
@[simp]
theorem pullback_zero : (0 : InhomogeneousTerm j J).pullback g hnr = 0 :=
  ((eq_pullback_iff 0 g hnr).2 fun q v ↦ by simp).symm

/-- **Transport of values in charts.** Let `χ` be a chart of `M` and `ψ` a chart of `N` with
`χ = ψ ∘ g` and `χ⁻¹ = g⁻¹ ∘ ψ⁻¹`, such as `g ≫ ψ`. At a domain point `x`, on a vector `w`
tangent to the domain, the pulled-back term `g^* ν` at the point `χ⁻¹ v`, pushed forward along
`χ`, is `ν` at the point `ψ⁻¹ v`, pushed forward along `ψ`. -/
theorem mvfderiv_val_tangentHom_pullback {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {χ : OpenPartialHomeomorph M G} {ψ : OpenPartialHomeomorph N G} (hχ : ⇑χ = ψ ∘ g)
    (hχs : ⇑χ.symm = g.symm ∘ ψ.symm) (x : P) (w : TangentSpace IP x) (v : G) :
    mvfderiv I χ (χ.symm v) ((ν.pullback g hnr).val.tangentHom (x, χ.symm v) w) =
      mvfderiv I' ψ (ψ.symm v) (ν.val.tangentHom (x, ψ.symm v) w) := by
  have hr : (r : ℕ∞ω) ≠ 0 := ENat.coe_ne_zero_of_add_one_le hnr
  set y := g.symm (ψ.symm v) with hy_def
  have hy : g y = ψ.symm v := g.apply_symm_apply _
  rw [hχs, Function.comp_apply, ← hy_def, hχ, mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_apply_eq_mfderiv_apply, ← hy, g.mfderiv_comp_diffeomorph hr,
    ContinuousLinearMap.comp_apply]
  -- The base point `(x, y).2` of the pullback identity is `y` by definition.
  exact congrArg _ (DomainDependentHomSection.mfderiv_tangentHom_pullback_apply g ν.val hnr
    (x, y) w)

/-- **Transport in charts.** Let `χ` be a chart of `M` and `ψ` a chart of `N` with
`χ = ψ ∘ g` and `χ⁻¹ = g⁻¹ ∘ ψ⁻¹`, such as `g ≫ ψ`. Read in a chart `φ` of the domain and in
`χ`, the pulled-back term `g^* ν` is `ν` read in `φ` and `ψ`. -/
theorem chartTerm_pullback {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : OpenPartialHomeomorph P ℂ) {χ : OpenPartialHomeomorph M G}
    {ψ : OpenPartialHomeomorph N G} (hχ : ⇑χ = ψ ∘ g) (hχs : ⇑χ.symm = g.symm ∘ ψ.symm) :
    (ν.pullback g hnr).chartTerm φ χ = ν.chartTerm φ ψ := by
  funext z v
  rw [chartTerm_apply, chartTerm_apply, ν.mvfderiv_val_tangentHom_pullback g hnr hχ hχs]

/-- **Transport in charts.** Read in a chart `φ` of the domain and the chart `g ≫ ψ` of `M`, the
pulled-back term `g^* ν` is `ν` read in `φ` and `ψ`. -/
@[simp]
theorem chartTerm_pullback_trans {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : OpenPartialHomeomorph P ℂ) (ψ : OpenPartialHomeomorph N G) :
    (ν.pullback g hnr).chartTerm φ (g.toHomeomorph.toOpenPartialHomeomorph.trans ψ) =
      ν.chartTerm φ ψ :=
  ν.chartTerm_pullback g hnr φ rfl rfl

section Extend

variable {HQ Q : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ ℂ HQ} [TopologicalSpace Q]
  [ChartedSpace HQ Q] [IsManifold IQ ∞ Q] {jQ : ContMDiffAlmostComplexStructure IQ n Q}
  {JQ : ContMDiffAlmostComplexStructureFamily I' N IQ Q n}

/-- **Transport in extended charts.** Let `χ` be a chart of `M` and `ψ` a chart of `N` with
`χ = ψ ∘ g` and `χ⁻¹ = g⁻¹ ∘ ψ⁻¹`, such as `g ≫ ψ`. Read in the extended chart of a chart `φ` of a
domain `Q` modelled on `ℂ`, possibly with corners, and in `χ`, the pulled-back term `g^* ν` is `ν`
read in `φ` and `ψ`. -/
theorem chartTermExtend_pullback {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (νQ : InhomogeneousTerm jQ JQ) (φ : OpenPartialHomeomorph Q HQ)
    {χ : OpenPartialHomeomorph M G} {ψ : OpenPartialHomeomorph N G} (hχ : ⇑χ = ψ ∘ g)
    (hχs : ⇑χ.symm = g.symm ∘ ψ.symm) :
    (νQ.pullback g hnr).chartTermExtend φ χ = νQ.chartTermExtend φ ψ := by
  funext z v
  rw [chartTermExtend_apply, chartTermExtend_apply,
    νQ.mvfderiv_val_tangentHom_pullback g hnr hχ hχs]

/-- **Transport in extended charts.** Read in the extended chart of a chart `φ` of the domain and
in the chart `g ≫ ψ` of `M`, the pulled-back term `g^* ν` is `ν` read in `φ` and `ψ`. -/
@[simp]
theorem chartTermExtend_pullback_trans {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (νQ : InhomogeneousTerm jQ JQ) (φ : OpenPartialHomeomorph Q HQ)
    (ψ : OpenPartialHomeomorph N G) :
    (νQ.pullback g hnr).chartTermExtend φ (g.toHomeomorph.toOpenPartialHomeomorph.trans ψ) =
      νQ.chartTermExtend φ ψ :=
  chartTermExtend_pullback g hnr νQ φ rfl rfl

end Extend

end InhomogeneousTerm

end TauCeti
