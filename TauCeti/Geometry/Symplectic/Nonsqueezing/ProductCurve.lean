/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Analysis.Complex.RiemannSurface.MappingDegree
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.RiemannSphere
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Torus.AlmostComplex

/-!
# The class-`A` spheres of `S²(a) × T` for the product structure

Gromov's proof of the nonsqueezing theorem counts pseudoholomorphic spheres in the class
`A = [S² × pt]` of the product `S²(a) × T` of the Riemann sphere `OnePoint ℂ`, with `a` times its
Fubini–Study form, and a torus `T = ∀ i : ι ⊕ ι, AddCircle (p i)` with its standard symplectic form
`ω_T`. For the product `J = i × J_T` of the complex structure of the sphere and the standard
structure of the torus (`TauCeti.SmoothAlmostComplexStructure.prod`,
`TauCeti.torusAlmostComplexStructure`), this file identifies these spheres: they are exactly the
maps `z ↦ (g • z, t)` for a Möbius transformation `g ∈ GL(2, ℂ)` and a point `t ∈ T`.

Let `u : OnePoint ℂ → S² × T` be smooth and pseudoholomorphic for `J`. Its components are
pseudoholomorphic (`TauCeti.SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff`).

* The torus component is constant, for any almost complex structure on the first factor and any
  `ω_T`-tame one on the torus
  (`TauCeti.snd_apply_eq_of_isPseudoholomorphic_prod_of_tames_torusSymplecticForm`): the sphere is
  simply connected, so the torus component has zero area, and hence zero energy
  (`TauCeti.apply_eq_of_isPseudoholomorphic_of_tames_torusSymplecticForm`).
* The sphere component is a holomorphic map of the Riemann sphere, and it has mapping degree one
  exactly when it is a Möbius transformation
  (`MDifferentiable.degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul`).

So `u` has sphere component of degree one exactly when `u = (g • ·, t)`
(`TauCeti.degree_fst_comp_eq_one_iff_exists_smul`), and every such map is smooth and
pseudoholomorphic (`TauCeti.contMDiff_smul_prodMk_const`,
`TauCeti.isPseudoholomorphic_smul_prodMk_const`, stated for any target `M` in place of `T`). The
class of `u` is read off from its area: by
`TauCeti.integralTopForm_mpullback_prod_torusSymplecticForm_eq_degree_mul` the area
`∫ u^*(pr₁^*(a • ω_FS) + pr₂^*ω_T)` is `a` times the degree of the sphere component, so for
`a ≠ 0` the spheres of area `a` are exactly the maps `(g • ·, t)`
(`TauCeti.integralTopForm_mpullback_eq_iff_exists_smul`).

## Main results

* `TauCeti.snd_apply_eq_of_isPseudoholomorphic_prod_of_tames_torusSymplecticForm`: the torus
  component of a pseudoholomorphic sphere in `P × T` is constant.
* `TauCeti.degree_fst_comp_eq_one_iff_exists_smul`: a pseudoholomorphic sphere has sphere
  component of degree one exactly when it is `z ↦ (g • z, t)`.
* `TauCeti.integralTopForm_mpullback_eq_iff_exists_smul`: the same with the area `a` in place of
  the degree.
* `TauCeti.contMDiff_smul_prodMk_const`, `TauCeti.isPseudoholomorphic_smul_prodMk_const`: the maps
  `z ↦ (g • z, t)` into `S² × M` are smooth and pseudoholomorphic.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §0.3.A (the nonsqueezing theorem, proved through `S² × T^(2n-2)`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 9.3 (the proof of the nonsqueezing theorem).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

variable {ι : Type*} [Fintype ι] {p : ι ⊕ ι → ℝ} [∀ i, Fact (0 < p i)]
  {u : OnePoint ℂ → OnePoint ℂ × ∀ i, AddCircle (p i)}

/-- **The torus component of a pseudoholomorphic sphere in `P × T` is constant.** Let `P` be a
manifold with an almost complex structure `J`, and let `K` be an almost complex structure on the
torus tamed by `ω_T`, such as the standard one. A smooth map `v : OnePoint ℂ → P × T`,
pseudoholomorphic for the product of `J` and `K`, has constant torus component. -/
theorem snd_apply_eq_of_isPseudoholomorphic_prod_of_tames_torusSymplecticForm {E H P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    {J : SmoothAlmostComplexStructure I P}
    {K : SmoothAlmostComplexStructure (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))}
    {v : OnePoint ℂ → P × ∀ i, AddCircle (p i)}
    (hv : ContMDiff 𝓘(ℝ, ℂ) (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) ∞ v)
    (hK : (torusSymplecticForm p).Tames K)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      (J.prod K) v)
    (z z' : OnePoint ℂ) : (v z).2 = (v z').2 :=
  apply_eq_of_isPseudoholomorphic_of_tames_torusSymplecticForm p
    (o := (complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
    (SmoothAlmostComplexStructure.orientation_eq_orientationAt_of_apply_one_eq_ofComplexManifold _)
    (contMDiff_snd.comp hv) hK
    (SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff.1 hhol).2 z z'

/-- **The class-`A` spheres of `S² × T` for the product structure.** A smooth map
`u : OnePoint ℂ → S² × T`, pseudoholomorphic for the product of the complex structure of the
Riemann sphere and the standard structure of the torus, has sphere component of mapping degree one
exactly when it is `z ↦ (g • z, t)` for a Möbius transformation `g` and a point `t` of the
torus. -/
theorem degree_fst_comp_eq_one_iff_exists_smul
    (hu : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
        (torusAlmostComplexStructure p)) u) :
    degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (Prod.fst ∘ u) = 1 ↔
      ∃ (g : GL (Fin 2) ℂ) (t : ∀ i, AddCircle (p i)), u = fun z ↦ (g • z, t) := by
  -- The sphere component is a holomorphic map of the Riemann sphere.
  have hfst : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Prod.fst ∘ u) :=
    isPseudoholomorphic_ofComplexManifold_iff.1
      (SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff.1 hhol).1
  rw [hfst.degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨g, (u OnePoint.infty).2, funext fun z ↦ Prod.ext (congrFun hg z) ?_⟩, ?_⟩
  · exact snd_apply_eq_of_isPseudoholomorphic_prod_of_tames_torusSymplecticForm hu
      (compatible_torusAlmostComplexStructure p).tames hhol z OnePoint.infty
  · rintro ⟨g, t, rfl⟩
    exact ⟨g, rfl⟩

section Mobius

variable {F H' M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [TopologicalSpace M] [ChartedSpace H' M]

/-- The maps `z ↦ (g • z, t)` from the Riemann sphere to `S² × M` are smooth. -/
theorem contMDiff_smul_prodMk_const (g : GL (Fin 2) ℂ) (t : M) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod I') ∞ (fun z : OnePoint ℂ ↦ (g • z, t)) :=
  -- The Möbius action is holomorphic, hence smooth for the underlying real structure.
  haveI := ContMDiffConstSMul.restrictScalars ℝ
    (inferInstance : ContMDiffConstSMul 𝓘(ℂ) ∞ (GL (Fin 2) ℂ) (OnePoint ℂ))
  (contMDiff_const_smul g).prodMk contMDiff_const

/-- The maps `z ↦ (g • z, t)` from the Riemann sphere to `S² × M` are pseudoholomorphic for the
product of the complex structure of the sphere and any almost complex structure `L` on `M`. -/
theorem isPseudoholomorphic_smul_prodMk_const [FiniteDimensional ℝ F] [IsManifold I' ∞ M]
    (L : SmoothAlmostComplexStructure I' M) (g : GL (Fin 2) ℂ) (t : M) :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod L)
      (fun z : OnePoint ℂ ↦ (g • z, t)) :=
  SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff.2
    ⟨isPseudoholomorphic_ofComplexManifold_iff.2
      ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) g).mdifferentiable (by simp)),
      isPseudoholomorphic_const _ _ t⟩

end Mobius

/-- **The pseudoholomorphic spheres of area `a` in `S²(a) × T`.** For `a ≠ 0`, a smooth map
`u : OnePoint ℂ → S²(a) × T`, pseudoholomorphic for the product of the complex structure of the
Riemann sphere and the standard structure of the torus, has symplectic area
`∫ u^*(pr₁^*(a • ω_FS) + pr₂^*ω_T) = a` exactly when it is `z ↦ (g • z, t)` for a Möbius
transformation `g` and a point `t` of the torus. -/
theorem integralTopForm_mpullback_eq_iff_exists_smul {a : ℝ} (ha : a ≠ 0)
    (hu : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
        (torusAlmostComplexStructure p)) u) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (torusSymplecticForm p))).val = a ↔
      ∃ (g : GL (Fin 2) ℂ) (t : ∀ i, AddCircle (p i)), u = fun z ↦ (g • z, t) := by
  rw [← degree_fst_comp_eq_one_iff_exists_smul hu hhol,
    integralTopForm_mpullback_prod_torusSymplecticForm_eq_degree_mul _ _
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)) hu,
    SmoothForm.smul_toRoughForm, integralTopForm_smul, OnePoint.integralTopForm_fubiniStudyForm,
    mul_one, mul_eq_right₀ ha]
  exact_mod_cast Iff.rfl

end TauCeti
