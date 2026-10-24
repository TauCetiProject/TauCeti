/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.QuotientTorus
public import TauCeti.Geometry.Toric.Analytic.Fan.TorusAction.Holomorphic

/-!
# Complex structures on global toric orbits

The orbit of a cone `σ` carries the complex structure of the torus of the quotient lattice
`N ⧸ N_σ`. Its inclusion into the analytic realization is holomorphic, and a map into the orbit
is holomorphic exactly when its composite with this inclusion is holomorphic. Thus this
structure agrees with the independently constructed affine orbit charts, rather than merely
identifying the underlying topological spaces.

The inclusion is holomorphic because a section of the quotient lattice map expresses it as a
torus translate of the distinguished point. Conversely, characters of the quotient lattice are
monomials on the affine chart of `σ`, so holomorphy into the realization detects holomorphy into
the quotient torus. In particular, the complex structure is independent of the free presentation
used to chart that torus. The orbit keeps its subspace topology and is locally closed.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and Lemma 3.2.5.
-/

public section

open Function Multiplicative Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular) (σ : Φ.cones)
  {ι : Type*} [Fintype ι]
  (e : IntegralCharacter (N ⧸ coneSublattice i σ.1) ≃+ (ι →₀ ℤ))

/-- The complex structure on the global orbit of `σ`, transported from its quotient torus.
The topology is the subspace topology of the analytic realization. -/
@[instance_reducible]
noncomputable def analyticConeOrbitChartedSpace :
    ChartedSpace (ι → ℂ) (Φ.analyticConeOrbit hΦ σ) :=
  let := complexTorusChartedSpace e
  (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).isLocalHomeomorph.chartedSpaceComap

/-- A global cone orbit is a complex manifold for its quotient-torus complex structure. -/
theorem isManifold_analyticConeOrbit (n : ℕ∞ω) :
    let := Φ.analyticConeOrbitChartedSpace hΦ σ e
    IsManifold 𝓘(ℂ, ι → ℂ) n (Φ.analyticConeOrbit hΦ σ) := by
  let := complexTorusChartedSpace e
  have := isManifold_complexTorusChartedSpace e n
  exact (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The canonical identification of a cone orbit with its quotient torus is biholomorphic. -/
noncomputable def analyticConeOrbitTorusDiffeomorph (n : ℕ∞ω) :
    let := Φ.analyticConeOrbitChartedSpace hΦ σ e
    let := complexTorusChartedSpace e
    (Φ.analyticConeOrbit hΦ σ) ≃ₘ^n⟮𝓘(ℂ, ι → ℂ), 𝓘(ℂ, ι → ℂ)⟯
      ComplexTorus (N ⧸ coneSublattice i σ.1) := by
  let := complexTorusChartedSpace e
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  have h := (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).isLocalHomeomorph
  exact (h.isLocalDiffeomorph_chartedSpaceComap (n := n)).diffeomorphOfBijective
    (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).bijective

/-- The orbit biholomorphism has the existing quotient-torus homeomorphism as its underlying map. -/
@[simp]
theorem coe_analyticConeOrbitTorusDiffeomorph (n : ℕ∞ω) :
    let := Φ.analyticConeOrbitChartedSpace hΦ σ e
    let := complexTorusChartedSpace e
    ⇑(Φ.analyticConeOrbitTorusDiffeomorph hΦ σ e n) =
      Φ.analyticConeOrbitTorusHomeomorph hΦ σ := by
  simp only [analyticConeOrbitTorusDiffeomorph, coe_diffeomorphOfBijective]

/-- The inverse orbit biholomorphism has the inverse quotient-torus homeomorphism as its map. -/
@[simp]
theorem coe_analyticConeOrbitTorusDiffeomorph_symm (n : ℕ∞ω) :
    let := Φ.analyticConeOrbitChartedSpace hΦ σ e
    let := complexTorusChartedSpace e
    ⇑(Φ.analyticConeOrbitTorusDiffeomorph hΦ σ e n).symm =
      (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).symm := by
  let := complexTorusChartedSpace e
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  have h : (Φ.analyticConeOrbitTorusDiffeomorph hΦ σ e n).toEquiv =
      (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).toEquiv :=
    Equiv.ext fun x ↦ congrFun (Φ.coe_analyticConeOrbitTorusDiffeomorph hΦ σ e n) x
  exact congrArg (fun d : _ ≃ _ ↦ ⇑d.symm) h

/-- The inclusion of a global cone orbit in the analytic realization is holomorphic. -/
theorem contMDiff_subtypeVal_analyticConeOrbit (n : ℕ∞ω) :
    let := Φ.analyticConeOrbitChartedSpace hΦ σ e
    let := Φ.analyticChartedSpace hΦ
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Subtype.val : Φ.analyticConeOrbit hΦ σ → Φ.analyticRealization hΦ) := by
  classical
  have := Φ.lattice.free
  have := Φ.lattice.finite
  let B := Module.Free.chooseBasis ℤ N
  have := Module.Finite.finite_basis B
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ N)
  let eN := B.integralCharacterRepr
  let := complexTorusChartedSpace e
  let := complexTorusChartedSpace eN
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  let := Φ.analyticChartedSpace hΦ
  have := Φ.contMDiffSMul_complexTorus_analyticRealization hΦ eN n
  obtain ⟨g, hg⟩ := exists_complexTorusMap_comp_complexTorusMap_eq_id
    (QuotientAddGroup.mk'_surjective (coneSublattice i σ.1))
  have hc : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (fun t ↦ complexTorusMap g t • Φ.analyticDistinguishedPoint hΦ σ) :=
    (contMDiff_complexTorusMap e eN g n).smul
      (contMDiff_const (c := Φ.analyticDistinguishedPoint hΦ σ))
  refine (hc.comp (Φ.analyticConeOrbitTorusDiffeomorph hΦ σ e n).contMDiff).congr fun x ↦ ?_
  have hx := Φ.coe_analyticConeOrbitTorusHomeomorph_symm_complexTorusMap hΦ σ
    (complexTorusMap g (Φ.analyticConeOrbitTorusHomeomorph hΦ σ x))
  have hsec := DFunLike.congr_fun hg (Φ.analyticConeOrbitTorusHomeomorph hΦ σ x)
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at hsec
  rw [hsec, Homeomorph.symm_apply_apply] at hx
  simpa only [Function.comp_apply, coe_analyticConeOrbitTorusDiffeomorph] using hx

/-- Every point of an orbit lies in the target of the partial diffeomorphism of a
containing chart. -/
theorem mem_target_analyticAffineChartPartialDiffeomorph_of_mem_analyticConeOrbit
    {υ : Φ.cones} (h : σ ≤ υ) {k l s : ℕ}
    {B : Module.Basis (ToricRay υ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay υ.1 ≃ Fin k)
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice υ.1) s) (n : ℕ∞ω)
    {x : Φ.analyticRealization hΦ} (hx : x ∈ Φ.analyticConeOrbit hΦ σ) :
    x ∈ (Φ.analyticAffineChartPartialDiffeomorph hΦ υ hB κ g n).target := by
  rw [analyticAffineChartPartialDiffeomorph_target]
  exact (Φ.mem_range_analyticAffineChartι_iff hΦ hx).2 h

/-- On a global orbit, the inverse partial chart agrees with the inverse orbit parametrization. -/
theorem analyticAffineChartPartialDiffeomorph_symm_analyticConeOrbit
    {υ : Φ.cones} (h : σ ≤ υ) {k l s : ℕ}
    {B : Module.Basis (ToricRay υ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay υ.1 ≃ Fin k)
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice υ.1) s) (n : ℕ∞ω)
    (x : Φ.analyticConeOrbit hΦ σ) :
    let := affinePointTopology g
    let := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2).toIsToricCone hB κ g
    let := Φ.analyticChartedSpace hΦ
    (Φ.analyticAffineChartPartialDiffeomorph hΦ υ hB κ g n).toPartialEquiv.symm x.1 =
      ((Φ.analyticConeOrbitChartEquiv hΦ σ h).symm x).1 := by
  let := affinePointTopology g
  let := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2).toIsToricCone hB κ g
  let := Φ.analyticChartedSpace hΦ
  rw [← Φ.analyticAffineChartι_analyticConeOrbitChartEquiv_symm_apply hΦ σ h x]
  exact Φ.analyticAffineChartPartialDiffeomorph_symm_analyticAffineChartι hΦ υ hB κ g n _

/-- A quotient character on the global orbit is its monomial evaluated in an inverse affine
chart of the cone. Applying this to a coordinate character computes each quotient-torus
coordinate. -/
theorem val_analyticConeOrbitTorusHomeomorph_eq_monomial_symm
    {k l s : ℕ} {B : Module.Basis (ToricRay σ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay σ.1 ≃ Fin k)
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice σ.1) s) (n : ℕ∞ω)
    (x : Φ.analyticConeOrbit hΦ σ) (m : N ⧸ coneSublattice i σ.1 →+ ℤ) :
    let := affinePointTopology g
    let := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
    let := Φ.analyticChartedSpace hΦ
    ((Φ.analyticConeOrbitTorusHomeomorph hΦ σ x m : ℂˣ) : ℂ) =
      (Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n).toPartialEquiv.symm x.1
        (MonoidAlgebra.single (ofAdd
          ⟨m.comp (QuotientAddGroup.mk' (coneSublattice i σ.1)),
            (Φ.isToricCone σ.2).rational.comp_mk'_mem_dualSemigroup Φ.lattice m⟩) 1) := by
  let := affinePointTopology g
  let := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
  let := Φ.analyticChartedSpace hΦ
  rw [Φ.analyticAffineChartPartialDiffeomorph_symm_analyticConeOrbit hΦ σ le_rfl hB κ g n x]
  let y := (Φ.analyticConeOrbitChartEquiv hΦ σ le_rfl).symm x
  have hy : y.1 ∈ affineConeOrbit Φ.lattice (⊤ : σ.1.Face) := by
    simpa only [orbitFace_refl] using y.2
  have hx : x = ⟨Φ.analyticAffineChartι hΦ σ y.1,
      (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).2 rfl⟩ :=
    Subtype.ext (Φ.analyticAffineChartι_analyticConeOrbitChartEquiv_symm_apply
      hΦ σ le_rfl x).symm
  change ((Φ.analyticConeOrbitTorusHomeomorph hΦ σ x m : ℂˣ) : ℂ) = _
  conv_lhs => rw [hx]
  exact Φ.val_analyticConeOrbitTorusHomeomorph_apply hΦ σ hy m

/-- Holomorphy of a map into a global orbit can be checked after inclusion into the realization.
This characterizes the orbit structure intrinsically, independently of the quotient coordinates. -/
theorem contMDiff_subtypeVal_analyticConeOrbit_comp_iff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    {I : ModelWithCorners ℂ E H} [TopologicalSpace M] [ChartedSpace H M]
    {f : M → Φ.analyticConeOrbit hΦ σ} {n : ℕ∞ω} :
    let := Φ.analyticConeOrbitChartedSpace hΦ σ e
    let := Φ.analyticChartedSpace hΦ
    ContMDiff I 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n (fun x ↦ (f x).1) ↔
      ContMDiff I 𝓘(ℂ, ι → ℂ) n f := by
  classical
  let := complexTorusChartedSpace e
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  let := Φ.analyticChartedSpace hΦ
  refine ⟨fun hf ↦ ?_, (Φ.contMDiff_subtypeVal_analyticConeOrbit hΦ σ e n).comp⟩
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay σ.1) := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  let g := (Φ.analyticChartGenerators σ).2
  let := affinePointTopology g
  let := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n
  have hp := P.contMDiffOn_invFun.comp_contMDiff hf fun x ↦
    Φ.mem_target_analyticAffineChartPartialDiffeomorph_of_mem_analyticConeOrbit
      hΦ σ le_rfl hB κ g n (f x).2
  have htorus : ContMDiff I 𝓘(ℂ, ι → ℂ) n
      (fun x ↦ Φ.analyticConeOrbitTorusHomeomorph hΦ σ (f x)) := by
    apply (contMDiff_complexTorusAmbient_comp_iff e).1
    rw [contMDiff_pi_module_iff]
    intro j
    let m := e.symm (Finsupp.single j 1)
    let s : dualSemigroup Φ.lattice σ.1 :=
      ⟨m.comp (QuotientAddGroup.mk' (coneSublattice i σ.1)),
        (Φ.isToricCone σ.2).rational.comp_mk'_mem_dualSemigroup Φ.lattice m⟩
    exact ((contMDiff_apply_single Φ.lattice hσ.toIsToricCone hB κ g s n).comp hp).congr
      fun x ↦ by
        simpa only [Function.comp_apply, complexTorusAmbient_apply, PartialEquiv.invFun_as_coe,
          P, m, s] using
          Φ.val_analyticConeOrbitTorusHomeomorph_eq_monomial_symm hΦ σ hB κ g n (f x) m
  have h := (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).isLocalHomeomorph
  exact h.contMDiff_chartedSpaceComap_iff.2 ⟨hf.continuous.subtype_mk _, htorus⟩

/-- Changing the presentation of the quotient character lattice preserves the complex structure
on the global orbit. -/
theorem contMDiff_id_analyticConeOrbitChartedSpace {ι' : Type*} [Fintype ι']
    (e' : IntegralCharacter (N ⧸ coneSublattice i σ.1) ≃+ (ι' →₀ ℤ)) (n : ℕ∞ω) :
    @ContMDiff ℂ _ (ι → ℂ) _ _ (ι → ℂ) _ 𝓘(ℂ, ι → ℂ)
      (Φ.analyticConeOrbit hΦ σ) _ (Φ.analyticConeOrbitChartedSpace hΦ σ e)
      (ι' → ℂ) _ _ (ι' → ℂ) _ 𝓘(ℂ, ι' → ℂ)
      (Φ.analyticConeOrbit hΦ σ) _ (Φ.analyticConeOrbitChartedSpace hΦ σ e') n id := by
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  exact (Φ.contMDiff_subtypeVal_analyticConeOrbit_comp_iff hΦ σ e').1
    (Φ.contMDiff_subtypeVal_analyticConeOrbit hΦ σ e n)

/-- The global quotient-torus structure agrees with the affine orbit structure for any
containing cone, extending basis and finite monomial generating family. -/
noncomputable def analyticConeOrbitChartDiffeomorph {υ : Φ.cones} (h : σ ≤ υ)
    {l s : ℕ} {B : Module.Basis (ToricRay υ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice υ.1) s)
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice (Φ.orbitFace h)}]
    (n : ℕ∞ω) :
    letI := affinePointTopology g
    letI := affineConeOrbitChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2)
      hB (Φ.orbitFace h) g
    letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
    (affineConeOrbit Φ.lattice (Φ.orbitFace h)) ≃ₘ^n⟮
      𝓘(ℂ, (({ρ : ToricRay υ.1 // ρ ∉
        ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice (Φ.orbitFace h)} → ℂ) ×
          (Fin l → ℂ))), 𝓘(ℂ, ι → ℂ)⟯ Φ.analyticConeOrbit hΦ σ := by
  have : Finite (ToricRay υ.1) :=
    ToricRay.finite_of_fg ((isRegular_iff.mp hΦ) υ.1 υ.2).fg
  let κ := Finite.equivFin (ToricRay υ.1)
  letI := affinePointTopology g
  letI := affineConeOrbitChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2)
    hB (Φ.orbitFace h) g
  letI := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2).toIsToricCone hB κ g
  letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
  letI := Φ.analyticChartedSpace hΦ
  let d := Φ.analyticConeOrbitChartEquiv hΦ σ h
  refine { toEquiv := d, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (Φ.contMDiff_subtypeVal_analyticConeOrbit_comp_iff hΦ σ e).1
    exact ((Φ.contMDiff_analyticAffineChartι hΦ υ hB κ g n).comp
      (contMDiff_subtypeVal_affineConeOrbit Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2)
        hB κ (Φ.orbitFace h) g n)).congr fun x ↦
          Φ.coe_analyticConeOrbitChartEquiv_apply hΦ σ h x
  · apply contMDiff_of_contMDiff_subtypeVal_affineConeOrbit Φ.lattice
      ((isRegular_iff.mp hΦ) υ.1 υ.2) hB κ (Φ.orbitFace h) g
    let P := Φ.analyticAffineChartPartialDiffeomorph hΦ υ hB κ g n
    exact (P.contMDiffOn_invFun.comp_contMDiff
      (Φ.contMDiff_subtypeVal_analyticConeOrbit hΦ σ e n) (fun x ↦
        Φ.mem_target_analyticAffineChartPartialDiffeomorph_of_mem_analyticConeOrbit
          hΦ σ h hB κ g n x.2)).congr fun x ↦
      (Φ.analyticAffineChartPartialDiffeomorph_symm_analyticConeOrbit hΦ σ h hB κ g n x).symm

/-- The affine orbit biholomorphism is the existing affine parametrization of the global orbit. -/
@[simp]
theorem coe_analyticConeOrbitChartDiffeomorph {υ : Φ.cones} (h : σ ≤ υ)
    {l s : ℕ} {B : Module.Basis (ToricRay υ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice υ.1) s)
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice (Φ.orbitFace h)}]
    (n : ℕ∞ω) :
    letI := affinePointTopology g
    letI := affineConeOrbitChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2)
      hB (Φ.orbitFace h) g
    letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
    ⇑(Φ.analyticConeOrbitChartDiffeomorph hΦ σ e h hB g n) =
      Φ.analyticConeOrbitChartEquiv hΦ σ h :=
  (rfl)

/-- The inverse affine orbit biholomorphism is the inverse affine parametrization. -/
@[simp]
theorem coe_analyticConeOrbitChartDiffeomorph_symm {υ : Φ.cones} (h : σ ≤ υ)
    {l s : ℕ} {B : Module.Basis (ToricRay υ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice υ.1) s)
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice (Φ.orbitFace h)}]
    (n : ℕ∞ω) :
    letI := affinePointTopology g
    letI := affineConeOrbitChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2)
      hB (Φ.orbitFace h) g
    letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
    ⇑(Φ.analyticConeOrbitChartDiffeomorph hΦ σ e h hB g n).symm =
      (Φ.analyticConeOrbitChartEquiv hΦ σ h).symm :=
  (rfl)

end TauCeti.Toric.Fan
