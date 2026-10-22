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
  funext x
  apply (Φ.analyticConeOrbitTorusHomeomorph hΦ σ).injective
  rw [← coe_analyticConeOrbitTorusDiffeomorph Φ hΦ σ e n,
    Diffeomorph.apply_symm_apply, coe_analyticConeOrbitTorusDiffeomorph,
    Homeomorph.apply_symm_apply]

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
  have hrange (x : M) : (f x).1 ∈ P.target := by
    rw [analyticAffineChartPartialDiffeomorph_target]
    have hx := (f x).2
    simp only [analyticConeOrbit_def] at hx
    exact image_subset_range _ _ hx
  have hp := P.contMDiffOn_invFun.comp_contMDiff hf hrange
  have htorus : ContMDiff I 𝓘(ℂ, ι → ℂ) n
      (fun x ↦ Φ.analyticConeOrbitTorusHomeomorph hΦ σ (f x)) := by
    apply (contMDiff_complexTorusAmbient_comp_iff e).1
    rw [contMDiff_pi_module_iff]
    intro j
    let m := e.symm (Finsupp.single j 1)
    let s : dualSemigroup Φ.lattice σ.1 :=
      ⟨m.comp (QuotientAddGroup.mk' (coneSublattice i σ.1)),
        (Φ.isToricCone σ.2).rational.comp_mk'_mem_dualSemigroup Φ.lattice m⟩
    refine ((contMDiff_apply_single Φ.lattice hσ.toIsToricCone hB κ g s n).comp hp).congr
      fun x ↦ ?_
    have hx := (f x).2
    simp only [analyticConeOrbit_def] at hx
    obtain ⟨y, hy, hfy⟩ := hx
    have hPx : P.invFun (f x).1 = y := by
      rw [← hfy]
      exact Φ.analyticAffineChartPartialDiffeomorph_symm_analyticAffineChartι
        hΦ σ hB κ g n y
    have hfx : f x = ⟨Φ.analyticAffineChartι hΦ σ y,
        (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).2 rfl⟩ :=
      Subtype.ext hfy.symm
    simp only [Function.comp_apply, complexTorusAmbient_apply, hPx]
    rw [hfx]
    exact Φ.val_analyticConeOrbitTorusHomeomorph_apply hΦ σ hy m
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

/-- The affine orbit of `σ` in any containing chart parametrizes the entire global orbit.
The parametrization is the affine chart inclusion, independent of coordinate choices. -/
noncomputable def analyticConeOrbitChartEquiv {υ : Φ.cones} (h : σ ≤ υ) :
    affineConeOrbit Φ.lattice (Φ.orbitFace h) ≃ Φ.analyticConeOrbit hΦ σ :=
  ((Φ.isOpenEmbedding_analyticAffineChartι hΦ υ).isEmbedding.homeomorphImage
    (affineConeOrbit Φ.lattice (Φ.orbitFace h))).toEquiv.trans (Set.equivOfEq (by
      rw [← Φ.preimage_analyticAffineChartι_analyticConeOrbit hΦ h,
        image_preimage_eq_inter_range]
      exact inter_eq_left.mpr fun _ hx ↦ (Φ.mem_range_analyticAffineChartι_iff hΦ hx).2 h))

/-- The affine parametrization of a global orbit is given by the affine chart inclusion. -/
@[simp]
theorem coe_analyticConeOrbitChartEquiv_apply {υ : Φ.cones} (h : σ ≤ υ)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace h)) :
    (Φ.analyticConeOrbitChartEquiv hΦ σ h x : Φ.analyticRealization hΦ) =
      Φ.analyticAffineChartι hΦ υ x.1 :=
  (rfl)

/-- Every global cone orbit is locally closed in the analytic realization. -/
theorem isLocallyClosed_analyticConeOrbit : IsLocallyClosed (Φ.analyticConeOrbit hΦ σ) := by
  let := affinePointTopology (Φ.analyticChartGenerators σ).2
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  have hι := Φ.isOpenEmbedding_analyticAffineChartι hΦ σ
  have hc := isLocallyClosed_affineConeOrbit Φ.lattice hσ (⊤ : σ.1.Face)
    (Φ.analyticChartGenerators σ).2
  rw [← Φ.analyticAffineChart_str_eq σ] at hc
  rw [analyticConeOrbit_def]
  exact hc.image hι.isInducing hι.isOpen_range.isLocallyClosed

/-- The global quotient-torus structure agrees with the affine orbit structure for any
containing cone, extending basis, ray numbering and finite monomial generating family. -/
noncomputable def analyticConeOrbitChartDiffeomorph {υ : Φ.cones} (h : σ ≤ υ)
    {k l s : ℕ} {B : Module.Basis (ToricRay υ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay υ.1 ≃ Fin k)
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
          (Φ.coe_analyticConeOrbitChartEquiv_apply hΦ σ h x).symm
  · apply contMDiff_of_contMDiff_subtypeVal_affineConeOrbit Φ.lattice
      ((isRegular_iff.mp hΦ) υ.1 υ.2) hB κ (Φ.orbitFace h) g
    let P := Φ.analyticAffineChartPartialDiffeomorph hΦ υ hB κ g n
    have hrange (x : Φ.analyticConeOrbit hΦ σ) : x.1 ∈ P.target := by
      rw [analyticAffineChartPartialDiffeomorph_target]
      exact (Φ.mem_range_analyticAffineChartι_iff hΦ x.2).2 h
    refine (P.contMDiffOn_invFun.comp_contMDiff
      (Φ.contMDiff_subtypeVal_analyticConeOrbit hΦ σ e n) hrange).congr fun x ↦ ?_
    have hx := Φ.coe_analyticConeOrbitChartEquiv_apply hΦ σ h (d.symm x)
    simp only [d, Equiv.apply_symm_apply] at hx
    simp only [Function.comp_apply]
    rw [hx]
    exact (Φ.analyticAffineChartPartialDiffeomorph_symm_analyticAffineChartι
      hΦ υ hB κ g n (d.symm x).1).symm

/-- The affine orbit biholomorphism is the existing affine parametrization of the global orbit. -/
@[simp]
theorem coe_analyticConeOrbitChartDiffeomorph {υ : Φ.cones} (h : σ ≤ υ)
    {k l s : ℕ} {B : Module.Basis (ToricRay υ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay υ.1 ≃ Fin k)
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice υ.1) s)
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice (Φ.orbitFace h)}]
    (n : ℕ∞ω) :
    letI := affinePointTopology g
    letI := affineConeOrbitChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) υ.1 υ.2)
      hB (Φ.orbitFace h) g
    letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
    ⇑(Φ.analyticConeOrbitChartDiffeomorph hΦ σ e h hB κ g n) =
      Φ.analyticConeOrbitChartEquiv hΦ σ h :=
  (rfl)

end TauCeti.Toric.Fan
