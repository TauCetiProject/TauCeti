/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.TorusAction
public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Complex

/-!
# Torus orbits in the algebraic–analytic comparison

For a regular fan `Φ` and a cone `σ`, the algebraic–analytic comparison restricts to a
homeomorphism from the torus orbit of `σ` in the complex points of the toric scheme onto the
analytic cone orbit, with both orbits carrying their subspace topologies. Composed with the
identification of the analytic orbit with the torus of the quotient lattice `N ⧸ N_σ`, it
identifies the algebraic orbit with that quotient torus, torus-equivariantly and sending the
distinguished point of `σ` to `1`.

Pulling back the quotient-torus complex structure of the analytic orbit makes the algebraic orbit
a complex manifold, biholomorphic to the analytic orbit and to the quotient torus. This structure
is intrinsic: its inclusion into the algebraic complex points is holomorphic, and a map into the
orbit is holomorphic exactly when its composite with this inclusion is. In particular it does not
depend on the free presentation of the quotient character lattice used to chart the torus.

## Main declarations

* `TauCeti.Toric.Fan.algebraicAnalyticConeOrbitHomeomorph`: the comparison restricted to the
  orbit of a cone.
* `TauCeti.Toric.Fan.algebraicConeOrbitTorusHomeomorph`: the algebraic orbit of `σ` is
  homeomorphic to the torus of `N ⧸ N_σ`, equivariantly
  (`TauCeti.Toric.Fan.algebraicConeOrbitTorusHomeomorph_smul`).
* `TauCeti.Toric.Fan.algebraicConeOrbitChartedSpace`: the complex structure on the algebraic
  orbit, with `TauCeti.Toric.Fan.isManifold_algebraicConeOrbit`.
* `TauCeti.Toric.Fan.algebraicAnalyticConeOrbitDiffeomorph` and
  `TauCeti.Toric.Fan.algebraicConeOrbitTorusDiffeomorph`: the biholomorphisms of the algebraic
  orbit with the analytic orbit and with the quotient torus.
* `TauCeti.Toric.Fan.contMDiff_subtypeVal_coneOrbit_comp_iff`: holomorphy into the algebraic orbit
  is detected in the algebraic complex points.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and Lemma 3.2.5.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (hΦ : Φ.IsRegular) (σ : Φ.cones)

/-- The algebraic–analytic comparison restricted to the torus orbit of a cone, with both orbits
carrying their subspace topologies. -/
noncomputable def algebraicAnalyticConeOrbitHomeomorph :
    AlgebraicComplexPoint.coneOrbit Φ σ ≃ₜ Φ.analyticConeOrbit hΦ σ :=
  (algebraicAnalyticHomeomorph hΦ).sets
    (by simpa only [coe_algebraicAnalyticHomeomorph] using
      (preimage_algebraicAnalyticEquiv_analyticConeOrbit hΦ σ).symm)

/-- Restriction to an orbit commutes with the inclusions into the ambient spaces. -/
@[simp]
theorem coe_algebraicAnalyticConeOrbitHomeomorph_apply
    (x : AlgebraicComplexPoint.coneOrbit Φ σ) :
    (algebraicAnalyticConeOrbitHomeomorph hΦ σ x).1 = algebraicAnalyticEquiv hΦ x.1 := by
  simp [algebraicAnalyticConeOrbitHomeomorph]

/-- The inverse restricted comparison is the restriction of the inverse ambient comparison. -/
@[simp]
theorem coe_algebraicAnalyticConeOrbitHomeomorph_symm_apply
    (x : Φ.analyticConeOrbit hΦ σ) :
    ((algebraicAnalyticConeOrbitHomeomorph hΦ σ).symm x).1 =
      (algebraicAnalyticEquiv hΦ).symm x.1 := by
  simp [algebraicAnalyticConeOrbitHomeomorph]

/-! ### The algebraic orbit as a quotient torus -/

/-- **Algebraic orbits are quotient tori.** The torus orbit of a cone `σ` in the complex points
of the toric scheme of a regular fan, with the subspace topology, is homeomorphic to the torus of
the quotient lattice `N ⧸ N_σ`. -/
noncomputable def algebraicConeOrbitTorusHomeomorph :
    AlgebraicComplexPoint.coneOrbit Φ σ ≃ₜ ComplexTorus (N ⧸ coneSublattice i σ.1) :=
  (algebraicAnalyticConeOrbitHomeomorph hΦ σ).trans (Φ.analyticConeOrbitTorusHomeomorph hΦ σ)

/-- The algebraic quotient-torus identification factors through the analytic orbit. -/
theorem algebraicConeOrbitTorusHomeomorph_apply (x : AlgebraicComplexPoint.coneOrbit Φ σ) :
    algebraicConeOrbitTorusHomeomorph hΦ σ x =
      Φ.analyticConeOrbitTorusHomeomorph hΦ σ (algebraicAnalyticConeOrbitHomeomorph hΦ σ x) :=
  (rfl)

/-- The distinguished point of `σ` corresponds to the identity of the quotient torus. -/
@[simp]
theorem algebraicConeOrbitTorusHomeomorph_distinguishedPoint :
    algebraicConeOrbitTorusHomeomorph hΦ σ
        ⟨AlgebraicComplexPoint.distinguishedPoint σ,
          AlgebraicComplexPoint.distinguishedPoint_mem_coneOrbit σ⟩ = 1 := by
  have h : algebraicAnalyticConeOrbitHomeomorph hΦ σ
      ⟨AlgebraicComplexPoint.distinguishedPoint σ,
        AlgebraicComplexPoint.distinguishedPoint_mem_coneOrbit σ⟩ =
      ⟨Φ.analyticDistinguishedPoint hΦ σ,
        Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ⟩ :=
    Subtype.ext (by simp)
  rw [algebraicConeOrbitTorusHomeomorph_apply, h,
    analyticConeOrbitTorusHomeomorph_analyticDistinguishedPoint]

/-- The identification of the algebraic orbit of `σ` with the quotient torus is equivariant:
translating by a torus point `t` multiplies by the image of `t` in the quotient torus. -/
theorem algebraicConeOrbitTorusHomeomorph_smul (t : ComplexTorus N)
    (x : AlgebraicComplexPoint.coneOrbit Φ σ) :
    algebraicConeOrbitTorusHomeomorph hΦ σ
        ⟨t • x.1, AlgebraicComplexPoint.smul_mem_coneOrbit t x.2⟩ =
      complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1)) t *
        algebraicConeOrbitTorusHomeomorph hΦ σ x := by
  have h : algebraicAnalyticConeOrbitHomeomorph hΦ σ
      ⟨t • x.1, AlgebraicComplexPoint.smul_mem_coneOrbit t x.2⟩ =
      ⟨t • (algebraicAnalyticConeOrbitHomeomorph hΦ σ x).1,
        Φ.smul_mem_analyticConeOrbit hΦ t (algebraicAnalyticConeOrbitHomeomorph hΦ σ x).2⟩ :=
    Subtype.ext (by simp)
  rw [algebraicConeOrbitTorusHomeomorph_apply, h, analyticConeOrbitTorusHomeomorph_smul,
    algebraicConeOrbitTorusHomeomorph_apply]

/-- The inverse identification sends the image of a torus point `t` in the quotient torus to the
translate of the distinguished point of `σ` by `t`. -/
@[simp]
theorem coe_algebraicConeOrbitTorusHomeomorph_symm_complexTorusMap (t : ComplexTorus N) :
    ((algebraicConeOrbitTorusHomeomorph hΦ σ).symm
        (complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1)) t) :
        Φ.AlgebraicComplexPoint) =
      t • AlgebraicComplexPoint.distinguishedPoint σ := by
  rw [algebraicConeOrbitTorusHomeomorph, Homeomorph.symm_trans_apply,
    coe_algebraicAnalyticConeOrbitHomeomorph_symm_apply,
    coe_analyticConeOrbitTorusHomeomorph_symm_complexTorusMap, algebraicAnalyticEquiv_symm_smul,
    algebraicAnalyticEquiv_symm_analyticDistinguishedPoint]

/-! ### The complex structure on the algebraic orbit -/

variable {ι : Type*} [Fintype ι] (e : IntegralCharacter (N ⧸ coneSublattice i σ.1) ≃+ (ι →₀ ℤ))

/-- The complex structure on the algebraic orbit of `σ`, pulled back from the quotient-torus
structure of the analytic orbit. The topology is the subspace topology of the algebraic complex
points. -/
@[instance_reducible]
noncomputable def algebraicConeOrbitChartedSpace :
    ChartedSpace (ι → ℂ) (AlgebraicComplexPoint.coneOrbit Φ σ) :=
  letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
  (algebraicAnalyticConeOrbitHomeomorph hΦ σ).isLocalHomeomorph.chartedSpaceComap

/-- The algebraic orbit of a cone is a complex manifold. -/
theorem isManifold_algebraicConeOrbit (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    IsManifold 𝓘(ℂ, ι → ℂ) n (AlgebraicComplexPoint.coneOrbit Φ σ) := by
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  have := Φ.isManifold_analyticConeOrbit hΦ σ e n
  exact (algebraicAnalyticConeOrbitHomeomorph hΦ σ).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The orbit restriction of the algebraic–analytic comparison is a complex diffeomorphism of
order `n`. At analytic order `n = ω`, it is a biholomorphism. -/
noncomputable def algebraicAnalyticConeOrbitDiffeomorph (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
    AlgebraicComplexPoint.coneOrbit Φ σ ≃ₘ^n⟮𝓘(ℂ, ι → ℂ), 𝓘(ℂ, ι → ℂ)⟯
      Φ.analyticConeOrbit hΦ σ := by
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  let := algebraicConeOrbitChartedSpace hΦ σ e
  have h := (algebraicAnalyticConeOrbitHomeomorph hΦ σ).isLocalHomeomorph
  exact (h.isLocalDiffeomorph_chartedSpaceComap (n := n)).diffeomorphOfBijective
    (algebraicAnalyticConeOrbitHomeomorph hΦ σ).bijective

/-- The orbit diffeomorphism has the restricted comparison as its underlying map. -/
@[simp]
theorem coe_algebraicAnalyticConeOrbitDiffeomorph (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
    ⇑(algebraicAnalyticConeOrbitDiffeomorph hΦ σ e n) =
      algebraicAnalyticConeOrbitHomeomorph hΦ σ := by
  simp only [algebraicAnalyticConeOrbitDiffeomorph, coe_diffeomorphOfBijective]

/-- The inverse orbit diffeomorphism has the inverse restricted comparison as its map. -/
@[simp]
theorem coe_algebraicAnalyticConeOrbitDiffeomorph_symm (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
    ⇑(algebraicAnalyticConeOrbitDiffeomorph hΦ σ e n).symm =
      (algebraicAnalyticConeOrbitHomeomorph hΦ σ).symm := by
  let := algebraicConeOrbitChartedSpace hΦ σ e
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  funext x
  apply (algebraicAnalyticConeOrbitHomeomorph hΦ σ).injective
  rw [← coe_algebraicAnalyticConeOrbitDiffeomorph hΦ σ e n, Diffeomorph.apply_symm_apply,
    coe_algebraicAnalyticConeOrbitDiffeomorph, Homeomorph.apply_symm_apply]

/-- The identification of the algebraic orbit with the quotient torus is a complex
diffeomorphism of order `n`, a biholomorphism at analytic order `n = ω`. -/
noncomputable def algebraicConeOrbitTorusDiffeomorph (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := complexTorusChartedSpace e
    AlgebraicComplexPoint.coneOrbit Φ σ ≃ₘ^n⟮𝓘(ℂ, ι → ℂ), 𝓘(ℂ, ι → ℂ)⟯
      ComplexTorus (N ⧸ coneSublattice i σ.1) :=
  letI := Φ.analyticConeOrbitChartedSpace hΦ σ e
  letI := algebraicConeOrbitChartedSpace hΦ σ e
  letI := complexTorusChartedSpace e
  (algebraicAnalyticConeOrbitDiffeomorph hΦ σ e n).trans
    (Φ.analyticConeOrbitTorusDiffeomorph hΦ σ e n)

/-- The quotient-torus biholomorphism has the quotient-torus homeomorphism as its map. -/
@[simp]
theorem coe_algebraicConeOrbitTorusDiffeomorph (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := complexTorusChartedSpace e
    ⇑(algebraicConeOrbitTorusDiffeomorph hΦ σ e n) = algebraicConeOrbitTorusHomeomorph hΦ σ := by
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  let := algebraicConeOrbitChartedSpace hΦ σ e
  let := complexTorusChartedSpace e
  funext x
  simp [algebraicConeOrbitTorusDiffeomorph, algebraicConeOrbitTorusHomeomorph_apply]

/-- The inverse quotient-torus biholomorphism has the inverse quotient-torus homeomorphism as its
map. -/
@[simp]
theorem coe_algebraicConeOrbitTorusDiffeomorph_symm (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := complexTorusChartedSpace e
    ⇑(algebraicConeOrbitTorusDiffeomorph hΦ σ e n).symm =
      (algebraicConeOrbitTorusHomeomorph hΦ σ).symm := by
  let := algebraicConeOrbitChartedSpace hΦ σ e
  let := complexTorusChartedSpace e
  funext x
  apply (algebraicConeOrbitTorusHomeomorph hΦ σ).injective
  rw [← coe_algebraicConeOrbitTorusDiffeomorph hΦ σ e n, Diffeomorph.apply_symm_apply,
    coe_algebraicConeOrbitTorusDiffeomorph, Homeomorph.apply_symm_apply]

/-- The inclusion of the algebraic orbit of a cone into the algebraic complex points is
holomorphic. -/
theorem contMDiff_subtypeVal_coneOrbit (n : ℕ∞ω) :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := algebraicComplexPointChartedSpace hΦ
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Subtype.val : AlgebraicComplexPoint.coneOrbit Φ σ → Φ.AlgebraicComplexPoint) := by
  let := Φ.analyticChartedSpace hΦ
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  let := algebraicConeOrbitChartedSpace hΦ σ e
  let := algebraicComplexPointChartedSpace hΦ
  refine ((algebraicAnalyticDiffeomorph hΦ n).symm.contMDiff.comp
    ((Φ.contMDiff_subtypeVal_analyticConeOrbit hΦ σ e n).comp
      (algebraicAnalyticConeOrbitDiffeomorph hΦ σ e n).contMDiff)).congr fun x ↦ ?_
  simp

/-- Holomorphy of a map into the algebraic orbit of a cone can be checked after inclusion into the
algebraic complex points. This characterizes the orbit structure intrinsically. -/
theorem contMDiff_subtypeVal_coneOrbit_comp_iff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    {I : ModelWithCorners ℂ E H} [TopologicalSpace M] [ChartedSpace H M]
    {f : M → AlgebraicComplexPoint.coneOrbit Φ σ} {n : ℕ∞ω} :
    letI := algebraicConeOrbitChartedSpace hΦ σ e
    letI := algebraicComplexPointChartedSpace hΦ
    ContMDiff I 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n (fun x ↦ (f x).1) ↔
      ContMDiff I 𝓘(ℂ, ι → ℂ) n f := by
  let := Φ.analyticChartedSpace hΦ
  let := Φ.analyticConeOrbitChartedSpace hΦ σ e
  let := algebraicConeOrbitChartedSpace hΦ σ e
  let := algebraicComplexPointChartedSpace hΦ
  let d := algebraicAnalyticDiffeomorph hΦ n
  let dσ := algebraicAnalyticConeOrbitDiffeomorph hΦ σ e n
  refine ⟨fun hf ↦ ?_, (contMDiff_subtypeVal_coneOrbit hΦ σ e n).comp⟩
  -- Transport to the analytic orbit, where holomorphy is detected in the realization.
  have ha : ContMDiff I 𝓘(ℂ, ι → ℂ) n (dσ ∘ f) :=
    (Φ.contMDiff_subtypeVal_analyticConeOrbit_comp_iff hΦ σ e).1
      ((d.contMDiff.comp hf).congr fun x ↦ by simp [d, dσ])
  exact (dσ.symm.contMDiff.comp ha).congr fun x ↦ by simp

/-- Changing the presentation of the quotient character lattice preserves the complex structure
on the algebraic orbit. -/
theorem contMDiff_id_algebraicConeOrbitChartedSpace {ι' : Type*} [Fintype ι']
    (e' : IntegralCharacter (N ⧸ coneSublattice i σ.1) ≃+ (ι' →₀ ℤ)) (n : ℕ∞ω) :
    @ContMDiff ℂ _ (ι → ℂ) _ _ (ι → ℂ) _ 𝓘(ℂ, ι → ℂ)
      (AlgebraicComplexPoint.coneOrbit Φ σ) _ (algebraicConeOrbitChartedSpace hΦ σ e)
      (ι' → ℂ) _ _ (ι' → ℂ) _ 𝓘(ℂ, ι' → ℂ)
      (AlgebraicComplexPoint.coneOrbit Φ σ) _ (algebraicConeOrbitChartedSpace hΦ σ e') n id := by
  let := algebraicConeOrbitChartedSpace hΦ σ e
  exact (contMDiff_subtypeVal_coneOrbit_comp_iff hΦ σ e').1
    (contMDiff_subtypeVal_coneOrbit hΦ σ e n)

end TauCeti.Toric.Fan
