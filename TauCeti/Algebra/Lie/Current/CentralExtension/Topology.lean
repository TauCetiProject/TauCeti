/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.CentralExtension.Basic
public import TauCeti.Algebra.Lie.Current.ContinuousCohomology
public import TauCeti.Topology.Algebra.Lie.TwoCocycle

/-!
# Topological residue central extensions

The residue central extension has the product of the order topology on formal currents and
the discrete topology on its central coefficient module. Its bracket is jointly continuous,
the projection is open with a continuous linear section, and polynomial central extensions
have dense image. Level rescaling is continuous, including the map to level zero.

The topology on `TrivialLieModule R (currentAlgebra R L) R` is an explicit discrete topology
parameter. Thus this file does not replace any topology on `R`, in particular the usual
topology on the complex numbers. The continuous projection, section, kernel inclusion and
exactness are supplied by `LieAlgebra.ofTwoCocycle.projCLM`, `sectionCLM`, `inclCLM` and
`range_inclCLM` in the general cocycle-extension API.

The forms use Mathlib's sign `Res(f dg) Φ(x,y)`; the affine level form `κ` corresponds to
`Φ = -κ`. No degree derivation is included.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.
-/

public section

noncomputable section

open Filter Topology LieAlgebra LieModule.Cohomology
open TauCeti.LieModule.Cohomology

attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "C" => currentAlgebra R L
local notation "Z" => TrivialLieModule R C R

variable [TopologicalSpace (TrivialLieModule R (currentAlgebra R L) R)]
  [DiscreteTopology (TrivialLieModule R (currentAlgebra R L) R)]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs

/-- The residue central extension of formal currents has jointly continuous bracket. -/
theorem continuous_lie_ofTwoCocycle :
    Continuous fun p : ofTwoCocycle c × ofTwoCocycle c ↦ ⁅p.1, p.2⁆ := by
  apply ofTwoCocycle.continuous_lie c (continuous_lie R L)
  · simpa only [trivial_lie_zero] using
      (continuous_const : Continuous fun _ : C × Z ↦ (0 : Z))
  · simpa only [twoCocycleOfBilinear_coe] using
      mem_continuousTwoCochain_iff_continuous.mp
        (twoCochainOfBilinear_mem_continuousTwoCochain R L Φ hΦs)

/-- A zero neighbourhood basis in the residue extension consists of currents of order at
least `N` with zero central coordinate. -/
theorem hasBasis_nhds_zero_ofTwoCocycle :
    (𝓝 (0 : ofTwoCocycle c)).HasBasis (fun _ : ℤ ↦ True)
      (fun N ↦ {v | ofTwoCocycle.proj c v ∈ orderSubmodule R L N ∧
        ((ofProd c).symm v).2 = 0}) := by
  rw [(ofProdContinuousLinearEquiv c).symm.toHomeomorph.nhds_eq_comap]
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, coe_ofProdContinuousLinearEquiv_symm,
    of_symm_zero, ← Prod.mk_zero_zero, nhds_prod_eq, nhds_discrete Z]
  have h := ((hasBasis_nhds_zero R L).prod
    (Filter.hasBasis_pure (0 : Z))).comap (ofProd c).symm
  refine h.to_hasBasis (fun i _ ↦ ⟨i.1, trivial, ?_⟩)
    (fun N _ ↦ ⟨(N, ()), ⟨trivial, trivial⟩, ?_⟩)
  · rintro v hv
    exact ⟨by simpa only [ofTwoCocycle.proj_apply, SetLike.mem_coe] using hv.1, hv.2⟩
  · rintro v hv
    exact ⟨by simpa only [ofTwoCocycle.proj_apply, SetLike.mem_coe] using hv.1, hv.2⟩

section Level

variable {Ψ : LinearMap.BilinForm R L} (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)

/-- Rescaling a residue extension is continuous even when the scalar is zero. -/
theorem continuous_levelHom {r : R} (h : Ψ = r • Φ) :
    Continuous (levelHom hΦ hΦs hΨ hΨs h) := by
  apply (ofProdContinuousLinearEquiv (twoCocycleOfBilinear R L Ψ hΨ hΨs)).symm.toHomeomorph
    |>.isInducing.continuous_iff.mpr
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph, coe_ofProdContinuousLinearEquiv_symm,
    Function.comp_def, ofProd_symm_levelHom, Prod.map] using
    (continuous_id'.prodMap (continuous_of_discreteTopology : Continuous fun z : Z ↦ r • z)).comp
      (ofProdContinuousLinearEquiv c).symm.continuous

/-- A unit level rescaling is a homeomorphism as well as a Lie equivalence. -/
theorem isHomeomorph_levelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    IsHomeomorph (levelEquiv hΦ hΦs hΨ hΨs h) := by
  let e := levelEquiv hΦ hΦs hΨ hΨs h
  have he : Continuous e := by
    simpa only [e, ← LieEquiv.coe_toLieHom, toLieHom_levelEquiv] using
      continuous_levelHom Φ hΦ hΦs hΨ hΨs h
  have hi : Continuous e.symm := by
    have hinv (v : ofTwoCocycle (twoCocycleOfBilinear R L Ψ hΨ hΨs)) :
        (ofProd c).symm (e.symm v) =
          (((ofProd _).symm v).1, u⁻¹ • ((ofProd _).symm v).2) := by
      obtain ⟨⟨v, z⟩, rfl⟩ := (ofProd (twoCocycleOfBilinear R L Ψ hΨ hΨs)).surjective v
      simp [e]
    apply (ofProdContinuousLinearEquiv c).symm.toHomeomorph.isInducing.continuous_iff.mpr
    have hu : Continuous fun z : Z ↦ u⁻¹ • z := continuous_of_discreteTopology
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, coe_ofProdContinuousLinearEquiv_symm,
      Function.comp_def, hinv, Prod.map] using
      (continuous_id'.prodMap hu).comp
        (ofProdContinuousLinearEquiv (twoCocycleOfBilinear R L Ψ hΨ hΨs)).symm.continuous
  exact ({ e.toLinearEquiv.toEquiv with continuous_toFun := he, continuous_invFun := hi } :
    ofTwoCocycle c ≃ₜ ofTwoCocycle (twoCocycleOfBilinear R L Ψ hΨ hΨs)).isHomeomorph

end Level

omit [DiscreteTopology Z] in
/-- The polynomial residue central extension is dense in the formal one. -/
theorem denseRange_ofLoopExtension [HasUniqueDiv R] :
    DenseRange (ofLoopExtension Φ hΦ hΦs) := by
  let f := (TrivialLieModule.equiv R C R).symm.toLinearMap ∘ₗ
    (TrivialLieModule.equiv R (LieAlgebra.loopAlgebra R ℤ L) R).toLinearMap
  have hf : Function.Surjective f :=
    (TrivialLieModule.equiv R C R).symm.surjective.comp
      (TrivialLieModule.equiv R (LieAlgebra.loopAlgebra R ℤ L) R).surjective
  have hd := (ofProdContinuousLinearEquiv c).surjective.denseRange.comp
    ((denseRange_ofLoop R L).prodMap hf.denseRange)
    (ofProdContinuousLinearEquiv c).continuous
  simp only [Function.comp_def, coe_ofProdContinuousLinearEquiv, Prod.map] at hd
  intro v
  apply closure_mono (s := Set.range fun p : LieAlgebra.loopAlgebra R ℤ L ×
    TrivialLieModule R (LieAlgebra.loopAlgebra R ℤ L) R ↦
      ofProd c (ofLoop R L p.1, f p.2)) ?_ (hd v)
  rintro _ ⟨⟨p, z⟩, rfl⟩
  exact ⟨ofProd _ (p, z), by simp [f]⟩

end TauCeti.CurrentAlgebra
