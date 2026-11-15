/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.CentralExtension
public import TauCeti.Algebra.Lie.Current.ContinuousCohomology
public import TauCeti.Algebra.Lie.Current.CoordinateAction
public import TauCeti.Algebra.Lie.Extension.Topology

/-!
# The residue central extension as a topological Lie algebra

For an invariant symmetric bilinear form `Φ` on a Lie algebra `L` over a commutative ring `R`, the
residue central extension `ĝ = L((t)) ⊕ R K` is Mathlib's `LieAlgebra.ofTwoCocycle` of the residue
cocycle `TauCeti.CurrentAlgebra.twoCocycleOfBilinear`. It carries the topology of
`TauCeti.Algebra.Lie.Extension.Topology`: the product of the order topology of the formal currents
and the discrete topology of the central line `R K`. No topology on `R` is used.

From the general theory of that file, the projection `ĝ → L((t))` is a continuous open quotient
map, the section `u ↦ (u, 0)` is a continuous linear open embedding whose image meets the central
kernel `R K` of the projection only in zero, this kernel is discrete, and `ĝ` is Hausdorff when
`L` is a free module. This file adds the properties specific to residue extensions:

* the bracket of `ĝ` is jointly continuous, because the bracket of formal currents and the residue
  cocycle are continuous (`TauCeti.CurrentAlgebra.continuous_lie_residueExtension`);
* the residue extension of the polynomial loop algebra has dense image
  (`TauCeti.CurrentAlgebra.denseRange_ofLoopExtension`);
* level rescaling `K ↦ r • K` and the lifts of formal coordinate changes are continuous, so the
  level isomorphisms and the coordinate automorphisms are homeomorphisms.

The form uses Mathlib's residue convention `Res(f dg) Φ(x, y)`; the affine convention with level
form `κ` is the case `Φ = -κ`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for the topology of the affine
  central extension of the formal loop algebra.
-/

public section

noncomputable section

open scoped LaurentSeries
open Filter PowerSeries LieAlgebra LieModule.Cohomology TauCeti.LieModule.Cohomology

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [LieRing L]

section CommRing

variable [CommRing R] [LieAlgebra R L]

local notation "C" => currentAlgebra R L

section Bracket

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs

/-- **The residue central extension is a topological Lie algebra.** Its bracket is jointly
continuous. -/
theorem continuous_lie_residueExtension :
    Continuous fun p : ofTwoCocycle c × ofTwoCocycle c ↦ ⁅p.1, p.2⁆ :=
  (ofTwoCocycle.continuous_lie_iff c).mpr ⟨continuous_lie R L,
    twoCocycleOfBilinear_coe R L Φ hΦ hΦs ▸
      twoCochainOfBilinear_mem_continuousTwoCochain R L Φ hΦs,
    fun m ↦ Eventually.of_forall fun u ↦ trivial_lie_zero _ _ u m⟩

end Bracket

section Level

variable {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)

/-- Level rescaling `K ↦ r • K` is continuous. -/
theorem continuous_levelHom {r : R} (h : Ψ = r • Φ) :
    Continuous (levelHom hΦ hΦs hΨ hΨs h) := by
  refine ofTwoCocycle.continuous_iff.mpr ⟨?_, ?_⟩
  · simpa using ofTwoCocycle.continuous_ofProd_symm_fst _
  · simpa [Function.comp_def] using (ofTwoCocycle.isLocallyConstant_snd _).comp (r • ·)

/-- For a unit `u`, the level isomorphism `K ↦ u • K` is continuous. -/
theorem continuous_levelEquiv {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    Continuous (levelEquiv hΦ hΦs hΨ hΨs h) := by
  rw [← LieEquiv.coe_toLieHom, toLieHom_levelEquiv]
  exact continuous_levelHom hΦ hΦs hΨ hΨs h

/-- For a unit `u`, the inverse `K ↦ u⁻¹ • K` of the level isomorphism is continuous. -/
theorem continuous_levelEquiv_symm {u : Rˣ} (h : Ψ = (u : R) • Φ) :
    Continuous (levelEquiv hΦ hΦs hΨ hΨs h).symm := by
  have hv (w : ofTwoCocycle (twoCocycleOfBilinear R L Ψ hΨ hΨs)) :
      (ofProd _).symm ((levelEquiv hΦ hΦs hΨ hΨs h).symm w) =
        (((ofProd _).symm w).1, u⁻¹ • ((ofProd _).symm w).2) := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (ofProd _).surjective w
    simp
  refine ofTwoCocycle.continuous_iff.mpr ⟨?_, ?_⟩
  · simpa [hv] using ofTwoCocycle.continuous_ofProd_symm_fst _
  · simpa [hv, Function.comp_def] using (ofTwoCocycle.isLocallyConstant_snd _).comp (u⁻¹ • ·)

end Level

section Loop

variable [HasUniqueDiv R] (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
  (hΦs : Φ.IsSymm)

/-- The residue central extension of the polynomial loop algebra is dense in that of formal
currents. -/
theorem denseRange_ofLoopExtension : DenseRange (ofLoopExtension Φ hΦ hΦs) := by
  let c := twoCocycleOfBilinear R L Φ hΦ hΦs
  let : TopologicalSpace (TrivialLieModule R C R) := ⊥
  have : DiscreteTopology (TrivialLieModule R C R) := ⟨rfl⟩
  let g : TrivialLieModule R (LieAlgebra.loopAlgebra R ℤ L) R → TrivialLieModule R C R :=
    fun z ↦ (TrivialLieModule.equiv R C R).symm (TrivialLieModule.equiv R _ R z)
  have h : ⇑(ofLoopExtension Φ hΦ hΦs) =
      (ofTwoCocycle.ofProdContinuousLinearEquiv c ∘ Prod.map (ofLoop R L) g) ∘ (ofProd _).symm := by
    ext v
    obtain ⟨⟨u, z⟩, rfl⟩ := (ofProd _).surjective v
    simp [g, c]
  have hg : Function.Surjective g :=
    (TrivialLieModule.equiv R C R).symm.surjective.comp (TrivialLieModule.equiv R _ R).surjective
  rw [h, DenseRange, (ofProd _).symm.surjective.range_comp]
  exact (ofTwoCocycle.ofProdContinuousLinearEquiv c).surjective.denseRange.comp
    ((denseRange_ofLoop R L).prodMap hg.denseRange)
    (ofTwoCocycle.ofProdContinuousLinearEquiv c).continuous

end Loop

end CommRing

section Coordinate

variable {K : Type*} [Field K] [LieAlgebra K L]
  (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

/-- The lift of a formal coordinate change to the residue central extension is continuous. -/
theorem continuous_coordinateExtensionLieEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) :
    Continuous (coordinateExtensionLieEquiv Φ hΦ hΦs σ) := by
  refine ofTwoCocycle.continuous_iff.mpr ⟨?_, ?_⟩
  · simpa [Function.comp_def] using
      (continuous_substLieEquiv _).comp (ofTwoCocycle.continuous_ofProd_symm_fst _)
  · simpa using ofTwoCocycle.isLocallyConstant_snd _

/-- The inverse of the lift of a formal coordinate change is continuous. -/
theorem continuous_coordinateExtensionLieEquiv_symm (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) :
    Continuous (coordinateExtensionLieEquiv Φ hΦ hΦs σ).symm := by
  rw [coordinateExtensionLieEquiv_symm]
  exact continuous_coordinateExtensionLieEquiv Φ hΦ hΦs σ.symm

end Coordinate

end TauCeti.CurrentAlgebra
