/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Surjective

/-!
# Hamiltonian variations make the linearized operator of the pair of pants capped at `1` onto

Plumbing the negative PSS plane with Hamiltonian `H_1` into the input end at `1` of the pair of
pants `ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞`, along a neck of length `L > 4`, gives a
Floer datum on the standard cylinder, with components `TauCeti.Floer.cappedCylinderComponent Hb L 1`
and `TauCeti.Floer.cappedCylinderComponent Hb L Complex.I`
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder`). It is `H_∞(t) dt` far out on the
negative end and `H_0(t) dt` far out on the positive end. The unit property of the pair-of-pants
product counts the rigid cylinders of this datum: in the unit homotopies of
`TauCeti.Geometry.Symplectic.Floer.Cap.Unit`, the product with the unit and the continuation map
are the two ends of one family of counts. These moduli spaces are cut out transversally once the
universal linearized operator, which adds to `D_u` the variations of the perturbation, is onto.

This file proves that finitely many Hamiltonian variations already make it onto. Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `J`
be `C²` almost complex structures on the cylinder, compatible with `ω` and cylindrical on the ends,
and let `u` be a `C²` map asymptotic to nondegenerate one-periodic orbits of `H_∞` and `H_0`. For
every nonempty open subset `U` of the open strip `ℝ × (0, 1)` and every neighbourhood `W` of the
graph of `u` over `U`, there are finitely many variation terms `-X_{δKᵢ}(u)`
(`TauCeti.SymplecticForm.hamiltonianVariations`) of smooth variations `δKᵢ` of compact support in
`W` such that every element of `L²(ℝ × S¹, F)` is `D_u ξ + ∑ cᵢ (-X_{δKᵢ}(u))`
(`exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_cappedCylinderComponent`, in
the namespace `TauCeti.SymplecticForm`). The open set `U` may lie anywhere on the cylinder: in the
core of the pair of pants, on the neck, or in the inserted plane. No hypothesis is placed on `u`
over `U`, which may be constant there.

The capped datum is cylindrical near the ends
(`TauCeti.Floer.isCylindricalNearEnds_cappedCylinderComponent`), so this is the case of the capped
datum of
`exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_of_cylindrical_of_compatible`,
in the namespace `TauCeti.SymplecticForm`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 (the universal operator is onto) and
  Section 8.1.
-/

public section

open Set Filter Function Topology MeasureTheory
open scoped NNReal Manifold
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open Floer StripSobolev

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Finitely many Hamiltonian variations make the linearized operator of the pair of pants
capped at `1` onto.** Let `F` be a finite-dimensional complex inner product space whose symplectic
form `ω` is `Im ⟪·, ·⟫`, let `Hb r` be jointly `C³` Hamiltonians of period one in `t`, with
`Hb ∞` and `Hb 0` of globally Lipschitz suspended vector fields, and let `L > 4`. Let `J(z)` be
`C²` almost complex structures on the cylinder, compatible with `ω`, equal to `Jp_t` for `s ≥ R`
and to `Jm_t` for `s ≤ -R`. Let `u` be a `C²` map whose loops converge uniformly to a one-periodic
orbit `xm` of `Hb ∞` at `-∞` and to a one-periodic orbit `xp` of `Hb 0` at `+∞`, starting at
nondegenerate fixed points of the time-one maps, with slice defects tending uniformly to zero at
the corresponding ends. Then for every nonempty open subset `U` of the open strip `ℝ × (0, 1)` and
every neighbourhood `W` of the graph of `u` over `U`, finitely many Hamiltonian variations in `W`
together with the range of the linearized operator `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of
`J` and of the datum of the pair of pants with Hamiltonians `Hb` capped at `1` along a neck of
length `L` span `L²(ℝ × S¹, F)`. -/
theorem exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_cappedCylinderComponent
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hb : Puncture → ℝ → F → ℝ}
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r))) {L : ℝ}
    (hL : 4 < L) {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension (Hb inf)))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension (Hb zero))) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hb inf t) (xm t)) t)
    (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (Hb inf) hXm 0 1)
      (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hb zero t) (xp t)) t)
    (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (Hb zero) hXp 0 1)
      (xp 0))
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {J : ℝ × ℝ → F → AlmostComplexStructure F}
    (hJ : ContDiff ℝ 2 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJc : ∀ z y, ω.Compatible (J z y)) {R : ℝ} (hJRp : ∀ s t, R ≤ s → J (s, t) = Jp t)
    (hJRm : ∀ s t, s ≤ -R → J (s, t) = Jm t) {u : ℝ × ℝ → F} (hu : ContDiff ℝ 2 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb inf t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ univ ×ˢ Ioo (0 : ℝ) 1)
    {W : Set ((ℝ × ℝ) × F)} (hW : ∀ z ∈ U, W ∈ 𝓝 (z, u z)) :
    ∃ t : Finset (Lp F 2 stripMeasure), (t : Set _) ⊆ ω.hamiltonianVariations
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u W ∧
      (ω.floerSobolevOperator 2 (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u).range ⊔
          Submodule.span ℝ t = ⊤ :=
  exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_of_cylindrical_of_compatible ω
    hω (isCylindricalNearEnds_cappedCylinderComponent hHb (fun r ↦ (hHbs r).of_le (by norm_num))
      hL (fun _ ↦ (hJ.of_le (by norm_num)).contDiffAt) hJRp hJRm)
    hJ (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1)
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I) hJc hu hXm (hHbs inf)
    (hHb inf) hxm hxmper hndm huxm hδm hXp (hHbs zero) (hHb zero) hxp hxpper hndp huxp hδp hU
    hUne hUΩ hW

end TauCeti.SymplecticForm
