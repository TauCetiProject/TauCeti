/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Surjective

/-!
# Hamiltonian variations make the linearized operator of a continuation cylinder onto

A Floer continuation cylinder from `H₋` to `H₊` solves the Floer equation for the `s`-dependent
Hamiltonian `TauCeti.Floer.continuationHomotopy H₋ H₊` and the almost complex structures
`TauCeti.Floer.continuationAlmostComplex h₀ J₋ J₊`. Counts of rigid continuation cylinders define
the continuation maps between Floer complexes of different Hamiltonians, and with different end
Hamiltonians they are also one end of the family behind the unit of the pair-of-pants product. The
moduli spaces are cut out transversally once the universal linearized operator, which adds to
`D_u` the variations of the perturbation, is onto.

This file proves that finitely many Hamiltonian variations already make it onto: for a
continuation cylinder `u` between nondegenerate one-periodic orbits, with compatible end
structures, every nonempty open subset `U` of the open strip `ℝ × (0, 1)` and every
neighbourhood `W` of the graph of `u` over `U`, there are finitely many variation terms
`-X_{δKᵢ}(u)` (`TauCeti.SymplecticForm.hamiltonianVariations`) of smooth variations `δKᵢ` of
compact support in `W` such that every element of `L²(ℝ × S¹, F)` is `D_u ξ + ∑ cᵢ (-X_{δKᵢ}(u))`
(`exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_continuationHomotopy`, in the
namespace `TauCeti.SymplecticForm`). No hypothesis is placed on `u` over `U`, which may be constant
there.

The continuation datum is cylindrical near the ends
(`TauCeti.Floer.isCylindricalNearEnds_continuationHomotopy`) and compatible wherever `J₋` and `J₊`
are (`TauCeti.Floer.compatible_continuationAlmostComplex`), so this is the case of continuation
data of
`exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_of_cylindrical_of_compatible`,
in the namespace `TauCeti.SymplecticForm`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 (the universal operator is onto).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps.
-/

public section

open Set Filter Function Topology MeasureTheory
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer StripSobolev

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Finitely many Hamiltonian variations make the linearized operator of a continuation
cylinder onto.** Let `F` be a finite-dimensional complex inner product space whose symplectic form
`ω` is `Im ⟪·, ·⟫`, let `J₋` and `J₊` be `C²` families of `ω`-compatible almost complex
structures, and let `H₋`, `H₊` be one-periodic, jointly `C³` time-dependent Hamiltonians whose
suspended vector fields are globally Lipschitz, with one-periodic orbits `x₋` of `H₋` and `x₊` of
`H₊` whose initial points are nondegenerate fixed points of the time-one maps. Let `u` be a `C²`
map whose loops converge uniformly to `x₋` at `-∞` and to `x₊` at `+∞`, with slice defects
`∂t u - X_{H±_t}(u)` tending uniformly to zero at the corresponding end. Then for every nonempty
open subset `U` of the open strip `ℝ × (0, 1)` and every neighbourhood `W` of the graph of `u` over
`U`, finitely many Hamiltonian variations in `W` together with the range of the linearized
operator `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the continuation datum from `H₋` to `H₊`
span `L²(ℝ × S¹, F)`. -/
theorem exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_continuationHomotopy
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {J₀ : AlmostComplexStructure F}
    (h₀ : ω.Compatible J₀) {Jm Jp : ℝ → F → AlmostComplexStructure F}
    {hJmt : ∀ t x, ω.Tames (Jm t x)} {hJpt : ∀ t x, ω.Tames (Jp t x)}
    (hJm : ContDiff ℝ 2 fun p : ℝ × F ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 2 fun p : ℝ × F ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJmc : ∀ t x, ω.Compatible (Jm t x)) (hJpc : ∀ t x, ω.Compatible (Jp t x))
    {Hm Hp : ℝ → F → ℝ} {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1)
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    {u : ℝ × ℝ → F} (hu : ContDiff ℝ 2 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ univ ×ˢ Ioo (0 : ℝ) 1)
    {W : Set ((ℝ × ℝ) × F)} (hW : ∀ z ∈ U, W ∈ 𝓝 (z, u z)) :
    ∃ t : Finset (Lp F 2 stripMeasure), (t : Set _) ⊆ ω.hamiltonianVariations
        (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp hJmt hJpt w y).toLinearMap
          |>.toContinuousLinearMap)
        (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u W ∧
      (ω.floerSobolevOperator 2
        (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp hJmt hJpt w y).toLinearMap
          |>.toContinuousLinearMap)
        (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u).range ⊔ Submodule.span ℝ t = ⊤ :=
  exists_finset_subset_hamiltonianVariations_range_sup_span_eq_top_of_cylindrical_of_compatible ω
    hω (isCylindricalNearEnds_continuationHomotopy h₀ (hJm.of_le (by norm_num))
      (hJp.of_le (by norm_num)) (hHm.of_le (by norm_num)) (hHp.of_le (by norm_num)) u)
    (contDiff_continuationAlmostComplex h₀ hJm hJp) contDiff_const
    (contDiff_uncurry_continuationHomotopy hHm hHp)
    (fun _ _ ↦ compatible_continuationAlmostComplex h₀ (hJmc _ _) (hJpc _ _)) hu hXm hHmper hxm
    hxmper hndm huxm hδm hXp hHpper hxp hxpper hndp huxp hδp hU hUne hUΩ hW

end TauCeti.SymplecticForm
