/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacewiseCohomology
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant

/-!
# Single-place idelic Brauer invariants

For a finite Galois extension `L/K` of number fields, Shapiro's lemma identifies the second
cohomology of the semi-local units at `v` with the relative Brauer group of `L_w/K_v`, for a
place `w` above `v`. Inflation into `Br K_v`, followed by the local invariant, is injective and
has image the subgroup killed by the local degree `[L_w : K_v]`.

Every element of that subgroup is realized by an idelic cohomology class supported at `v`,
with zero semi-local components at every other finite place and at every infinite place.
Thus a place of full local degree supplies an idelic class with invariant `1 / [L : K]`.
The invariant coordinates are recorded separately at each place, before taking their sum.

The construction combines positive-degree Shapiro with `idelesCohomologyLocalization_surjective`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Proposition 2.5, and Chapter VIII, §4.
* J. Tate, *Global class field theory*, in Cassels and Fröhlich, *Algebraic Number Theory*,
  Chapter VII, §11.
-/

public section
noncomputable section

open CategoryTheory IsDedekindDomain NumberField
open scoped AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
  (σ : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))

/-- Shapiro's identification of semi-local degree-two cohomology with the relative Brauer
group of the completion at the given place `w` above `v`. -/
def semilocalBrauerShapiroEquiv :
    tateCohomology (semilocalUnitsRep L v) 2 ≃+
      groupCohomology (Rep.ofMulDistribMulAction
        Gal(w.adicCompletion L/v.adicCompletion K) (w.adicCompletion L)ˣ) 2 :=
  (v.semilocalUnitsTateCohomologyIsoPos w 2 ≪≫
    (_root_.TateCohomology.isoGroupCohomology 2).app
      (Rep.ofAlgebraAutOnUnits
        (v.adicCompletion K) (w.adicCompletion L))).toLinearEquiv.toAddEquiv

/-- The semi-local Brauer equivalence is Shapiro followed by the Tate-to-ordinary comparison. -/
theorem semilocalBrauerShapiroEquiv_apply
    (x : tateCohomology (semilocalUnitsRep L v) 2) :
    semilocalBrauerShapiroEquiv v w x =
      ((_root_.TateCohomology.isoGroupCohomology 2).app
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))).hom
          ((v.semilocalUnitsTateCohomologyIsoPos w 2).hom x) :=
  (rfl)

/-- The local invariant computed through the chosen place `w` above `v` and embedding
`σ : L_w → K_vˢ`: Shapiro, relative Brauer inflation, then the invariant of `K_v`.
Independence of these choices is not established here. -/
def semilocalInv :
    tateCohomology (semilocalUnitsRep L v) 2 →+ AddCircle (1 : ℚ) :=
  (invMap (v.adicCompletion K)).toAddMonoidHom.comp
    ((relBrInfl (v.adicCompletion K) (w.adicCompletion L) σ).comp
      (semilocalBrauerShapiroEquiv v w).toAddMonoidHom)

/-- The semi-local invariant is the invariant of the inflated Shapiro class. -/
theorem semilocalInv_apply (x : tateCohomology (semilocalUnitsRep L v) 2) :
    semilocalInv v w σ x = invMap (v.adicCompletion K)
      (relBrInfl (v.adicCompletion K) (w.adicCompletion L) σ
        (semilocalBrauerShapiroEquiv v w x)) :=
  (rfl)

/-- A semi-local Brauer class is determined by its invariant. -/
theorem semilocalInv_injective : Function.Injective (semilocalInv v w σ) :=
  (invMap (v.adicCompletion K)).injective.comp
    ((relBrInfl_injective (v.adicCompletion K) (w.adicCompletion L) σ).comp
      (semilocalBrauerShapiroEquiv v w).injective)

@[simp]
theorem semilocalInv_eq_zero_iff
    (x : tateCohomology (semilocalUnitsRep L v) 2) :
    semilocalInv v w σ x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (semilocalInv_injective v w σ)

/-- The possible semi-local invariants are exactly those killed by the local degree. -/
theorem mem_range_semilocalInv_iff (t : AddCircle (1 : ℚ)) :
    t ∈ (semilocalInv v w σ).range ↔
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) • t = 0 := by
  -- Pass from bundled hom composition to a function range to use surjectivity of Shapiro.
  change t ∈ Set.range ((invMap (v.adicCompletion K) ∘
    relBrInfl (v.adicCompletion K) (w.adicCompletion L) σ) ∘
      semilocalBrauerShapiroEquiv v w) ↔ _
  rw [(semilocalBrauerShapiroEquiv v w).surjective.range_comp,
    range_invMap_comp_relBrInfl]
  exact AddSubgroup.torsionBy.nsmul_iff

/-- Every allowable invariant is realized by an idelic class supported at one finite place.
All other semi-local components, including the archimedean ones, vanish. -/
theorem exists_semilocalInv_eq_of_finrank_nsmul_eq_zero (t : AddCircle (1 : ℚ))
    (ht : Module.finrank (v.adicCompletion K) (w.adicCompletion L) • t = 0) :
    ∃ x : tateCohomology (idelesRep K L) ((2 : ℕ) : ℤ),
      semilocalInv v w σ
        (((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map (idelesToSemilocalUnits L v)).hom x) = t ∧
      (∀ u : HeightOneSpectrum (𝓞 K), u ≠ v →
        ((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map (idelesToSemilocalUnits L u)).hom x = 0) ∧
      ∀ u : InfinitePlace K,
        ((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map
          (idelesToInfiniteSemilocalUnits L u)).hom x = 0 := by
  classical
  obtain ⟨y, hy⟩ := (mem_range_semilocalInv_iff v w σ t).mpr ht
  obtain ⟨x, hx⟩ := idelesCohomologyLocalization_surjective K L 2 (DFinsupp.single v y, 0)
  refine ⟨x, ?_, fun u hu ↦ ?_, fun u ↦ ?_⟩
  · have h := congrArg (fun z ↦ z.1 v) hx
    simp only [idelesCohomologyLocalization_fst_apply, DFinsupp.single_eq_same] at h
    exact (congrArg (semilocalInv v w σ) h).trans hy
  · have h := congrArg (fun z ↦ z.1 u) hx
    simpa only [idelesCohomologyLocalization_fst_apply, DFinsupp.single_eq_of_ne hu] using h
  · simpa only [idelesCohomologyLocalization_snd_apply, Pi.zero_apply] using
      congrArg (fun z ↦ z.2 u) hx

/-- A finite place supplies an idelic class with invariant the reciprocal of its local degree,
with zero components at every other place. At a place of full local degree this is `1 / [L : K]`.
The prescribed semi-local component has additive order exactly the local degree. -/
theorem exists_semilocalInv_eq_one_div_finrank :
    ∃ x : tateCohomology (idelesRep K L) ((2 : ℕ) : ℤ),
      semilocalInv v w σ
        (((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map (idelesToSemilocalUnits L v)).hom x) =
          ((1 / Module.finrank (v.adicCompletion K) (w.adicCompletion L) : ℚ) : AddCircle (1 : ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 K), u ≠ v →
        ((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map (idelesToSemilocalUnits L u)).hom x = 0) ∧
      (∀ u : InfinitePlace K,
        ((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map
          (idelesToInfiniteSemilocalUnits L u)).hom x = 0) ∧
      addOrderOf (((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map
        (idelesToSemilocalUnits L v)).hom x) =
          Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  let n := Module.finrank (v.adicCompletion K) (w.adicCompletion L)
  have hn : 0 < n := Module.finrank_pos
  have hord := AddCircle.addOrderOf_period_div (p := (1 : ℚ)) hn
  have ht := addOrderOf_nsmul_eq_zero ((1 / n : ℚ) : AddCircle (1 : ℚ))
  rw [hord] at ht
  obtain ⟨x, hx, hfin, hinf⟩ := exists_semilocalInv_eq_of_finrank_nsmul_eq_zero v w σ
    ((1 / n : ℚ) : AddCircle (1 : ℚ)) ht
  refine ⟨x, hx, hfin, hinf, ?_⟩
  rw [← addOrderOf_injective (semilocalInv v w σ)
    (semilocalInv_injective v w σ), hx]
  exact hord

end TauCeti.ClassFieldTheory
