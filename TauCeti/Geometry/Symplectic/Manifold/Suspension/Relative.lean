/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.SeamFamily
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Extension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Block structures on a symplectic suspension prescribed on a closed region

Let `φ` be a symplectomorphism of a finite-dimensional manifold `M` with symplectic form `σ`,
let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its mapping torus and let
`X_φ = (ℝ / ℤ)_s × Y_φ` carry the form `Ω = ds ∧ dt + σ_v`. Block almost complex structures on
`X_φ` descend from vertical families `K_((s,t),x)` of almost complex structures on `T_x M` along the
covering map `q : (ℝ × ℝ) × M → X_φ`, `((s, t), x) ↦ ([s], [t, x])`, provided the family is
periodic in `s` and satisfies the seam identity
`dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).

This file extends such families from a closed region. Let `A ⊆ U ⊆ X_φ` with `A` closed and `U`
open, and let `K` be a vertical family prescribed only over the deck-invariant open set `q⁻¹ U`:
smooth and `σ`-compatible there, periodic in `s` and satisfying the seam identity there. Given any
background vertical family `K₀` that is smooth, compatible, periodic and seam-compatible
everywhere, there is a vertical family `K'` with the same four properties everywhere which equals
`K` over `q⁻¹ A` and `K₀` outside `q⁻¹ U`
(`TauCeti.SmoothMappingTorus.exists_vertical_family_eqOn`).

The family `K'` is the Cayley cutoff of `K` against `K₀`
(`TauCeti.SmoothTwoForm.IsNondegenerate.cayleyCutoff`) with weight `ρ ∘ q`, for a smooth cutoff
`ρ` on `X_φ` that is one on `A` and supported in `U`. The weight is invariant under the deck
transformations because it is pulled back from `X_φ`, and the Cayley cutoff commutes with the
differentials `dφ⁻¹` intertwining the two families, so the seam identity survives the cutoff. No
`φ`-invariance of `K` or of `K₀` is needed beyond the seam identity, and no compactness of `M`.

Descending `K'` built against the seam family of a `σ`-compatible structure `J₀` on `M`
(`TauCeti.SmoothMappingTorus.seamFamily`) gives a smooth block structure on `X_φ` that is compatible
with `Ω`, sends `∂_s` to the suspension vector field `T`, is the block structure of `K` over `A`,
and acts as `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure` outside `U`
(`TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_eqOn`). A region of the mapping torus
itself is the case `A = univ ×ˢ A_Y` of a product with the whole `s`-circle.

## Main results

* `TauCeti.SmoothMappingTorus.exists_vertical_family_eqOn`: a vertical family prescribed over the
  preimage of a neighbourhood of a closed set extends to a global smooth, compatible, periodic and
  seam-compatible family, equal to a given background family away from the neighbourhood.
* `TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_eqOn`: the corresponding
  `Ω`-compatible block structure on `X_φ`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Sections 2.5 and 4.1 (compatible Cayley charts and relative extension of
  compatible almost complex structures).
* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  `ℝ × Y_φ`).
-/

public noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M}

/-- **Relative extension of seam-compatible vertical families.** Let `A ⊆ U` be a closed and an open
subset of `X_φ = (ℝ / ℤ) × Y_φ`, and let `K` be a vertical family on `(ℝ × ℝ) × M` that is smooth,
`σ`-compatible, periodic in `s` and seam-compatible over the preimage of `U` under the covering
map. Then for every smooth, `σ`-compatible, periodic and seam-compatible background family `K₀`
there is a family `K'` with these four properties everywhere, equal to `K` over the preimage of
`A` and to `K₀` outside the preimage of `U`. -/
theorem exists_vertical_family_eqOn (hσn : σ.IsNondegenerate)
    {K₀ : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
    (hK₀s : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K₀ p).toLinearMap.toContinuousLinearMap))
    (hK₀ : ∀ p, (hσn.symplecticFormAt p.2).Compatible (K₀ p))
    (hK₀per : ∀ p : (ℝ × ℝ) × M, K₀ (p.1 + (1, 0), p.2) = K₀ p)
    (hK₀seam : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K₀ p v) = K₀ (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    {U A : Set (UnitAddCircle × SmoothMappingTorus φ)} (hU : IsOpen U) (hA : IsClosed A)
    (hAU : A ⊆ U) {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K p).toLinearMap.toContinuousLinearMap) (suspensionCover φ ⁻¹' U))
    (hK : ∀ p ∈ suspensionCover φ ⁻¹' U, (hσn.symplecticFormAt p.2).Compatible (K p))
    (hKper : ∀ p ∈ suspensionCover φ ⁻¹' U, K (p.1 + (1, 0), p.2) = K p)
    (hKseam : ∀ p ∈ suspensionCover φ ⁻¹' U, ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ K' : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          p.2 (K' p).toLinearMap.toContinuousLinearMap) ∧
      (∀ p, (hσn.symplecticFormAt p.2).Compatible (K' p)) ∧
      (∀ p : (ℝ × ℝ) × M, K' (p.1 + (1, 0), p.2) = K' p) ∧
      (∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K' p v) =
          K' (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ p ∈ suspensionCover φ ⁻¹' A, K' p = K p) ∧
      (∀ p ∉ suspensionCover φ ⁻¹' U, K' p = K₀ p) := by
  -- A smooth cutoff on `X_φ`, one near `A` and zero near the complement of `U`.
  have : LocallyCompactSpace (ModelProd ℝ (ModelProd ℝ H)) :=
    (𝓘(ℝ).prod (𝓘(ℝ).prod I)).locallyCompactSpace
  have : LocallyCompactSpace (UnitAddCircle × SmoothMappingTorus φ) :=
    ChartedSpace.locallyCompactSpace (ModelProd ℝ (ModelProd ℝ H)) _
  obtain ⟨ρ, h0, h1, hρ⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (n := ⊤) hU.isClosed_compl hA (disjoint_compl_left_iff_subset.2 hAU)
  have hsupp : tsupport ρ ⊆ U := fun y hy ↦ by_contra fun hyU ↦
    (notMem_tsupport_iff_eventuallyEq.2 (h0.filter_mono (nhds_le_nhdsSet hyU))) hy
  have hρs := ρ.contMDiff
  have hone : ∀ y ∈ A, ρ y = 1 := fun y hy ↦ h1.self_of_nhdsSet y hy
  have hq := (isLocalDiffeomorph_suspensionCover φ).contMDiff
  -- The weight `ρ ∘ q` is pulled back from `X_φ`, so it is invariant under the deck
  -- transformations, and so is the prescribed region `q⁻¹ U`.
  have hW : IsOpen (suspensionCover φ ⁻¹' U) := hU.preimage hq.continuous
  have hρW : tsupport (ρ ∘ suspensionCover φ) ⊆ suspensionCover φ ⁻¹' U :=
    (tsupport_comp_subset_preimage ρ hq.continuous).trans (preimage_mono hsupp)
  have hper (p : (ℝ × ℝ) × M) : suspensionCover φ (p.1 + (1, 0), p.2) = suspensionCover φ p := by
    simpa using suspensionCover_deck φ 1 0 p
  have hseam (p : (ℝ × ℝ) × M) :
      suspensionCover φ (p.1 + (0, 1), φ.symm p.2) = suspensionCover φ p := by
    simpa [zpow_neg, Diffeomorph.inv_apply] using suspensionCover_deck φ 0 1 p
  have hρ' (p : (ℝ × ℝ) × M) : (ρ ∘ suspensionCover φ) p ∈ Icc 0 1 := hρ _
  refine ⟨hσn.cayleyCutoff (f := Prod.snd) hK₀ hK hρ',
    hσn.contMDiff_cayleyCutoff hK₀ hK hρ' contMDiff_snd hW hK₀s hKs (hρs.comp hq) hρW,
    hσn.compatible_cayleyCutoff hK₀ hK hρ', fun p ↦ ?_, fun p v ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ hσn.cayleyCutoff_of_notMem hK₀ hK hρ' hp⟩
  · -- Periodicity in `s`: the identity of `T_x M` intertwines the families at `p` and `p + ∂_s`.
    ext v
    have := hσn.apply_cayleyCutoff_apply hK₀ hK hρ' (q := p) (q' := (p.1 + (1, 0), p.2))
      (ContinuousLinearEquiv.refl ℝ _) (fun v ↦ by simp [hK₀per p])
      (fun hp v ↦ by simp [hKper p hp]) (by simp only [mem_preimage, hper p])
      (by simp [hper p]) v
    simpa using this.symm
  · -- The seam identity: `dφ⁻¹` intertwines the families at `p` and at its seam translate.
    set L := φ.symm.mfderivToContinuousLinearEquiv (by simp) p.2
    have hL (w : TangentSpace I p.2) : L w = mfderiv I I φ.symm p.2 w := by
      rw [← ContinuousLinearEquiv.coe_coe, Diffeomorph.mfderivToContinuousLinearEquiv_coe]
    have := hσn.apply_cayleyCutoff_apply hK₀ hK hρ' (q := p) (q' := (p.1 + (0, 1), φ.symm p.2))
      L (fun w ↦ by simpa only [hL] using hK₀seam p w)
      (fun hp w ↦ by simpa only [hL] using hKseam p hp w)
      (by simp only [mem_preimage, hseam p]) (by simp [hseam p]) v
    simpa only [hL] using this
  · exact hσn.cayleyCutoff_of_eq_one hK₀ hK hρ' (hAU hp) (hone _ hp)

variable (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
  {J₀ : SmoothAlmostComplexStructure I M} (hJ₀ : σ.Compatible J₀)

include hσ hJ₀ in
/-- **Compatible block structures on a symplectic suspension, prescribed on a closed region.** Let
`A ⊆ U` be a closed and an open subset of `X_φ = (ℝ / ℤ) × Y_φ`, and let `K` be a vertical family
that is smooth, `σ`-compatible, periodic in `s` and seam-compatible over the preimage of `U` under
the covering map. Then there is a smooth almost complex structure `J` on `X_φ`, compatible with
`Ω = ds ∧ dt + σ_v`, sending `∂_s` to the suspension vector field `T` everywhere, acting over `A`
as the block structure `a ∂_s + b ∂_t + v ↦ -b ∂_s + a ∂_t + K v`, and acting outside `U` as the
structure `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure` built from `J₀`. Both actions are
stated on the vectors `a ∂_s + b ∂_t + v` of the coordinates `(s, t, x)`. -/
theorem exists_compatible_suspensionForm_eqOn
    {U A : Set (UnitAddCircle × SmoothMappingTorus φ)} (hU : IsOpen U) (hA : IsClosed A)
    (hAU : A ⊆ U) {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K p).toLinearMap.toContinuousLinearMap) (suspensionCover φ ⁻¹' U))
    (hK : ∀ p ∈ suspensionCover φ ⁻¹' U,
      (hJ₀.isNondegenerate.symplecticFormAt p.2).Compatible (K p))
    (hKper : ∀ p ∈ suspensionCover φ ⁻¹' U, K (p.1 + (1, 0), p.2) = K p)
    (hKseam : ∀ p ∈ suspensionCover φ ⁻¹' U, ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
        (UnitAddCircle × SmoothMappingTorus φ),
      (suspensionForm φ σ hσ).Compatible J ∧
      (∀ y, J y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
        (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2)) ∧
      (∀ (s t : ℝ) (x : M), ((s : UnitAddCircle), mk φ t x) ∈ A →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            (Manifold.tangentSpaceProdEquiv _).symm
              (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K ((s, t), x) v)))) ∧
      (∀ (s t : ℝ) (x : M), ((s : UnitAddCircle), mk φ t x) ∉ U →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            seamAlmostComplexStructure hσ hJ₀ ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))))) := by
  obtain ⟨K', hK's, hK', hK'per, hK'seam, hK'A, hK'U⟩ :=
    exists_vertical_family_eqOn hJ₀.isNondegenerate (contMDiff_seamFamily hσ hJ₀)
      (compatible_seamFamily hσ hJ₀ hJ₀.isNondegenerate) (seamFamily_add_fst hσ hJ₀)
      (mfderiv_symm_seamFamily hσ hJ₀) hU hA hAU hKs hK hKper hKseam
  refine ⟨suspensionAlmostComplexStructure φ hK's hK'per hK'seam,
    compatible_suspensionAlmostComplexStructure φ _ _ _ hJ₀.isNondegenerate hK',
    suspensionAlmostComplexStructure_apply_symm_one_zero φ _ _ _, fun s t x hA a b v ↦ ?_,
    fun s t x hU a b v ↦ ?_⟩
  · rw [suspensionAlmostComplexStructure_mk, hK'A ((s, t), x) (by simpa using hA)]
  · rw [suspensionAlmostComplexStructure_mk, seamAlmostComplexStructure_mk_apply,
      hK'U ((s, t), x) (by simpa using hU)]

end TauCeti.SmoothMappingTorus
