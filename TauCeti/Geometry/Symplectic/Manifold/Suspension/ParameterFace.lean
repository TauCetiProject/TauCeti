/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Prescribed
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Seam-compatible families with prescribed values on closed parameter faces

Let `φ` be a symplectomorphism of a finite-dimensional manifold `(M, σ)`, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its mapping torus and let
`X_φ = (ℝ / ℤ)_s × Y_φ` carry the form `Ω = ds ∧ dt + σ_v`. A block almost complex structure on
`X_φ` descends from a *vertical family* `K_((s,t),x)` of `σ`-compatible structures on `T_x M`,
smooth in `((s, t), x)`, periodic in `s` and satisfying the seam identity
`dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).

This file specialises the relative construction of `Suspension/Prescribed.lean` to families over
a parameter manifold `Λ`, for instance a compact manifold with corners, with values prescribed on
a closed set `F ⊆ Λ`, such as a union of closed faces. Let `K_l` be a background family of
vertical families, jointly smooth in `(l, ((s, t), x))`, each `σ`-compatible, periodic in `s` and
seam-compatible; the vertical families `TauCeti.SmoothMappingTorus.seamFamily` built from a
smooth family of compatible structures `K₀ l` on `M` are an example
(`TauCeti.SmoothMappingTorus.contMDiff_seamFamily_family`). Let `L_l` be a second family with the
same properties, but given only for parameters `l` in an open neighbourhood `W` of `F`.
Prescribing a single family on a neighbourhood of all of `F` encodes the agreement of the data on
overlaps and face intersections. Then there is a family `K'_l` with all these properties for every
`l ∈ Λ`, equal to `L_l` for `l ∈ F` and to `K_l` for `l ∉ W`
(`TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eqOn`). It also equals `K_l` at every
point where `L_l` already does. With the seam-family background
(`TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eqOn_seamFamily`) this is the
compatibility with the fixed time-end collars: where the prescribed data restrict to the seam
family on a collar `|t - k| ≤ 1/3`, for instance to `K₀ l` on `|t| ≤ 1/3`, so does the result.

The family is the cutoff interpolation of
`TauCeti.SmoothMappingTorus.exists_verticalFamily_eq_of_invariant_cutoff`, for the open set
`W × ((ℝ × ℝ) × M)` and a cutoff that depends only on the parameter: a smooth `ρ : Λ → [0, 1]`
equal to one exactly on `F` and with topological support in `W`. Both are invariant under the
deck transformations, so the construction never passes to the mapping torus. Hence the seam
identity may be that of a diffeomorphism `Φ l` varying with the parameter, and neither a
separation nor a countability assumption on `M` is needed, unlike for the closed regions of
`TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn`.

The descended block structures `J_l` on `X_φ` are then jointly smooth in `(l, y)`, compatible
with `Ω`, send `∂_s` to the suspension vector field `T`, act through `L_l` for `l ∈ F`, are the
structures descended from `K_l` for `l ∉ W`, and agree with them wherever `L_l` is `K_l`
(`TauCeti.SmoothMappingTorus.exists_suspensionAlmostComplexStructure_family_eqOn`). With the
seam-family background these are the structures
`TauCeti.SmoothMappingTorus.seamAlmostComplexStructure` built from `K₀ l`
(`TauCeti.SmoothMappingTorus.exists_suspensionAlmostComplexStructure_family_eqOn_seamFamily`).
Neither closedness of `σ` nor compactness of `M` or of `Λ` is used. For the descended structures
the symplectomorphism `φ` is the same for every parameter, since the structures `J_l` live on the
one manifold `X_φ`.

## Main results

* `TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eqOn`: relative extension of
  parametrized seam-compatible vertical families from a closed set of parameters.
* `TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eqOn_seamFamily`: the same with the
  seam families as background.
* `TauCeti.SmoothMappingTorus.exists_suspensionAlmostComplexStructure_family_eqOn`: the
  descended smooth family of `Ω`-compatible block structures on `X_φ`, with prescribed vertical
  part over the closed set of parameters, and the structures descended from the background away
  from its neighbourhood and wherever the prescription agrees with the background.
* `TauCeti.SmoothMappingTorus.exists_suspensionAlmostComplexStructure_family_eqOn_seamFamily`: the
  same with the seam structures as background, keeping the collar structures wherever the
  prescription has them.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  `ℝ × Y_φ`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Sections 2.5 and 4.1 (compatible Cayley charts and relative extension).
-/

public noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} (hσn : σ.IsNondegenerate)
  {Λ : Type*} {EΛ HΛ : Type*} [NormedAddCommGroup EΛ] [NormedSpace ℝ EΛ] [TopologicalSpace HΛ]
  {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ] [ChartedSpace HΛ Λ]
  [IsManifold IΛ ∞ Λ] [FiniteDimensional ℝ EΛ] [T2Space Λ] [SigmaCompactSpace Λ]
  {Φ : Λ → M ≃ₘ⟮I, I⟯ M}
  {K : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
  (hK : ∀ l p, (hσn.symplecticFormAt p.2).Compatible (K l p))
  {W : Set Λ} (L : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2))
  (hL : ∀ l ∈ W, ∀ p, (hσn.symplecticFormAt p.2).Compatible (L l p))

/-! ### Relative parametrized vertical families -/

include hK hL in
/-- **Parametrized seam-compatible vertical families with values prescribed on a closed set of
parameters.** Let `Φ l` be diffeomorphisms of `M` and let `K l` be a family, over a Hausdorff
σ-compact finite-dimensional manifold `Λ`, of `σ`-compatible vertical families on
`(ℝ × ℝ) × M`, jointly smooth in `(l, ((s, t), x))`, periodic in `s` and satisfying the seam
identity of `Φ l`, and let `L l` be a family with these properties for the parameters `l` in an
open set `W`. For every closed set `F ⊆ W`, for instance a union of closed faces of `Λ`, there is a
family `K' l` with these properties for every `l`, which is `L l` for `l ∈ F`, is `K l` for
`l ∉ W`, and agrees with `K l` at every point where `L l` does. -/
theorem exists_verticalFamily_family_eqOn
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hKp : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I (Φ l).symm p.2 (K l p v) =
        K l (p.1 + (0, 1), (Φ l).symm p.2) (mfderiv I I (Φ l).symm p.2 v))
    (hW : IsOpen W) {F : Set Λ} (hF : IsClosed F) (hFW : F ⊆ W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hLp : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I (Φ l).symm p.2 (L l p v) =
        L l (p.1 + (0, 1), (Φ l).symm p.2) (mfderiv I I (Φ l).symm p.2 v)) :
    ∃ K' : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          r.2.2 (K' r.1 r.2).toLinearMap.toContinuousLinearMap) ∧
      (∀ l p, K' l (p.1 + (1, 0), p.2) = K' l p) ∧
      (∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I (Φ l).symm p.2 (K' l p v) =
          K' l (p.1 + (0, 1), (Φ l).symm p.2) (mfderiv I I (Φ l).symm p.2 v)) ∧
      (∀ l p, (hσn.symplecticFormAt p.2).Compatible (K' l p)) ∧
      (∀ l ∈ F, K' l = L l) ∧
      (∀ l ∉ W, K' l = K l) ∧
      (∀ l p, (l ∈ W → L l p = K l p) → K' l p = K l p) := by
  obtain ⟨ρ, hsρ, hrange, ht, hone⟩ :=
    hF.exists_contMDiff_tsupport_subset_eq_one_iff (I := IΛ) hW hFW
  -- Cut off over the open set `W × ((ℝ × ℝ) × M)`, with a weight depending only on the parameter;
  -- both are invariant under the deck transformations.
  obtain ⟨K', hK's, hK'p, hK't, hK'c, hlocal, -, hagree⟩ :=
    exists_verticalFamily_eq_of_invariant_cutoff hσn (V := Prod.fst ⁻¹' W) hK
      (fun l p hl ↦ hL l hl p) (fun r ↦ ρ r.1) (fun r ↦ hrange r.1) hKs hKp hKt
      (hW.preimage continuous_fst) (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl)
      (hLs.mono fun _ hr ↦ ⟨hr, mem_univ _⟩) (fun l p hl ↦ hLp l hl p) (fun l p hl ↦ hLt l hl p)
      (hsρ.comp contMDiff_fst)
      ((tsupport_comp_subset_preimage ρ continuous_fst).trans (preimage_mono ht))
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  exact ⟨K', hK's, hK'p, hK't, hK'c, fun l hl ↦ funext fun p ↦ hlocal l p ((hone l).mp hl),
    fun l hl ↦ funext fun p ↦ hagree l p fun h ↦ (hl h).elim, hagree⟩

include hL in
/-- **Parametrized seam-compatible vertical families with values prescribed on a closed set of
parameters, around the seam families.** Let `φ` preserve the nondegenerate form `σ`, and let
`K₀ l` be a smooth family of `σ`-compatible almost complex structures on `M`, over a Hausdorff
σ-compact finite-dimensional manifold `Λ`. Let `L l` be a family of vertical families on
`(ℝ × ℝ) × M` given for the parameters `l` in an open set `W`, jointly smooth there,
`σ`-compatible, periodic in `s` and satisfying the seam identity of `φ`. For every closed set
`F ⊆ W` there is a family `K' l` with these properties for every `l`, which is `L l` for `l ∈ F`,
is the seam family of `K₀ l` (`TauCeti.SmoothMappingTorus.seamFamily`) for `l ∉ W`, and agrees
with it at every point where `L l` does. -/
theorem exists_verticalFamily_family_eqOn_seamFamily
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    {K₀ : Λ → SmoothAlmostComplexStructure I M} (hK₀ : ∀ l, σ.Compatible (K₀ l))
    (hK₀s : ContMDiff (IΛ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Λ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₀ q.1).toEndomorphism q.2)))
    (hW : IsOpen W) {F : Set Λ} (hF : IsClosed F) (hFW : F ⊆ W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hLp : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ K' : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          r.2.2 (K' r.1 r.2).toLinearMap.toContinuousLinearMap) ∧
      (∀ l p, K' l (p.1 + (1, 0), p.2) = K' l p) ∧
      (∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K' l p v) =
          K' l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ l p, (hσn.symplecticFormAt p.2).Compatible (K' l p)) ∧
      (∀ l ∈ F, K' l = L l) ∧
      (∀ l ∉ W, K' l = seamFamily hσ (hK₀ l)) ∧
      (∀ l p, (l ∈ W → L l p = seamFamily hσ (hK₀ l) p) → K' l p = seamFamily hσ (hK₀ l) p) :=
  exists_verticalFamily_family_eqOn hσn (fun l ↦ compatible_seamFamily hσ (hK₀ l) hσn) L hL
    (Φ := fun _ ↦ φ) (contMDiff_seamFamily_family hσ hK₀ hK₀s)
    (fun l ↦ seamFamily_add_fst hσ (hK₀ l)) (fun l ↦ mfderiv_symm_seamFamily hσ (hK₀ l)) hW hF hFW
    hLs hLp hLt

/-! ### Descended families of block structures -/

section Descended

variable [T2Space M] [LocallyCompactSpace M]

include hK hL in
/-- **Families of compatible block structures on a symplectic suspension with values prescribed on
a closed set of parameters.** Let `φ` preserve the nondegenerate form `σ`. With the hypotheses of
`exists_verticalFamily_family_eqOn`, for every closed set `F ⊆ W` there is a family `J l` of almost
complex structures on `(ℝ / ℤ) × Y_φ`, jointly smooth in `(l, y)`, such that:

* each `J l` is compatible with `Ω = ds ∧ dt + σ_v` and sends `∂_s` to the suspension vector field
  `T`;
* for `l ∈ F`, in the coordinates `(s, t, x)`, `J l` sends `a ∂_s + b ∂_t + v` to
  `-b ∂_s + a ∂_t + L_l((s, t), x) v`;
* for `l ∉ W`, `J l` is the structure descended from `K l`
  (`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`);
* at every point `([s], [t, x])` where `L l` is `K l`, `J l` agrees with the structure descended
  from `K l`. -/
theorem exists_suspensionAlmostComplexStructure_family_eqOn
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hKp : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K l p v) =
        K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hW : IsOpen W) {F : Set Λ} (hF : IsClosed F) (hFW : F ⊆ W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hLp : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ J : Λ → SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
        (UnitAddCircle × SmoothMappingTorus φ),
      ContMDiff (IΛ.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I)))
        ((𝓘(ℝ).prod (𝓘(ℝ).prod I)).prod 𝓘(ℝ, (ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))) ∞
        (fun r : Λ × (UnitAddCircle × SmoothMappingTorus φ) ↦
          TotalSpace.mk' ((ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))
            (E := fun y : UnitAddCircle × SmoothMappingTorus φ ↦
              TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y →L[ℝ]
                TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y) r.2
            ((J r.1).toEndomorphism r.2)) ∧
      (∀ l, (suspensionForm φ σ hσ).Compatible (J l)) ∧
      (∀ l y, J l y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
        (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2)) ∧
      (∀ l ∈ F, ∀ (s t : ℝ) (x : M) (a b : ℝ) (v : TangentSpace I x),
        J l ((s : UnitAddCircle), mk φ t x)
            ((Manifold.tangentSpaceProdEquiv _).symm
              (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
          (Manifold.tangentSpaceProdEquiv _).symm
            (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
              ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, L l ((s, t), x) v)))) ∧
      (∀ l ∉ W, J l = suspensionAlmostComplexStructure φ
        (hKs.comp ((contMDiff_const (c := l)).prodMk contMDiff_id)) (hKp l) (hKt l)) ∧
      (∀ l (s t : ℝ) (x : M), (l ∈ W → L l ((s, t), x) = K l ((s, t), x)) →
        J l ((s : UnitAddCircle), mk φ t x) =
          suspensionAlmostComplexStructure φ
            (hKs.comp ((contMDiff_const (c := l)).prodMk contMDiff_id)) (hKp l) (hKt l)
            ((s : UnitAddCircle), mk φ t x)) := by
  obtain ⟨K', hK's, hK'p, hK't, hK'c, hlocal, hbase, hagree⟩ :=
    exists_verticalFamily_family_eqOn hσn hK L hL (Φ := fun _ ↦ φ) hKs hKp hKt hW hF hFW hLs hLp
      hLt
  refine ⟨fun l ↦ suspensionAlmostComplexStructure φ
      (hK's.comp (contMDiff_const.prodMk contMDiff_id)) (hK'p l) (hK't l),
    contMDiff_suspensionAlmostComplexStructure_family φ hK's hK'p hK't,
    fun l ↦ compatible_suspensionAlmostComplexStructure φ _ _ _ hσn (hK'c l),
    fun l ↦ suspensionAlmostComplexStructure_apply_symm_one_zero φ _ _ _,
    fun l hl s t x a b v ↦ ?_, fun l hl ↦ ?_, fun l s t x h ↦ funext fun ξ ↦ ?_⟩
  · -- `dsimp` evaluates the slice `p ↦ (l, p)` of the parametrized vertical family at `l`.
    rw [suspensionAlmostComplexStructure_mk]
    dsimp only [id]
    rw [hlocal l hl]
  · -- Off `W` the two vertical families are equal.
    dsimp only
    congr 1
    exact hbase l hl
  · obtain ⟨a, b, v, rfl⟩ := exists_eq_symm_tangentSpaceProdEquiv (φ := φ) _ t x ξ
    rw [suspensionAlmostComplexStructure_mk, suspensionAlmostComplexStructure_mk]
    dsimp only [id]
    rw [hagree l _ h]

include hL in
/-- **Families of compatible block structures on a symplectic suspension with values prescribed on
a closed set of parameters, around the seam structures.** Let `φ` preserve the nondegenerate form
`σ`, and let `K₀ l` be a smooth family of `σ`-compatible almost complex structures on `M`, over a
Hausdorff σ-compact finite-dimensional manifold `Λ`. Let `L l` be a family of vertical families on
`(ℝ × ℝ) × M` given for the parameters `l` in an open set `W`, jointly smooth there,
`σ`-compatible, periodic in `s` and satisfying the seam identity. For every closed set `F ⊆ W`
there is a family `J l` of almost complex structures on `(ℝ / ℤ) × Y_φ`, jointly smooth in
`(l, y)`, such that:

* each `J l` is compatible with `Ω = ds ∧ dt + σ_v` and sends `∂_s` to the suspension vector field
  `T`;
* for `l ∈ F`, in the coordinates `(s, t, x)`, `J l` sends `a ∂_s + b ∂_t + v` to
  `-b ∂_s + a ∂_t + L_l((s, t), x) v`;
* for `l ∉ W`, `J l` is the seam structure built from `K₀ l`;
* at every point `([s], [t, x])` where `L l` is the seam family of `K₀ l`, `J l` agrees with the
  seam structure. In particular, on the collars `|t - k| ≤ 1/3` where `L l` is the corresponding
  pullback of `K₀ l` (`TauCeti.SmoothMappingTorus.seamFamily_of_mem_Icc`), `J l` keeps the seam
  structure, which for `|t| ≤ 1/3` sends `a ∂_s + b ∂_t + v` to `-b ∂_s + a ∂_t + K₀ l v`
  (`TauCeti.SmoothMappingTorus.seamAlmostComplexStructure_mk`). -/
theorem exists_suspensionAlmostComplexStructure_family_eqOn_seamFamily
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    {K₀ : Λ → SmoothAlmostComplexStructure I M} (hK₀ : ∀ l, σ.Compatible (K₀ l))
    (hK₀s : ContMDiff (IΛ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Λ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₀ q.1).toEndomorphism q.2)))
    (hW : IsOpen W) {F : Set Λ} (hF : IsClosed F) (hFW : F ⊆ W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hLp : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ J : Λ → SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
        (UnitAddCircle × SmoothMappingTorus φ),
      ContMDiff (IΛ.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I)))
        ((𝓘(ℝ).prod (𝓘(ℝ).prod I)).prod 𝓘(ℝ, (ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))) ∞
        (fun r : Λ × (UnitAddCircle × SmoothMappingTorus φ) ↦
          TotalSpace.mk' ((ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))
            (E := fun y : UnitAddCircle × SmoothMappingTorus φ ↦
              TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y →L[ℝ]
                TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y) r.2
            ((J r.1).toEndomorphism r.2)) ∧
      (∀ l, (suspensionForm φ σ hσ).Compatible (J l)) ∧
      (∀ l y, J l y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
        (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2)) ∧
      (∀ l ∈ F, ∀ (s t : ℝ) (x : M) (a b : ℝ) (v : TangentSpace I x),
        J l ((s : UnitAddCircle), mk φ t x)
            ((Manifold.tangentSpaceProdEquiv _).symm
              (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
          (Manifold.tangentSpaceProdEquiv _).symm
            (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
              ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, L l ((s, t), x) v)))) ∧
      (∀ l ∉ W, J l = seamAlmostComplexStructure hσ (hK₀ l)) ∧
      (∀ l (s t : ℝ) (x : M), (l ∈ W → L l ((s, t), x) = seamFamily hσ (hK₀ l) ((s, t), x)) →
        J l ((s : UnitAddCircle), mk φ t x) =
          seamAlmostComplexStructure hσ (hK₀ l) ((s : UnitAddCircle), mk φ t x)) := by
  -- The background is the family of seam families built from `K₀ l`, whose descended structures
  -- are the seam structures.
  obtain ⟨J, hJs, hJc, hJT, hlocal, hbase, hagree⟩ :=
    exists_suspensionAlmostComplexStructure_family_eqOn hσn
      (fun l ↦ compatible_seamFamily hσ (hK₀ l) hσn) L hL hσ
      (contMDiff_seamFamily_family hσ hK₀ hK₀s) (fun l ↦ seamFamily_add_fst hσ (hK₀ l))
      (fun l ↦ mfderiv_symm_seamFamily hσ (hK₀ l)) hW hF hFW hLs hLp hLt
  refine ⟨J, hJs, hJc, hJT, hlocal, fun l hl ↦ ?_, fun l s t x h ↦ ?_⟩
  · rw [hbase l hl, seamAlmostComplexStructure_def]
  · rw [hagree l s t x h, seamAlmostComplexStructure_def]

end Descended

end TauCeti.SmoothMappingTorus
