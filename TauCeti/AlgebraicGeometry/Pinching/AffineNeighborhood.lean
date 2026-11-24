/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# Compatible affine neighbourhoods of a pinching datum

Let `i : Z ⟶ Y` be a closed immersion and `g : Z ⟶ Z'` a closed map of schemes, such as a finite
morphism, and let `z'` be a point of `Z'` whose fibre `g⁻¹(z')` is finite. Suppose the finite set
`i(g⁻¹(z'))` lies in an affine open `W` of `Y`. Then there are affine opens `U ⊆ Y` and
`V ⊆ Z'` with `z' ∈ V` and `i⁻¹(U) = g⁻¹(V)`, that is `U ∩ Z = g⁻¹(V)`. In particular `U` contains
`i(g⁻¹(z'))`. Moreover `U` and `V` can be chosen inside any prescribed open neighbourhoods of
`i(g⁻¹(z'))` and `z'`, so such compatible pairs form a basis of neighbourhoods.

These are the charts on which Ferrand pinches `Y` along `g`: over a compatible pair the pinched
scheme is the spectrum of the fibre product of rings `Γ(Y, U) ×_{Γ(Z, U ∩ Z)} Γ(Z', V)`, and the
basis property lets the affine pinches over overlapping pairs be compared on smaller compatible
pairs.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_preimage_eq_preimage`: compatible affine
  neighbourhoods `U` and `V` with `i⁻¹(U) = g⁻¹(V)`, inside prescribed neighbourhoods.

## References

* D. Ferrand, *Conducteur, descente et pincement*, Bull. Soc. Math. France 131 (2003),
  Théorème 7.1 B and its proof.
* [Stacks Project, Lemma 37.14.2](https://stacks.math.columbia.edu/tag/0E25).
-/

public section

namespace AlgebraicGeometry.Scheme.Hom

variable {Z Y Z' : Scheme}

/-- **Compatible affine neighbourhoods** (Ferrand). Let `i : Z ⟶ Y` be a closed immersion and
`g : Z ⟶ Z'` a closed map, and let `z' : Z'` have finite fibre `g⁻¹(z')` whose image under `i`
lies in an affine open `W` of `Y`. Then for all open neighbourhoods `U₀` of `i(g⁻¹(z'))` and
`V₀` of `z'` there are affine opens `U ≤ U₀` of `Y` and `V ≤ V₀` of `Z'` with `z' ∈ V` and
`i⁻¹(U) = g⁻¹(V)`. Taking `U₀ = W` and `V₀ = ⊤` gives a single compatible pair.

A finite `g` is closed with finite fibres (`AlgebraicGeometry.Scheme.Hom.isClosedMap`,
`AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`). -/
theorem exists_isAffineOpen_preimage_eq_preimage (i : Z ⟶ Y) (g : Z ⟶ Z')
    [IsClosedImmersion i] (hg : IsClosedMap g) {z' : Z'} (hfin : (g ⁻¹' {z'}).Finite)
    {W : Y.Opens} (hW : IsAffineOpen W) (hgW : g ⁻¹' {z'} ⊆ i ⁻¹ᵁ W)
    {U₀ : Y.Opens} (hgU₀ : g ⁻¹' {z'} ⊆ i ⁻¹ᵁ U₀) {V₀ : Z'.Opens} (hV₀ : z' ∈ V₀) :
    ∃ (U : Y.Opens) (V : Z'.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ U ≤ U₀ ∧ V ≤ V₀ ∧
      z' ∈ V ∧ i ⁻¹ᵁ U = g ⁻¹ᵁ V := by
  set F := g ⁻¹' {z'}
  -- Shrink `W` to an affine basic open `W'` that still contains `i(F)` and lies in `U₀`.
  obtain ⟨r, hFr, hrU₀⟩ := hW.exists_basicOpen_superset_le (hfin.image i)
    (Set.image_subset_iff.mpr hgW) (Set.image_subset_iff.mpr hgU₀)
  set W' := Y.basicOpen r
  have hW' : IsAffineOpen W' := hW.basicOpen r
  have hiW' : IsAffineOpen (i ⁻¹ᵁ W') := hW'.preimage i
  have hFW' : F ⊆ i ⁻¹ᵁ W' := Set.image_subset_iff.mp hFr
  -- An affine `V' ∋ z'` inside `V₀`, and a basic open `D(s)` of the affine `i⁻¹(W')` between
  -- `F` and `g⁻¹(V')`.
  obtain ⟨V', hV', hzV', hV'V₀⟩ := exists_isAffineOpen_mem_and_subset hV₀
  have hFV' : F ⊆ g ⁻¹ᵁ V' := fun z hz ↦ g.mem_preimage.mpr (hz.symm ▸ hzV')
  obtain ⟨s, hFs, hsV'⟩ := hiW'.exists_basicOpen_superset_le hfin hFW' hFV'
  -- Since `g` is closed, shrink `V'` to a basic open `D(h) ∋ z'` with `g⁻¹(D(h)) ⊆ D(s)`.
  obtain ⟨M, hM, hMs⟩ := Filter.mem_comap.mp
    (hg.comap_nhds_le ((Z.basicOpen s).isOpen.mem_nhdsSet.mpr hFs))
  obtain ⟨M', hM'M, hM', hzM'⟩ := mem_nhds_iff.mp hM
  obtain ⟨h, hhM, hzh⟩ := hV'.exists_basicOpen_le (V := ⟨M', hM'⟩) ⟨z', hzM'⟩ hzV'
  have hgh : g ⁻¹ᵁ Z'.basicOpen h ≤ Z.basicOpen s := fun _ hx ↦ hMs (hM'M (hhM hx))
  -- `g⁻¹(D(h))` is a basic open of `D(s)`, hence of `i⁻¹(W')`; lift its equation along `i`.
  obtain ⟨t, ht⟩ := hiW'.basicOpen_basicOpen_is_basicOpen s (g.appLE V' _ hsV' h)
  rw [Scheme.basicOpen_appLE, inf_eq_right.mpr hgh] at ht
  obtain ⟨e, rfl⟩ := i.app_surjective W' hW' t
  refine ⟨Y.basicOpen e, Z'.basicOpen h, hW'.basicOpen e, hV'.basicOpen h,
    (Y.basicOpen_le e).trans hrU₀, (Z'.basicOpen_le h).trans hV'V₀, hzh, ?_⟩
  rw [Scheme.preimage_basicOpen, ht]

end AlgebraicGeometry.Scheme.Hom
