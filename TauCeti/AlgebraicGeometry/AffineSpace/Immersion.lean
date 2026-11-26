/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.QuasiAffine

import TauCeti.AlgebraicGeometry.Morphisms.Immersion
import TauCeti.RingTheory.Localization.Away.FiniteType

/-!
# Immersions of quasi-affine schemes into affine space

A morphism locally of finite type from a quasi-affine scheme factors through an immersion
into a finite-dimensional affine space over its target. The coordinates in
`AffineSpace.homOfVector` come from a finite cover by affine basic opens and numerators of
generators on those opens.

## References

* [The Stacks Project, Lemma 29.40.2](https://stacks.math.columbia.edu/tag/04II).
-/

public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace AffineSpace

/-- Restricting the coordinates before pulling them back along `homOfVector` gives the
corresponding restricted entries of the coordinate family. -/
@[simp]
lemma homOfVector_appLE_coord {X S : Scheme.{u}} {ι : Type u}
    (f : X ⟶ S) (v : ι → Γ(X, ⊤)) (W : 𝔸(ι; S).Opens) (U : X.Opens)
    (e : U ≤ AffineSpace.homOfVector f v ⁻¹ᵁ W) (i : ι) :
    (AffineSpace.homOfVector f v).appLE W U e
      (𝔸(ι; S).presheaf.map (homOfLE le_top).op (AffineSpace.coord S i)) =
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (v i) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  -- At the top open, `appLE` is `appTop` followed by restriction.
  change X.presheaf.map _ ((homOfVector f v).appTop _) = _
  rw [homOfVector_appTop_coord]
  rfl

end AffineSpace

namespace Scheme.Hom

private lemma exists_finite_basicOpen_immersion
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : Γ(X, ⊤)) (hr : IsAffineOpen (X.basicOpen r))
    (V : S.Opens) (hV : IsAffineOpen V) (hrV : X.basicOpen r ≤ f ⁻¹ᵁ V) :
    ∃ s : Finset Γ(X, ⊤), ∀ {ι : Type u} (v : ι → Γ(X, ⊤)) (j : ι),
      v j = r → (∀ a ∈ s, a ∈ Set.range v) →
      IsImmersion ((X.basicOpen r).ι ≫ AffineSpace.homOfVector f v) := by
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
  obtain ⟨s, hs⟩ := IsLocalization.Away.exists_finset_surjective_of_finiteType r
    (f.appLE V (X.basicOpen r) hrV).hom (f.finiteType_appLE hV hr hrV)
  refine ⟨s, fun {ι} v j hj hvs ↦ ?_⟩
  let Y := 𝔸(ι; S)
  let p : Y ⟶ S := Y ↘ S
  let g : X ⟶ Y := AffineSpace.homOfVector f v
  let W : Y.Opens := (p ⁻¹ᵁ V) ⊓ Y.basicOpen (AffineSpace.coord S j)
  have hgW : X.basicOpen r ≤ g ⁻¹ᵁ W := by
    dsimp [W, g, p, Y]
    simp only [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      AffineSpace.homOfVector_over, Scheme.preimage_basicOpen_top,
      AffineSpace.homOfVector_appTop_coord, hj]
    exact le_inf hrV le_rfl
  have hW : IsAffineOpen W := by
    simpa only [Scheme.basicOpen_res] using
      (hV.preimage p).basicOpen (Y.presheaf.map (homOfLE le_top).op
        (AffineSpace.coord S j))
  let γ := (g.appLE W (X.basicOpen r) hgW).hom
  have hcoord (i : ι) : γ (Y.presheaf.map (homOfLE le_top).op
      (AffineSpace.coord S i)) = algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) (v i) :=
    AffineSpace.homOfVector_appLE_coord f v W (X.basicOpen r) hgW i
  have hsurj : Function.Surjective γ := by
    apply hs γ
    · intro a
      refine ⟨p.appLE V W inf_le_left a, ?_⟩
      -- Express evaluation as composition to use the structural morphism equation.
      change (p.appLE V W inf_le_left ≫ g.appLE W _ hgW) a = _
      simp only [Scheme.Hom.appLE_comp_appLE, g, p, Y,
        AffineSpace.homOfVector_over]
    · intro a ha
      obtain ⟨i, rfl⟩ := hvs a ha
      exact ⟨_, hcoord i⟩
    · refine ⟨Y.presheaf.map (homOfLE le_top).op (AffineSpace.coord S j), ?_, ?_⟩
      · have hu := (Y.toRingedSpace.isUnit_res_basicOpen (AffineSpace.coord S j)).map
          (Y.presheaf.map (homOfLE (show W ≤ _ from inf_le_right)).op).hom
        -- Express the two restrictions as a composite so functoriality combines them.
        change IsUnit ((Y.presheaf.map
          (homOfLE (Y.basicOpen_le (AffineSpace.coord S j))).op ≫ Y.presheaf.map
          (homOfLE (show W ≤ _ from inf_le_right)).op) (AffineSpace.coord S j)) at hu
        simpa only [← Functor.map_comp, ← op_comp, homOfLE_comp] using hu
      · simpa only [hj] using hcoord j
  have : IsClosedImmersion (g.resLE W (X.basicOpen r) hgW) := by
    have : IsAffine (X.basicOpen r).toScheme := hr
    have : IsAffine W.toScheme := hW
    apply IsClosedImmersion.of_surjective_of_isAffine
    exact (RingHom.surjective_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso g W (X.basicOpen r) hgW)).mpr hsurj
  rw [← g.resLE_comp_ι hgW]
  infer_instance

/-- A quasi-affine scheme locally of finite type over `S` admits an immersion into a
finite-dimensional affine space over `S`. -/
@[stacks 04II]
theorem exists_isImmersion_affineSpace {X S : Scheme.{u}} [X.IsQuasiAffine]
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (ι : Type u) (_ : Finite ι) (i : X ⟶ 𝔸(ι; S)),
      IsImmersion i ∧ i ≫ 𝔸(ι; S) ↘ S = f := by
  classical
  have H (x : X) : ∃ (r : Γ(X, ⊤)) (V : S.Opens),
      IsAffineOpen (X.basicOpen r) ∧ IsAffineOpen V ∧
        x ∈ X.basicOpen r ∧ X.basicOpen r ≤ f ⁻¹ᵁ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, hrV⟩ :=
      (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
    exact ⟨r, V, hr, hV, hxr, hrV⟩
  choose r V hr hV hxr hrV using H
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (X.basicOpen (r x) : Set X))
    (fun x ↦ (X.basicOpen (r x)).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxr x⟩)
  choose s hs using fun j : t ↦
    exists_finite_basicOpen_immersion f (r j) (hr j) (V j) (hV j) (hrV j)
  let ι := Σ j : t, Option (s j)
  let v : ι → Γ(X, ⊤) := fun i ↦ i.2.elim (r i.1) (fun a ↦ a.val)
  refine ⟨ι, inferInstance, AffineSpace.homOfVector f v, ?_,
    AffineSpace.homOfVector_over f v⟩
  let : MorphismProperty.HasOfPostcompProperty @IsImmersion @IsOpenImmersion :=
    ⟨fun a b _ h ↦ by
      have := h
      exact IsImmersion.of_comp a b⟩
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  let j : t := ⟨y, hyt⟩
  let U := 𝔸(ι; S).basicOpen (AffineSpace.coord S (⟨j, none⟩ : ι))
  have heq : AffineSpace.homOfVector f v ⁻¹ᵁ U = X.basicOpen (r j) := by
    rw [Scheme.preimage_basicOpen_top, AffineSpace.homOfVector_appTop_coord]
    rfl
  refine ⟨U, ?_, ?_⟩
  · -- Membership in a target open is membership in its inverse image on the source.
    change x ∈ AffineSpace.homOfVector f v ⁻¹ᵁ U
    rw [heq]
    exact hxy
  · rw [heq]
    exact hs j v ⟨j, none⟩ rfl fun a ha ↦ ⟨⟨j, some ⟨a, ha⟩⟩, rfl⟩

end Scheme.Hom

end AlgebraicGeometry
