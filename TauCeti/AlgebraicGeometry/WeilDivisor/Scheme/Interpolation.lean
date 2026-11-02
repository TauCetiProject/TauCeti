/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ResidueSequence.Basic
public import TauCeti.FieldTheory.FunctionField.Basic
import TauCeti.AlgebraicGeometry.LineBundle.HighDegree

/-!
# Residue interpolation by global sections on curves

Let `X` be a proper integral curve over a field `k`, with discrete valuation local rings at
codimension-one points and exact constant field `k`. If `deg D > 2g - 2`, the residue morphism
`𝒪_X(D + y) ⟶ κ(y)_y` is surjective on global sections. Equivalently, sections of `𝒪_X(E)`
can prescribe their leading coefficient at `y` whenever `deg E - [κ(y) : k] > 2g - 2`.
The closed point `y` may have any residue degree; no rational point is required.

The map is the actual residue morphism from the divisor-sheaf residue sequence: after choosing
a rational function `g` of order `D(y) + 1`, it takes the residue of `g f`. A prescribed nonzero
residue is realized by a global section with exact order `-D(y) - 1` at `y`. Thus the result
provides the pointwise generation input for complete linear systems, without asserting a
relative generation or Picard representability theorem.

The main results are `surjective_toSkyscraperResidueField_app_top_of_high_degree`, its
Riemann–Roch-space form `surjective_residueMap_of_high_degree`, and
`exists_globalSection_residue_eq_and_ord_eq_of_high_degree`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Corollary 3.2 and its proof.
* The Stacks Project, Lemma 53.22.4, Tag 0E3D (restriction to a closed point).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (hdim : ∀ x : X, coheight x ≤ 1)
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)

include hdim hF hk

-- The order and residue-map statements need the locally Noetherian structure
-- supplied by properness.

/-- If `deg D > 2g - 2`, every global section of the residue skyscraper at a closed point `y`
is the residue of a global section of `𝒪_X(D + y)`. For `E = D + y`, the bound is
`deg E - [κ(y) : k] > 2g - 2`, including points of higher residue degree. -/
theorem surjective_toSkyscraperResidueField_app_top_of_high_degree :
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    ∀ {D : SchemeWeilDivisor X} {y : CodimensionOnePoint X} {g : X.functionFieldˣ}
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1)
    (_hD : 2 * (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ) - 2 <
      relativeDegree (X ↘ Spec (.of k)) D),
    Function.Surjective (Scheme.Modules.Hom.app (toSkyscraperResidueField g hg) ⊤) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  intro D y g hg hD
  have : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have := finiteDimensional_cohomology_one_trivial_of_isProper k (X := X)
    ((isFunctionField_functionField_iff k).mp hF)
  have hdegree := InvertibleSheaf.eulerDegree_eq_relativeDegree k hdim
    (eqToIso (toInvertibleSheaf_obj hdim D))
  have hvan := InvertibleSheaf.subsingleton_cohomology_one_of_two_mul_genus_sub_two_lt_eulerDegree
    hdim hF hk (toInvertibleSheaf hdim D) (by rwa [hdegree])
  rw [toInvertibleSheaf_obj] at hvan
  have hclosed : IsClosed ({(y : X)} : Set X) :=
    isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim y.property
  have hvan' : Subsingleton (Scheme.Modules.Cohomology (residueShortComplex g hg).X₁ 1) := by
    rwa [residueShortComplex_X₁]
  have hsurj := Scheme.Modules.sections_surjective
    (residueShortComplex_shortExact hclosed hg) hvan'
  rwa [residueShortComplex_def] at hsurj

/-- For `deg D > 2g - 2`, the existing residue linear map `L(D + y) → κ(y)` is surjective.
The source is the submodule of global rational functions satisfying the divisor bounds. -/
theorem surjective_residueMap_of_high_degree :
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    ∀ {D : SchemeWeilDivisor X} {y : CodimensionOnePoint X} {g : X.functionField}
    (hg0 : g ≠ 0) (hg : X.ord g y = WeilDivisor.coeff D y + 1)
    (_hD : 2 * (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ) - 2 <
      relativeDegree (X ↘ Spec (.of k)) D),
    Function.Surjective (residueMap D y hg0 hg) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  intro D y g hg0 hg hD a
  have hyTop : (y : X) ∈ (⊤ : X.Opens) := by simp
  let e := Scheme.skyscraperResidueFieldEquiv (y : X) hyTop
  obtain ⟨s, hs⟩ := surjective_toSkyscraperResidueField_app_top_of_high_degree
    k hdim hF hk (g := Units.mk0 g hg0) hg hD (e.symm a)
  refine ⟨⟨Scheme.Modules.Hom.app (sheafι _) ⊤ s, sheafι_app_mem _ ⊤ s⟩, ?_⟩
  have hres := residueMap_sheafι_app (g := Units.mk0 g hg0) hg s
  rw [hs, e.apply_symm_apply] at hres
  simpa only [Units.val_mk0] using hres

/-- A nonzero prescribed residue is realized by a global section of `𝒪_X(D + y)` with the
exact allowed order at `y`, provided `deg D > 2g - 2`. The residue uses any multiplier `g`
of order `D(y) + 1`; the conclusion concerns the associated rational function of the section. -/
theorem exists_globalSection_residue_eq_and_ord_eq_of_high_degree :
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    ∀ {D : SchemeWeilDivisor X} {y : CodimensionOnePoint X} {g : X.functionFieldˣ}
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1)
    (_hD : 2 * (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ) - 2 <
      relativeDegree (X ↘ Spec (.of k)) D)
    (a : X.residueField y) (_ha : a ≠ 0),
    ∃ s : Γ(sheaf (D + WeilDivisor.ofPoint y), ⊤),
      Scheme.skyscraperResidueFieldEquiv (y : X) (by simp)
          (Scheme.Modules.Hom.app (toSkyscraperResidueField g hg) ⊤ s) = a ∧
        X.ord (Scheme.rationalFunctionsEquiv ⊤
          (Scheme.Modules.Hom.app (sheafι _) ⊤ s)) y = -WeilDivisor.coeff D y - 1 := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  intro D y g hg hD a ha
  have hyTop : (y : X) ∈ (⊤ : X.Opens) := by simp
  let e := Scheme.skyscraperResidueFieldEquiv (y : X) hyTop
  obtain ⟨s, hs⟩ := surjective_toSkyscraperResidueField_app_top_of_high_degree
    k hdim hF hk hg hD (e.symm a)
  have hres : e (Scheme.Modules.Hom.app (toSkyscraperResidueField g hg) ⊤ s) = a := by
    rw [hs, e.apply_symm_apply]
  have hnot : Scheme.Modules.Hom.app (sheafι _) ⊤ s ∉ sections D ⊤ := by
    intro hmem
    have hz := (toSkyscraperResidueField_app_eq_zero_iff hg ⊤ s).mpr hmem
    exact ha (hres.symm.trans (by rw [hz, map_zero]))
  have hsection := sheafι_app_mem (D + WeilDivisor.ofPoint y) ⊤ s
  have hf : Scheme.rationalFunctionsEquiv ⊤
      (Scheme.Modules.Hom.app (sheafι _) ⊤ s) ≠ 0 := by
    intro hf
    exact hnot (mem_sections_iff.mpr (Or.inl hf))
  have hbound := (mem_sections_iff.mp hsection).resolve_left hf
  refine ⟨s, hres, ?_⟩
  have hy := hbound y (by simp)
  simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self] at hy
  by_contra hne
  apply hnot
  refine mem_sections_iff.mpr (Or.inr fun z hz ↦ ?_)
  by_cases hzy : z = y
  · subst z
    omega
  · simpa [WeilDivisor.coeff_ofPoint_of_ne hzy] using hbound z hz

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
