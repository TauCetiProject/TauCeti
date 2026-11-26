/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Difference
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus

/-!
# The canonical section of the line bundle of an effective Cartier divisor

Let `D` be an effective Cartier divisor on an integral scheme `X`. The inclusion
`𝒪_X ⟶ 𝒪_X(D)` sends the constant function `1` to a global section `s_D` of the line bundle
`𝒪_X(D)`, its *canonical section*: inside the sheaf `𝒦_X` of rational functions it is the
rational function `1`. Near a point `x` where `f` is a local equation of `D`, the line bundle is
`f⁻¹ 𝒪_X` and `s_D` is `f · f⁻¹`, so `s_D` generates `𝒪_X(D)` at `x` exactly when `f` is a unit of
the local ring `𝒪_{X,x}`. Its nonvanishing locus is therefore the complement of the support of
`D`. This file records the two halves of this description that are needed to control the
nonvanishing locus:

* `s_D` does not vanish at the generic point;
* at a point of the nonvanishing locus, the inverse of every local equation of `D` is regular.

On an integral scheme of dimension at most one with Noetherian underlying space, for instance a
proper integral curve over a field, the complement of a nonempty open `V` is a finite set of closed
points. Each of them is a zero of an effective Cartier divisor, the divisor of a regular function
on an affine neighbourhood vanishing at that point
(`TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.exists_isEffective_restrict_eq`). Their sum is an
effective divisor `D` whose canonical section vanishes at every point outside `V`, so that its
nonvanishing locus `X_{s_D}` is a nonempty open contained in `V`. This is the kind of section of a
line bundle along which sections of quasi-coherent sheaves over `X_{s_D}` extend to global
sections after twisting by a power of `𝒪_X(D)`
(`AlgebraicGeometry.Scheme.Modules.exists_map_eq_tmulRight_tensorPowSection`; Hartshorne, Lemma
II.5.14).

## Main declarations

* `Scheme.CartierDivisor.IsEffective.canonicalSection`: the canonical global section `s_D` of
  `𝒪_X(D)`.
* `Scheme.CartierDivisor.IsEffective.genericPoint_mem_nonvanishingLocus`: `s_D` does not vanish at
  the generic point.
* `Scheme.CartierDivisor.IsEffective.inv_mem_range_of_mem_nonvanishingLocus`: where `s_D` does not
  vanish, every local equation of `D` is a unit of the local ring.
* `Scheme.CartierDivisor.exists_isEffective_nonvanishingLocus_le`: on an
  integral scheme of dimension at most one with Noetherian underlying space, every nonempty open
  contains the nonvanishing locus of the canonical section of some effective Cartier divisor.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6, the line bundle `𝓛(D)` of a Cartier divisor
  and its section `1` (Proposition II.6.13 and Remark II.6.17.1).
* The Stacks Project, *Divisors*, Definition 31.14.1 (Tag 01WR), the canonical section of the
  invertible sheaf of an effective Cartier divisor.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X] {D : CartierDivisor X}

/-- The **canonical section** `s_D` of the line bundle `𝒪_X(D)` of an effective Cartier divisor:
the image of the constant function `1` under the inclusion `𝒪_X ⟶ 𝒪_X(D)`. As a rational
function it is `1` (`IsEffective.rationalFunctionsEquiv_sheafι_app_map_canonicalSection`). -/
def IsEffective.canonicalSection (hD : D.IsEffective) : Γ(D.sheaf, ⊤) :=
  Scheme.Modules.Hom.app (D.unitToSheaf hD) ⊤ (1 : Γ(X, ⊤))

/-- The canonical section of `𝒪_X(D)` is the image of `1` under `𝒪_X ⟶ 𝒪_X(D)`. -/
theorem IsEffective.canonicalSection_def (hD : D.IsEffective) :
    hD.canonicalSection = Scheme.Modules.Hom.app (D.unitToSheaf hD) ⊤ (1 : Γ(X, ⊤)) :=
  (rfl)

/-- Read as a rational function over a nonempty open `U`, the canonical section of `𝒪_X(D)` is
the constant function `1`. -/
theorem IsEffective.rationalFunctionsEquiv_sheafι_app_map_canonicalSection (hD : D.IsEffective)
    (U : X.Opens) [Nonempty U] :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U
      (D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op hD.canonicalSection)) = 1 := by
  -- The restriction of `s_D` to `U` is the image of the function `1` on `U`.
  have hres : D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op hD.canonicalSection =
      Scheme.Modules.Hom.app (D.unitToSheaf hD) U (1 : Γ(X, U)) := by
    have h := (Scheme.Modules.Hom.mapPresheaf (D.unitToSheaf hD)).naturality_apply
      (homOfLE le_top : U ⟶ ⊤).op (1 : Γ(X, ⊤))
    -- The restriction maps of the unit module are those of the structure sheaf.
    change Scheme.Modules.Hom.app (D.unitToSheaf hD) U (X.presheaf.map _ 1) = _ at h
    rw [map_one] at h
    exact h.symm
  have hι : Scheme.Modules.Hom.app D.sheafι U
      (Scheme.Modules.Hom.app (D.unitToSheaf hD) U (1 : Γ(X, U))) =
        Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U (1 : Γ(X, U)) :=
    congrArg (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ rationalFunctions X ↦
      Scheme.Modules.Hom.app φ U (1 : Γ(X, U))) (D.unitToSheaf_ι hD)
  rw [hres, hι, Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one]

/-- **The canonical section does not vanish at the generic point.** For an effective Cartier
divisor `D` on an integral scheme, the generic point lies in the nonvanishing locus of the
canonical section of `𝒪_X(D)`, which is therefore a dense open subset. -/
theorem IsEffective.genericPoint_mem_nonvanishingLocus (hD : D.IsEffective) :
    genericPoint X ∈ D.sheaf.nonvanishingLocus hD.canonicalSection := by
  obtain ⟨V, t, hV⟩ := Scheme.Modules.exists_mem_trivialization D.sheaf
    (genericPoint X)
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  let i : V ⟶ ⊤ := homOfLE le_top
  let s := D.sheaf.presheaf.map i.op hD.canonicalSection
  -- Over `V`, the section `s_D` is `r` times the basis section, with `r ≠ 0` because `s_D` is the
  -- rational function `1`; hence the basic open set of `r` is a nonempty part of `X_{s_D}`.
  set r := Scheme.Modules.trivializationCoordinate D.sheaf t (𝟙 V) s with hr_def
  have hr : r ≠ 0 := by
    intro hr0
    have hs : s = 0 := by
      rw [Scheme.Modules.eq_trivializationCoordinate_smul_map_trivializationGenerator
        D.sheaf t (𝟙 V) s, ← hr_def, hr0, zero_smul]
    have h1 := hD.rationalFunctionsEquiv_sheafι_app_map_canonicalSection V
    -- `s` is by definition the restriction of `s_D` to `V` in `𝒪_X(D) = D.sheaf`.
    change rationalFunctionsEquiv V (Scheme.Modules.Hom.app D.sheafι V s) = 1 at h1
    rw [hs, map_zero, map_zero] at h1
    exact zero_ne_one h1
  have hne : X.basicOpen r ≠ ⊥ := fun h ↦ hr ((basicOpen_eq_bot_iff r).mp h)
  have hmem : genericPoint X ∈ X.basicOpen r := by
    by_contra h
    exact hne (Scheme.eq_bot_of_genericPoint_notMem h)
  rw [← Scheme.Modules.nonvanishingLocus_eq_basicOpen t (𝟙 V) s,
    Scheme.Modules.nonvanishingLocus_map] at hmem
  exact hmem.2

/-- **Local equations are units where the canonical section does not vanish.** Let `D` be an
effective Cartier divisor on an integral scheme and `x` a point of the nonvanishing locus of the
canonical section of `𝒪_X(D)`. Then the inverse of every local equation `f` of `D` at `x` is
regular at `x`; as `f` itself is regular there, `f` is a unit of the local ring `𝒪_{X,x}`. -/
theorem IsEffective.inv_mem_range_of_mem_nonvanishingLocus (hD : D.IsEffective) {x : X}
    (hx : x ∈ D.sheaf.nonvanishingLocus hD.canonicalSection)
    {f : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) :
    ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  obtain ⟨V, hxV, hV⟩ := isLocalEquationAt_iff.mp hf
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let W : X.Opens := V ⊓ D.sheaf.nonvanishingLocus hD.canonicalSection
  have hxW : x ∈ W := ⟨hxV, hx⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  -- Over `W`, the rational function `f⁻¹` is a section of `𝒪_X(D) = f⁻¹ 𝒪_X`.
  let g : Γ(rationalFunctions X, W) := (rationalFunctionsEquiv W).symm ↑(f⁻¹)
  have hg : g ∈ D.sections W := by
    refine (mem_sections_iff_of_rationalUnitClass_eq inf_le_left hV).mpr ⟨1, ?_⟩
    rw [map_one, LinearEquiv.apply_symm_apply, Units.mul_inv]
  -- Since `s_D` generates `𝒪_X(D)` over `W`, the section `f⁻¹` is a regular multiple `a • s_D`.
  let j : W ⟶ ⊤ := homOfLE le_top
  have hW : W ≤ D.sheaf.nonvanishingLocus
      (D.sheaf.presheaf.map j.op hD.canonicalSection) := by
    rw [Scheme.Modules.nonvanishingLocus_map]
    exact le_inf le_rfl inf_le_right
  obtain ⟨a, ha⟩ := Scheme.Modules.surjective_smul_of_le_nonvanishingLocus hW (sectionMk g hg)
  have ha' := congrArg (fun t ↦ rationalFunctionsEquiv W (Scheme.Modules.Hom.app D.sheafι W t)) ha
  -- Read in rational functions, `a • s_D = f⁻¹` says that `a` is the rational function `f⁻¹`.
  simp only [Scheme.Modules.Hom.app_smul, map_smul, sheafι_app_sectionMk, g,
    LinearEquiv.apply_symm_apply] at ha'
  rw [hD.rationalFunctionsEquiv_sheafι_app_map_canonicalSection, Algebra.smul_def, mul_one,
    RingHom.algebraMap_toAlgebra] at ha'
  rw [← ha', ← Scheme.algebraMap_germ_eq_germToFunctionField X hxW]
  exact RingHom.mem_range_self _ _

section Curve

variable [NoetherianSpace X] (hX : ∀ x : X, Order.coheight x ≤ 1)
include hX

/-- At a point `y` other than the generic point of a scheme of dimension at most one, some
effective Cartier divisor has a local equation at `y` whose inverse is not regular at `y`: the
divisor of a regular function on an affine neighbourhood of `y` that vanishes at `y` but not at
the generic point. -/
private lemma exists_isEffective_isLocalEquationAt_inv_notMem {y : X}
    (hy : y ≠ genericPoint X) :
    ∃ G : CartierDivisor X, G.IsEffective ∧ ∃ f : X.functionFieldˣ, G.IsLocalEquationAt y f ∧
      ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∉
        (algebraMap (X.presheaf.stalk y) X.functionField).range := by
  have hdim : topologicalKrullDim X ≤ 1 :=
    TauCeti.topologicalKrullDim_le_of_forall_coheight_le hX
  obtain ⟨A, hA, hyA, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top y)
  have : Nonempty A := ⟨⟨y, hyA⟩⟩
  have hηA : genericPoint X ∈ A := Scheme.genericPoint_mem A
  -- The point `y` is closed, so `A ∖ {y}` is an open neighbourhood of the generic point, and
  -- contains a basic open neighbourhood `D(b)` of it.
  let W : X.Opens := A ⊓ ⟨{y}ᶜ, (Scheme.isClosed_singleton_of_ne_genericPoint hdim hy).isOpen_compl⟩
  obtain ⟨b, hbW, hηb⟩ := hA.exists_basicOpen_le (V := W) ⟨genericPoint X, hηA, hy.symm⟩ hηA
  have hb0 : X.germToFunctionField A b ≠ 0 :=
    ((X.mem_basicOpen b _ hηA).mp hηb).ne_zero
  obtain ⟨G, hG, hGA⟩ := exists_isEffective_restrict_eq hX b (Units.mk0 _ hb0) rfl
  refine ⟨G, hG, Units.mk0 _ hb0, isLocalEquationAt_of_rationalUnitClass_eq hGA.symm hyA, ?_⟩
  -- If `b⁻¹` were regular at `y`, the germ of `b` at `y` would be a unit, so `y ∈ D(b) ⊆ W`.
  rintro ⟨c, hc⟩
  have hunit : IsUnit (X.presheaf.germ A y hyA b) := by
    refine IsUnit.of_mul_eq_one c (IsFractionRing.injective (X.presheaf.stalk y)
      X.functionField ?_)
    simp [hc, Scheme.algebraMap_germ_eq_germToFunctionField, hb0]
  exact (hbW ((X.mem_basicOpen b y hyA).mpr hunit)).2 rfl

/-- **Effective divisors with prescribed nonvanishing locus.** On an integral scheme whose
underlying space is Noetherian and all of whose points have codimension at most one, for instance
a proper integral curve over a field, every nonempty open subset `V` contains the nonvanishing
locus of the canonical section of `𝒪_X(D)` for some effective Cartier divisor `D`. That locus
contains the generic point (`IsEffective.genericPoint_mem_nonvanishingLocus`), so it is a nonempty
open subset of `V`. -/
theorem exists_isEffective_nonvanishingLocus_le (V : X.Opens) [Nonempty V] :
    ∃ (D : CartierDivisor X) (hD : D.IsEffective),
      D.sheaf.nonvanishingLocus hD.canonicalSection ≤ V := by
  classical
  have hdim : topologicalKrullDim X ≤ 1 :=
    TauCeti.topologicalKrullDim_le_of_forall_coheight_le hX
  have hηV : genericPoint X ∈ V := Scheme.genericPoint_mem V
  -- The complement of `V` is a finite set of points other than the generic point.
  have hZ : ((V : Set X)ᶜ).Finite :=
    Scheme.finite_of_isClosed_of_genericPoint_notMem hdim V.isOpen.isClosed_compl
      fun h ↦ h hηV
  have hne (y : X) (hy : y ∉ V) : y ≠ genericPoint X := fun h ↦ hy (h ▸ hηV)
  choose G hG f hf hfinv using fun (y : X) (hy : y ∉ V) ↦
    exists_isEffective_isLocalEquationAt_inv_notMem hX (hne y hy)
  let G' (y : X) : CartierDivisor X := if hy : y ∈ V then 0 else G y hy
  have hG' (y : X) : (G' y).IsEffective := by
    by_cases hy : y ∈ V
    · simp only [G', hy, ↓reduceDIte]
      exact isEffective_zero
    · simp only [G', hy, ↓reduceDIte]
      exact hG y hy
  have hsum (t : Finset X) : (∑ y ∈ t, G' y).IsEffective :=
    (mem_effectiveSubmonoid _).mp <|
      (effectiveSubmonoid X).sum_mem fun y _ ↦ (mem_effectiveSubmonoid _).mpr (hG' y)
  refine ⟨∑ y ∈ hZ.toFinset, G' y, hsum _, fun x hx ↦ ?_⟩
  by_contra hxV
  -- At a point `x` outside `V`, a local equation of the sum is `f · e`, with `f` the chosen
  -- equation of `G x` and `e` a regular local equation of the other summands.
  have hxZ : x ∈ hZ.toFinset := hZ.mem_toFinset.mpr hxV
  obtain ⟨e, he, her⟩ := isEffective_iff_exists.mp (hsum (hZ.toFinset.erase x)) x
  have hfx : (G' x).IsLocalEquationAt x (f x hxV) := by
    simp only [G', hxV, ↓reduceDIte]
    exact hf x hxV
  have hloc := hfx.mul he
  rw [Finset.add_sum_erase _ _ hxZ] at hloc
  have hinv := (hsum _).inv_mem_range_of_mem_nonvanishingLocus hx hloc
  -- Then `f⁻¹ = (f e)⁻¹ · e` would be regular at `x`.
  refine hfinv x hxV ?_
  have heq : ((f x hxV)⁻¹ : X.functionFieldˣ).val =
      ((f x hxV * e)⁻¹ : X.functionFieldˣ).val * e := by
    rw [← Units.val_mul]
    simp
  rw [heq]
  exact Subring.mul_mem _ hinv her

end Curve

end Scheme.CartierDivisor

end

end AlgebraicGeometry

end TauCeti
