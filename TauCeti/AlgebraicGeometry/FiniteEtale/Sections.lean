/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.RingTheory.Depth.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.Etale.Finiteness
import TauCeti.RingTheory.Localization.Away.Basic

/-!
# Sections of a finite étale cover of the punctured spectrum are finite

Let `A` be a Noetherian integrally closed local domain of depth at least two, `U` its punctured
spectrum and `V` a finite étale scheme over `U`. The ring of global sections `Γ(V, 𝒪_V)`, an
`A`-algebra through `V ⟶ U ⟶ Spec A`, is a finite `A`-module.

Write `R = Γ(V, 𝒪_V)`. Since `U` has depth at least two, `V` is the restriction of `Spec R ⟶ Spec A`
to `U` (`TauCeti.IsLocalRing.isPullback_puncturedSpectrum_toSpecΓ`). So for each `z` in the
maximal ideal, the restriction of `Spec R ⟶ Spec A` over `D(z) ⊆ U` is finite étale, that is,
the localization `R_z` is finite étale over `A_z`. These localizations are flat, so every element
of `R` killed by a nonzero element of `A` vanishes on each `D(z)`; the opens `D(z)` cover `V`, so
`R` is torsion free. The finiteness criterion
`TauCeti.Algebra.finite_of_isWeaklyRegular_of_isLocalization`, applied to a weakly regular pair of
the maximal ideal, then shows that `R` is finite over `A`.

This is the finiteness step in the proof that a finite étale cover of the punctured spectrum of a
normal local domain of dimension at least two is the restriction of the spectrum of a finite
normal algebra (Stacks, Lemma 58.20.3 (0BM9)).

## Main results

* `TauCeti.IsLocalRing.finite_etale_awayMap_puncturedSpectrum`: for `z` in the maximal ideal, the
  localization at `z` of the ring of sections is finite étale over `A_z`.
* `TauCeti.IsLocalRing.isTorsionFree_sections_puncturedSpectrum`: the ring of sections is a
  torsion-free `A`-module.
* `TauCeti.IsLocalRing.finite_sections_puncturedSpectrum`: the ring of sections is a finite
  `A`-module.

## References

* [Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9).
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- For a finite étale scheme `V` over the punctured spectrum of a Noetherian local ring of depth
at least two and `z` in the maximal ideal, the localization at `z` of the `A`-algebra `Γ(V, 𝒪_V)`
is finite étale over `A_z`. -/
theorem finite_etale_awayMap_puncturedSpectrum (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) {z : A} (hz : z ∈ maximalIdeal A) :
    (Localization.awayMap ((Scheme.ΓSpecIso (.of A)).inv ≫
        (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom z).Finite ∧
      (Localization.awayMap ((Scheme.ΓSpecIso (.of A)).inv ≫
        (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom z).Etale := by
  set φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
  let U := puncturedSpectrum A
  let g := Spec.map φ
  -- Instance search does not derive `RespectsIso` for these properties at a fixed universe.
  have : MorphismProperty.RespectsIso @IsFinite.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- Over `U`, the morphism `Spec Γ(V, 𝒪_V) ⟶ Spec A` is the finite étale `V ⟶ U`.
  have hpb := isPullback_puncturedSpectrum_toSpecΓ A hdepth V.obj.hom
  let e := hpb.isoIsPullback _ _ (isPullback_morphismRestrict g U)
  have : IsFinite (g ∣_ U) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.hom, hpb.isoIsPullback_hom_fst]
    infer_instance
  have : Etale (g ∣_ U) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale e.hom, hpb.isoIsPullback_hom_fst]
    infer_instance
  -- The basic open `D(z)` lies in `U`, and the restriction over it is `Spec` of `A_z ⟶ R_z`.
  let D : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen z
  have hD : U.ι ''ᵁ (U.ι ⁻¹ᵁ D) = D := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
    intro p hp
    refine (mem_puncturedSpectrum_iff A p).2 fun h ↦ hp ?_
    rw [h]
    exact hz
  let iso := (SpecMapRestrictBasicOpenIso φ z).symm ≪≫
    (morphismRestrictRestrict g U (U.ι ⁻¹ᵁ D) ≪≫ morphismRestrictEq g hD).symm
  exact ⟨(IsFinite.SpecMap_iff _).mp ((MorphismProperty.arrow_mk_iso_iff @IsFinite iso).mpr
      inferInstance),
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      ((MorphismProperty.arrow_mk_iso_iff @Etale iso).mpr inferInstance)⟩

variable [IsDomain A]

/-- The ring of sections of a finite étale scheme over the punctured spectrum of a Noetherian
local domain of depth at least two is a torsion-free module over the local ring. -/
theorem isTorsionFree_sections_puncturedSpectrum (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
    Module.IsTorsionFree A Γ(V.obj.left, ⊤) := by
  set φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
  let := φ.hom.toAlgebra
  let X := V.obj.left
  let R := Γ(X, ⊤)
  refine .of_smul_eq_zero fun a s has ↦ or_iff_not_imp_left.2 fun ha ↦ ?_
  -- For `z` in the maximal ideal, `s` is killed by a power of `z`, as `R_z` is flat over `A_z`.
  have hpow (z : A) (hz : z ∈ maximalIdeal A) : ∃ n : ℕ, algebraMap A R z ^ n * s = 0 := by
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨1, by simp⟩
    let := (Localization.awayMap (algebraMap A R) z).toAlgebra
    have := Localization.isScalarTower_awayMap R z
    have : Algebra.Etale (Localization.Away z) (Localization.Away (algebraMap A R z)) :=
      (finite_etale_awayMap_puncturedSpectrum hdepth V hz).2
    have hreg : IsSMulRegular (Localization.Away (algebraMap A R z))
        (algebraMap A (Localization.Away z) a) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors <| mem_nonZeroDivisors_of_ne_zero <|
        (map_ne_zero_iff _ (IsLocalization.injective _
          (powers_le_nonZeroDivisors_of_noZeroDivisors hz0))).2 ha
    have hs : algebraMap R (Localization.Away (algebraMap A R z)) s = 0 := by
      have h := congr(IsScalarTower.toAlgHom A R (Localization.Away (algebraMap A R z)) $has)
      rw [map_smul, map_zero, IsScalarTower.coe_toAlgHom',
        ← algebraMap_smul (Localization.Away z)] at h
      exact hreg (h.trans (smul_zero _).symm)
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers (algebraMap A R z)) _
      s).1 hs
    exact ⟨n, hn⟩
  -- Hence `s` vanishes on each basic open `D(z) ⊆ X`, where `z` acts invertibly.
  have hvan (z : maximalIdeal A) :
      X.presheaf.map (homOfLE (X.basicOpen_le (algebraMap A R z))).op s = 0 := by
    obtain ⟨n, hn⟩ := hpow z z.2
    have := congr(X.presheaf.map (homOfLE (X.basicOpen_le (algebraMap A R z))).op $hn)
    rw [map_mul, map_pow, map_zero] at this
    exact ((X.toRingedSpace.isUnit_res_basicOpen _).pow n).mul_right_eq_zero.1 this
  -- These basic opens cover `X`, since `X` lies over the punctured spectrum.
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun z : maximalIdeal A ↦ X.basicOpen (algebraMap A R z)) ⊤ (fun z ↦ homOfLE le_top)
    (fun v _ ↦ ?_) s 0 fun z ↦ (hvan z).trans (map_zero _).symm
  -- The image `p` of `v` in `Spec A` is not the closed point, so it avoids some `z ∈ 𝔪`.
  let p : PrimeSpectrum A := (V.obj.hom ≫ (puncturedSpectrum A).ι) v
  obtain ⟨z, hzm, hzp⟩ : ∃ z ∈ maximalIdeal A, z ∉ p.asIdeal := by
    by_contra! h
    refine (mem_puncturedSpectrum_iff A p).1 (V.obj.hom v).2 (PrimeSpectrum.ext ?_)
    exact le_antisymm (le_maximalIdeal p.isPrime.ne_top) h
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hzm⟩, ?_⟩
  have hD : X.basicOpen (algebraMap A R z) =
      (V.obj.hom ≫ (puncturedSpectrum A).ι) ⁻¹ᵁ
        (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv z) := by
    rw [Scheme.preimage_basicOpen_top, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
      RingHom.comp_apply]
  rw [hD, Scheme.Hom.mem_preimage, basicOpen_eq_of_affine]
  exact hzp

/-- **Finiteness of sections.** Let `A` be a Noetherian integrally closed local domain of depth at
least two. The ring of global sections of a finite étale scheme over the punctured spectrum of `A`
is a finite `A`-module. -/
theorem finite_sections_puncturedSpectrum [IsIntegrallyClosed A]
    (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
    Module.Finite A Γ(V.obj.left, ⊤) := by
  set φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
  let := φ.hom.toAlgebra
  have := isTorsionFree_sections_puncturedSpectrum hdepth V
  -- The maximal ideal contains a weakly regular pair `x, y`.
  obtain ⟨rs, hlen, hmem, hxy⟩ :=
    _root_.IsLocalRing.exists_isWeaklyRegular_of_le_depth (ModuleCat.of A A) (n := 2) hdepth
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
  -- The localizations of `R = Γ(V, 𝒪_V)` at `x` and `y` are finite étale over `A_x` and `A_y`.
  let R := Γ(V.obj.left, ⊤)
  let := (Localization.awayMap (algebraMap A R) x).toAlgebra
  let := (Localization.awayMap (algebraMap A R) y).toAlgebra
  have := Localization.isScalarTower_awayMap R x
  have := Localization.isScalarTower_awayMap R y
  have hx := finite_etale_awayMap_puncturedSpectrum hdepth V (hmem x (by simp))
  have : Module.Finite (Localization.Away x) (Localization.Away (algebraMap A R x)) := hx.1
  have : Algebra.Etale (Localization.Away x) (Localization.Away (algebraMap A R x)) := hx.2
  have : Module.Finite (Localization.Away y) (Localization.Away (algebraMap A R y)) :=
    (finite_etale_awayMap_puncturedSpectrum hdepth V (hmem y (by simp))).1
  exact TauCeti.Algebra.finite_of_isWeaklyRegular_of_isLocalization (Localization.Away x)
    (Localization.Away (algebraMap A R x)) (Localization.Away y)
    (Localization.Away (algebraMap A R y)) hxy

end TauCeti.IsLocalRing
