/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The normalizer action on characters

For a closed diagonalizable subgroup `D(X) → G`, a rational point normalizing the subgroup
induces an automorphism of `X` by pullback along inverse conjugation. These automorphisms form
a group homomorphism, with the variance suited to the action on weight spaces. Points of the
diagonalizable subgroup act trivially on characters. The kernel consists exactly of normalizing
points whose conjugation restricts to the identity on the subgroup scheme.

Normalization means stabilization of the defining Hopf ideal, not normalization of rational
points alone. Thus the construction detects the subgroup scheme, including nonreduced ones.
The coordinate map is assumed surjective, expressing that `D(X) → G` is a closed immersion.
The base has connected prime spectrum, as required to recover characters from group-like
elements. Neither smoothness nor finite generation is required.

The construction uses `HopfIdeal.kerLiftBialgEquiv` to descend conjugation and
`TauCeti.MonoidAlgebra.groupLikeEquiv` to recover the character automorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

open WithConv

namespace BialgHom

open TauCeti

noncomputable section

variable {R H X : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)

/-- The rational points stabilizing the defining Hopf ideal of a closed diagonalizable
subgroup. This is the rational normalizer of the subgroup scheme. -/
noncomputable def normalizerPoints : Subgroup (WithConv (H →ₐ[R] R)) :=
  MulAction.stabilizer (WithConv (H →ₐ[R] R)) (HopfIdeal.kerOfSurjective π hπ)

/-- Normalizer membership means that conjugation preserves the defining Hopf ideal. -/
@[simp]
theorem mem_normalizerPoints (g : WithConv (H →ₐ[R] R)) :
    g ∈ normalizerPoints π hπ ↔
      (HopfIdeal.kerOfSurjective π hπ).conjugate g = HopfIdeal.kerOfSurjective π hπ := by
  rw [normalizerPoints, MulAction.mem_stabilizer_iff, HopfIdeal.smul_eq_conjugate]

/-- The points of the diagonalizable subgroup map into its scheme normalizer. -/
noncomputable def mapDomainToNormalizer :
    WithConv (MonoidAlgebra R X →ₐ[R] R) →* normalizerPoints π hπ :=
  (AlgHom.mapDomain π).codRestrict (normalizerPoints π hπ) fun t ↦ by
    rw [mem_normalizerPoints]
    apply HopfIdeal.ext
    intro x
    rw [HopfIdeal.mem_conjugate, HopfIdeal.mem_kerOfSurjective,
      HopfIdeal.mem_kerOfSurjective]
    have h := AlgHom.congr_fun (comp_pointConjugationAlgHom_mapDomain_of_isCocomm π t) x
    simpa only [AlgHom.comp_apply, BialgHom.coe_toAlgHom] using (congrArg (· = 0) h).to_iff

/-- The normalizer inclusion recovers the original point of the ambient group. -/
@[simp]
theorem coe_mapDomainToNormalizer (t : WithConv (MonoidAlgebra R X →ₐ[R] R)) :
    (mapDomainToNormalizer π hπ t : WithConv (H →ₐ[R] R)) = AlgHom.mapDomain π t := (rfl)

private theorem conjugation_ker_le (g : normalizerPoints π hπ) :
    (HopfIdeal.kerOfSurjective π hπ).toIdeal ≤
      RingHom.ker (π.comp (HopfAlgebra.pointConjugationBialgEquiv (g : WithConv
        (H →ₐ[R] R))⁻¹).toBialgHom).toAlgHom.toRingHom := by
  intro x hx
  have hg := (mem_normalizerPoints π hπ _).mp (g⁻¹).property
  simp only [Subgroup.coe_inv] at hg
  have hx' : x ∈ (HopfIdeal.kerOfSurjective π hπ).conjugate
      (g : WithConv (H →ₐ[R] R))⁻¹ := by
    rw [hg]
    exact hx
  rw [HopfIdeal.mem_conjugate, HopfIdeal.mem_kerOfSurjective] at hx'
  simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom, BialgHom.comp_apply,
    ← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom, BialgEquiv.toBialgHom_eq_coe,
    BialgEquiv.coe_toBialgHom] using hx'

/-- Pullback on the subgroup's coordinate algebra along inverse conjugation. -/
private noncomputable def normalizerCoordinateMap (g : normalizerPoints π hπ) :
    MonoidAlgebra R X →ₐc[R] MonoidAlgebra R X :=
  (Bialgebra.Quotient.liftBialgHom (HopfIdeal.kerOfSurjective π hπ).toIdeal
    (π.comp (HopfAlgebra.pointConjugationBialgEquiv (g : WithConv (H →ₐ[R] R))⁻¹).toBialgHom)
    (conjugation_ker_le π hπ g)).comp
      (HopfIdeal.kerLiftBialgEquiv π hπ).symm.toBialgHom

private theorem normalizerCoordinateMap_apply (g : normalizerPoints π hπ) (x : H) :
    normalizerCoordinateMap π hπ g (π x) =
      π (HopfAlgebra.pointConjugationAlgHom (g : WithConv (H →ₐ[R] R))⁻¹ x) := by
  have he : (HopfIdeal.kerLiftBialgEquiv π hπ).symm (π x) =
      Ideal.Quotient.mk (HopfIdeal.kerOfSurjective π hπ).toIdeal x := by
    apply EquivLike.injective (HopfIdeal.kerLiftBialgEquiv π hπ)
    rw [(HopfIdeal.kerLiftBialgEquiv π hπ).apply_symm_apply,
      HopfIdeal.kerLiftBialgEquiv_apply, HopfIdeal.kerLiftBialgHom_mk]
  simp only [normalizerCoordinateMap, BialgHom.comp_apply,
    BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_coe, he,
    Bialgebra.Quotient.liftBialgHom_mk]
  rw [← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  rfl

private theorem normalizerCoordinateMap_one :
    normalizerCoordinateMap π hπ 1 = BialgHom.id R (MonoidAlgebra R X) := by
  apply BialgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  simp [normalizerCoordinateMap_apply]

private theorem normalizerCoordinateMap_mul (g h : normalizerPoints π hπ) :
    normalizerCoordinateMap π hπ (g * h) =
      (normalizerCoordinateMap π hπ g).comp (normalizerCoordinateMap π hπ h) := by
  apply BialgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  simp only [normalizerCoordinateMap_apply, BialgHom.comp_apply, Subgroup.coe_mul,
    mul_inv_rev, HopfAlgebra.pointConjugationAlgHom_mul, AlgHom.comp_apply]

variable [ConnectedSpace (PrimeSpectrum R)]

/-- The automorphism of the character group induced by inverse conjugation by a normalizing
rational point. -/
private noncomputable def normalizerCharacterEquiv (g : normalizerPoints π hπ) : X ≃* X where
  toFun := MonoidAlgebra.mapDomainBialgHomPreimage R (normalizerCoordinateMap π hπ g)
  invFun := MonoidAlgebra.mapDomainBialgHomPreimage R (normalizerCoordinateMap π hπ g⁻¹)
  left_inv x := by
    let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
    apply MonoidAlgebra.single_left_injective (R := R) (M := X) one_ne_zero
    dsimp only
    rw [← MonoidAlgebra.mapDomainBialgHomPreimage_single,
      ← MonoidAlgebra.mapDomainBialgHomPreimage_single]
    rw [← BialgHom.comp_apply, ← normalizerCoordinateMap_mul]
    simp [normalizerCoordinateMap_one]
  right_inv x := by
    let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
    apply MonoidAlgebra.single_left_injective (R := R) (M := X) one_ne_zero
    dsimp only
    rw [← MonoidAlgebra.mapDomainBialgHomPreimage_single,
      ← MonoidAlgebra.mapDomainBialgHomPreimage_single]
    rw [← BialgHom.comp_apply, ← normalizerCoordinateMap_mul]
    simp [normalizerCoordinateMap_one]
  map_mul' := (MonoidAlgebra.mapDomainBialgHomPreimage R
    (normalizerCoordinateMap π hπ g)).map_mul

private theorem normalizerCharacterEquiv_single (g : normalizerPoints π hπ) (x : X) :
    normalizerCoordinateMap π hπ g (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single (normalizerCharacterEquiv π hπ g x) 1 :=
  MonoidAlgebra.mapDomainBialgHomPreimage_single R _ x

private theorem normalizerCoordinateMap_eq_domCongr (g : normalizerPoints π hπ) :
    (normalizerCoordinateMap π hπ g).toAlgHom =
      (MonoidAlgebra.domCongr R R (normalizerCharacterEquiv π hπ g)).toAlgHom := by
  apply MonoidAlgebra.algHom_ext (R := R) (A := R) (M := X)
  · intro x
    simpa only [AlgEquiv.coe_toAlgHom, MonoidAlgebra.domCongr_single,
      BialgHom.coe_toAlgHom] using normalizerCharacterEquiv_single π hπ g x
  · ext

/-- Inverse conjugation defines the normalizer's action on the character group. -/
noncomputable def normalizerCharacterHom : normalizerPoints π hπ →* MulAut X where
  toFun := normalizerCharacterEquiv π hπ
  map_one' := by
    let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
    ext x
    apply MonoidAlgebra.single_left_injective (R := R) (M := X) one_ne_zero
    dsimp only
    rw [← normalizerCharacterEquiv_single]
    simp [normalizerCoordinateMap_one]
  map_mul' g h := by
    let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
    ext x
    apply MonoidAlgebra.single_left_injective (R := R) (M := X) one_ne_zero
    dsimp only
    simp only [MulAut.mul_apply]
    rw [← normalizerCharacterEquiv_single, ← normalizerCharacterEquiv_single,
      ← normalizerCharacterEquiv_single]
    exact BialgHom.congr_fun (normalizerCoordinateMap_mul π hπ g h) _

/-- The induced character automorphism is characterized by the coordinate equation for
inverse conjugation on the closed subgroup. -/
@[simp]
theorem normalizerCharacterHom_comp (g : normalizerPoints π hπ) :
    π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom (g : WithConv (H →ₐ[R] R))⁻¹) =
      (MonoidAlgebra.domCongr R R (normalizerCharacterHom π hπ g)).toAlgHom.comp π.toAlgHom := by
  -- The homomorphism packages the private character equivalence; only this projection is unfolded.
  dsimp only [normalizerCharacterHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← normalizerCoordinateMap_eq_domCongr]
  apply AlgHom.ext
  intro x
  exact (normalizerCoordinateMap_apply π hπ g x).symm

/-- The normalization equation determines the induced character automorphism uniquely. -/
theorem normalizerCharacterHom_unique (g : normalizerPoints π hπ) (w : X ≃* X)
    (hw : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom (g : WithConv (H →ₐ[R] R))⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom) :
    w = normalizerCharacterHom π hπ g := by
  let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have he : (MonoidAlgebra.domCongr R R w).toAlgHom =
      (MonoidAlgebra.domCongr R R (normalizerCharacterHom π hπ g)).toAlgHom := by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact AlgHom.congr_fun (hw.symm.trans (normalizerCharacterHom_comp π hπ g)) x
  ext x
  apply MonoidAlgebra.single_left_injective (R := R) (M := X) one_ne_zero
  simpa using AlgHom.congr_fun he (MonoidAlgebra.single x 1)

/-- A normalizing point acts trivially on characters exactly when its inverse conjugation
restricts to the identity on the subgroup scheme. -/
theorem normalizerCharacterHom_eq_one_iff (g : normalizerPoints π hπ) :
    normalizerCharacterHom π hπ g = 1 ↔
      π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom (g : WithConv (H →ₐ[R] R))⁻¹) =
        π.toAlgHom := by
  constructor
  · intro hg
    simpa only [hg, MulAut.one_def, MonoidAlgebra.domCongr_refl,
      AlgEquiv.refl_toAlgHom, AlgHom.id_comp] using normalizerCharacterHom_comp π hπ g
  · intro hg
    symm
    apply normalizerCharacterHom_unique
    simpa only [MulAut.one_def, MonoidAlgebra.domCongr_refl,
      AlgEquiv.refl_toAlgHom, AlgHom.id_comp] using hg

/-- Points of the diagonalizable subgroup act trivially on its character group. -/
@[simp]
theorem normalizerCharacterHom_mapDomainToNormalizer
    (t : WithConv (MonoidAlgebra R X →ₐ[R] R)) :
    normalizerCharacterHom π hπ (mapDomainToNormalizer π hπ t) = 1 := by
  rw [normalizerCharacterHom_eq_one_iff, coe_mapDomainToNormalizer, ← map_inv]
  exact comp_pointConjugationAlgHom_mapDomain_of_isCocomm π t⁻¹

end

end BialgHom
