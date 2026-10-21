/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.FieldTheory.Kummer.Cyclic
public import TauCeti.RingTheory.LaurentSeries.Level.Adjoin
public import TauCeti.RingTheory.LaurentSeries.Substitution
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The Kummer action on ramified Laurent levels

Let `K` be a field and `d` a positive integer. The ramified level `K⸨u⸩`, with `u ^ d = X`, is
obtained from `K⸨X⸩` by adjoining a root of `T ^ d - X`. Every `d`-th root of unity `η` of `K`
gives a `K⸨X⸩`-algebra automorphism `u ↦ η u` of the level, the rescaling `f (u) ↦ f (η u)`: it
multiplies the coefficient of `uᵏ` by `ηᵏ`, so it fixes the series in `u ^ d = X`.

When `K` has a primitive `d`-th root of unity, the level is a splitting field of `T ^ d - X` over
`K⸨X⸩`, hence a Galois extension. Mathlib's Kummer theory (`autEquivRootsOfUnity`) identifies its
Galois group with the `d`-th roots of unity, and the automorphism attached to `η` is exactly the
rescaling above. So every Galois automorphism of the level is a coefficientwise rescaling.

The same statements are transported to the actual level-`d` subfield of the Puiseux field, the
Laurent series in `t ^ (1 / d)`. There the automorphism attached to `η` multiplies the
coefficient of `t ^ (k / d)` by `ηᵏ`. For `n ∣ m`, the automorphism of level `m` attached to `η`
restricts on level `n` to the automorphism attached to `η ^ (m / n)`. These are the finite-level
Galois actions out of which the absolute Galois group of `K⸨X⸩` is assembled, when `K` is
algebraically closed of characteristic zero.

## Main definitions

* `TauCeti.LaurentSeries.Level.kummer K d`: the Kummer automorphisms `u ↦ η u` of the wrapped
  level `K⸨u⸩`, as a homomorphism from the `d`-th roots of unity of `K` to its Galois group.
* `TauCeti.LaurentSeries.Level.galEquivRootsOfUnity K d`: the Galois group of the level is the
  group of `d`-th roots of unity of `K`.
* `TauCeti.puiseuxField.levelKummer K d` and `TauCeti.puiseuxField.levelGalEquivRootsOfUnity K d`:
  the same for the actual level-`d` subfield of the Puiseux field.

## Main results

* `TauCeti.LaurentSeries.rescale_expand`: rescaling commutes with expansion `X ↦ X ^ d` up to
  raising the scalar to the `d`-th power.
* `TauCeti.LaurentSeries.Level.kummer_parameter`: the Kummer automorphism attached to `η` sends
  `u` to `η u`.
* `TauCeti.LaurentSeries.Level.isSplittingField` and `TauCeti.LaurentSeries.Level.isGalois`: with
  a primitive `d`-th root of unity in `K`, the level is a splitting field of `T ^ d - X`, hence
  Galois over `K⸨X⸩`.
* `TauCeti.LaurentSeries.Level.galEquivRootsOfUnity_symm_apply`: the Galois automorphism attached
  to `η` is the Kummer automorphism attached to `η`.
* `TauCeti.puiseuxField.levelKummer_levelParameter`: on the actual level, the Kummer automorphism
  attached to `η` sends `t ^ (1 / d)` to `η t ^ (1 / d)`.
* `TauCeti.puiseuxField.coeff_levelKummer`: on the actual level, the Kummer automorphism attached
  to `η` multiplies the coefficient of `t ^ (k / d)` by `ηᵏ`.
* `TauCeti.puiseuxField.levelKummer_inclusion`: restriction of Kummer automorphisms from level `m`
  to level `n`, for `n ∣ m`, along the power map `TauCeti.rootsOfUnityPowOfDvd`.
-/

public section

open HahnSeries LaurentSeries
open scoped LaurentSeries

namespace TauCeti.LaurentSeries

variable {K : Type*} [Field K]

/-- Rescaling an expanded series by `a` is expanding the series rescaled by `a ^ d`:
`f ((a X) ^ d) = (f (a ^ d X)) (X ^ d)`. -/
theorem rescale_expand (a : Kˣ) (d : ℕ+) (f : K⸨X⸩) :
    rescale a (expand K d f) = expand K d (rescale (a ^ (d : ℕ)) f) := by
  ext n
  rw [coeff_rescale]
  by_cases hn : (d : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_expand_mul, coeff_expand_mul, coeff_rescale, zpow_mul, zpow_natCast,
      Units.val_pow_eq_pow_val]
  · rw [coeff_expand_of_not_dvd d f hn, coeff_expand_of_not_dvd d _ hn, mul_zero]

/-- Rescaling by a `d`-th root of unity fixes every series expanded by `X ↦ X ^ d`. -/
theorem rescale_expand_of_pow_eq_one {a : Kˣ} {d : ℕ+} (ha : a ^ (d : ℕ) = 1) (f : K⸨X⸩) :
    rescale a (expand K d f) = expand K d f := by
  rw [rescale_expand, ha, map_one, AlgEquiv.one_apply]

namespace Level

variable (K) (d : ℕ+)

/-- The Kummer automorphisms `u ↦ η u` of the ramified level `K⸨u⸩` over `K⸨X⸩ = K⸨u ^ d⸩`,
attached to the `d`-th roots of unity `η` of the coefficient field. On underlying Laurent series
the automorphism attached to `η` is the rescaling `f (u) ↦ f (η u)`. -/
noncomputable def kummer : rootsOfUnity d K →* Gal(Level K d/K⸨X⸩) where
  toFun η := AlgEquiv.ofRingEquiv
    (f := ((ringEquivLaurentSeries K d).trans (rescale (η : Kˣ)).toRingEquiv).trans
      (ringEquivLaurentSeries K d).symm)
    fun f ↦ (ringEquivLaurentSeries K d).injective <| by
      have hη : (η : Kˣ) ^ (d : ℕ) = 1 := (mem_rootsOfUnity _ _).mp η.prop
      simp [rescale_expand_of_pow_eq_one hη]
  map_one' := by
    ext f : 1
    apply (ringEquivLaurentSeries K d).injective
    simp
  map_mul' η ζ := by
    ext f : 1
    apply (ringEquivLaurentSeries K d).injective
    simp

variable {K d}

/-- On underlying Laurent series, the Kummer automorphism attached to `η` is rescaling by `η`. -/
@[simp]
theorem ringEquivLaurentSeries_kummer (η : rootsOfUnity d K) (f : Level K d) :
    ringEquivLaurentSeries K d (kummer K d η f) =
      rescale (η : Kˣ) (ringEquivLaurentSeries K d f) := by
  simp [kummer]

/-- The Kummer automorphism attached to `η` multiplies the level parameter by `η`. -/
@[simp]
theorem kummer_parameter (η : rootsOfUnity d K) :
    kummer K d η (parameter K d) =
      Algebra.algebraMap K⸨X⸩ (Level K d) (Algebra.algebraMap K K⸨X⸩ ((η : Kˣ) : K)) *
        parameter K d := by
  apply (ringEquivLaurentSeries K d).injective
  simp [_root_.LaurentSeries.algebraMap_apply, HahnSeries.C_apply, expand_single,
    HahnSeries.single_mul_single]

section Galois

open Polynomial

variable (K d) [HasEnoughRootsOfUnity K d]

/-- If the coefficient field has a primitive `d`-th root of unity, then the ramified level
`K⸨u⸩` is a splitting field of `T ^ d - X` over `K⸨X⸩`: its roots are the `η u`. -/
instance isSplittingField :
    IsSplittingField K⸨X⸩ (Level K d) (X ^ (d : ℕ) - Polynomial.C (single 1 1)) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.primitiveRoots_nonempty_of_injective d
      (Algebra.algebraMap K K⸨X⸩).injective
  exact isSplittingField_X_pow_sub_C_of_adjoin_eq_top ((mem_primitiveRoots d.pos).mp hζ)
    (parameter_pow K d) (adjoin_parameter_eq_top K d)

/-- If the coefficient field has a primitive `d`-th root of unity, then the ramified level
`K⸨u⸩` is a Galois extension of `K⸨X⸩`. -/
instance isGalois : IsGalois K⸨X⸩ (Level K d) :=
  isGalois_of_isSplittingField_X_pow_sub_C
    (HasEnoughRootsOfUnity.primitiveRoots_nonempty_of_injective d
      (Algebra.algebraMap K K⸨X⸩).injective)
    (irreducible_X_pow_sub_C_single K d) (Level K d)

/-- If the coefficient field has a primitive `d`-th root of unity, then the Galois group of the
ramified level `K⸨u⸩` over `K⸨X⸩` is the group of `d`-th roots of unity of `K`. An automorphism
`σ` corresponds to the root of unity `σ u / u`, and the inverse is `kummer`
(`TauCeti.LaurentSeries.Level.galEquivRootsOfUnity_symm_apply`). -/
noncomputable def galEquivRootsOfUnity : Gal(Level K d/K⸨X⸩) ≃* rootsOfUnity d K :=
  (autEquivRootsOfUnity (HasEnoughRootsOfUnity.primitiveRoots_nonempty_of_injective d
      (Algebra.algebraMap K K⸨X⸩).injective) (irreducible_X_pow_sub_C_single K d)
      (Level K d)).trans
    (rootsOfUnityEquivOfPrimitiveRoots (Algebra.algebraMap K K⸨X⸩).injective
      (HasEnoughRootsOfUnity.primitiveRoots_nonempty K d)).symm

/-- A Galois automorphism `σ` multiplies the level parameter `u` by its root of unity. -/
private theorem apply_parameter (σ : Gal(Level K d/K⸨X⸩)) :
    σ (parameter K d) =
      Algebra.algebraMap K⸨X⸩ (Level K d)
          (Algebra.algebraMap K K⸨X⸩ ((galEquivRootsOfUnity K d σ : Kˣ) : K)) *
        parameter K d := by
  rw [← autEquivRootsOfUnity_smul (HasEnoughRootsOfUnity.primitiveRoots_nonempty_of_injective d
      (Algebra.algebraMap K K⸨X⸩).injective)
      (irreducible_X_pow_sub_C_single K d) _ (parameter_pow K d)]
  simp [galEquivRootsOfUnity, rootsOfUnityEquivOfPrimitiveRoots_symm_apply, Subgroup.smul_def,
    Units.smul_def, Algebra.smul_def]

/-- The Galois automorphism attached to a root of unity `η` is the Kummer automorphism
`u ↦ η u`. -/
@[simp]
theorem galEquivRootsOfUnity_symm_apply (η : rootsOfUnity d K) :
    (galEquivRootsOfUnity K d).symm η = kummer K d η := by
  -- both automorphisms are determined by their value on the generator `u`
  apply AlgEquiv.coe_toAlgHom_injective
  apply (powerBasis K d).algHom_ext
  rw [powerBasis_gen, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, kummer_parameter,
    apply_parameter, MulEquiv.apply_symm_apply]

/-- The root of unity attached to the Kummer automorphism `u ↦ η u` is `η`. -/
@[simp]
theorem galEquivRootsOfUnity_kummer (η : rootsOfUnity d K) :
    galEquivRootsOfUnity K d (kummer K d η) = η := by
  rw [← galEquivRootsOfUnity_symm_apply, MulEquiv.apply_symm_apply]

end Galois

end Level

end TauCeti.LaurentSeries

namespace TauCeti.puiseuxField

open LaurentSeries

variable (K : Type*) [Field K] (d : ℕ+)

/-- The Kummer automorphisms `t ^ (1 / d) ↦ η t ^ (1 / d)` of the actual level-`d` subfield of the
Puiseux field, attached to the `d`-th roots of unity `η` of the coefficient field. The
automorphism attached to `η` multiplies the coefficient of `t ^ (k / d)` by `ηᵏ`
(`TauCeti.puiseuxField.coeff_levelKummer`). -/
noncomputable def levelKummer : rootsOfUnity d K →* Gal(level K d/K⸨X⸩) :=
  (AlgEquiv.autCongr (levelEquiv K d)).toMonoidHom.comp (Level.kummer K d)

variable {K d}

/-- The Kummer automorphisms of the actual level correspond to those of the wrapped level under
`levelEquiv`. -/
@[simp]
theorem levelKummer_levelEquiv (η : rootsOfUnity d K) (f : Level K d) :
    levelKummer K d η (levelEquiv K d f) = levelEquiv K d (Level.kummer K d η f) := by
  simp [levelKummer, AlgEquiv.autCongr_apply]

/-- The Kummer automorphism attached to `η` multiplies the actual level parameter `t ^ (1 / d)` by
`η`. This is not a simp lemma: `simp` already computes it through `levelPowerBasis_gen`,
`levelKummer_levelEquiv` and `TauCeti.LaurentSeries.Level.kummer_parameter`. -/
theorem levelKummer_levelParameter (η : rootsOfUnity d K) :
    levelKummer K d η (levelParameter K d) =
      algebraMap K⸨X⸩ (level K d) (algebraMap K K⸨X⸩ ((η : Kˣ) : K)) * levelParameter K d := by
  rw [levelParameter, levelPowerBasis_gen, levelKummer_levelEquiv, Level.kummer_parameter, map_mul,
    AlgEquiv.commutes]

/-- If `x` is the level-`d` image of the Laurent series `f`, then its image under the Kummer
automorphism attached to `η` is the level-`d` image of the rescaled series `f (η X)`. -/
theorem coe_levelKummer_of_coe_eq (η : rootsOfUnity d K) {x : level K d} {f : K⸨X⸩}
    (hx : (x : puiseuxField K) = levelEmbedding K d f) :
    (levelKummer K d η x : puiseuxField K) = levelEmbedding K d (rescale (η : Kˣ) f) := by
  obtain ⟨g, rfl⟩ := (levelEquiv K d).surjective x
  rw [coe_levelEquiv_apply, Level.toPuiseux_apply] at hx
  rw [levelKummer_levelEquiv, coe_levelEquiv_apply, Level.toPuiseux_apply,
    Level.ringEquivLaurentSeries_kummer, (levelEmbedding K d).injective hx]

/-- The Kummer automorphism attached to `η` multiplies the coefficient of `t ^ (k / d)` by `ηᵏ`.
The other coefficients of a level-`d` series vanish
(`LaurentSeries.coeff_ramifiedEmbedding_of_not_den_dvd`). -/
@[simp]
theorem coeff_levelKummer (η : rootsOfUnity d K) (x : level K d) (k : ℤ) :
    ((levelKummer K d η x : puiseuxField K) : HahnSeries ℚ K).coeff ((k : ℚ) / d) =
      ((η : Kˣ) : K) ^ k * ((x : puiseuxField K) : HahnSeries ℚ K).coeff ((k : ℚ) / d) := by
  obtain ⟨f, hf⟩ : ∃ f, levelEmbedding K d f = x := (mem_level_iff K d x).mp x.2
  rw [coe_levelKummer_of_coe_eq η hf.symm, ← hf, coe_levelEmbedding, coe_levelEmbedding,
    coeff_ramifiedEmbedding_intCast_div, coeff_ramifiedEmbedding_intCast_div, coeff_rescale]

/-- **Restriction of Kummer automorphisms.** For `n ∣ m`, the Kummer automorphism of level `m`
attached to `η` restricts on level `n` to the Kummer automorphism attached to `η ^ (m / n)`. -/
theorem levelKummer_inclusion {n m : ℕ+} (h : n ∣ m) (η : rootsOfUnity m K) (x : level K n) :
    levelKummer K m η (IntermediateField.inclusion (level_le_level_of_dvd K h) x) =
      IntermediateField.inclusion (level_le_level_of_dvd K h)
        (levelKummer K n (rootsOfUnityPowOfDvd (PNat.dvd_iff.mp h) η) x) := by
  obtain ⟨e, rfl⟩ := h
  have he : ((n * e : ℕ+) : ℕ) / n = e := by rw [PNat.mul_coe, Nat.mul_div_cancel_left _ n.pos]
  obtain ⟨f, hf⟩ : ∃ f, levelEmbedding K n f = x := (mem_level_iff K n x).mp x.2
  -- `x` is the level-`n * e` image of `f (X ^ e)`
  have hx : ((IntermediateField.inclusion (level_le_level_of_dvd K ⟨e, rfl⟩) x :
      level K (n * e)) : puiseuxField K) = levelEmbedding K (n * e) (expand K e f) := by
    rw [IntermediateField.coe_inclusion, ← hf, levelEmbedding_expand]
  apply Subtype.ext
  rw [IntermediateField.coe_inclusion, coe_levelKummer_of_coe_eq _ hf.symm,
    coe_levelKummer_of_coe_eq η hx, rescale_expand, coe_rootsOfUnityPowOfDvd_apply, he,
    levelEmbedding_expand]

section Galois

variable (K d) [HasEnoughRootsOfUnity K d]

/-- If the coefficient field has a primitive `d`-th root of unity, then the level-`d` subfield of
the Puiseux field is a Galois extension of `K⸨X⸩`. -/
instance isGalois_level : IsGalois K⸨X⸩ (level K d) :=
  IsGalois.of_algEquiv (levelEquiv K d)

/-- If the coefficient field has a primitive `d`-th root of unity, then the Galois group of the
level-`d` subfield of the Puiseux field over `K⸨X⸩` is the group of `d`-th roots of unity of `K`.
The inverse is `levelKummer` (`TauCeti.puiseuxField.levelGalEquivRootsOfUnity_symm_apply`). -/
noncomputable def levelGalEquivRootsOfUnity : Gal(level K d/K⸨X⸩) ≃* rootsOfUnity d K :=
  (AlgEquiv.autCongr (levelEquiv K d)).symm.trans (Level.galEquivRootsOfUnity K d)

/-- The Galois automorphism of the level-`d` subfield attached to a root of unity `η` is the
Kummer automorphism `t ^ (1 / d) ↦ η t ^ (1 / d)`. -/
@[simp]
theorem levelGalEquivRootsOfUnity_symm_apply (η : rootsOfUnity d K) :
    (levelGalEquivRootsOfUnity K d).symm η = levelKummer K d η := by
  simp [levelGalEquivRootsOfUnity, levelKummer]

/-- The root of unity attached to the Kummer automorphism attached to `η` is `η`. -/
@[simp]
theorem levelGalEquivRootsOfUnity_levelKummer (η : rootsOfUnity d K) :
    levelGalEquivRootsOfUnity K d (levelKummer K d η) = η := by
  rw [← levelGalEquivRootsOfUnity_symm_apply, MulEquiv.apply_symm_apply]

end Galois

end TauCeti.puiseuxField
