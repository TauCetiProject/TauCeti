/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.SubgroupConductor.Basic

import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormLimitation
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient

/-!
# Extensions whose norm group is a ray subgroup

Let `L/K` be an extension of number fields whose idele-class norm group `N_{L/K}(C_L)` is the ray
subgroup of a modulus `𝔪`, as for the ray class field of `𝔪`, or for `ℚ(ζ_n)/ℚ` and `(n)·∞`.

A divisor `𝔫` of `𝔪` is admissible for `L/K` exactly when the transition map from the ray class
group of `𝔪` to that of `𝔫` is injective (`raySubgroup_le_raySubgroup_iff`), so the conductor of
`L/K` is the conductor of the trivial subgroup of the ray class group of `𝔪`
(`abelianConductor_eq_rayClassConductor_bot_of_range_eq`).

If `L/K` is Galois, norm groups detect embeddings of abelian extensions
(`range_ideleClassNormMap_le_iff_nonempty_algHom`), so a finite abelian extension `E/K` embeds in
`L` exactly when its conductor divides `𝔪` (`nonempty_algHom_iff_abelianConductor_dvd_of_range_eq`).

## Main results

* `TauCeti.ClassFieldTheory.abelianConductor_eq_rayClassConductor_bot_of_range_eq`: the conductor
  of `L/K` is the conductor of the trivial subgroup of the ray class group of `𝔪`.
* `TauCeti.ClassFieldTheory.nonempty_algHom_iff_abelianConductor_dvd_of_range_eq`: a finite
  abelian extension of `K` embeds in `L` exactly when its conductor divides `𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
-/

public section

namespace TauCeti.ClassFieldTheory

open _root_.NumberField TauCeti.GlobalNumberFields

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {𝔪 : Modulus K}

/-- **The conductor of an extension whose norm group is the ray subgroup of `𝔪`** is the conductor
of the trivial subgroup of the ray class group of `𝔪`: for a divisor `𝔫` of `𝔪`, both conductors
divide `𝔫` exactly when the transition map from `𝔪` to `𝔫` is injective. -/
theorem abelianConductor_eq_rayClassConductor_bot_of_range_eq
    (h : (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range =
      raySubgroup 𝔪) :
    abelianConductor K L = Subgroup.rayClassConductor (⊥ : Subgroup (RayClassGroup 𝔪)) := by
  have key {𝔫 : Modulus K} (h𝔫 : 𝔫 ∣ 𝔪) : abelianConductor K L ∣ 𝔫 ↔ (classMap h𝔫).ker ≤ ⊥ := by
    rw [← isAdmissibleModulus_iff_abelianConductor_dvd, isAdmissibleModulus_iff, h,
      raySubgroup_le_raySubgroup_iff h𝔫]
  have hdvd := (isAdmissibleModulus_iff_abelianConductor_dvd 𝔪).mp
    (isAdmissibleModulus_iff.mpr h.ge)
  exact Modulus.dvd_antisymm
    ((key (Subgroup.rayClassConductor_dvd ⊥)).mpr (Subgroup.ker_classMap_rayClassConductor_le ⊥))
    ((Subgroup.rayClassConductor_dvd_iff hdvd ⊥).mpr ((key hdvd).mp (Modulus.dvd_refl _)))

/-- **A finite abelian extension `E/K` embeds in a Galois extension `L/K` whose norm group is the
ray subgroup of `𝔪` exactly when the conductor of `E/K` divides `𝔪`**: norm groups detect
embeddings of abelian extensions. -/
theorem nonempty_algHom_iff_abelianConductor_dvd_of_range_eq [IsGalois K L] (E : Type) [Field E]
    [NumberField E] [Algebra K E] [IsAbelianGalois K E]
    (h : (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range =
      raySubgroup 𝔪) :
    Nonempty (E →ₐ[K] L) ↔ abelianConductor K E ∣ 𝔪 := by
  rw [← range_ideleClassNormMap_le_iff_nonempty_algHom, h, ← isAdmissibleModulus_iff,
    isAdmissibleModulus_iff_abelianConductor_dvd]

end TauCeti.ClassFieldTheory
