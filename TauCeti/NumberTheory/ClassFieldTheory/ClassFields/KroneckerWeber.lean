/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormLimitation
public import TauCeti.NumberTheory.NumberField.Global.Cyclotomic.RayClass

import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RaySubgroup

/-!
# The norm group of `ℚ(ζ_n)/ℚ` and the Kronecker–Weber theorem

Let `F = ℚ(ζ_n)` be the `n`-th cyclotomic field. Its global Artin map is explicit: it is the ray
class map `C_ℚ → Cl_{(n)·∞}` followed by the identification
`GlobalNumberFields.ratModulusEquivGal n F : Cl_{(n)·∞} ≃* Gal(F/ℚ)`
(`ideleClassArtinMap_eq_ratModulusEquivGal_rayClassQuotient`), which sends the ray class of a
prime `p ∤ n` to the automorphism `ζ_n ↦ ζ_n ^ p`. Consequently the idele-class norm group
`N_{F/ℚ}(C_F)` is the ray subgroup of `(n)·∞` (`range_ideleClassNormMap_eq_raySubgroup_ratModulus`),
the modulus `(n)·∞` is admissible for `F/ℚ` (`isAdmissibleModulus_ratModulus`), and the
ray-class Artin map of `F/ℚ` at `(n)·∞` is `ratModulusEquivGal n F`
(`rayClassArtinMap_ratModulus`).

The comparison is made through the conductor: the global Artin map of `F/ℚ` factors through the
ray class group of some admissible modulus `(N)·∞` with `n ∣ N`, and on the ray classes of primes
`p ∤ N` both maps are arithmetic Frobenius at `p`, so they agree, because the ideal-theoretic Artin
map is determined by its values on primes.

The **Kronecker–Weber theorem** (`kroneckerWeber`) follows from the uniqueness half of the global
class-field correspondence. Norm groups detect embeddings of abelian extensions
(`range_ideleClassNormMap_le_iff_nonempty_algHom`), so a finite abelian extension `E/ℚ` embeds in
`ℚ(ζ_n)` exactly when the ray subgroup of `(n)·∞` lies in the norm group of `E`, that is, when the
conductor of `E/ℚ` divides `(n)·∞` (`nonempty_algHom_iff_abelianConductor_dvd_ratModulus`). The real
place imposes no condition, so this happens exactly when the absolute norm of the finite part of
the conductor divides `n` (`nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd`), and in
particular `E` embeds in the cyclotomic field of that level.

## Main results

* `TauCeti.ClassFieldTheory.ideleClassArtinMap_eq_ratModulusEquivGal_rayClassQuotient`: the global
  Artin map of `ℚ(ζ_n)/ℚ` is the ray class map modulo `(n)·∞` followed by `ratModulusEquivGal`.
* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_eq_raySubgroup_ratModulus`: the idele-class
  norm group of `ℚ(ζ_n)/ℚ` is the ray subgroup of `(n)·∞`.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_ratModulus`: `(n)·∞` is admissible for
  `ℚ(ζ_n)/ℚ`.
* `TauCeti.ClassFieldTheory.rayClassArtinMap_ratModulus`: the ray-class Artin map of `ℚ(ζ_n)/ℚ`
  at `(n)·∞` is `ratModulusEquivGal`.
* `TauCeti.ClassFieldTheory.nonempty_algHom_iff_abelianConductor_dvd_ratModulus`: a finite abelian
  extension `E/ℚ` embeds in `ℚ(ζ_n)` exactly when its conductor divides `(n)·∞`.
* `TauCeti.ClassFieldTheory.nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd` and
  `TauCeti.ClassFieldTheory.nonempty_algHom_cyclotomicField_iff`: it embeds in `ℚ(ζ_n)` exactly
  when the absolute norm of the finite part of its conductor divides `n`.
* `TauCeti.ClassFieldTheory.kroneckerWeber`: every finite abelian extension of `ℚ` embeds in a
  cyclotomic field.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, Example 3.11, and Chapter VIII,
  Theorem 3.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, Theorem 7.7 and Corollary 7.8.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField TauCeti.GlobalNumberFields

/-! ### The global Artin map of `ℚ(ζ_n)/ℚ` -/

section Cyclotomic

variable (n : ℕ) [NeZero n] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]

/-- On the ray class group of an admissible multiple `𝔫` of `(n)·∞`, the ray-class Artin map of
`ℚ(ζ_n)/ℚ` is the transition map to `(n)·∞` followed by `ratModulusEquivGal`: on ideals both are
the ideal-theoretic Artin map. -/
private theorem rayClassArtinMap_eq_ratModulusEquivGal_classMap [IsAbelianGalois ℚ F]
    {𝔫 : Modulus ℚ} (h : IsAdmissibleModulus ℚ F 𝔫) (hd : ratModulus n (NeZero.ne n) ∣ 𝔫)
    (c : RayClassGroup 𝔫) :
    rayClassArtinMap 𝔫 h c = ratModulusEquivGal n F (classMap hd c) := by
  obtain ⟨I, rfl⟩ := rayClassMk_surjective 𝔫 c
  rw [rayClassArtinMap_rayClassMk, NumberFieldArithmetic.artinHomAway_mono _ _
      (fun _ hv Q _ _ ↦ isUnramifiedAt_of_notMem_ratModulus_support n F hv Q) _
      (Modulus.support_mono hd),
    ← ratModulusEquivGal_comp_rayClassMk n F, MonoidHom.comp_apply, MonoidHom.comp_apply,
    classMap_rayClassMk, MonoidHom.coe_ofClass]

/-- **The global Artin map of `ℚ(ζ_n)/ℚ` is explicit**: the Artin symbol of an idele class is the
image under `ratModulusEquivGal` of its ray class modulo `(n)·∞`. -/
theorem ideleClassArtinMap_eq_ratModulusEquivGal_rayClassQuotient [IsAbelianGalois ℚ F]
    (c : IdeleClassGroup (𝓞 ℚ) ℚ) :
    ideleClassArtinMap ℚ F c =
      ratModulusEquivGal n F (rayClassQuotient (ratModulus n (NeZero.ne n)) c) := by
  -- Pass to a modulus `(N n)·∞` that is admissible, being a multiple of the conductor.
  obtain ⟨N, hN, hdvd⟩ : ∃ (N : ℕ) (hN : N ≠ 0), abelianConductor ℚ F ∣ ratModulus N hN :=
    ⟨_, _, dvd_ratModulus_absNorm _⟩
  have hNn : N * n ≠ 0 := mul_ne_zero hN (NeZero.ne n)
  have h : IsAdmissibleModulus ℚ F (ratModulus (N * n) hNn) :=
    (isAdmissibleModulus_iff_abelianConductor_dvd _).mpr
      (Modulus.dvd_trans hdvd (ratModulus_dvd_ratModulus_iff.mpr (dvd_mul_right N n)))
  rw [← rayClassArtinMap_rayClassQuotient h,
    rayClassArtinMap_eq_ratModulusEquivGal_classMap n F h
      (ratModulus_dvd_ratModulus_iff.mpr (dvd_mul_left n N)),
    classMap_rayClassQuotient]

/-- **The norm group of `ℚ(ζ_n)/ℚ` is the ray subgroup of `(n)·∞`**: an idele class of `ℚ` is a
norm from `ℚ(ζ_n)` exactly when it satisfies the congruence and sign conditions of `(n)·∞`. -/
theorem range_ideleClassNormMap_eq_raySubgroup_ratModulus :
    (ideleClassNormMap ℚ F : IdeleClassGroup (𝓞 F) F →* IdeleClassGroup (𝓞 ℚ) ℚ).range =
      raySubgroup (ratModulus n (NeZero.ne n)) := by
  have := IsCyclotomicExtension.isAbelianGalois {n} ℚ F
  ext c
  rw [← ker_ideleClassArtinMap, ← ker_rayClassQuotient, MonoidHom.mem_ker, MonoidHom.mem_ker,
    ideleClassArtinMap_eq_ratModulusEquivGal_rayClassQuotient n F, MulEquiv.map_eq_one_iff]

/-- **The modulus `(n)·∞` is admissible for `ℚ(ζ_n)/ℚ`**: the conductor of `ℚ(ζ_n)/ℚ` divides
`(n)·∞`. -/
theorem isAdmissibleModulus_ratModulus : IsAdmissibleModulus ℚ F (ratModulus n (NeZero.ne n)) :=
  isAdmissibleModulus_iff.mpr (range_ideleClassNormMap_eq_raySubgroup_ratModulus n F).ge

/-- **Ray-class reciprocity for `ℚ(ζ_n)/ℚ`**: the ray-class Artin map at `(n)·∞` is the
identification `ratModulusEquivGal` of the ray class group with `Gal(ℚ(ζ_n)/ℚ)`. -/
@[simp]
theorem rayClassArtinMap_ratModulus [IsAbelianGalois ℚ F]
    (c : RayClassGroup (ratModulus n (NeZero.ne n))) :
    rayClassArtinMap _ (isAdmissibleModulus_ratModulus n F) c = ratModulusEquivGal n F c := by
  rw [rayClassArtinMap_eq_ratModulusEquivGal_classMap n F _ (Modulus.dvd_refl _),
    classMap_refl_apply]

end Cyclotomic

/-! ### The cyclotomic fields containing an abelian extension -/

section Level

variable (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E] (n : ℕ) [NeZero n]

/-- **A finite abelian extension `E/ℚ` embeds in `ℚ(ζ_n)` exactly when its conductor divides
`(n)·∞`**: the norm group of `ℚ(ζ_n)` is the ray subgroup of `(n)·∞`, and norm groups detect
embeddings of abelian extensions. -/
theorem nonempty_algHom_iff_abelianConductor_dvd_ratModulus (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] :
    Nonempty (E →ₐ[ℚ] F) ↔ abelianConductor ℚ E ∣ ratModulus n (NeZero.ne n) := by
  have := IsCyclotomicExtension.isGalois {n} ℚ F
  exact nonempty_algHom_iff_abelianConductor_dvd_of_range_eq E
    (range_ideleClassNormMap_eq_raySubgroup_ratModulus n F)

/-- **A finite abelian extension `E/ℚ` embeds in `ℚ(ζ_n)` exactly when the absolute norm of the
finite part of its conductor divides `n`.** -/
theorem nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd (F : Type) [Field F]
    [NumberField F] [IsCyclotomicExtension {n} ℚ F] :
    Nonempty (E →ₐ[ℚ] F) ↔ Ideal.absNorm (abelianConductor ℚ E).finitePart ∣ n := by
  rw [nonempty_algHom_iff_abelianConductor_dvd_ratModulus E n F, dvd_ratModulus_iff]

/-- **A finite abelian extension `E/ℚ` embeds in `CyclotomicField n ℚ` exactly when the absolute
norm of the finite part of its conductor divides `n`.** -/
theorem nonempty_algHom_cyclotomicField_iff :
    Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ) ↔
      Ideal.absNorm (abelianConductor ℚ E).finitePart ∣ n := by
  -- Instance search finds `Algebra ℚ (CyclotomicField n ℚ)` through the `ℚ`-algebra structure of
  -- a characteristic-zero field, so the cyclotomic instance is supplied explicitly.
  have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  exact nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd E n _

end Level

/-! ### The Kronecker–Weber theorem -/

/-- **The Kronecker–Weber theorem**: every finite abelian extension of `ℚ` embeds in a cyclotomic
field `ℚ(ζ_n)`. -/
theorem kroneckerWeber (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E] :
    ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ) := by
  have hf := Ideal.absNorm_eq_zero_iff.not.mpr (abelianConductor ℚ E).finitePart_ne_bot
  have : NeZero (Ideal.absNorm (abelianConductor ℚ E).finitePart) := ⟨hf⟩
  exact ⟨_, hf, (nonempty_algHom_cyclotomicField_iff E _).mpr dvd_rfl⟩

end TauCeti.ClassFieldTheory
