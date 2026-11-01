/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.SubgroupConductor.Rat

import TauCeti.NumberTheory.Cyclotomic.OddLevel

/-!
# The least cyclotomic field containing an abelian extension of `ℚ`

By the Kronecker–Weber theorem every finite abelian extension `E/ℚ` embeds in some cyclotomic
field `ℚ(ζ_n)`, and it does so exactly when the absolute norm `f` of the finite part of the
conductor `abelianConductor ℚ E` divides `n`
(`nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd`). In particular `f` is the least
cyclotomic level of `E` (`isLeast_absNorm_abelianConductor_finitePart`).

The level `f` is never `2` modulo `4` (`absNorm_abelianConductor_finitePart_mod_four_ne_two`):
for odd `m` the fields `ℚ(ζ_{2m})` and `ℚ(ζ_m)` coincide, so a level `2m` can always be halved.

For the cyclotomic field `F = ℚ(ζ_n)` itself, the norm group is the ray subgroup of `(n)·∞`, so the
conductor of `F/ℚ` is the conductor of the trivial subgroup of the ray class group modulo `(n)·∞`
(`abelianConductor_eq_rayClassConductor_bot`). Hence the conductor of `ℚ(ζ_n)/ℚ` is trivial for
`n ≤ 2` (`abelianConductor_eq_one_of_le_two`), `(n)·∞` for `n > 2` with `n ≢ 2 mod 4`
(`abelianConductor_eq_ratModulus`), and `(n / 2)·∞` for `n > 2` with `n ≡ 2 mod 4`
(`abelianConductor_eq_ratModulus_of_mod_four_eq_two`).

## Main results

* `TauCeti.ClassFieldTheory.isLeast_absNorm_abelianConductor_finitePart`: the absolute norm of the
  finite part of the conductor is the least cyclotomic level of `E`.
* `TauCeti.ClassFieldTheory.absNorm_abelianConductor_finitePart_mod_four_ne_two`: the least
  cyclotomic level is not `2` modulo `4`.
* `TauCeti.ClassFieldTheory.abelianConductor_eq_rayClassConductor_bot`: the conductor of
  `ℚ(ζ_n)/ℚ` is the conductor of the trivial subgroup of the ray class group modulo `(n)·∞`.
* `TauCeti.ClassFieldTheory.abelianConductor_eq_one_of_le_two`,
  `TauCeti.ClassFieldTheory.abelianConductor_eq_ratModulus` and
  `TauCeti.ClassFieldTheory.abelianConductor_eq_ratModulus_of_mod_four_eq_two`: the conductor of
  `ℚ(ζ_n)/ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6 (the conductor of an abelian extension)
  and Chapter VI, Corollary 7.8.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 3 (the conductor of an abelian
  number field as its least cyclotomic level).
-/

public section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField TauCeti.GlobalNumberFields

/-! ### The least cyclotomic level -/

section LeastLevel

variable (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E]

/-- **The least cyclotomic level of a finite abelian extension `E/ℚ`** is the absolute norm of the
finite part of its conductor: it is the least `n ≠ 0` such that `E` embeds in `ℚ(ζ_n)`. -/
theorem isLeast_absNorm_abelianConductor_finitePart :
    IsLeast {n : ℕ | n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)}
      (Ideal.absNorm (abelianConductor ℚ E).finitePart) := by
  have hf := Ideal.absNorm_eq_zero_iff.not.mpr (abelianConductor ℚ E).finitePart_ne_bot
  have : NeZero (Ideal.absNorm (abelianConductor ℚ E).finitePart) := ⟨hf⟩
  refine ⟨⟨hf, (nonempty_algHom_cyclotomicField_iff E _).mpr dvd_rfl⟩, fun n ⟨hn, hE⟩ ↦ ?_⟩
  have : NeZero n := ⟨hn⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((nonempty_algHom_cyclotomicField_iff E n).mp hE)

/-- **The least cyclotomic level of a finite abelian extension of `ℚ` is not `2` modulo `4`**: for
odd `m` the cyclotomic field `ℚ(ζ_{2m})` is also `ℚ(ζ_m)`. -/
theorem absNorm_abelianConductor_finitePart_mod_four_ne_two :
    Ideal.absNorm (abelianConductor ℚ E).finitePart % 4 ≠ 2 := by
  generalize hf : Ideal.absNorm (abelianConductor ℚ E).finitePart = f
  intro h4
  have : NeZero f := ⟨by omega⟩
  have : NeZero (f / 2) := ⟨by omega⟩
  -- `ℚ(ζ_f)` contains `E`, and it is also the cyclotomic field of level `f / 2`.
  have hE := (nonempty_algHom_cyclotomicField_iff E f).mpr hf.dvd
  -- The cyclotomic instance of `CyclotomicField f ℚ` is supplied explicitly, as in
  -- `nonempty_algHom_cyclotomicField_iff`.
  have : IsCyclotomicExtension {f} ℚ (CyclotomicField f ℚ) :=
    CyclotomicField.isCyclotomicExtension f ℚ
  have : IsCyclotomicExtension {f / 2} ℚ (CyclotomicField f ℚ) :=
    IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two h4
  have hdvd := (nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd E (f / 2)
    (CyclotomicField f ℚ)).mp hE
  rw [hf] at hdvd
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

end LeastLevel

/-! ### The conductor of `ℚ(ζ_n)/ℚ` -/

section Cyclotomic

variable (n : ℕ) [NeZero n] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]

/-- For a divisor `𝔫` of `𝔪`, the ray subgroup of `𝔫` lies in that of `𝔪` exactly when the
transition map from `𝔪` to `𝔫` is injective: both ray subgroups are kernels of the surjective ray
class map modulo `𝔪`, composed with the transition map in the case of `𝔫`. -/
private theorem raySubgroup_le_raySubgroup_iff {𝔪 𝔫 : Modulus ℚ} (h : 𝔫 ∣ 𝔪) :
    raySubgroup 𝔫 ≤ raySubgroup 𝔪 ↔ (classMap h).ker ≤ ⊥ := by
  rw [← ker_rayClassQuotient, ← ker_rayClassQuotient, ← classMap_comp_rayClassQuotient h,
    ← MonoidHom.comap_ker, ← MonoidHom.comap_bot (rayClassQuotient 𝔪),
    Subgroup.comap_le_comap_of_surjective (rayClassQuotient_surjective 𝔪)]

/-- **The conductor of `ℚ(ζ_n)/ℚ` is the conductor of the trivial subgroup of the ray class group
modulo `(n)·∞`**: the norm group of `ℚ(ζ_n)` is the ray subgroup of `(n)·∞`, so for a divisor `𝔫`
of `(n)·∞` both conductors divide `𝔫` exactly when the transition map from `(n)·∞` to `𝔫` is
injective. -/
theorem abelianConductor_eq_rayClassConductor_bot :
    abelianConductor ℚ F =
      Subgroup.rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus n (NeZero.ne n)))) := by
  have key {𝔫 : Modulus ℚ} (h : 𝔫 ∣ ratModulus n (NeZero.ne n)) :
      abelianConductor ℚ F ∣ 𝔫 ↔ (classMap h).ker ≤ ⊥ := by
    rw [← isAdmissibleModulus_iff_abelianConductor_dvd, isAdmissibleModulus_iff,
      range_ideleClassNormMap_eq_raySubgroup_ratModulus n F, raySubgroup_le_raySubgroup_iff h]
  have hdvd :=
    (isAdmissibleModulus_iff_abelianConductor_dvd _).mp (isAdmissibleModulus_ratModulus n F)
  exact Modulus.dvd_antisymm
    ((key (Subgroup.rayClassConductor_dvd ⊥)).mpr (Subgroup.ker_classMap_rayClassConductor_le ⊥))
    ((Subgroup.rayClassConductor_dvd_iff hdvd ⊥).mpr ((key hdvd).mp (Modulus.dvd_refl _)))

/-- **The conductor of `ℚ(ζ_n)/ℚ` is trivial** for `n ≤ 2`. -/
theorem abelianConductor_eq_one_of_le_two (h2 : n ≤ 2) :
    abelianConductor ℚ F = Modulus.one ℚ := by
  rw [abelianConductor_eq_rayClassConductor_bot n F,
    Subgroup.rayClassConductor_bot_ratModulus_of_le_two h2]

/-- **The conductor of `ℚ(ζ_n)/ℚ` is `(n)·∞`** for `n > 2` not equal to `2` modulo `4`. -/
theorem abelianConductor_eq_ratModulus (h2 : 2 < n) (h4 : n % 4 ≠ 2) :
    abelianConductor ℚ F = ratModulus n (NeZero.ne n) := by
  rw [abelianConductor_eq_rayClassConductor_bot n F,
    Subgroup.rayClassConductor_bot_ratModulus h2 h4]

omit [NeZero n] in
/-- **The conductor of `ℚ(ζ_n)/ℚ` is `(n / 2)·∞`** for `n > 2` equal to `2` modulo `4`, as
`ℚ(ζ_n) = ℚ(ζ_{n / 2})`. -/
theorem abelianConductor_eq_ratModulus_of_mod_four_eq_two (h2 : 2 < n) (h4 : n % 4 = 2) :
    abelianConductor ℚ F = ratModulus (n / 2) (by omega) := by
  have : NeZero n := ⟨by omega⟩
  rw [abelianConductor_eq_rayClassConductor_bot n F,
    Subgroup.rayClassConductor_bot_ratModulus_of_mod_four_eq_two h2 h4]

end Cyclotomic

end TauCeti.ClassFieldTheory
