/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Prime
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Tower.Basic
import Mathlib.Tactic.NormNum.Prime
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Sqrt5
import TauCeti.NumberTheory.ClassFieldTheory.Global.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FiveThirteen
import TauCeti.NumberTheory.NumberField.Cyclotomic.Subfields
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Finite Artin maps in cyclic and biquadratic degree-four towers

The three commuting squares for `ideleClassArtinMap` — top-field restriction in
`TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity` and ground-field norm and transfer in
`TauCeti.NumberTheory.ClassFieldTheory.Global.Tower.Basic` — behave quite differently in the two
abelian Galois groups of order four, the cyclic group `C₄` and the Klein four-group `C₂ × C₂`. This
file works out both cases explicitly over `ℚ`:

1. **Cyclic of order four (`ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`):** let `L` be a fifth cyclotomic extension of `ℚ`
   (`Gal(L/ℚ) ≃* (ℤ/5ℤ)ˣ`) and `E` its quadratic subfield (`[E : ℚ] = 2`).
   * **Norm square:** the image of `N_{E/ℚ}(C_E)` under `ideleClassArtinMap ℚ L` is
     `E.fixingSubgroup`, corresponding under `Rat.galEquivZMod 5 L` to `{1, -1} ≤ (ℤ/5ℤ)ˣ`.
   * **Transfer square:** read in `(ℤ/5ℤ)ˣ`, the transferred Artin symbol
     `ideleClassArtinMap E L (ideleClassExtension ℚ E c)` is the square of
     `ideleClassArtinMap ℚ L c`. Because `2² ≡ -1 (mod 5)`, the composite
     `(ideleClassArtinMap E L).comp (ideleClassExtension ℚ E)` is **surjective** onto `Gal(L/E)`.
   * **Prime evaluations:** at a prime `v` of `ℚ` with `5 ∉ v`, both the quadratic Artin symbol
     `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)` (equal by `restrictNormal_ideleClassArtinMap`
     to the restriction of `ideleClassArtinMap ℚ L (primeIdeleClass ℚ v)`) and the transferred
     symbol `ideleClassArtinMap E L (ideleClassExtension ℚ E (primeIdeleClass ℚ v))` are trivial if
     and only if `N(v) ≡ ±1 (mod 5)`. At primes with `N(v) ≡ 4 (mod 5)`, the Artin symbol in
     `Gal(L/ℚ)` has order `2`, yet both the quadratic symbol on `E` and the transferred symbol on
     `L/E` are trivial. On any fifth root of unity `ζ ∈ L`, the transferred symbol fixes `ζ` when
     `N(v) ≡ ±1 (mod 5)` and sends `ζ` to `ζ⁻¹` when `N(v) ≡ ±2 (mod 5)`.

2. **Klein four-group (`ℚ(√5, √13)/ℚ` across all three quadratic subfields):** let `L` be generated
   over `ℚ` by `s` and `t` with `s² = 5` and `t² = 13`. By
   `TauCeti.NumberTheory.Multiquadratic.FiveThirteen`, `L/ℚ` is abelian Galois of exponent dividing
   `2` with three pairwise distinct quadratic subfields `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯`.
   * **Transfer square:** because `Gal(L/ℚ)` has exponent dividing `2`, the transferred Artin map
     `(ideleClassArtinMap E L).comp (ideleClassExtension ℚ E) : C_ℚ →* Gal(L/E)` is **identically
     trivial** on every quadratic subfield `E`, and every rational idele class becomes a norm from
     `L` over each of `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯`.
   * **Norm images and quadratic prime evaluations:** the norm-Artin images for `ℚ⟮s⟯`, `ℚ⟮t⟯`, and
     `ℚ⟮s * t⟯` are pairwise distinct subgroups of `Gal(L/ℚ)`. Specializing the general quadratic
     prime evaluations of `TauCeti.NumberTheory.ClassFieldTheory.Global.Quadratic` gives
     Legendre-symbol criteria `(5/p) = 1`, `(13/p) = 1`, and `(65/p) = 1` at odd primes
     `p ∉ {5, 13}`, while at `p = 2` the quadratic symbols on `ℚ⟮s⟯` and `ℚ⟮t⟯` are nontrivial and
     the symbol on `ℚ⟮s * t⟯` is trivial.

## Main results

* `TauCeti.ClassFieldTheory.mem_range_ideleClassArtinMap_comp_ideleClassNormMap_zeta5_iff`:
  characterization of the norm-Artin image in `Gal(ℚ(ζ₅)/ℚ)` as `{±1}` in `(ℤ/5ℤ)ˣ`.
* `TauCeti.ClassFieldTheory.galEquivZMod_ideleClassArtinMap_ideleClassExtension_zeta5`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_comp_ideleClassExtension_zeta5_surjective`: squaring
  formula and surjectivity of the transferred Artin map for `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_zeta5_quadratic_prime_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_zeta5_prime_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_zeta5_prime_apply`:
  prime-by-prime evaluation of the quadratic and transferred Artin symbols in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_five_thirteen_eq_one`,
  `TauCeti.ClassFieldTheory.ideleClassExtension_mem_range_ideleClassNormMap_five_thirteen`:
  identically trivial transfer Artin map and norm principalization over every quadratic subfield of
  `ℚ(√5, √13)`.
* `TauCeti.ClassFieldTheory.range_ideleClassArtinMap_comp_ideleClassNormMap_five_thirteen_ne`:
  pairwise distinctness of the three norm-Artin images in `Gal(L/ℚ)`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_five_thirteen_prime_odd`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_five_thirteen_prime_two`: prime evaluations of the
  quadratic Artin symbols on `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §5.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3, and Chapter VIII.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField GlobalNumberFields _root_.IntermediateField
  IsCyclotomicExtension
open scoped IsMulCommutative

/-! ### Cyclic Galois group of order four: `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)` -/

section Zeta5

variable {L : Type} [Field L] [NumberField L] [IsCyclotomicExtension {5} ℚ L]

local instance isAbelianGalois_zeta5 : IsAbelianGalois ℚ L :=
  IsCyclotomicExtension.isAbelianGalois {5} ℚ L

/-- **Norm square in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** For the quadratic subfield `E` of `L/ℚ`, the image of
`N_{E/ℚ}(C_E)` under `ideleClassArtinMap ℚ L` consists of the automorphisms with cyclotomic
coordinate `±1` in `(ℤ/5ℤ)ˣ`. -/
theorem mem_range_ideleClassArtinMap_comp_ideleClassNormMap_zeta5_iff
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (σ : Gal(L/ℚ)) :
    σ ∈ ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ E : IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 ℚ) ℚ)).range ↔
      Rat.galEquivZMod 5 L σ = 1 ∨ Rat.galEquivZMod 5 L σ = -1 := by
  rw [range_ideleClassArtinMap_comp_ideleClassNormMap_intermediateField,
    IntermediateField.mem_fixingSubgroup_zeta5_iff hE]

/-- **Transfer square in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** Under `Rat.galEquivZMod 5 L`, the global Artin
symbol in `Gal(L/E)` of an extended idele class `ideleClassExtension ℚ E c` equals the square of the
global Artin symbol of `c` in `Gal(L/ℚ)`. -/
theorem galEquivZMod_ideleClassArtinMap_ideleClassExtension_zeta5
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (c : IdeleClassGroup (𝓞 ℚ) ℚ) :
    Rat.galEquivZMod 5 L
        (AlgEquiv.restrictScalars ℚ (ideleClassArtinMap E L (ideleClassExtension ℚ E c))) =
      Rat.galEquivZMod 5 L (ideleClassArtinMap ℚ L c) ^ 2 := by
  rw [restrictScalars_ideleClassArtinMap_ideleClassExtension, hE, map_pow]

/-- **Surjectivity of the transfer Artin map in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** For the quadratic subfield
`E` of a fifth cyclotomic extension `L/ℚ`, composing `ideleClassArtinMap E L` with
`ideleClassExtension ℚ E` surjects onto `Gal(L/E)`. -/
theorem ideleClassArtinMap_comp_ideleClassExtension_zeta5_surjective
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) :
    Function.Surjective ((ideleClassArtinMap E L).comp (ideleClassExtension ℚ E)) := by
  intro τ
  have hmem : AlgEquiv.restrictScalars ℚ τ ∈ E.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker,
      ← AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom ℚ E L]
    exact ⟨τ, rfl⟩
  obtain ⟨u, hu⟩ := (by decide : ∀ c : (ZMod 5)ˣ, c = 1 ∨ c = -1 → ∃ u : (ZMod 5)ˣ, c = u ^ 2) _
    ((IntermediateField.mem_fixingSubgroup_zeta5_iff hE _).mp hmem)
  obtain ⟨c, hc⟩ := ideleClassArtinMap_surjective ℚ L ((Rat.galEquivZMod 5 L).symm u)
  refine ⟨c, AlgEquiv.restrictScalars_injective ℚ ((Rat.galEquivZMod 5 L).injective ?_)⟩
  rw [MonoidHom.comp_apply, galEquivZMod_ideleClassArtinMap_ideleClassExtension_zeta5 hE,
    hc, MulEquiv.apply_symm_apply, ← hu]

/-- For the quadratic subfield `E` of a fifth cyclotomic extension `L/ℚ` and a prime `v` of `ℚ` not
dividing `5`, the Artin symbol `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)` is trivial if and only
if `N(v) ≡ ±1 (mod 5)`. -/
theorem ideleClassArtinMap_zeta5_quadratic_prime_eq_one_iff
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) :
    ideleClassArtinMap ℚ E (primeIdeleClass ℚ v) = 1 ↔
      Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 := by
  rw [ideleClassArtinMap_intermediateField_eq_one_iff (L := L),
    IntermediateField.mem_fixingSubgroup_iff]
  exact globalArtinMap_zeta5_restrict_Qsqrt5 (IsSepClosed.lift : L →ₐ[ℚ] SeparableClosure ℚ)
    hE v hv (globalArtinMap_eq_ofMul_ideleClassArtinMap ℚ L _ _)

/-- **Transfer Artin symbol at primes in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** For the quadratic subfield `E` of
`L/ℚ` and a prime `v` of `ℚ` not dividing `5`, the transferred symbol
`ideleClassArtinMap E L (ideleClassExtension ℚ E (primeIdeleClass ℚ v))` is trivial if and only if
`N(v) ≡ ±1 (mod 5)`. -/
theorem ideleClassArtinMap_ideleClassExtension_zeta5_prime_eq_one_iff
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) :
    ideleClassArtinMap E L (ideleClassExtension ℚ E (primeIdeleClass ℚ v)) = 1 ↔
      Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 := by
  rw [ideleClassArtinMap_ideleClassExtension_eq_one_iff, hE,
    ← (Rat.galEquivZMod 5 L).injective.eq_iff, map_pow, map_one]
  have hval : (Rat.galEquivZMod 5 L (ideleClassArtinMap ℚ L (primeIdeleClass ℚ v)) : ZMod 5).val =
      Ideal.absNorm v.asIdeal % 5 := by
    rw [galEquivZMod_ideleClassArtinMap_prime v hv, ZMod.val_natCast]
  rw [← hval]
  exact (by decide : ∀ u : (ZMod 5)ˣ, u ^ 2 = 1 ↔ (u : ZMod 5).val = 1 ∨ (u : ZMod 5).val = 4) _

/-- **Action of the transferred Artin symbol on fifth roots of unity.** At a prime `v` of `ℚ` not
dividing `5`, the transferred Artin symbol in `Gal(L/E)` fixes every fifth root of unity `ζ ∈ L`
when `N(v) ≡ ±1 (mod 5)` and inverts `ζ` when `N(v) ≡ ±2 (mod 5)`. -/
theorem ideleClassArtinMap_ideleClassExtension_zeta5_prime_apply
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) {ζ : L} (hζ : ζ ^ 5 = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) :
    ideleClassArtinMap E L (ideleClassExtension ℚ E (primeIdeleClass ℚ v)) ζ =
      if Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 then ζ else ζ⁻¹ := by
  split_ifs with hc
  · rw [(ideleClassArtinMap_ideleClassExtension_zeta5_prime_eq_one_iff hE v hv).mpr hc,
      AlgEquiv.one_apply]
  · have hp := _root_.Rat.HeightOneSpectrum.prime_absNorm_asIdeal v
    have hne5 : Ideal.absNorm v.asIdeal ≠ 5 := fun h5 ↦
      hv ((_root_.Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd v (n := 5)).mpr
        (dvd_of_eq h5))
    have h5_ndvd : ¬ 5 ∣ Ideal.absNorm v.asIdeal := fun hdvd ↦
      hne5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hdvd).symm
    obtain ⟨k, hk⟩ : 5 ∣ Ideal.absNorm v.asIdeal ^ 2 + 1 := by
      have h0 : Ideal.absNorm v.asIdeal % 5 ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp h5_ndvd
      rcases (by omega : Ideal.absNorm v.asIdeal % 5 = 2 ∨ Ideal.absNorm v.asIdeal % 5 = 3) with
        h2 | h3
      · exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, Nat.pow_mod, h2])
      · exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, Nat.pow_mod, h3])
    set σ := ideleClassArtinMap ℚ L (primeIdeleClass ℚ v)
    have hσζ : σ ζ = ζ ^ Ideal.absNorm v.asIdeal :=
      globalArtinMap_cyclotomic_prime (IsSepClosed.lift : L →ₐ[ℚ] SeparableClosure ℚ)
        hζ v hv (globalArtinMap_eq_ofMul_ideleClassArtinMap ℚ L _ _)
    have hsq : ideleClassArtinMap E L (ideleClassExtension ℚ E (primeIdeleClass ℚ v)) ζ =
        (σ ^ 2) ζ := by
      rw [← AlgEquiv.restrictScalars_apply ℚ,
        restrictScalars_ideleClassArtinMap_ideleClassExtension, hE]
    rw [hsq, sq, AlgEquiv.mul_apply, hσζ, map_pow, hσζ, ← pow_mul, ← sq]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hk, pow_mul, hζ, one_pow]

end Zeta5

/-! ### Klein four-group: `ℚ(√5, √13)/ℚ` across all three quadratic subfields -/

section KleinFourArtin

variable {L : Type} [Field L] [NumberField L] [IsAbelianGalois ℚ L] {s t : L}

/-- **Transfer square in `ℚ(√5, √13)/ℚ`: universal vanishing across all quadratic subfields.**
For every quadratic subfield `E` of `L = ℚ(√5, √13)` — that is, `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯` by
`Multiquadratic.finrank_eq_two_iff_five_thirteen` — the transferred Artin map `C_ℚ →* Gal(L/E)` is
identically trivial. The instance `IsAbelianGalois ℚ L` is supplied by
`Multiquadratic.isAbelianGalois_five_thirteen`. -/
theorem ideleClassArtinMap_ideleClassExtension_five_thirteen_eq_one
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (c : IdeleClassGroup (𝓞 ℚ) ℚ) :
    ideleClassArtinMap E L (ideleClassExtension ℚ E c) = 1 :=
  ideleClassArtinMap_ideleClassExtension_eq_one_of_exponent_dvd
    (hE.symm ▸ Multiquadratic.aut_exponent_dvd_two_five_thirteen hs ht hst) c

omit [IsAbelianGalois ℚ L] in
/-- **Norm principalization over every quadratic subfield of `ℚ(√5, √13)`.** Extending any rational
idele class `c ∈ C_ℚ` to any of the three quadratic subfields `E` of `ℚ(√5, √13)` makes it a norm
from `L`. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_five_thirteen
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (c : IdeleClassGroup (𝓞 ℚ) ℚ) :
    ideleClassExtension ℚ E c ∈
      (ideleClassNormMap E L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range := by
  have := Multiquadratic.isAbelianGalois_five_thirteen hs ht hst
  exact ideleClassExtension_mem_range_ideleClassNormMap_of_exponent_dvd
    (hE.symm ▸ Multiquadratic.aut_exponent_dvd_two_five_thirteen hs ht hst) c

/-- **Distinctness of the norm-Artin images in `ℚ(√5, √13)/ℚ`.** The images of `N_{E/ℚ}(C_E)` under
`ideleClassArtinMap ℚ L` for the three quadratic subfields `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯` are
pairwise distinct subgroups of `Gal(L/ℚ)`. -/
theorem range_ideleClassArtinMap_comp_ideleClassNormMap_five_thirteen_ne
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) :
    ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ ℚ⟮s⟯ :
          IdeleClassGroup (𝓞 ℚ⟮s⟯) ℚ⟮s⟯ →* IdeleClassGroup (𝓞 ℚ) ℚ)).range ≠
      ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ ℚ⟮t⟯ :
          IdeleClassGroup (𝓞 ℚ⟮t⟯) ℚ⟮t⟯ →* IdeleClassGroup (𝓞 ℚ) ℚ)).range ∧
    ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ ℚ⟮s⟯ :
          IdeleClassGroup (𝓞 ℚ⟮s⟯) ℚ⟮s⟯ →* IdeleClassGroup (𝓞 ℚ) ℚ)).range ≠
      ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ ℚ⟮s * t⟯ :
          IdeleClassGroup (𝓞 ℚ⟮s * t⟯) ℚ⟮s * t⟯ →* IdeleClassGroup (𝓞 ℚ) ℚ)).range ∧
    ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ ℚ⟮t⟯ :
          IdeleClassGroup (𝓞 ℚ⟮t⟯) ℚ⟮t⟯ →* IdeleClassGroup (𝓞 ℚ) ℚ)).range ≠
      ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ ℚ⟮s * t⟯ :
          IdeleClassGroup (𝓞 ℚ⟮s * t⟯) ℚ⟮s * t⟯ →* IdeleClassGroup (𝓞 ℚ) ℚ)).range := by
  simp only [range_ideleClassArtinMap_comp_ideleClassNormMap_intermediateField]
  have hinj : Function.Injective
      (IntermediateField.fixingSubgroup : IntermediateField ℚ L → Subgroup Gal(L/ℚ)) :=
    Function.LeftInverse.injective fun K ↦ IsGalois.fixedField_fixingSubgroup K
  obtain ⟨h1, h2, h3⟩ := Multiquadratic.adjoin_five_thirteen_ne hs ht
  exact ⟨hinj.ne h1, hinj.ne h2, hinj.ne h3⟩

omit [NumberField L] [IsAbelianGalois ℚ L] in
/-- The product `s * t` satisfies `(s * t)² = 65` in `L`. -/
private lemma mul_sq_int_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) :
    (s * t) ^ 2 = algebraMap ℤ L 65 := by
  rw [mul_pow, hs, ht]
  norm_num

/-- **Quadratic Artin symbols at odd primes in `ℚ(√5, √13)/ℚ`.** At an odd rational prime
`p ∉ {5, 13}` represented by `v` (`N(v) = p`), the quadratic Artin symbols
`ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)` on `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯` are trivial if and
only if `legendreSym p 5 = 1`, `legendreSym p 13 = 1`, and `legendreSym p 65 = 1`, respectively. -/
theorem ideleClassArtinMap_five_thirteen_prime_odd
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13)
    (v : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} [Fact p.Prime]
    (hpv : Ideal.absNorm v.asIdeal = p) (hodd : p ≠ 2) (hp5 : p ≠ 5) (hp13 : p ≠ 13) :
    (ideleClassArtinMap ℚ ℚ⟮s⟯ (primeIdeleClass ℚ v) = 1 ↔ legendreSym p 5 = 1) ∧
      (ideleClassArtinMap ℚ ℚ⟮t⟯ (primeIdeleClass ℚ v) = 1 ↔ legendreSym p 13 = 1) ∧
      (ideleClassArtinMap ℚ ℚ⟮s * t⟯ (primeIdeleClass ℚ v) = 1 ↔ legendreSym p 65 = 1) := by
  have hp_prime : p.Prime := Fact.out
  have hp5' : ¬ (p : ℤ) ∣ 5 := fun hdvd ↦
    hp5 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_five).mp (by exact_mod_cast hdvd))
  have hp13' : ¬ (p : ℤ) ∣ 13 := fun hdvd ↦
    hp13 ((Nat.prime_dvd_prime_iff_eq hp_prime (by norm_num)).mp (by exact_mod_cast hdvd))
  have hp65' : ¬ (p : ℤ) ∣ 65 := fun hdvd ↦ by
    have hd : (p : ℤ) ∣ 5 * 13 := by simpa using hdvd
    exact ((Nat.prime_iff_prime_int.mp hp_prime).dvd_mul.mp hd).elim hp5' hp13'
  exact ⟨ideleClassArtinMap_adjoin_sqrt_prime_odd_eq_one_iff (by simpa using hs) v hpv hodd hp5',
    ideleClassArtinMap_adjoin_sqrt_prime_odd_eq_one_iff (by simpa using ht) v hpv hodd hp13',
    ideleClassArtinMap_adjoin_sqrt_prime_odd_eq_one_iff (mul_sq_int_five_thirteen hs ht)
      v hpv hodd hp65'⟩

/-- **Quadratic Artin symbols at `2` in `ℚ(√5, √13)/ℚ`.** At the dyadic prime `v` of `ℚ`
(`N(v) = 2`), the quadratic Artin symbols `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)` on `ℚ⟮s⟯`
and `ℚ⟮t⟯` are nontrivial, whereas on `ℚ⟮s * t⟯` it is `1`. -/
theorem ideleClassArtinMap_five_thirteen_prime_two
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Ideal.absNorm v.asIdeal = 2) :
    ideleClassArtinMap ℚ ℚ⟮s⟯ (primeIdeleClass ℚ v) ≠ 1 ∧
      ideleClassArtinMap ℚ ℚ⟮t⟯ (primeIdeleClass ℚ v) ≠ 1 ∧
      ideleClassArtinMap ℚ ℚ⟮s * t⟯ (primeIdeleClass ℚ v) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ne_eq, ideleClassArtinMap_adjoin_sqrt_prime_two_eq_one_iff (d := 5) (by simpa using hs)
      (by decide) v hv]
    decide
  · rw [ne_eq, ideleClassArtinMap_adjoin_sqrt_prime_two_eq_one_iff (d := 13) (by simpa using ht)
      (by decide) v hv]
    decide
  · rw [ideleClassArtinMap_adjoin_sqrt_prime_two_eq_one_iff (mul_sq_int_five_thirteen hs ht)
      (by decide) v hv]
    decide

end KleinFourArtin

end TauCeti.ClassFieldTheory
