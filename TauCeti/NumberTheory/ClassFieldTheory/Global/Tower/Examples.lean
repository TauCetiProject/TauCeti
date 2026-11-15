/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Prime
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Tower.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Prime
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.FieldTheory.IntermediateField.Quadratic
import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Sqrt5
import TauCeti.NumberTheory.Multiquadratic.Frobenius
import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
import TauCeti.NumberTheory.Multiquadratic.Prime.Radicands
import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
import TauCeti.NumberTheory.Multiquadratic.Subfield.Classification
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Finite Artin maps in cyclic and biquadratic degree-four towers

The three commuting squares of `TauCeti.NumberTheory.ClassFieldTheory.Global.Tower.Basic` —
restriction, norm, and transfer — behave quite differently in the two abelian Galois groups of order
four, the cyclic group `C₄` and the Klein four-group `C₂ × C₂`. This file works out both cases
explicitly over `ℚ`:

1. **Cyclic of order four (`ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`):** let `L` be a fifth cyclotomic extension of `ℚ`
   (`Gal(L/ℚ) ≃* (ℤ/5ℤ)ˣ`) and `E` its quadratic subfield (`[E : ℚ] = 2`).
   * **Norm square:** the image of `N_{E/ℚ}(C_E)` under `ideleClassArtinMap ℚ L` is
     `E.fixingSubgroup`, corresponding under `Rat.galEquivZMod 5 L` to `{1, -1} ≤ (ℤ/5ℤ)ˣ`.
   * **Transfer square:** read in `(ℤ/5ℤ)ˣ`, the transferred Artin symbol
     `ideleClassArtinMap E L (ideleClassExtension ℚ E c)` is the square of
     `ideleClassArtinMap ℚ L c`. Because `2² ≡ -1 (mod 5)`, the composite
     `(ideleClassArtinMap E L).comp (ideleClassExtension ℚ E)` is **surjective** onto `Gal(L/E)`.
   * **Prime evaluations:** at a prime `v` of `ℚ` with `5 ∉ v`, both the restricted symbol in
     `Gal(E/ℚ)` and the transferred symbol in `Gal(L/E)` are trivial if and only if
     `N(v) ≡ ±1 (mod 5)`; on any fifth root of unity `ζ ∈ L`, the transferred symbol fixes `ζ` when
     `N(v) ≡ ±1 (mod 5)` and sends `ζ` to `ζ⁻¹` when `N(v) ≡ ±2 (mod 5)`.

2. **Klein four-group (`ℚ(√5, √13)/ℚ` across all three quadratic subfields):** let `L` be generated
   over `ℚ` by `s` and `t` with `s² = 5` and `t² = 13`.
   * **Quadratic subfields:** an intermediate field `E` of `L/ℚ` has `[E : ℚ] = 2` if and only if
     `E = ℚ⟮s⟯`, `E = ℚ⟮t⟯`, or `E = ℚ⟮s * t⟯`, and these three subfields are pairwise distinct.
   * **Transfer square:** because `Gal(L/ℚ)` has exponent dividing `2`, the transferred Artin map
     `(ideleClassArtinMap E L).comp (ideleClassExtension ℚ E) : C_ℚ →* Gal(L/E)` is **identically
     trivial** on every quadratic subfield `E`, and every rational idele class becomes a norm from
     `L` over each of `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯`.
   * **Norm and restriction squares:** the norm-Artin images for `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯` are
     their three pairwise distinct fixing subgroups in `Gal(L/ℚ)`. Restricting
     `ideleClassArtinMap ℚ L (primeIdeleClass ℚ v)` to the three quadratic subfields gives
     Legendre-symbol criteria `(5/p) = 1`, `(13/p) = 1`, and `(65/p) = 1` at odd primes
     `p ∉ {5, 13}`, while at `p = 2` the restrictions to `ℚ⟮s⟯` and `ℚ⟮t⟯` are nontrivial and the
     restriction to `ℚ⟮s * t⟯` is trivial.

## Main results

* `TauCeti.ClassFieldTheory.galEquivZMod_ideleClassArtinMap_prime`: cyclotomic coordinate of
  `ideleClassArtinMap ℚ M (primeIdeleClass ℚ v)` at a prime not dividing `m`.
* `TauCeti.ClassFieldTheory.mem_fixingSubgroup_zeta5_iff`,
  `TauCeti.ClassFieldTheory.mem_range_ideleClassArtinMap_comp_ideleClassNormMap_zeta5_iff`:
  identification of `E.fixingSubgroup` and the norm-Artin image in `Gal(ℚ(ζ₅)/ℚ)` with `{±1}` in
  `(ℤ/5ℤ)ˣ`.
* `TauCeti.ClassFieldTheory.galEquivZMod_ideleClassArtinMap_ideleClassExtension_zeta5`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_comp_ideleClassExtension_zeta5_surjective`: squaring
  formula and surjectivity of the transferred Artin map for `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_zeta5_quadratic_prime_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_zeta5_prime_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_zeta5_prime_apply`:
  prime-by-prime evaluation of the restricted and transferred Artin symbols in
  `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.
* `TauCeti.ClassFieldTheory.isAbelianGalois_five_thirteen`,
  `TauCeti.ClassFieldTheory.finrank_eq_two_iff_five_thirteen`,
  `TauCeti.ClassFieldTheory.adjoin_five_thirteen_ne`: abelianity and classification of the three
  distinct quadratic subfields of `ℚ(√5, √13)`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_five_thirteen_eq_one`,
  `TauCeti.ClassFieldTheory.ideleClassExtension_mem_range_ideleClassNormMap_five_thirteen`:
  identically trivial transfer Artin map and norm principalization over every quadratic subfield of
  `ℚ(√5, √13)`.
* `TauCeti.ClassFieldTheory.range_ideleClassArtinMap_comp_ideleClassNormMap_five_thirteen_ne`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_five_thirteen_prime_odd_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_five_thirteen_prime_two`: distinctness of the three
  norm-Artin images and prime evaluations of the three restricted Artin symbols in `ℚ(√5, √13)`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3, and Chapter VIII.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField GlobalNumberFields _root_.IntermediateField
  IsCyclotomicExtension
open scoped IsMulCommutative

/-- Rewrites `globalArtinMap` of an abelian extension in terms of `ideleClassArtinMap`. -/
private lemma globalArtinMap_eq_ofMul_ideleClassArtinMap {K M : Type} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    (ι : M →ₐ[K] SeparableClosure K) (c : IdeleClassGroup (𝓞 K) K) :
    globalArtinMap K M ι (.ofMul c) =
      .ofMul (Group.Abelianization.of (ideleClassArtinMap K M c)) := by
  simpa only [ofMul_toMul] using congrArg Additive.ofMul (of_ideleClassArtinMap K M ι c).symm

/-! ### Cyclotomic coordinate of `ideleClassArtinMap` -/

/-- In a rational cyclotomic field, the coordinate under `Rat.galEquivZMod` of the finite Artin
symbol `ideleClassArtinMap ℚ M (primeIdeleClass ℚ v)` at a prime not dividing the level is the
absolute norm of that prime modulo the level. The instance `IsAbelianGalois ℚ M` is supplied by
`IsCyclotomicExtension.isAbelianGalois`. -/
theorem galEquivZMod_ideleClassArtinMap_prime {m : ℕ} [NeZero m] {M : Type} [Field M]
    [NumberField M] [IsCyclotomicExtension {m} ℚ M] [IsAbelianGalois ℚ M]
    (v : HeightOneSpectrum (𝓞 ℚ)) (hm : (m : 𝓞 ℚ) ∉ v.asIdeal) :
    (Rat.galEquivZMod m M (ideleClassArtinMap ℚ M (primeIdeleClass ℚ v)) : ZMod m) =
      Ideal.absNorm v.asIdeal :=
  galEquivZMod_globalArtinMap_prime (IsSepClosed.lift : M →ₐ[ℚ] SeparableClosure ℚ) v hm
    (globalArtinMap_eq_ofMul_ideleClassArtinMap _ _)

/-! ### Cyclic Galois group of order four: `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)` -/

section Zeta5

variable {L : Type} [Field L] [NumberField L] [IsCyclotomicExtension {5} ℚ L]

local instance isAbelianGalois_zeta5 : IsAbelianGalois ℚ L :=
  IsCyclotomicExtension.isAbelianGalois {5} ℚ L

/-- For a quadratic subfield `E` of a fifth cyclotomic extension `L/ℚ`, an automorphism
`σ ∈ Gal(L/ℚ)` belongs to `E.fixingSubgroup` if and only if its coordinate in `(ℤ/5ℤ)ˣ` is `±1`. -/
theorem mem_fixingSubgroup_zeta5_iff {E : IntermediateField ℚ L}
    (hE : Module.finrank ℚ E = 2) (σ : Gal(L/ℚ)) :
    σ ∈ E.fixingSubgroup ↔ Rat.galEquivZMod 5 L σ = 1 ∨ Rat.galEquivZMod 5 L σ = -1 := by
  have hH : E.fixingSubgroup.index = 2 :=
    (IntermediateField.finrank_eq_fixingSubgroup_index L E).symm.trans hE
  constructor
  · intro hσH
    by_contra hc
    rw [not_or] at hc
    have hgen : ∀ d : (ZMod 5)ˣ, ∃ k < 4, d = Rat.galEquivZMod 5 L σ ^ k :=
      (by decide : ∀ c : (ZMod 5)ˣ, c ≠ 1 → c ≠ -1 → ∀ d, ∃ k < 4, d = c ^ k) _ hc.1 hc.2
    have htop : E.fixingSubgroup = ⊤ := (Subgroup.eq_top_iff' _).mpr fun τ ↦ by
      obtain ⟨k, -, hk⟩ := hgen (Rat.galEquivZMod 5 L τ)
      have hτ : τ = σ ^ k := (Rat.galEquivZMod 5 L).injective (by rw [map_pow]; exact hk)
      exact hτ ▸ pow_mem hσH k
    rw [htop, Subgroup.index_top] at hH
    omega
  · intro hc
    obtain ⟨d, hd⟩ := (by decide : ∀ c : (ZMod 5)ˣ, c = 1 ∨ c = -1 → ∃ d : (ZMod 5)ˣ, c = d ^ 2)
      _ hc
    have hσd : σ = ((Rat.galEquivZMod 5 L).symm d) ^ 2 := (Rat.galEquivZMod 5 L).injective
      (by rw [map_pow, MulEquiv.apply_symm_apply]; exact hd)
    exact hσd ▸ Subgroup.sq_mem_of_index_two hH _

/-- **Norm square in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** For the quadratic subfield `E` of `L/ℚ`, the image of
`N_{E/ℚ}(C_E)` under `ideleClassArtinMap ℚ L` consists of the automorphisms with cyclotomic
coordinate `±1` in `(ℤ/5ℤ)ˣ`. -/
theorem mem_range_ideleClassArtinMap_comp_ideleClassNormMap_zeta5_iff
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (σ : Gal(L/ℚ)) :
    σ ∈ ((ideleClassArtinMap ℚ L).comp
        (ideleClassNormMap ℚ E : IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 ℚ) ℚ)).range ↔
      Rat.galEquivZMod 5 L σ = 1 ∨ Rat.galEquivZMod 5 L σ = -1 := by
  rw [range_ideleClassArtinMap_comp_ideleClassNormMap_intermediateField,
    mem_fixingSubgroup_zeta5_iff hE]

/-- **Transfer square in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** Under `Rat.galEquivZMod 5 L`, the global Artin
symbol in `Gal(L/E)` of an extended idele class `ideleClassExtension ℚ E c` equals the square of the
global Artin symbol of `c` in `Gal(L/ℚ)`. -/
theorem galEquivZMod_ideleClassArtinMap_ideleClassExtension_zeta5
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (c : IdeleClassGroup (𝓞 ℚ) ℚ) :
    Rat.galEquivZMod 5 L
        (AlgEquiv.restrictScalars ℚ (ideleClassArtinMap E L (ideleClassExtension ℚ E c))) =
      Rat.galEquivZMod 5 L (ideleClassArtinMap ℚ L c) ^ 2 := by
  rw [restrictScalars_ideleClassArtinMap_ideleClassExtension, hE, map_pow]

/-- **Surjectivity of the transfer Artin map in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** Unlike the Klein-four case,
composing `ideleClassArtinMap E L` with `ideleClassExtension ℚ E` surjects onto `Gal(L/E)`, because
the squares in `(ℤ/5ℤ)ˣ` exhaust `{1, -1}`. -/
theorem ideleClassArtinMap_comp_ideleClassExtension_zeta5_surjective
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) :
    Function.Surjective ((ideleClassArtinMap E L).comp (ideleClassExtension ℚ E)) := by
  intro τ
  have hmem : AlgEquiv.restrictScalars ℚ τ ∈ E.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker,
      ← AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom ℚ E L]
    exact ⟨τ, rfl⟩
  obtain ⟨u, hu⟩ := (by decide : ∀ c : (ZMod 5)ˣ, c = 1 ∨ c = -1 → ∃ u : (ZMod 5)ˣ, c = u ^ 2) _
    ((mem_fixingSubgroup_zeta5_iff hE _).mp hmem)
  obtain ⟨c, hc⟩ := ideleClassArtinMap_surjective ℚ L ((Rat.galEquivZMod 5 L).symm u)
  refine ⟨c, AlgEquiv.restrictScalars_injective ℚ ((Rat.galEquivZMod 5 L).injective ?_)⟩
  rw [MonoidHom.comp_apply, galEquivZMod_ideleClassArtinMap_ideleClassExtension_zeta5 hE,
    hc, MulEquiv.apply_symm_apply, ← hu]

/-- **Restriction square at primes in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** For a prime `v` of `ℚ` not dividing
`5`, the Artin symbol in `Gal(E/ℚ)` is trivial if and only if `N(v) ≡ ±1 (mod 5)`. -/
theorem ideleClassArtinMap_zeta5_quadratic_prime_eq_one_iff
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) :
    ideleClassArtinMap ℚ E (primeIdeleClass ℚ v) = 1 ↔
      Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 := by
  rw [← restrictNormal_ideleClassArtinMap (L := L),
    ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ E L,
    ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    IntermediateField.mem_fixingSubgroup_iff]
  exact globalArtinMap_zeta5_restrict_Qsqrt5 (IsSepClosed.lift : L →ₐ[ℚ] SeparableClosure ℚ)
    hE v hv (globalArtinMap_eq_ofMul_ideleClassArtinMap _ _)

/-- **Transfer square at primes in `ℚ ⊆ ℚ(√5) ⊆ ℚ(ζ₅)`.** For a prime `v` of `ℚ` not dividing `5`,
the transferred symbol `ideleClassArtinMap E L (ideleClassExtension ℚ E (primeIdeleClass ℚ v))`
is trivial if and only if `N(v) ≡ ±1 (mod 5)`. At primes with `N(v) ≡ 4 (mod 5)`, the Artin symbol
in `Gal(L/ℚ)` is nontrivial (order `2`), yet both its restriction to `E` and its transfer to `L/E`
are trivial. -/
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
  · have hp : (Ideal.absNorm v.asIdeal).Prime := by
      rw [_root_.Rat.HeightOneSpectrum.absNorm_asIdeal]
      exact _root_.Rat.HeightOneSpectrum.prime_natGenerator v
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
        hζ v hv (globalArtinMap_eq_ofMul_ideleClassArtinMap _ _)
    have hsq : ideleClassArtinMap E L (ideleClassExtension ℚ E (primeIdeleClass ℚ v)) ζ =
        (σ ^ 2) ζ := by
      rw [← AlgEquiv.restrictScalars_apply ℚ,
        restrictScalars_ideleClassArtinMap_ideleClassExtension, hE]
    rw [hsq, sq, AlgEquiv.mul_apply, hσζ, map_pow, hσζ, ← pow_mul, ← sq]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hk, pow_mul, hζ, one_pow]

end Zeta5

/-! ### Klein four-group: `ℚ(√5, √13)/ℚ` across all three quadratic subfields -/

/-- Evaluating the product of `![s, t]` over `{0, 1}`. -/
private lemma prod_pair_five_thirteen {M : Type*} [CommMonoid M] (s t : M) :
    ∏ i ∈ ({0, 1} : Finset (Fin 2)), (![s, t] : Fin 2 → M) i = s * t := by
  rw [Finset.prod_pair (by decide : (0 : Fin 2) ≠ 1)]
  simp

section KleinFourSubfields

variable {L : Type*} [Field L] [CharZero L] {s t : L}

/-- The pair `![s, t]` satisfies the radicand equations for `![5, 13]`. -/
private lemma sq_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) :
    ∀ i, (![s, t] : Fin 2 → L) i ^ 2 = algebraMap ℚ L ((![5, 13] : Fin 2 → ℕ) i : ℚ) := by
  intro i
  fin_cases i <;> simp [hs, ht]

/-- Square-class independence of the prime radicands `![5, 13]`. -/
private lemma indep_five_thirteen :
    ∀ S : Finset (Fin 2), S.Nonempty → ¬ IsSquare (∏ i ∈ S, ((![5, 13] : Fin 2 → ℕ) i : ℚ)) :=
  Multiquadratic.not_isSquare_prod_primes_of_injective ![5, 13] (by decide) (by decide)

/-- Rewriting `ℚ⟮s, t⟯ = ⊤` as `adjoin ℚ (Set.range ![s, t]) = ⊤`. -/
private lemma adjoin_range_five_thirteen (hst : ℚ⟮s, t⟯ = ⊤) :
    IntermediateField.adjoin ℚ (Set.range (![s, t] : Fin 2 → L)) = ⊤ := by
  rw [← hst]
  congr 1
  ext x
  simp [eq_comm, or_comm]

/-- A field generated over `ℚ` by square roots of `5` and `13` is abelian Galois over `ℚ`. -/
theorem isAbelianGalois_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤) :
    IsAbelianGalois ℚ L :=
  have := Multiquadratic.isGalois_of_adjoin_eq_top (sq_five_thirteen hs ht)
    (adjoin_range_five_thirteen hst)
  have := Multiquadratic.isMulCommutative_of_adjoin_eq_top (sq_five_thirteen hs ht)
    (adjoin_range_five_thirteen hst)
  {}

/-- **Classification of the quadratic subfields of `ℚ(√5, √13)`.** If `L` is generated over `ℚ` by
square roots `s` of `5` and `t` of `13`, then an intermediate field `E` of `L/ℚ` has degree `2` over
`ℚ` if and only if `E = ℚ⟮s⟯`, `E = ℚ⟮t⟯`, or `E = ℚ⟮s * t⟯`. -/
theorem finrank_eq_two_iff_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
    (E : IntermediateField ℚ L) :
    Module.finrank ℚ E = 2 ↔ E = ℚ⟮s⟯ ∨ E = ℚ⟮t⟯ ∨ E = ℚ⟮s * t⟯ := by
  have hroot := sq_five_thirteen hs ht
  constructor
  · intro hE
    obtain ⟨S, hS, rfl⟩ := Multiquadratic.exists_finset_of_finrank_two_of_adjoin_eq_top
      hroot indep_five_thirteen (adjoin_range_five_thirteen hst) E hE
    rcases (by decide : ∀ S : Finset (Fin 2), S.Nonempty →
        S = {0} ∨ S = {1} ∨ S = {0, 1}) S hS with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (by rw [prod_pair_five_thirteen]))
  · rintro (rfl | rfl | rfl)
    · rw [show s = ∏ i ∈ ({0} : Finset (Fin 2)), (![s, t] : Fin 2 → L) i by simp]
      exact IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare
        (Multiquadratic.prod_root_sq hroot {0})
        (indep_five_thirteen {0} (Finset.singleton_nonempty 0))
    · rw [show t = ∏ i ∈ ({1} : Finset (Fin 2)), (![s, t] : Fin 2 → L) i by simp]
      exact IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare
        (Multiquadratic.prod_root_sq hroot {1})
        (indep_five_thirteen {1} (Finset.singleton_nonempty 1))
    · rw [← prod_pair_five_thirteen s t]
      exact IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare
        (Multiquadratic.prod_root_sq hroot {0, 1})
        (indep_five_thirteen {0, 1} ⟨0, by simp⟩)

/-- **Distinctness of the three quadratic subfields of `ℚ(√5, √13)`.** The subfields `ℚ⟮s⟯`, `ℚ⟮t⟯`,
and `ℚ⟮s * t⟯` are pairwise distinct. -/
theorem adjoin_five_thirteen_ne (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) :
    ℚ⟮s⟯ ≠ ℚ⟮t⟯ ∧ ℚ⟮s⟯ ≠ ℚ⟮s * t⟯ ∧ ℚ⟮t⟯ ≠ ℚ⟮s * t⟯ := by
  have hinj := Multiquadratic.adjoin_prod_root_injective (sq_five_thirteen hs ht)
    indep_five_thirteen
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (by decide : ({0} : Finset (Fin 2)) ≠ {1}) (hinj (by simpa using h))
  · exact (by decide : ({0} : Finset (Fin 2)) ≠ {0, 1})
      (hinj (by simpa [prod_pair_five_thirteen] using h))
  · exact (by decide : ({1} : Finset (Fin 2)) ≠ {0, 1})
      (hinj (by simpa [prod_pair_five_thirteen] using h))

end KleinFourSubfields

section KleinFourArtin

variable {L : Type} [Field L] [NumberField L] [IsAbelianGalois ℚ L] {s t : L}

/-- **Transfer square in `ℚ(√5, √13)/ℚ`: universal vanishing across all quadratic subfields.**
For every quadratic subfield `E` of `L = ℚ(√5, √13)` — that is, `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯` by
`finrank_eq_two_iff_five_thirteen` — the transferred Artin map `C_ℚ →* Gal(L/E)` is identically
trivial. The instance `IsAbelianGalois ℚ L` is supplied by `isAbelianGalois_five_thirteen`. -/
theorem ideleClassArtinMap_ideleClassExtension_five_thirteen_eq_one
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (c : IdeleClassGroup (𝓞 ℚ) ℚ) :
    ideleClassArtinMap E L (ideleClassExtension ℚ E c) = 1 := by
  have hexp : Monoid.exponent Gal(L/ℚ) ∣ Module.finrank ℚ E := by
    rw [hE]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one
      (Multiquadratic.aut_pow_two_eq_one_of_adjoin_eq_top
        (sq_five_thirteen hs ht) (adjoin_range_five_thirteen hst))
  exact ideleClassArtinMap_ideleClassExtension_eq_one_of_exponent_dvd hexp c

/-- **Norm principalization over every quadratic subfield of `ℚ(√5, √13)`.** Extending any rational
idele class `c ∈ C_ℚ` to any of the three quadratic subfields `E` of `ℚ(√5, √13)` makes it a norm
from `L`. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_five_thirteen
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
    {E : IntermediateField ℚ L} (hE : Module.finrank ℚ E = 2) (c : IdeleClassGroup (𝓞 ℚ) ℚ) :
    ideleClassExtension ℚ E c ∈
      (ideleClassNormMap E L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range := by
  rw [← ker_ideleClassArtinMap E L, MonoidHom.mem_ker]
  exact ideleClassArtinMap_ideleClassExtension_five_thirteen_eq_one hs ht hst hE c

/-- **Norm squares in `ℚ(√5, √13)/ℚ`.** The images of `N_{E/ℚ}(C_E)` under `ideleClassArtinMap ℚ L`
for the three quadratic subfields `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯` are their fixing subgroups, which
are three pairwise distinct subgroups of `Gal(L/ℚ)`. -/
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
    fun E₁ E₂ h ↦ by
      simpa only [IntermediateField.fixedField_fixingSubgroup] using
        congrArg IntermediateField.fixedField h
  obtain ⟨h1, h2, h3⟩ := adjoin_five_thirteen_ne hs ht
  exact ⟨hinj.ne h1, hinj.ne h2, hinj.ne h3⟩

/-- **Restriction squares at odd primes in `ℚ(√5, √13)/ℚ`.** At an odd rational prime `p ∉ {5, 13}`
represented by `v` (`N(v) = p`), the restrictions of `ideleClassArtinMap ℚ L (primeIdeleClass ℚ v)`
— equal by `restrictNormal_ideleClassArtinMap` to the three quadratic Artin symbols — are trivial on
`ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯` if and only if the Legendre symbols `(5/p)`, `(13/p)`, and `(65/p)`
equal `1`, respectively. -/
theorem ideleClassArtinMap_five_thirteen_prime_odd_eq_one_iff
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
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
  have hs_int : s ^ 2 = algebraMap ℤ L 5 := by rw [hs]; norm_num
  have ht_int : t ^ 2 = algebraMap ℤ L 13 := by rw [ht]; norm_num
  have hst_sq : (s * t) ^ 2 = algebraMap ℤ L 65 := by rw [mul_pow, hs, ht]; norm_num
  have hr : ∀ i, (![s, t] : Fin 2 → L) i ^ 2 = algebraMap ℤ L ((![5, 13] : Fin 2 → ℤ) i) := by
    intro i; fin_cases i <;> simp [hs, ht]
  have hcop : ∀ i, ¬ (p : ℤ) ∣ (![5, 13] : Fin 2 → ℤ) i := by
    intro i; fin_cases i <;> assumption
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    have h := _root_.Rat.HeightOneSpectrum.liesOver_span_absNorm v Q
    rwa [hpv] at h
  have := Multiquadratic.isUnramifiedAt_of_forall_not_dvd hr (adjoin_range_five_thirteen hst)
    hodd hcop Q
  have hF : IsArithFrobAt ℤ (ideleClassArtinMap ℚ L (primeIdeleClass ℚ v)) Q :=
    (Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ Q).mp
      (globalArtinMap_isArithFrobAt L (IsSepClosed.lift : L →ₐ[ℚ] SeparableClosure ℚ) v Q
        (globalArtinMap_eq_ofMul_ideleClassArtinMap _ _))
  refine ⟨?_, ?_, ?_⟩
  · rw [← restrictNormal_ideleClassArtinMap (L := L),
      ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ ℚ⟮s⟯ L,
      AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff,
      NumberField.isArithFrobAt_apply_sqrt_eq_self_iff hodd hp5' hs_int Q hF]
  · rw [← restrictNormal_ideleClassArtinMap (L := L),
      ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ ℚ⟮t⟯ L,
      AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff,
      NumberField.isArithFrobAt_apply_sqrt_eq_self_iff hodd hp13' ht_int Q hF]
  · rw [← restrictNormal_ideleClassArtinMap (L := L),
      ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ ℚ⟮s * t⟯ L,
      AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff,
      NumberField.isArithFrobAt_apply_sqrt_eq_self_iff hodd hp65' hst_sq Q hF]

/-- **Restriction squares at `2` in `ℚ(√5, √13)/ℚ`.** Since `5 ≡ 13 ≡ 5 (mod 8)` while
`65 ≡ 1 (mod 8)`, the dyadic prime `v` of `ℚ` (`N(v) = 2`) is unramified in `ℚ(√5, √13)`: its Artin
symbols in `ℚ⟮s⟯` and `ℚ⟮t⟯` are nontrivial, whereas its Artin symbol in `ℚ⟮s * t⟯` is `1`. -/
theorem ideleClassArtinMap_five_thirteen_prime_two
    (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Ideal.absNorm v.asIdeal = 2) :
    ideleClassArtinMap ℚ ℚ⟮s⟯ (primeIdeleClass ℚ v) ≠ 1 ∧
      ideleClassArtinMap ℚ ℚ⟮t⟯ (primeIdeleClass ℚ v) ≠ 1 ∧
      ideleClassArtinMap ℚ ℚ⟮s * t⟯ (primeIdeleClass ℚ v) = 1 := by
  have hs_int : s ^ 2 = algebraMap ℤ L 5 := by rw [hs]; norm_num
  have ht_int : t ^ 2 = algebraMap ℤ L 13 := by rw [ht]; norm_num
  have hst_sq : (s * t) ^ 2 = algebraMap ℤ L 65 := by rw [mul_pow, hs, ht]; norm_num
  have hr : ∀ i, (![s, t] : Fin 2 → L) i ^ 2 = algebraMap ℤ L ((![5, 13] : Fin 2 → ℤ) i) := by
    intro i; fin_cases i <;> simp [hs, ht]
  have hd4 : ∀ i, (![5, 13] : Fin 2 → ℤ) i % 4 = 1 := by
    intro i; fin_cases i <;> decide
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  have : Q.LiesOver (Ideal.span {(2 : ℤ)}) := by
    have h := _root_.Rat.HeightOneSpectrum.liesOver_span_absNorm v Q
    rwa [hv, Nat.cast_ofNat] at h
  have := Multiquadratic.isUnramifiedAt_of_forall_mod_four_eq_one hr
    (adjoin_range_five_thirteen hst) hd4 Q
  have hF : IsArithFrobAt ℤ (ideleClassArtinMap ℚ L (primeIdeleClass ℚ v)) Q :=
    (Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ Q).mp
      (globalArtinMap_isArithFrobAt L (IsSepClosed.lift : L →ₐ[ℚ] SeparableClosure ℚ) v Q
        (globalArtinMap_eq_ofMul_ideleClassArtinMap _ _))
  refine ⟨?_, ?_, ?_⟩
  · rw [ne_eq, ← restrictNormal_ideleClassArtinMap (L := L),
      ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ ℚ⟮s⟯ L,
      AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff,
      isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight hs_int (by norm_num) Q hF]
    decide
  · rw [ne_eq, ← restrictNormal_ideleClassArtinMap (L := L),
      ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ ℚ⟮t⟯ L,
      AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff,
      isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight ht_int (by norm_num) Q hF]
    decide
  · rw [← restrictNormal_ideleClassArtinMap (L := L),
      ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ ℚ⟮s * t⟯ L,
      AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff,
      isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight hst_sq (by norm_num) Q hF]
    decide

end KleinFourArtin

end TauCeti.ClassFieldTheory
