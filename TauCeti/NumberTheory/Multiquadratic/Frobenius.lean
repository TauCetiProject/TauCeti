/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius
public import TauCeti.NumberTheory.Multiquadratic.Galois.Group
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop

/-!
# Frobenius actions on multiquadratic generators

Let `K = ℚ(√d₁, …, √dₙ)` be a number field generated over `ℚ` by square roots `r i` of
integers `d i`, and let `p` be an odd prime dividing none of the `d i`. The multiquadratic
roadmap's Layer 1 states the splitting law in two forms: `p` splits completely iff every `d i`
is a quadratic residue mod `p` (`NumberField.ncard_primesOver_multiquadratic_iff`),
and, more precisely, the Frobenius at `p` acts on the generators by the Legendre symbols. This
file supplies the second, finer form. An arithmetic Frobenius exists at every prime `Q` of
`𝓞 K` above `p` and acts on each generator by the corresponding symbol,

`σ (r i) = legendreSym p (d i) • r i`

(`NumberField.exists_isArithFrobAt_multiquadratic`), and the Frobenius is trivial iff
every symbol is `1` (`isArithFrobAt_multiquadratic_eq_one_iff`).

The roadmap's actual sign-vector statement — the Frobenius equals `((d₁/p), …, (dₙ/p))` under
the identification `Gal ≅ (ℤ/2)ⁿ` — is then proved for the multiquadratic field taken as the
intermediate field `M = ℚ(√dᵢ : i) = adjoin ℚ (Set.range root)` itself, where
`TauCeti.Multiquadratic.galoisGroupEquiv` lives (its automorphisms are of `M`, not of an
abstract `K`). For a Frobenius `σ` on `M` at a prime over `p`,
`NumberField.signPattern_frobenius` gives each coordinate
`signPattern root σ i = if legendreSym p (d i) = 1 then 0 else 1`, and
`NumberField.galoisGroupEquiv_frobenius` packages this as
`galoisGroupEquiv σ = ((d₁/p), …, (dₙ/p))`.

## Main results

* `NumberField.exists_isArithFrobAt_multiquadratic`: at every prime `Q` over `p` there
  is a Frobenius, and it sends each generator `r i` to `legendreSym p (d i) • r i`.
* `NumberField.isArithFrobAt_multiquadratic_eq_one_iff`: a Frobenius at `Q` is the
  identity iff every `d i` is a quadratic residue mod `p`.
* `NumberField.signPattern_frobenius` and
  `NumberField.galoisGroupEquiv_frobenius`: the Frobenius sign pattern on the
  multiquadratic field is the Legendre vector `((d₁/p), …, (dₙ/p))` under `Gal ≅ (ℤ/2)ⁿ`.
* `TauCeti.Multiquadratic.isArithFrobAt_eq_one_iff_mod_eight`: for radicands `1` modulo `4`,
  Frobenius at `2` is trivial exactly when all radicands are `1` modulo `8`.
* `TauCeti.Multiquadratic.signPattern_frobenius_two` and
  `TauCeti.Multiquadratic.galoisGroupEquiv_frobenius_two`: its coordinates are `0` at
  radicands `1` modulo `8` and `1` at radicands `5` modulo `8`.
-/

public section

open NumberField Ideal

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}
  {p : ℕ} [Fact p.Prime]

/-- **A multiquadratic Frobenius is trivial iff every radicand is a residue.** Let
`K = ℚ(√d₁, …, √dₙ)` be generated over `ℚ` by the square roots `r i` of the integers `d i`,
let `p` be an odd prime with `p ∤ d i` for all `i`, and let `σ` be an arithmetic Frobenius at
an ideal `Q` of `𝓞 K` above `p`. Then `σ = 1` iff every `d i` is a quadratic residue mod `p`.
Combined with the splitting law, this is the Frobenius-theoretic reading of complete
splitting. -/
theorem isArithFrobAt_multiquadratic_eq_one_iff (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ = 1 ↔ ∀ i, legendreSym p (d i) = 1 := by
  constructor
  · rintro rfl i
    exact (isArithFrobAt_apply_sqrt_eq_self_iff hodd (hcop i) (hr i) Q hσ).mp
      (AlgEquiv.one_apply (r i))
  · intro hqr
    refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
    rintro x ⟨i, rfl⟩
    exact (isArithFrobAt_apply_sqrt_eq_self_iff hodd (hcop i) (hr i) Q hσ).mpr (hqr i)

/-- **The Frobenius of a multiquadratic field acts on each generator by a Legendre symbol.**
For a Galois number field `K` with elements `r i` satisfying `r i ² = d i ∈ ℤ`, an odd prime
`p` with `p ∤ d i` for all `i`, and any prime `Q` of `𝓞 K` above `p`, there is an arithmetic
Frobenius `σ ∈ Gal(K/ℚ)` at `Q`, and it sends each generator to the corresponding Legendre
multiple: `σ (r i) = legendreSym p (d i) • r i`. This is the generator-wise Frobenius input of
the multiquadratic splitting law; the sign-vector description under `galoisGroupEquiv` is not
formed here (see the module docstring). The `IsGalois ℚ K` hypothesis holds in particular when
the `r i` generate `K` (`TauCeti.Multiquadratic.isGalois` transported along `adjoin ℚ … = ⊤`). -/
theorem exists_isArithFrobAt_multiquadratic [IsGalois ℚ K] (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q ∧
      ∀ i, σ (r i) = legendreSym p (d i) • r i := by
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  exact ⟨σ, hσ, fun i => isArithFrobAt_apply_sqrt hodd (hcop i) (hr i) Q hσ⟩

/-! ### The Frobenius as a sign vector under `Gal ≅ (ℤ/2)ⁿ`

The `signPattern`/`galoisGroupEquiv` API of `TauCeti.NumberTheory.Multiquadratic.Galois.Group`
is stated for automorphisms of the intermediate field `M = adjoin ℚ (Set.range root)`. To match
the roadmap's `Gal(K/ℚ) ≅ (ℤ/2)ⁿ` Frobenius-vector statement we take that intermediate field
(a number field, `NumberField.of_intermediateField`) as the multiquadratic field itself, and
compute the Frobenius sign pattern there. -/

section SignVector

open TauCeti.Multiquadratic

variable {L : Type*} [Field L] [NumberField L] {root : ι → L} {d : ι → ℤ}

/-- The rational algebra structure on the multiquadratic intermediate field. -/
local instance algebraRatAdjoinRange :
    Algebra ℚ ↥(IntermediateField.adjoin ℚ (Set.range root)) :=
  (IntermediateField.adjoin ℚ (Set.range root)).algebra'

/-- The integer defining equation `root i ² = d i` recast with base field `ℚ`. Only characteristic
zero is needed (for the `ℤ → ℚ → L` scalar tower). -/
private theorem root_sq_algebraMap_rat {L : Type*} [Field L] [CharZero L] {root : ι → L}
    {d : ι → ℤ} (hroot : ∀ i, root i ^ 2 = algebraMap ℤ L (d i)) (i : ι) :
    root i ^ 2 = algebraMap ℚ L (d i : ℚ) := by
  rw [hroot i, IsScalarTower.algebraMap_apply ℤ ℚ L]; simp

/-- **The Frobenius sign pattern of a multiquadratic field is the Legendre encoding.** For the
multiquadratic field `M = ℚ(√dᵢ : i) = adjoin ℚ (Set.range root)`, an odd prime `p ∤ dᵢ`, and an
arithmetic Frobenius `σ` on `M` at a prime `Q` above `p`, the `i`-th coordinate of the sign
pattern is `0` when `dᵢ` is a quadratic residue mod `p` and `1` otherwise. -/
theorem signPattern_frobenius (hroot : ∀ i, root i ^ 2 = algebraMap ℤ L (d i))
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 ↥(IntermediateField.adjoin ℚ (Set.range root)))) [Q.LiesOver (span {(p : ℤ)})]
    {σ : ↥(IntermediateField.adjoin ℚ (Set.range root)) ≃ₐ[ℚ]
        ↥(IntermediateField.adjoin ℚ (Set.range root))}
    (hσ : IsArithFrobAt ℤ σ Q) (i : ι) :
    signPattern root σ i = if legendreSym p (d i) = 1 then 0 else 1 := by
  -- `gen root i`, an element of `M = adjoin ℚ (Set.range root)`, squares to `d i` in `𝓞 M`.
  have hcast : algebraMap ℤ ↥(IntermediateField.adjoin ℚ (Set.range root)) (d i) =
      algebraMap ℚ ↥(IntermediateField.adjoin ℚ (Set.range root)) (d i : ℚ) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ ↥(IntermediateField.adjoin ℚ (Set.range root))]; simp
  have hgensq : gen root i ^ 2 =
      algebraMap ℤ ↥(IntermediateField.adjoin ℚ (Set.range root)) (d i) := by
    rw [hcast]; exact gen_sq (root_sq_algebraMap_rat hroot) i
  have hd0 : d i ≠ 0 := fun h => hcop i (h ▸ dvd_zero _)
  -- The Frobenius acts on that generator by the Legendre symbol; feed it to the sign-pattern
  -- bridge of `Galois.Group`.
  have haction : σ (gen root i) = legendreSym p (d i) • gen root i :=
    isArithFrobAt_apply_sqrt hodd (hcop i) hgensq Q hσ
  exact signPattern_eq_ite_of_zsmul_gen (root_sq_algebraMap_rat hroot) σ
    (legendreSym.eq_one_or_neg_one p
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop i))
    (by exact_mod_cast hd0) haction

/-- **The Frobenius of a multiquadratic field is the Legendre sign vector.** Under square-class
independence of the `dᵢ` (so `TauCeti.Multiquadratic.galoisGroupEquiv` is the identification
`Gal(M/ℚ) ≅ (ℤ/2)ⁿ`), an arithmetic Frobenius `σ` at a prime `Q` above the odd prime `p ∤ dᵢ`
maps to the vector of Legendre symbols `i ↦ (dᵢ/p)`. This is the roadmap's Layer 1 Frobenius
statement. -/
theorem galoisGroupEquiv_frobenius [Finite ι] (hroot : ∀ i, root i ^ 2 = algebraMap ℤ L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 ↥(IntermediateField.adjoin ℚ (Set.range root)))) [Q.LiesOver (span {(p : ℤ)})]
    {σ : ↥(IntermediateField.adjoin ℚ (Set.range root)) ≃ₐ[ℚ]
        ↥(IntermediateField.adjoin ℚ (Set.range root))}
    (hσ : IsArithFrobAt ℤ σ Q) :
    galoisGroupEquiv
        (fun i => by rw [hroot i, IsScalarTower.algebraMap_apply ℤ ℚ L]; simp) hindep σ =
      Multiplicative.ofAdd (fun i => if legendreSym p (d i) = 1 then 0 else 1) := by
  rw [galoisGroupEquiv_apply]
  congr 1
  funext i
  exact signPattern_frobenius hroot p hodd hcop Q hσ i

end SignVector

end NumberField

/-! ### Dyadic Frobenius sign patterns in multiquadratic fields

For square roots of integers `dᵢ ≡ 1 (mod 4)`, Frobenius at a prime over `2` has sign
coordinate `0` if `dᵢ ≡ 1 (mod 8)` and `1` if `dᵢ ≡ 5 (mod 8)`. Under square-class
independence these are its coordinates in the explicit Galois-group isomorphism with `(ℤ/2)ⁿ`.
In particular, Frobenius is the identity exactly when every radicand is `1` modulo `8`.

The condition modulo `4` lets one use integral half-generators to separate the two conjugates
modulo `2`. For prime-discriminant composita of odd discriminant, all generators satisfy this
condition. This complements the odd-prime Legendre-symbol calculation above.
-/

open IntermediateField

namespace TauCeti.Multiquadratic

/-- Frobenius above `2` on a field generated by square roots of `dᵢ ≡ 1 (mod 4)` is trivial
exactly when all the radicands are `1` modulo `8`. No independence assumption is needed. -/
theorem isArithFrobAt_eq_one_iff_mod_eight
    {K : Type*} [Field K] [CharZero K] {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(2 : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ = 1 ↔ ∀ i, d i % 8 = 1 := by
  constructor
  · rintro rfl i
    exact (isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight (hr i) (hd i) Q hσ).mp
      (AlgEquiv.one_apply _)
  · intro h
    refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
    rintro _ ⟨i, rfl⟩
    exact (isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight (hr i) (hd i) Q hσ).mpr (h i)

variable {L : Type*} [Field L] [CharZero L] {ι : Type*} {d : ι → ℤ} {root : ι → L}

/-- The sign vector of a dyadic Frobenius has a `1` exactly at the radicands congruent to `5`
modulo `8`. -/
theorem signPattern_frobenius_two
    (hroot : ∀ i, root i ^ 2 = algebraMap ℤ L (d i)) (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 ↥(adjoin ℚ (Set.range root)))) [Q.LiesOver (span {(2 : ℤ)})]
    {σ : ↥(adjoin ℚ (Set.range root)) ≃ₐ[ℚ] ↥(adjoin ℚ (Set.range root))}
    (hσ : IsArithFrobAt ℤ σ Q) (i : ι) :
    signPattern root σ i = if d i % 8 = 1 then 0 else 1 := by
  have hsq : gen root i ^ 2 = algebraMap ℤ ↥(adjoin ℚ (Set.range root)) (d i) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ]
    exact gen_sq (K := ℚ) (d := fun j ↦ (d j : ℚ))
      (fun j ↦ by simpa using hroot j) i
  simp only [signPattern,
    isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight hsq (hd i) Q hσ]

/-- Under square-class independence, the Galois-group coordinates of Frobenius above `2` are
`0` at radicands `1` modulo `8` and `1` at radicands `5` modulo `8`. -/
theorem galoisGroupEquiv_frobenius_two [Finite ι]
    (hroot : ∀ i, root i ^ 2 = algebraMap ℤ L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 ↥(adjoin ℚ (Set.range root)))) [Q.LiesOver (span {(2 : ℤ)})]
    {σ : ↥(adjoin ℚ (Set.range root)) ≃ₐ[ℚ] ↥(adjoin ℚ (Set.range root))}
    (hσ : IsArithFrobAt ℤ σ Q) :
    galoisGroupEquiv (fun i ↦ by simpa using hroot i) hindep σ =
      Multiplicative.ofAdd (fun i ↦ if d i % 8 = 1 then 0 else 1) := by
  rw [galoisGroupEquiv_apply]
  congr 1
  funext i
  exact signPattern_frobenius_two hroot hd Q hσ i

end TauCeti.Multiquadratic
