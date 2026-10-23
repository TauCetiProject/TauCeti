/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Norm.Basic
import TauCeti.Algebra.Group.PowerClassGroup.Card
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Finite

/-!
# The cokernel of the completed norm

Let `L/K` be a finite Galois extension of nonarchimedean local fields, let `p` be a prime with
`p ≠ 0` in `K`, and let `A(K) = lim_m Kˣ/(Kˣ)^(p^m)` be the `p`-adic completion of `Kˣ`. The field
norm induces the completed norm `N : A(L) → A(K)` (`TauCeti.padicCompletionUnitsNorm`). Its
cokernel is the maximal `p`-quotient of `Gal(L/K)^ab`, read off from the norm residue isomorphism
`Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)^ab` (`TauCeti.ClassFieldTheory.normResidue`).

Concretely, for every `m` the class of `x ∈ A(K)` at level `m` followed by the norm residue
symbol modulo `p ^ m`-th powers is a surjective homomorphism

`padicCompletionUnitsNormResidue p K L m : A(K) → Gal(L/K)^ab / (Gal(L/K)^ab)^(p^m)`,

and once `p ^ m` contains the full power of `p` dividing `#Gal(L/K)^ab` its kernel is exactly the
image of `N`. For such `m` the target is the maximal `p`-quotient of `Gal(L/K)^ab`, of order the
full power of `p` dividing `#Gal(L/K)^ab = [Kˣ : N_{L/K}(Lˣ)]`, so `A(K) / N(A(L))` is the
`p`-completion of `Kˣ / N_{L/K}(Lˣ)`.

The proof is algebraic. Every element of `A(K)` is the class of a unit up to a `p ^ m`-multiple
(`TauCeti.exists_eq_padicCompletionUnitsOf_add_pow_smul`), and `n`-th powers of units being
norms forces `n • A(K) ⊆ N(A(L))` (`TauCeti.nsmul_mem_range_padicCompletionUnitsNorm`), which
for `n = #Gal(L/K)^ab` absorbs the `p ^ m`-multiples.

## Main definitions

* `TauCeti.padicCompletionUnitsNormResidue p K L m`: the completed norm residue map
  `A(K) → Gal(L/K)^ab / (Gal(L/K)^ab)^(p^m)`.
* `TauCeti.padicCompletionUnitsNormCokernelEquiv`: the resulting isomorphism
  `A(K) / N(A(L)) ≃ Gal(L/K)^ab / (Gal(L/K)^ab)^(p^m)`.

## Main results

* `TauCeti.nsmul_mem_range_padicCompletionUnitsNorm`: if every `n`-th power in `Kˣ` is a norm
  from `L`, then `n` kills the cokernel of the completed norm.
* `TauCeti.padicCompletionUnitsNormResidue_of`: on the class of a unit, the completed norm residue
  map is its norm residue symbol.
* `TauCeti.padicCompletionUnitsNormResidue_surjective`: the completed norm residue map is
  surjective.
* `TauCeti.padicCompletionUnitsNormResidue_padicCompletionUnitsNorm`: it kills completed norms.
* `TauCeti.ker_padicCompletionUnitsNormResidue`: its kernel is the image of the completed norm.
* `TauCeti.natCard_quotient_range_padicCompletionUnitsNorm`: the cokernel of the completed norm
  has order the full power of `p` dividing `#Gal(L/K)^ab`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., VII §4,
  especially the proof of (7.4.4).
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory

section Multiple

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- **A bound on the cokernel of the completed norm.** If `(Kˣ)^p` has finite index in `Kˣ` and
every `n`-th power in `Kˣ` is a norm from `L`, then `n • x` lies in the image of the completed norm
`A(L) → A(K)` for every `x ∈ A(K)`. For instance `n = [L : K]` always works
(`TauCeti.pow_finrank_mem_normGroup`). -/
theorem nsmul_mem_range_padicCompletionUnitsNorm
    [(powMonoidHom p : Kˣ →* Kˣ).range.FiniteIndex] {n : ℕ}
    (hn : ∀ u : Kˣ, u ^ n ∈ normGroup K L) (x : Additive ↑(padicCompletionUnits p K)) :
    n • x ∈ LinearMap.range (padicCompletionUnitsNorm p K L) := by
  have hx : x ∈ Submodule.span ℤ_[p]
      (Set.range fun u : Kˣ ↦ Additive.ofMul (padicCompletionUnitsOf p K u)) := by
    rw [span_range_padicCompletionUnitsOf_eq_top]
    trivial
  -- The elements whose `n`-th multiple is a completed norm form a submodule containing the
  -- classes of units, since `u ^ n` is the norm of some unit of `L`.
  refine (Submodule.span_le (p := (LinearMap.range (padicCompletionUnitsNorm p K L)).comap
    (n • LinearMap.id)).2 ?_ hx)
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := mem_normGroup_iff_exists_normUnits.1 (hn u)
  exact ⟨Additive.ofMul (padicCompletionUnitsOf p L v), by simp [hv]⟩

end Multiple

section Reciprocity

variable (p : ℕ) (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-- The **completed norm residue map** at level `m`: the class of an element of `A(K)` in
`Kˣ / (Kˣ)^(p^m)`, followed by the norm residue isomorphism `Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)^ab`
modulo `p ^ m`-th powers. -/
def padicCompletionUnitsNormResidue (m : ℕ) :
    Additive ↑(padicCompletionUnits p K) →+
      Additive (powerClassQuotient (Abelianization Gal(L/K)) (p ^ m)) :=
  MonoidHom.toAdditive <|
    (powerClassMap (p ^ m)
      ((normResidue K L).toMonoidHom.comp (QuotientGroup.mk' (normGroup K L)))).comp <|
    (QuotientGroup.quotientMulEquivOfEq
      (powerSubgroup_eq_range_powMonoidHom Kˣ (p ^ m)).symm).toMonoidHom.comp <|
    (Pi.evalMonoidHom _ m).comp (padicCompletionUnits p K).subtype

/-- The completed norm residue map at level `m` only depends on the level-`m` coordinate: if that
coordinate is the class of `u ∈ Kˣ`, the value is the norm residue symbol of `u`. -/
theorem padicCompletionUnitsNormResidue_eq {m : ℕ} {x : Additive ↑(padicCompletionUnits p K)}
    {u : Kˣ} (hu : x.toMul.1 m = QuotientGroup.mk u) :
    padicCompletionUnitsNormResidue p K L m x =
      Additive.ofMul (QuotientGroup.mk (normResidue K L (QuotientGroup.mk u)) :
        powerClassQuotient (Abelianization Gal(L/K)) (p ^ m)) := by
  simp [padicCompletionUnitsNormResidue, hu]

/-- On the class of a unit `u ∈ Kˣ`, the completed norm residue map is the norm residue symbol of
`u`, modulo `p ^ m`-th powers. -/
@[simp]
theorem padicCompletionUnitsNormResidue_of (m : ℕ) (u : Kˣ) :
    padicCompletionUnitsNormResidue p K L m (Additive.ofMul (padicCompletionUnitsOf p K u)) =
      Additive.ofMul (QuotientGroup.mk (normResidue K L (QuotientGroup.mk u)) :
        powerClassQuotient (Abelianization Gal(L/K)) (p ^ m)) :=
  padicCompletionUnitsNormResidue_eq p K L
    (by rw [toMul_ofMul, padicCompletionUnitsOf_apply, QuotientGroup.mk'_apply])

/-- The completed norm residue map is surjective, since the norm residue isomorphism is. -/
theorem padicCompletionUnitsNormResidue_surjective (m : ℕ) :
    Function.Surjective (padicCompletionUnitsNormResidue p K L m) := by
  intro y
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.toMul
  obtain ⟨c, rfl⟩ := (normResidue K L).surjective g
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨Additive.ofMul (padicCompletionUnitsOf p K u),
    (padicCompletionUnitsNormResidue_of p K L m u).trans (by rw [hg, ofMul_toMul])⟩

/-- The completed norm residue map at level `m` kills `p ^ m`-multiples, since its target has
exponent dividing `p ^ m`. -/
@[simp]
theorem padicCompletionUnitsNormResidue_pow_smul [Fact p.Prime] (m : ℕ)
    (y : Additive ↑(padicCompletionUnits p K)) :
    padicCompletionUnitsNormResidue p K L m ((p : ℤ_[p]) ^ m • y) = 0 := by
  simp [← Nat.cast_pow, ← toMul_eq_one]

/-- The completed norm residue map kills completed norms: the level-`m` coordinate of a completed
norm is the class of a norm, whose norm residue symbol is trivial. -/
@[simp]
theorem padicCompletionUnitsNormResidue_padicCompletionUnitsNorm [Fact p.Prime] (m : ℕ)
    (y : Additive ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsNormResidue p K L m (padicCompletionUnitsNorm p K L y) = 0 := by
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (y.toMul.1 m)
  rw [padicCompletionUnitsNormResidue_eq p K L (u := Algebra.normUnits K v)
    (by rw [padicCompletionUnitsNorm_apply, ← hv, padicCompletionPowerClassNorm_mk]),
    (normResidue_mk_eq_one_iff K L _).2 (normUnits_mem_normGroup K L v), QuotientGroup.mk_one,
    ofMul_one]

/-- If `p ^ m` contains the full power of `p` dividing `#Gal(L/K)^ab`, then every
`p ^ m`-multiple in `A(K)` is a completed norm. -/
private theorem pow_smul_mem_range_padicCompletionUnitsNorm [Fact p.Prime] (hpK : (p : K) ≠ 0)
    {m : ℕ}
    (hm : (Nat.card (Abelianization Gal(L/K))).factorization p ≤ m)
    (y : Additive ↑(padicCompletionUnits p K)) :
    (p : ℤ_[p]) ^ m • y ∈ LinearMap.range (padicCompletionUnitsNorm p K L) := by
  have := finiteIndex_range_powMonoidHom hpK
  set n := Nat.card (Abelianization Gal(L/K))
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  -- Write `p ^ m = n * (p ^ (m - v) * b⁻¹)` with `n = p ^ v * b` and `b` a `p`-adic unit.
  set b := ordCompl[p] n
  have hb : IsUnit (b : ℤ_[p]) := PadicInt.isUnit_iff.2
    (PadicInt.norm_natCast_eq_one_iff.2 (Nat.coprime_ordCompl Fact.out hn0))
  have hnb : (n : ℤ_[p]) = (p : ℤ_[p]) ^ n.factorization p * b := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hpm : (p : ℤ_[p]) ^ m =
      (n : ℤ_[p]) * ((p : ℤ_[p]) ^ (m - n.factorization p) * ↑hb.unit⁻¹) := by
    rw [hnb, mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' hm, IsUnit.mul_val_inv, mul_one]
  rw [hpm, mul_smul, padicCompletionUnits_natCast_smul]
  exact nsmul_mem_range_padicCompletionUnitsNorm p K L
    (pow_natCard_abelianization_mem_normGroup K L) _

/-- **The kernel of the completed norm residue map is the image of the completed norm**, once
`p ^ m` contains the full power of `p` dividing `#Gal(L/K)^ab`. Together with
`TauCeti.padicCompletionUnitsNormResidue_surjective`, this identifies the cokernel of
`A(L) → A(K)` with the maximal `p`-quotient of `Gal(L/K)^ab`. -/
theorem ker_padicCompletionUnitsNormResidue [Fact p.Prime] (hpK : (p : K) ≠ 0) {m : ℕ}
    (hm : (Nat.card (Abelianization Gal(L/K))).factorization p ≤ m) :
    (padicCompletionUnitsNormResidue p K L m).ker =
      (LinearMap.range (padicCompletionUnitsNorm p K L)).toAddSubgroup := by
  have := finiteIndex_range_powMonoidHom hpK
  ext x
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
  constructor
  · intro hx
    obtain ⟨u, y, rfl⟩ := exists_eq_padicCompletionUnitsOf_add_pow_smul p K m x
    -- The norm residue symbol of `u` is a `p ^ m`-th power, so `u` is a norm times a
    -- `p ^ m`-th power.
    obtain ⟨g, hg⟩ : ∃ g, g ^ p ^ m = normResidue K L u := by simpa using hx
    obtain ⟨c, rfl⟩ := (normResidue K L).surjective g
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective c
    have hnorm : u * (w ^ p ^ m)⁻¹ ∈ normGroup K L := by
      rw [← normResidue_mk_eq_one_iff]
      simp [hg]
    obtain ⟨v, hv⟩ := mem_normGroup_iff_exists_normUnits.1 hnorm
    rw [eq_mul_inv_iff_mul_eq] at hv
    simp only [← hv, map_mul, ofMul_mul, map_pow, ofMul_pow, ← padicCompletionUnits_natCast_smul,
      Nat.cast_pow, add_assoc, ← smul_add]
    refine add_mem ⟨Additive.ofMul (padicCompletionUnitsOf p L v), by simp⟩ ?_
    exact pow_smul_mem_range_padicCompletionUnitsNorm p K L hpK hm _
  · rintro ⟨y, rfl⟩
    exact padicCompletionUnitsNormResidue_padicCompletionUnitsNorm p K L m y

/-- **The cokernel of the completed norm** `A(L) → A(K)` is `Gal(L/K)^ab / (Gal(L/K)^ab)^(p^m)`,
the maximal `p`-quotient of `Gal(L/K)^ab`, once `p ^ m` contains the full power of `p` dividing
`#Gal(L/K)^ab`. The isomorphism is induced by the completed norm residue map
(`TauCeti.padicCompletionUnitsNormCokernelEquiv_mk`). -/
def padicCompletionUnitsNormCokernelEquiv [Fact p.Prime] (hpK : (p : K) ≠ 0) {m : ℕ}
    (hm : (Nat.card (Abelianization Gal(L/K))).factorization p ≤ m) :
    Additive ↑(padicCompletionUnits p K) ⧸
        (LinearMap.range (padicCompletionUnitsNorm p K L)).toAddSubgroup ≃+
      Additive (powerClassQuotient (Abelianization Gal(L/K)) (p ^ m)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (ker_padicCompletionUnitsNormResidue p K L hpK hm).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (padicCompletionUnitsNormResidue_surjective p K L m))

/-- The isomorphism `padicCompletionUnitsNormCokernelEquiv` sends the class of `x ∈ A(K)` to its
completed norm residue. -/
@[simp]
theorem padicCompletionUnitsNormCokernelEquiv_mk [Fact p.Prime] (hpK : (p : K) ≠ 0) {m : ℕ}
    (hm : (Nat.card (Abelianization Gal(L/K))).factorization p ≤ m)
    (x : Additive ↑(padicCompletionUnits p K)) :
    padicCompletionUnitsNormCokernelEquiv p K L hpK hm (QuotientAddGroup.mk x) =
      padicCompletionUnitsNormResidue p K L m x := by
  simp only [padicCompletionUnitsNormCokernelEquiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk,
    TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk]

/-- **The order of the cokernel of the completed norm** `A(L) → A(K)` is the full power of `p`
dividing `#Gal(L/K)^ab = [Kˣ : N_{L/K}(Lˣ)]`. -/
theorem natCard_quotient_range_padicCompletionUnitsNorm [Fact p.Prime] (hpK : (p : K) ≠ 0) :
    Nat.card (Additive ↑(padicCompletionUnits p K) ⧸
        (LinearMap.range (padicCompletionUnitsNorm p K L)).toAddSubgroup) =
      p ^ (Nat.card (Abelianization Gal(L/K))).factorization p := by
  rw [Nat.card_congr (padicCompletionUnitsNormCokernelEquiv p K L hpK le_rfl).toEquiv,
    Nat.card_congr Additive.toMul, natCard_powerClassQuotient_prime_pow _ le_rfl]

end Reciprocity

end TauCeti
