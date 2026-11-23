/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Group.FiniteMonoid
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.Finiteness.Cardinality
import TauCeti.RingTheory.Ideal.Extended

/-!
# The factorial idempotent of an element of a complete algebra

Let `R` be a commutative ring, `I` an ideal of `R`, and `S` an `R`-algebra, possibly
noncommutative, which is `I`-adically complete as an `R`-module and whose quotients
`S ⧸ I ^ k • S` are finite. For every `t : S` the factorial powers `t ^ n !` converge
`I`-adically to an idempotent `Ideal.factorialIdempotent I t` of `S`. In each finite quotient
`S ⧸ I ^ k • S` the factorial powers of the image of `t` are constant from `n = |S ⧸ I ^ k • S|`
on, so the convergence comes with an explicit threshold, and the limit is the idempotent power of
`t` in every finite quotient.

This is Hida's ordinary idempotent in its algebraic form. For a finite algebra `S` over a complete
noetherian local ring with finite residue field, taking `S` to be a Hecke algebra or the
endomorphism ring of a perfect complex, the factorial idempotent of `U_p` cuts out the ordinary
part. It lies in the subalgebra `R[t]`, commutes with everything that commutes with `t`, and is
natural for algebra homomorphisms. When `S` is commutative it is `0` modulo every prime ideal
containing `t` and `1` modulo every other prime ideal (over the extended ideal of `I`).

## Main definitions

* `Ideal.factorialIdempotent I t`: the `I`-adic limit of the factorial powers `t ^ n !`, when it
  exists, and `0` otherwise.

## Main results

* `Ideal.pow_factorial_sub_factorialIdempotent_mem`: `t ^ n ! - e ∈ I ^ k • S` as soon as
  `|S ⧸ I ^ k • S| ≤ n`.
* `Ideal.factorialIdempotent_eq_of_eventually_sub_mem`: in an `I`-adically separated algebra, the
  factorial idempotent is the only `I`-adic limit of the factorial powers.
* `Ideal.isIdempotentElem_factorialIdempotent`: the factorial idempotent is idempotent.
* `Commute.factorialIdempotent_right`: it commutes with everything that commutes with `t`.
* `AlgHom.map_factorialIdempotent`: it is natural for algebra homomorphisms.
* `Ideal.factorialIdempotent_mem_adjoin`: for a finite algebra over a complete noetherian ring
  with finite quotient `R ⧸ I`, it lies in `R[t]`.
* `Ideal.factorialIdempotent_eq_one_of_isUnit`, `Ideal.factorialIdempotent_eq_zero_of_isNilpotent`:
  units give `1` and nilpotents give `0`; more generally topologically nilpotent elements give
  `0` (`Ideal.factorialIdempotent_eq_zero_of_forall_exists_pow_mem`).
* `Ideal.Quotient.mk_factorialIdempotent`: for commutative `S` and a prime ideal `𝔪` containing
  the extension of `I`, the factorial idempotent is `0` modulo `𝔪` if `t ∈ 𝔪`, and `1` otherwise.

## References

* H. Hida, *Iwasawa modules attached to congruences of cusp forms*, Ann. Sci. École Norm. Sup.
  19 (1986), §1, (1.17a)–(1.17b).
* C. B. Khare, J. A. Thorne, *Potential automorphy and the Leopoldt conjecture*, Amer. J. Math.
  139 (2017), §2.4, Lemma 2.10 and its proof.
* F. Calegari, D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*, Invent. Math.
  211 (2018), §7.1.
-/

public section

open Filter
open scoped Nat

namespace Ideal

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

section FiniteQuotient

variable {J : Ideal R}

/-- The quotient ring `S ⧸ J S` is finite, with the cardinality of `S ⧸ J • S`. -/
private theorem finite_quotient_map_algebraMap [Finite (S ⧸ (J • ⊤ : Submodule R S))] {m : ℕ}
    (hm : Nat.card (S ⧸ (J • ⊤ : Submodule R S)) ≤ m) :
    Finite (S ⧸ J.map (algebraMap R S)) ∧ Nat.card (S ⧸ J.map (algebraMap R S)) ≤ m :=
  ⟨.of_equiv _ (quotSMulTopEquivQuotMap J).toEquiv,
    by rwa [← Nat.card_congr (quotSMulTopEquivQuotMap J).toEquiv]⟩

/-- The factorial powers of `t` agree modulo `J • S` from `n = |S ⧸ J • S|` on. -/
private theorem pow_factorial_sub_pow_factorial_mem [Finite (S ⧸ (J • ⊤ : Submodule R S))]
    (t : S) {m n : ℕ} (hm : Nat.card (S ⧸ (J • ⊤ : Submodule R S)) ≤ m) (hmn : m ≤ n) :
    t ^ (n !) - t ^ m ! ∈ J • (⊤ : Submodule R S) := by
  obtain ⟨_, hm⟩ := finite_quotient_map_algebraMap hm
  rw [← mem_map_algebraMap_iff, ← Quotient.eq, map_pow, map_pow]
  exact TauCeti.pow_factorial_eq_pow_factorial_of_card_le _ hm hmn

/-- The factorial power `t ^ m !` is idempotent modulo `J • S` once `|S ⧸ J • S| ≤ m`. -/
private theorem pow_factorial_mul_self_sub_mem [Finite (S ⧸ (J • ⊤ : Submodule R S))]
    (t : S) {m : ℕ} (hm : Nat.card (S ⧸ (J • ⊤ : Submodule R S)) ≤ m) :
    t ^ m ! * t ^ (m !) - t ^ m ! ∈ J • (⊤ : Submodule R S) := by
  obtain ⟨_, hm⟩ := finite_quotient_map_algebraMap hm
  rw [← mem_map_algebraMap_iff, ← Quotient.eq, map_mul, map_pow]
  exact TauCeti.isIdempotentElem_pow_factorial_of_card_le _ hm

/-- The factorial power `t ^ m !` of a unit is `1` modulo `J • S` once `|S ⧸ J • S| ≤ m`. -/
private theorem pow_factorial_sub_one_mem_of_isUnit [Finite (S ⧸ (J • ⊤ : Submodule R S))]
    {t : S} (ht : IsUnit t) {m : ℕ} (hm : Nat.card (S ⧸ (J • ⊤ : Submodule R S)) ≤ m) :
    t ^ (m !) - 1 ∈ J • (⊤ : Submodule R S) := by
  obtain ⟨_, hm⟩ := finite_quotient_map_algebraMap hm
  rw [← mem_map_algebraMap_iff, ← Quotient.eq, map_pow, map_one]
  exact (IsIdempotentElem.iff_eq_one_of_isUnit ((ht.map _).pow _)).mp
    (TauCeti.isIdempotentElem_pow_factorial_of_card_le _ hm)

end FiniteQuotient

variable (I : Ideal R)

open Classical in
/-- The **factorial idempotent** of `t`: an `I`-adic limit of the factorial powers `t ^ n !`,
that is, an element `e` with `t ^ n ! - e ∈ I ^ k • S` for every `k` and all large `n`, if one
exists, and `0` otherwise.

Such a limit exists when `S` is `I`-adically precomplete with finite quotients `S ⧸ I ^ k • S`
(`Ideal.pow_factorial_sub_factorialIdempotent_mem`); it is unique and idempotent when `S` is
moreover `I`-adically separated (`Ideal.factorialIdempotent_eq_of_eventually_sub_mem`,
`Ideal.isIdempotentElem_factorialIdempotent`). -/
noncomputable def factorialIdempotent (t : S) : S :=
  if h : ∃ e : S, ∀ k, ∀ᶠ n in atTop, t ^ (n !) - e ∈ I ^ k • (⊤ : Submodule R S) then
    h.choose else 0

variable {I}

/-- The factorial idempotent is an `I`-adic limit of the factorial powers whenever one exists. -/
private theorem eventually_pow_factorial_sub_factorialIdempotent_mem_of_exists {t : S}
    (h : ∃ e : S, ∀ k, ∀ᶠ n in atTop, t ^ (n !) - e ∈ I ^ k • (⊤ : Submodule R S)) (k : ℕ) :
    ∀ᶠ n in atTop, t ^ (n !) - I.factorialIdempotent t ∈ I ^ k • (⊤ : Submodule R S) := by
  simp only [factorialIdempotent, h, ↓reduceDIte]
  exact h.choose_spec k

/-- In an `I`-adically separated algebra, any `I`-adic limit of the factorial powers of `t` is
the factorial idempotent of `t`. -/
theorem factorialIdempotent_eq_of_eventually_sub_mem [IsHausdorff I S] {t e : S}
    (h : ∀ k, ∀ᶠ n in atTop, t ^ (n !) - e ∈ I ^ k • (⊤ : Submodule R S)) :
    I.factorialIdempotent t = e := by
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k ↦ SModEq.sub_mem.mpr ?_
  obtain ⟨n, hn, he⟩ :=
    ((eventually_pow_factorial_sub_factorialIdempotent_mem_of_exists ⟨e, h⟩ k).and (h k)).exists
  have := sub_mem he hn
  rwa [sub_sub_sub_cancel_left] at this

section Complete

variable [∀ k, Finite (S ⧸ (I ^ k • ⊤ : Submodule R S))]

/-- An `I`-adic limit of the factorial powers with the explicit thresholds `|S ⧸ I ^ k • S|`. -/
private theorem exists_pow_factorial_sub_mem [IsPrecomplete I S] (t : S) :
    ∃ L : S, ∀ k n, Nat.card (S ⧸ (I ^ k • ⊤ : Submodule R S)) ≤ n →
      t ^ (n !) - L ∈ I ^ k • (⊤ : Submodule R S) := by
  let c (k : ℕ) : ℕ := Nat.card (S ⧸ (I ^ k • ⊤ : Submodule R S))
  have hc : Monotone c := fun k l hkl ↦ Nat.card_le_card_of_surjective _
    (Submodule.factor_surjective (Submodule.pow_smul_top_le I S hkl))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹_› (f := fun k ↦ t ^ (c k)!) fun {k l} hkl ↦
    (SModEq.sub_mem.mpr (pow_factorial_sub_pow_factorial_mem t le_rfl (hc hkl))).symm
  refine ⟨L, fun k n hn ↦ ?_⟩
  have := add_mem (pow_factorial_sub_pow_factorial_mem t le_rfl hn) (SModEq.sub_mem.mp (hL k))
  rwa [sub_add_sub_cancel] at this

/-- **Factorial convergence with an explicit threshold.** In an `I`-adically precomplete algebra
with finite quotients `S ⧸ I ^ k • S`, the factorial power `t ^ n !` agrees with the factorial
idempotent modulo `I ^ k • S` as soon as `|S ⧸ I ^ k • S| ≤ n`. -/
theorem pow_factorial_sub_factorialIdempotent_mem [IsPrecomplete I S] (t : S) {k n : ℕ}
    (hn : Nat.card (S ⧸ (I ^ k • ⊤ : Submodule R S)) ≤ n) :
    t ^ (n !) - I.factorialIdempotent t ∈ I ^ k • (⊤ : Submodule R S) := by
  obtain ⟨L, hL⟩ := exists_pow_factorial_sub_mem (I := I) t
  have hlim := eventually_pow_factorial_sub_factorialIdempotent_mem_of_exists
    ⟨L, fun k ↦ eventually_atTop.mpr ⟨_, fun n ↦ hL k n⟩⟩ k
  obtain ⟨N, hN, he⟩ := (hlim.and (eventually_ge_atTop n)).exists
  -- `t ^ n ! - e = (t ^ n ! - L) - (t ^ N ! - L) + (t ^ N ! - e)`.
  have := add_mem (sub_mem (hL k n hn) (hL k N (hn.trans he))) hN
  rwa [sub_sub_sub_cancel_right, sub_add_sub_cancel] at this

/-- In an `I`-adically precomplete algebra with finite quotients `S ⧸ I ^ k • S`, the factorial
powers of `t` converge `I`-adically to the factorial idempotent of `t`. -/
theorem eventually_pow_factorial_sub_factorialIdempotent_mem [IsPrecomplete I S] (t : S)
    (k : ℕ) : ∀ᶠ n in atTop, t ^ (n !) - I.factorialIdempotent t ∈ I ^ k • (⊤ : Submodule R S) :=
  eventually_atTop.mpr ⟨_, fun _ ↦ pow_factorial_sub_factorialIdempotent_mem t⟩

/-- The factorial idempotent agrees with `t ^ n !` modulo the extended ideal `I ^ k S`, for
`n = |S ⧸ I ^ k • S|`. -/
private theorem factorialIdempotent_sub_pow_factorial_mem_map [IsPrecomplete I S] (t : S)
    (k : ℕ) : I.factorialIdempotent t - t ^ (Nat.card (S ⧸ (I ^ k • ⊤ : Submodule R S)))! ∈
      (I ^ k).map (algebraMap R S) := by
  rw [mem_map_algebraMap_iff, ← neg_sub, neg_mem_iff]
  exact pow_factorial_sub_factorialIdempotent_mem t le_rfl

variable [IsAdicComplete I S]

/-- The factorial idempotent is idempotent. -/
theorem isIdempotentElem_factorialIdempotent (t : S) :
    IsIdempotentElem (I.factorialIdempotent t) := by
  set e := I.factorialIdempotent t
  rw [isIdempotentElem_iff]
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k ↦ SModEq.sub_mem.mpr ?_
  set x := t ^ (Nat.card (S ⧸ (I ^ k • ⊤ : Submodule R S)))!
  have hx : e - x ∈ (I ^ k).map (algebraMap R S) :=
    factorialIdempotent_sub_pow_factorial_mem_map t k
  have hxx : x * x - x ∈ (I ^ k).map (algebraMap R S) :=
    (mem_map_algebraMap_iff _).mpr (pow_factorial_mul_self_sub_mem t le_rfl)
  have hsplit : e * e - e = (e - x) * e + x * (e - x) + (x * x - x) - (e - x) := by noncomm_ring
  rw [← mem_map_algebraMap_iff, hsplit]
  exact sub_mem (add_mem (add_mem (mul_mem_right _ _ hx) (mul_mem_left _ _ hx)) hxx) hx

/-- The factorial idempotent of `t` commutes with every element commuting with `t`. -/
theorem _root_.Commute.factorialIdempotent_right {s t : S} (h : Commute s t) :
    Commute s (I.factorialIdempotent t) := by
  set e := I.factorialIdempotent t
  rw [commute_iff_eq]
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k ↦ SModEq.sub_mem.mpr ?_
  set x := t ^ (Nat.card (S ⧸ (I ^ k • ⊤ : Submodule R S)))!
  have hx : e - x ∈ (I ^ k).map (algebraMap R S) :=
    factorialIdempotent_sub_pow_factorial_mem_map t k
  have hsplit : s * e - e * s = s * (e - x) - (e - x) * s + (s * x - x * s) := by noncomm_ring
  rw [← mem_map_algebraMap_iff, hsplit, (h.pow_right _).eq, sub_self, add_zero]
  exact sub_mem (mul_mem_left _ _ hx) (mul_mem_right _ _ hx)

/-- The factorial idempotent of `t` commutes with `t`. -/
theorem commute_factorialIdempotent (t : S) : Commute t (I.factorialIdempotent t) :=
  (Commute.refl t).factorialIdempotent_right

/-- The factorial idempotent of a unit is `1`. -/
theorem factorialIdempotent_eq_one_of_isUnit {t : S} (ht : IsUnit t) :
    I.factorialIdempotent t = 1 := by
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k ↦ SModEq.sub_mem.mpr ?_
  have := add_mem (factorialIdempotent_sub_pow_factorial_mem_map (I := I) t k)
    ((mem_map_algebraMap_iff _).mpr (pow_factorial_sub_one_mem_of_isUnit ht le_rfl))
  rwa [sub_add_sub_cancel, mem_map_algebraMap_iff] at this

end Complete

/-- The factorial idempotent of an idempotent is itself. -/
theorem _root_.IsIdempotentElem.factorialIdempotent_eq [IsHausdorff I S] {t : S}
    (ht : IsIdempotentElem t) : I.factorialIdempotent t = t :=
  factorialIdempotent_eq_of_eventually_sub_mem fun _ ↦
    (eventually_ge_atTop 0).mono fun n _ ↦ by simp [ht.pow_eq (Nat.factorial_ne_zero n)]

/-- The factorial idempotent of `0` is `0`. -/
@[simp]
theorem factorialIdempotent_zero [IsHausdorff I S] : I.factorialIdempotent (0 : S) = 0 :=
  IsIdempotentElem.zero.factorialIdempotent_eq

/-- The factorial idempotent of `1` is `1`. -/
@[simp]
theorem factorialIdempotent_one [IsHausdorff I S] : I.factorialIdempotent (1 : S) = 1 :=
  IsIdempotentElem.one.factorialIdempotent_eq

/-- The factorial idempotent is a fixed point: the factorial idempotent of a factorial idempotent
is itself. -/
@[simp]
theorem factorialIdempotent_factorialIdempotent [∀ k, Finite (S ⧸ (I ^ k • ⊤ : Submodule R S))]
    [IsAdicComplete I S] (t : S) :
    I.factorialIdempotent (I.factorialIdempotent t) = I.factorialIdempotent t :=
  (isIdempotentElem_factorialIdempotent t).factorialIdempotent_eq

/-- **Topologically nilpotent elements have factorial idempotent `0`.** If for every `k` some
power of `t` lies in `I ^ k • S`, then the factorial idempotent of `t` is `0`. -/
theorem factorialIdempotent_eq_zero_of_forall_exists_pow_mem [IsHausdorff I S] {t : S}
    (h : ∀ k, ∃ n, t ^ n ∈ I ^ k • (⊤ : Submodule R S)) : I.factorialIdempotent t = 0 := by
  refine factorialIdempotent_eq_of_eventually_sub_mem fun k ↦ ?_
  obtain ⟨n, hn⟩ := h k
  refine (eventually_ge_atTop n).mono fun m hm ↦ ?_
  rw [sub_zero, ← Nat.sub_add_cancel ((Nat.self_le_factorial m).trans' hm), pow_add,
    ← mem_map_algebraMap_iff]
  exact mul_mem_left _ _ ((mem_map_algebraMap_iff _).mpr hn)

/-- The factorial idempotent of a nilpotent element is `0`. -/
theorem factorialIdempotent_eq_zero_of_isNilpotent [IsHausdorff I S] {t : S}
    (ht : IsNilpotent t) : I.factorialIdempotent t = 0 := by
  obtain ⟨n, hn⟩ := ht
  exact factorialIdempotent_eq_zero_of_forall_exists_pow_mem fun _ ↦ ⟨n, by simp [hn]⟩

/-- **Naturality of the factorial idempotent.** An algebra homomorphism out of an `I`-adically
precomplete algebra with finite quotients `S ⧸ I ^ k • S`, into an `I`-adically separated
algebra, carries the factorial idempotent of `t` to that of its image. -/
theorem _root_.AlgHom.map_factorialIdempotent {S' : Type*} [Ring S'] [Algebra R S']
    [∀ k, Finite (S ⧸ (I ^ k • ⊤ : Submodule R S))] [IsPrecomplete I S] [IsHausdorff I S']
    (f : S →ₐ[R] S') (t : S) : f (I.factorialIdempotent t) = I.factorialIdempotent (f t) := by
  refine (factorialIdempotent_eq_of_eventually_sub_mem fun k ↦ ?_).symm
  filter_upwards [eventually_pow_factorial_sub_factorialIdempotent_mem (I := I) t k] with n hn
  have := Submodule.smul_top_le_comap_smul_top (I ^ k) f.toLinearMap hn
  rwa [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_sub, map_pow] at this

/-- **The factorial idempotent lies in `R[t]`.** For a finite algebra over an `I`-adically
complete noetherian ring with finite quotient `R ⧸ I`, the factorial idempotent of `t` lies in the
subalgebra generated by `t`. -/
theorem factorialIdempotent_mem_adjoin [IsNoetherianRing R] [IsAdicComplete I R]
    [Finite (R ⧸ I)] [Module.Finite R S] (t : S) :
    I.factorialIdempotent t ∈ Algebra.adjoin R {t} := by
  -- Compute the factorial idempotent inside `R[t]`, which is again finite over `R`, hence
  -- complete, and transport it along the inclusion.
  have (k : ℕ) : Finite (R ⧸ I ^ k) := finite_quotient_pow (IsNoetherian.noetherian I) k
  let B := Algebra.adjoin R {t}
  have : Module.Finite R B := Module.Finite.of_injective B.val.toLinearMap Subtype.val_injective
  have : IsAdicComplete I S := IsAdicComplete.of_finite I S
  have : IsAdicComplete I B := IsAdicComplete.of_finite I B
  have h := B.val.map_factorialIdempotent (I := I) ⟨t, Algebra.self_mem_adjoin_singleton R t⟩
  rw [Subalgebra.coe_val] at h
  rw [← h]
  exact (I.factorialIdempotent (S := B) _).property

open Classical in
/-- **The factorial idempotent modulo a prime ideal.** Let `S` be commutative, `I`-adically
precomplete with finite quotients `S ⧸ I ^ k • S`, and let `𝔪` be a prime ideal of `S`
containing the extension of `I`. Modulo `𝔪`, the factorial idempotent of `t` is `0` if `t ∈ 𝔪`
and `1` otherwise.

For a finite algebra over a local ring, every maximal ideal contains the extension of the
maximal ideal (`TauCeti.IsLocalRing.map_maximalIdeal_le_of_isMaximal`). -/
theorem Quotient.mk_factorialIdempotent {S : Type*} [CommRing S] [Algebra R S]
    [∀ k, Finite (S ⧸ (I ^ k • ⊤ : Submodule R S))] [IsPrecomplete I S] (𝔪 : Ideal S)
    [𝔪.IsPrime] (hI : I.map (algebraMap R S) ≤ 𝔪) (t : S) :
    Quotient.mk 𝔪 (I.factorialIdempotent t) = if t ∈ 𝔪 then 0 else 1 := by
  set n := Nat.card (S ⧸ (I ^ 1 • ⊤ : Submodule R S))
  have hI' : (I ^ 1).map (algebraMap R S) ≤ 𝔪 := by rwa [pow_one]
  -- Modulo `𝔪`, the factorial idempotent is the factorial power `t ^ n !`.
  have hmod : Quotient.mk 𝔪 (I.factorialIdempotent t) = Quotient.mk 𝔪 t ^ n ! := by
    rw [← map_pow, Quotient.eq]
    exact hI' (factorialIdempotent_sub_pow_factorial_mem_map t 1)
  split_ifs with ht
  · rw [hmod, Quotient.eq_zero_iff_mem.mpr ht, zero_pow (Nat.factorial_ne_zero n)]
  -- Otherwise the class of `t ^ n !` is a nonzero idempotent of the domain `S ⧸ 𝔪`.
  have hidem : IsIdempotentElem (Quotient.mk 𝔪 t ^ n !) := by
    rw [isIdempotentElem_iff, ← map_pow, ← map_mul, Quotient.eq]
    exact hI' ((mem_map_algebraMap_iff _).mpr (pow_factorial_mul_self_sub_mem t le_rfl))
  have hne : Quotient.mk 𝔪 t ^ n ! ≠ 0 :=
    pow_ne_zero _ (by rwa [Ne, Quotient.eq_zero_iff_mem])
  rw [hmod]
  exact hidem.eq_zero_or_one.resolve_left hne

end Ideal
