/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Teichmuller
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

import Mathlib.LinearAlgebra.SModEq.Pow
import TauCeti.Algebra.CharP.Quotient
import TauCeti.RingTheory.AdicCompletion.Pow
import TauCeti.RingTheory.Ideal.Quotient.Frobenius
import TauCeti.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.RingTheory.Perfect.Basic

/-!
# Ring homomorphisms out of the Witt vectors of a perfect ring

Let `k` be a perfect ring of characteristic `p`, and let `A` be a commutative ring which is
`I`-adically complete for an ideal `I` containing `p`. Every ring homomorphism `φ : k →+* A ⧸ I`
lifts to a unique ring homomorphism `TauCeti.WittVector.adicLift I φ : 𝕎 k →+* A` whose reduction
modulo `I` is `φ` applied to the `0`-th Witt coordinate. Thus ring homomorphisms `𝕎 k →+* A`
correspond to ring homomorphisms `k →+* A ⧸ I` (`TauCeti.WittVector.adicLiftEquiv`).

In particular, if `π : A →+* k` is surjective and `A` is complete for the ideal `ker π`, for
instance a complete local ring with residue field `k`, then there is exactly one ring homomorphism
`𝕎 k →+* A` over `k` (`TauCeti.WittVector.existsUnique_comp_eq_constantCoeff`). This is the
canonical `𝕎 k`-algebra structure on such a ring, used for instance to compare deformations over
complete local rings with residue field `k` with maps out of power series rings over `𝕎 k`.

The construction follows that of Fontaine's map in `Mathlib.RingTheory.Perfectoid.FontaineTheta`,
which is the case of the ideal `(p)`. If `p ∈ I` and the Witt coordinates of `x : 𝕎 A` lie in `I`,
then its `n`-th ghost component lies in `I ^ (n + 1)`
(`TauCeti.WittVector.ghostComponent_mem_pow_of_coeff_mem`). Hence the `n`-th ghost component,
reduced modulo `I ^ (n + 1)`, descends to
`TauCeti.WittVector.ghostComponentModPow I hpI n : 𝕎 (A ⧸ I) →+* A ⧸ I ^ (n + 1)`. Precomposing with
`𝕎` of `φ` and of the inverse of the `n`-th power of Frobenius on `k` gives compatible ring
homomorphisms `𝕎 k →+* A ⧸ I ^ (n + 1)`, whose limit is `adicLift I φ`. On a Teichmüller
representative `[x]` it is the limit of the powers `aₙ ^ p ^ n` of lifts `aₙ` of
`φ (x ^ (1 / p ^ n))` (`TauCeti.WittVector.adicLift_teichmuller_sModEq`), that is, Mathlib's
multiplicative Teichmüller map `Perfection.teichmuller₀`
(`TauCeti.WittVector.adicLift_teichmuller`).

The ideal `I` may be enlarged to an ideal `J ⊇ I` with `x ^ p ∈ I` for every `x ∈ J`: ring maps
`k →+* A ⧸ I` correspond to ring maps `k →+* A ⧸ J`, since Frobenius factors through
`A ⧸ I → A ⧸ J` (`Ideal.bijective_factor_comp_ringHom`). So every ring homomorphism
`k →+* A ⧸ J` still has exactly one lift `𝕎 k →+* A`
(`TauCeti.WittVector.existsUnique_mk_comp_eq_comp_constantCoeff`). Here `p ∈ I` is not needed:
`p ∈ J`, so `p ^ p ∈ I`, and `A` is also complete along `I ⊔ (p)` (`IsAdicComplete.sup_of_pow_le`).
For `I = (p)`, an example of such a `J` is the ideal of elements with divided powers.

Uniqueness holds under the weaker hypothesis that `A` is `I`-adically Hausdorff: two ring
homomorphisms `𝕎 k →+* A` which agree modulo `I` agree on `[x] = [x ^ (1 / p ^ n)] ^ p ^ n` modulo
`I ^ (n + 1)`, and Teichmüller expansions then show that they agree modulo `I ^ (n + 1)` everywhere
(`TauCeti.WittVector.eq_of_mk_comp_eq`).

## Main definitions

* `TauCeti.WittVector.ghostComponentModPow I hpI n`: the `n`-th ghost component `𝕎 (A ⧸ I) →+*
  A ⧸ I ^ (n + 1)`, for `p ∈ I`.
* `TauCeti.WittVector.adicLift I φ`: the lift `𝕎 k →+* A` of `φ : k →+* A ⧸ I`.
* `TauCeti.WittVector.adicLiftEquiv I hpI`: the bijection `(k →+* A ⧸ I) ≃ (𝕎 k →+* A)`.

## Main results

* `TauCeti.WittVector.mk_comp_adicLift`: `adicLift I φ` reduces to `φ ∘ constantCoeff` modulo `I`.
* `TauCeti.WittVector.eq_adicLift`: it is the only ring homomorphism with this property.
* `TauCeti.WittVector.eq_of_mk_comp_eq`: ring homomorphisms `𝕎 k →+* A` to an `I`-adically
  Hausdorff ring are determined by their reductions modulo `I`.
* `TauCeti.WittVector.comp_adicLift`, `TauCeti.WittVector.adicLift_comp_map`: naturality in `A`
  and in `k`.
* `TauCeti.WittVector.existsUnique_mk_comp_eq_comp_constantCoeff`: existence and uniqueness of a
  lift `𝕎 k →+* A` of a ring homomorphism `k →+* A ⧸ J`, for `J ⊇ I` with `x ^ p ∈ I` for `x ∈ J`.
* `TauCeti.WittVector.existsUnique_comp_eq_constantCoeff`: existence and uniqueness of a ring
  homomorphism `𝕎 k →+* A` over `k`, for `A` complete along the kernel of `π : A →+* k`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter II,
  §§4–5 (multiplicative representatives, and Proposition 10 on lifting homomorphisms of residue
  rings to `p`-rings).
-/

public section

noncomputable section

namespace TauCeti.WittVector

open _root_.WittVector

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] {I : Ideal A}

local notation "𝕎" => WittVector p

/-! ### Ghost components modulo powers of an ideal containing `p` -/

/-- If `p ∈ I` and the first `n + 1` Witt coordinates of `x` lie in `I`, then the `n`-th ghost
component `∑_{i ≤ n} pⁱ xᵢ ^ p ^ (n - i)` of `x` lies in `I ^ (n + 1)`. -/
theorem ghostComponent_mem_pow_of_coeff_mem (hpI : (p : A) ∈ I) {x : 𝕎 A} {n : ℕ}
    (hx : ∀ i ≤ n, x.coeff i ∈ I) : ghostComponent n x ∈ I ^ (n + 1) := by
  rw [ghostComponent_apply, wittPolynomial, MvPolynomial.aeval_sum]
  refine Ideal.sum_mem _ fun i hi ↦ ?_
  have hi : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [MvPolynomial.aeval_monomial, map_pow, map_natCast, Finsupp.prod_single_index,
    pow_zero]
  rw [show n + 1 = i + (n - i + 1) by omega, pow_add]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hpI i) <|
    Ideal.pow_le_pow_right (Nat.lt_pow_self hp.out.one_lt) (Ideal.pow_mem_pow (hx i hi) _)

variable (I) in
/-- For `p ∈ I`, the `n`-th ghost component `𝕎 A →+* A`, reduced modulo `I ^ (n + 1)`, factors
through the coordinatewise reduction `𝕎 A →+* 𝕎 (A ⧸ I)`. For `I = (p)` this is Mathlib's
`WittVector.ghostComponentModPPow`. -/
def ghostComponentModPow (hpI : (p : A) ∈ I) (n : ℕ) : 𝕎 (A ⧸ I) →+* A ⧸ I ^ (n + 1) :=
  RingHom.liftOfSurjective (map (Ideal.Quotient.mk I))
    (map_surjective _ Ideal.Quotient.mk_surjective)
    ⟨(Ideal.Quotient.mk (I ^ (n + 1))).comp (ghostComponent n), fun x hx ↦ by
      refine RingHom.mem_ker.mpr <| Ideal.Quotient.eq_zero_iff_mem.mpr <|
        ghostComponent_mem_pow_of_coeff_mem hpI fun i _ ↦ ?_
      have h := congrArg (fun y : 𝕎 (A ⧸ I) ↦ y.coeff i) (RingHom.mem_ker.mp hx)
      simp only [map_coeff, zero_coeff] at h
      exact Ideal.Quotient.eq_zero_iff_mem.mp h⟩

@[simp]
theorem ghostComponentModPow_map_mk (hpI : (p : A) ∈ I) (n : ℕ) (x : 𝕎 A) :
    ghostComponentModPow I hpI n (map (Ideal.Quotient.mk I) x) =
      Ideal.Quotient.mk (I ^ (n + 1)) (ghostComponent n x) :=
  RingHom.liftOfSurjective_comp_apply ..

@[simp]
theorem ghostComponentModPow_teichmuller_mk (hpI : (p : A) ∈ I) (n : ℕ) (a : A) :
    ghostComponentModPow I hpI n (teichmuller p (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ^ (n + 1)) (a ^ p ^ n) := by
  rw [← map_teichmuller, ghostComponentModPow_map_mk, ghostComponent_teichmuller]

/-! ### The lift of a homomorphism out of a perfect ring -/

variable {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]

variable (I) in
/-- The reduction of `adicLift I φ` modulo `I ^ (n + 1)`: the composite of `𝕎` of `φ` after the
inverse of the `n`-th power of Frobenius with `ghostComponentModPow I _ n`. -/
private def adicLiftModPow (φ : k →+* A ⧸ I) (n : ℕ) : 𝕎 k →+* A ⧸ I ^ (n + 1) :=
  (ghostComponentModPow I (Ideal.natCast_mem_of_ringHom_charP p φ) n).comp
    (map (φ.comp (iterateFrobeniusEquiv k p n).symm.toRingHom))

private theorem adicLiftModPow_teichmuller (φ : k →+* A ⧸ I) (n : ℕ) (x : k) {a : A}
    (ha : Ideal.Quotient.mk I a = φ ((iterateFrobeniusEquiv k p n).symm x)) :
    adicLiftModPow I φ n (teichmuller p x) = Ideal.Quotient.mk (I ^ (n + 1)) (a ^ p ^ n) := by
  rw [adicLiftModPow, RingHom.comp_apply, map_teichmuller, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← ha, ghostComponentModPow_teichmuller_mk]

private theorem factorPowSucc_comp_adicLiftModPow (φ : k →+* A ⧸ I) (n : ℕ) :
    (Ideal.Quotient.factorPowSucc I (n + 1)).comp (adicLiftModPow I φ (n + 1)) =
      adicLiftModPow I φ n := by
  refine eq_of_apply_teichmuller_eq _ _ (map_natCast (Ideal.Quotient.mk (I ^ (n + 1))) p ▸
    Ideal.Quotient.isNilpotent_mk_pow_of_mem (Ideal.natCast_mem_of_ringHom_charP p φ) (n + 1))
    fun x ↦ ?_
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (φ ((iterateFrobeniusEquiv k p (n + 1)).symm x))
  have ha' : Ideal.Quotient.mk I (a ^ p) = φ ((iterateFrobeniusEquiv k p n).symm x) := by
    rw [map_pow, ha, ← map_pow, TauCeti.iterateFrobeniusEquiv_symm_succ_pow]
  rw [RingHom.comp_apply, adicLiftModPow_teichmuller φ (n + 1) x ha,
    adicLiftModPow_teichmuller φ n x ha', ← pow_mul, ← pow_succ', Ideal.Quotient.factor_mk]

open IsAdicComplete

variable (I) [IsAdicComplete I A]

/-- The lift `𝕎 k →+* A` of a ring homomorphism `φ : k →+* A ⧸ I`, for a perfect ring `k` of
characteristic `p` and an `I`-adically complete ring `A`. It is the unique ring homomorphism
whose reduction modulo `I` is `φ` applied to the `0`-th Witt coordinate (`mk_comp_adicLift` and
`eq_adicLift`). -/
def adicLift (φ : k →+* A ⧸ I) : 𝕎 k →+* A :=
  Order.succ_strictMono.liftRingHom I _ (factorPowSucc_comp_adicLiftModPow φ _)

variable {I}

private theorem mk_pow_adicLift (φ : k →+* A ⧸ I) (n : ℕ) (x : 𝕎 k) :
    Ideal.Quotient.mk (I ^ (n + 1)) (adicLift I φ x) = adicLiftModPow I φ n x :=
  Order.succ_strictMono.mk_liftRingHom I _ (factorPowSucc_comp_adicLiftModPow φ _) x

/-- On a Teichmüller representative `[x]`, `adicLift I φ` is congruent modulo `I ^ (n + 1)` to
`a ^ p ^ n` for every lift `a` of `φ (x ^ (1 / p ^ n))`. -/
theorem adicLift_teichmuller_sModEq (φ : k →+* A ⧸ I) {n : ℕ} {x : k} {a : A}
    (ha : Ideal.Quotient.mk I a = φ ((iterateFrobeniusEquiv k p n).symm x)) :
    adicLift I φ (teichmuller p x) ≡ a ^ p ^ n [SMOD I ^ (n + 1)] := by
  rw [SModEq.idealQuotientMk, mk_pow_adicLift, adicLiftModPow_teichmuller φ n x ha]

/-- `adicLift I φ` reduces modulo `I` to `φ` applied to the `0`-th Witt coordinate. -/
@[simp]
theorem mk_adicLift (φ : k →+* A ⧸ I) (x : 𝕎 k) :
    Ideal.Quotient.mk I (adicLift I φ x) = φ (x.coeff 0) := by
  suffices (Ideal.Quotient.mk I).comp (adicLift I φ) = φ.comp constantCoeff from
    congr($this x)
  have hp0 : (p : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.natCast_mem_of_ringHom_charP p φ
  refine eq_of_apply_teichmuller_eq _ _ ⟨1, by rw [pow_one, hp0]⟩ fun y ↦ ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ y)
  have h := adicLift_teichmuller_sModEq φ (n := 0) (x := y) (a := a)
    (by rw [ha, iterateFrobeniusEquiv_zero, RingEquiv.symm_refl, RingEquiv.refl_apply])
  rw [zero_add, pow_one, pow_zero, pow_one, SModEq.idealQuotientMk] at h
  simp [h, ha]

/-- The reduction of `adicLift I φ` modulo `I` is `φ.comp constantCoeff`; this is the bundled form
of `mk_adicLift`. -/
theorem mk_comp_adicLift (φ : k →+* A ⧸ I) :
    (Ideal.Quotient.mk I).comp (adicLift I φ) = φ.comp constantCoeff :=
  RingHom.ext (mk_adicLift φ)

omit [IsAdicComplete I A] in
/-- Two ring homomorphisms from `𝕎 k` to an `I`-adically Hausdorff ring, with `p ∈ I`, are
equal as soon as they agree modulo `I`. -/
theorem eq_of_mk_comp_eq [IsHausdorff I A] (hpI : (p : A) ∈ I) {f g : 𝕎 k →+* A}
    (h : (Ideal.Quotient.mk I).comp f = (Ideal.Quotient.mk I).comp g) : f = g := by
  ext x
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n ↦ ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.idealQuotientMk]
  suffices (Ideal.Quotient.mk (I ^ n)).comp f = (Ideal.Quotient.mk (I ^ n)).comp g from
    congr($this x)
  refine eq_of_apply_teichmuller_eq _ _
    (map_natCast (Ideal.Quotient.mk (I ^ n)) p ▸ Ideal.Quotient.isNilpotent_mk_pow_of_mem hpI n)
    fun x ↦ ?_
  -- `[x] = [y] ^ p ^ n` for the `p ^ n`-th root `y` of `x`, and `f [y] ≡ g [y]` modulo `I`.
  set y := (iterateFrobeniusEquiv k p n).symm x
  have hx : teichmuller p x = teichmuller p y ^ p ^ n := by
    rw [← map_pow, ← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  have hy : f (teichmuller p y) ≡ g (teichmuller p y) [SMOD I] := by
    rw [SModEq.idealQuotientMk]
    exact congr($h (teichmuller p y))
  have := SModEq.mono (Ideal.pow_le_pow_right n.le_succ) (SModEq.pow_pow_add_one hpI hy n)
  rw [SModEq.idealQuotientMk] at this
  simpa [hx] using this

/-- `adicLift I φ` is the only ring homomorphism `𝕎 k →+* A` whose reduction modulo `I` is `φ`
applied to the `0`-th Witt coordinate. -/
theorem eq_adicLift (φ : k →+* A ⧸ I) {f : 𝕎 k →+* A}
    (hf : (Ideal.Quotient.mk I).comp f = φ.comp constantCoeff) : f = adicLift I φ :=
  eq_of_mk_comp_eq (Ideal.natCast_mem_of_ringHom_charP p φ) (hf.trans (mk_comp_adicLift φ).symm)

/-- `adicLift I φ` sends a Teichmüller representative `[x]` to Mathlib's multiplicative
Teichmüller lift of `Perfection.lift p k (A ⧸ I) φ x`, the element of `Perfection (A ⧸ I) p` whose
`n`-th coordinate is `φ (x ^ (1 / p ^ n))`. -/
theorem adicLift_teichmuller [CharP (A ⧸ I) p] (φ : k →+* A ⧸ I) (x : k) :
    adicLift I φ (teichmuller p x) =
      Perfection.teichmuller₀ p I (Perfection.lift p k (A ⧸ I) φ x) := by
  refine (Perfection.teichmuller₀_spec fun n ↦ ?_).symm
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ ((iterateFrobeniusEquiv k p n).symm x))
  exact ⟨a, by rw [ha, Perfection.coeff_lift_apply], (adicLift_teichmuller_sModEq φ ha).symm⟩

omit [IsAdicComplete I A] in
/-- The reduction modulo `I` of a ring homomorphism `f : 𝕎 k →+* A`, which factors through the
`0`-th Witt coordinate since its kernel is `(p)`. -/
private def residueHom (hpI : (p : A) ∈ I) (f : 𝕎 k →+* A) : k →+* A ⧸ I :=
  RingHom.liftOfSurjective constantCoeff (constantCoeff_surjective p)
    ⟨(Ideal.Quotient.mk I).comp f, fun x hx ↦ by
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp <|
        (mem_span_p_iff_coeff_zero_eq_zero x).mpr (RingHom.mem_ker.mp hx)
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr hpI, mul_zero]⟩

omit [IsAdicComplete I A] in
private theorem residueHom_comp_constantCoeff (hpI : (p : A) ∈ I) (f : 𝕎 k →+* A) :
    (residueHom hpI f).comp constantCoeff = (Ideal.Quotient.mk I).comp f :=
  RingHom.liftOfSurjective_comp ..

omit [IsAdicComplete I A] in
private theorem residueHom_apply (hpI : (p : A) ∈ I) (f : 𝕎 k →+* A) (x : k) :
    residueHom hpI f x = Ideal.Quotient.mk I (f (teichmuller p x)) := by
  have hx : constantCoeff (teichmuller p x) = x := by
    rw [constantCoeff_apply, teichmuller_coeff_zero]
  rw [← RingHom.comp_apply, ← residueHom_comp_constantCoeff hpI f, RingHom.comp_apply, hx]

variable (I) in
/-- **The universal property of `𝕎 k`**: for a perfect ring `k` of characteristic `p` and an
`I`-adically complete ring `A` with `p ∈ I`, ring homomorphisms `𝕎 k →+* A` correspond to ring
homomorphisms `k →+* A ⧸ I`. The inverse sends `f` to `x ↦ f [x]` modulo `I`
(`adicLiftEquiv_symm_apply`). -/
def adicLiftEquiv (hpI : (p : A) ∈ I) : (k →+* A ⧸ I) ≃ (𝕎 k →+* A) where
  toFun := adicLift I
  invFun := residueHom hpI
  left_inv φ := RingHom.ext fun x ↦ by rw [residueHom_apply, mk_adicLift, teichmuller_coeff_zero]
  right_inv f := (eq_adicLift _ (residueHom_comp_constantCoeff hpI f).symm).symm

@[simp]
theorem adicLiftEquiv_apply (hpI : (p : A) ∈ I) (φ : k →+* A ⧸ I) :
    adicLiftEquiv I hpI φ = adicLift I φ :=
  (rfl)

@[simp]
theorem adicLiftEquiv_symm_apply (hpI : (p : A) ∈ I) (f : 𝕎 k →+* A) (x : k) :
    (adicLiftEquiv I hpI).symm f x = Ideal.Quotient.mk I (f (teichmuller p x)) :=
  residueHom_apply hpI f x

/-- `adicLift` is natural in the complete ring: a ring homomorphism `g : A →+* B` with
`g (I) ⊆ J` carries `adicLift I φ` to the lift along `J` of `φ` followed by the map
`A ⧸ I →+* B ⧸ J` induced by `g`. -/
theorem comp_adicLift {B : Type*} [CommRing B] (J : Ideal B) [IsAdicComplete J B]
    (g : A →+* B) (hg : I ≤ J.comap g) (φ : k →+* A ⧸ I) :
    g.comp (adicLift I φ) = adicLift J ((Ideal.quotientMap J g hg).comp φ) := by
  refine eq_adicLift _ ?_
  rw [← RingHom.comp_assoc, ← Ideal.quotientMap_comp_mk hg, RingHom.comp_assoc,
    mk_comp_adicLift, RingHom.comp_assoc]

/-- `adicLift` is natural in the perfect ring: precomposing `adicLift I φ` with `𝕎 ψ` gives the
lift of `φ ∘ ψ`. -/
theorem adicLift_comp_map {k' : Type*} [CommRing k'] [CharP k' p] [PerfectRing k' p]
    (ψ : k' →+* k) (φ : k →+* A ⧸ I) :
    (adicLift I φ).comp (map ψ) = adicLift I (φ.comp ψ) := by
  refine eq_adicLift _ (RingHom.ext fun x ↦ ?_)
  simp [map_coeff]

/-- The case `p ∈ I` of `existsUnique_mk_comp_eq_comp_constantCoeff`. -/
private theorem existsUnique_mk_comp_eq_comp_constantCoeff_of_mem (hpI : (p : A) ∈ I)
    {J : Ideal A} (hIJ : I ≤ J) (hJ : ∀ x ∈ J, x ^ p ∈ I) (φ : k →+* A ⧸ J) :
    ∃! g : 𝕎 k →+* A, (Ideal.Quotient.mk J).comp g = φ.comp constantCoeff := by
  have hbij := Ideal.bijective_factor_comp_ringHom (k := k) hpI hJ hIJ
  obtain ⟨ψ, hψ : (Ideal.Quotient.factor hIJ).comp ψ = φ⟩ := hbij.2 φ
  refine ⟨adicLift I ψ, ?_, fun g hg ↦ ?_⟩
  · beta_reduce
    rw [← Ideal.Quotient.factor_comp_mk hIJ, RingHom.comp_assoc, mk_comp_adicLift,
      ← RingHom.comp_assoc, hψ]
  -- The reductions of `g` and of `adicLift I ψ` modulo `I` both lift `φ` along `A ⧸ I → A ⧸ J`.
  rw [← (adicLiftEquiv I hpI).apply_symm_apply g, adicLiftEquiv_apply]
  congr 1
  refine hbij.1 ?_
  beta_reduce
  rw [hψ]
  ext x
  have hx := congr($hg (teichmuller p x))
  simp only [RingHom.comp_apply, constantCoeff_apply, teichmuller_coeff_zero] at hx
  simp [hx]

/-- **Lifting modulo an ideal killed by Frobenius.** Let `A` be `I`-adically complete, and let
`J ⊇ I` be an ideal with `x ^ p ∈ I` for every `x ∈ J`. For a perfect ring `k` of characteristic
`p`, every ring homomorphism `φ : k →+* A ⧸ J` has exactly one lift `g : 𝕎 k →+* A` whose reduction
modulo `J` is `φ` applied to the `0`-th Witt coordinate. For `J = I` the lift is `adicLift I φ`. -/
theorem existsUnique_mk_comp_eq_comp_constantCoeff {J : Ideal A} (hIJ : I ≤ J)
    (hJ : ∀ x ∈ J, x ^ p ∈ I) (φ : k →+* A ⧸ J) :
    ∃! g : 𝕎 k →+* A, (Ideal.Quotient.mk J).comp g = φ.comp constantCoeff := by
  -- `p ∈ J` because `k` has characteristic `p`, so `p ^ p ∈ I`, and `A` is also complete along
  -- `I ⊔ (p)`, which contains `p`.
  have hpJ : (p : A) ∈ J := Ideal.natCast_mem_of_ringHom_charP p φ
  have : IsAdicComplete (I ⊔ Ideal.span {(p : A)}) A := .sup_of_pow_le (k := p) <| by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hJ _ hpJ
  exact existsUnique_mk_comp_eq_comp_constantCoeff_of_mem
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (sup_le hIJ ((Ideal.span_singleton_le_iff_mem _).mpr hpJ))
    (fun x hx ↦ Ideal.mem_sup_left (hJ x hx)) φ

/-- **The `𝕎 k`-algebra structure over `k`**: if `π : A →+* k` is surjective and `A` is complete
for the ideal `ker π` (for instance, a complete local ring with residue field `k` and residue map
`π`), there is exactly one ring homomorphism `𝕎 k →+* A` lifting the reduction `𝕎 k →+* k`
through `π`. -/
theorem existsUnique_comp_eq_constantCoeff {π : A →+* k} (hπ : Function.Surjective π)
    [IsAdicComplete (RingHom.ker π) A] :
    ∃! f : 𝕎 k →+* A, π.comp f = constantCoeff := by
  set e := RingHom.quotientKerEquivOfSurjective hπ
  have he (a : A) : e (Ideal.Quotient.mk (RingHom.ker π) a) = π a :=
    RingHom.quotientKerEquivOfSurjective_apply_mk hπ a
  refine ⟨adicLift (RingHom.ker π) e.symm.toRingHom, ?_, fun f hf ↦ eq_adicLift _ ?_⟩
  · ext x
    rw [RingHom.comp_apply, ← he, mk_adicLift]
    simp
  · ext x
    apply e.injective
    rw [RingHom.comp_apply, he, ← RingHom.comp_apply π, hf]
    simp

end TauCeti.WittVector
