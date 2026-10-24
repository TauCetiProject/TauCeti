/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Tensor
import TauCeti.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.TensorProduct.IdealSMul

/-!
# The local criterion for flatness along a regular element

Let `R` be a Noetherian ring, `S` a Noetherian `R`-algebra, `M` a finite `S`-module and `x ∈ R` an
element whose image in `S` lies in the Jacobson radical. If `x` is a nonzerodivisor on `M` and
`M ⧸ x M` is flat over `R ⧸ (x)`, then `M` is flat over `R` (`Module.Flat.of_flat_quotSMulTop`).
This is the case `I = (x)` of the variant of the local criterion for flatness (Stacks, Lemma
10.99.10 (00ML)) together with the remark following it: for a principal ideal, regularity of `x`
on `M` implies the vanishing of `Tor₁ᴿ(M, R ⧸ (x))`, and the two are equivalent when `x` is also
`R`-regular. No regularity of `x` on `R` is needed for the criterion. Conversely,
`M ⧸ x M` is flat over `R ⧸ (x)` whenever `M` is flat over `R`, so for an `M`-regular `x` the two
conditions are equivalent (`Module.flat_quotSMulTop_iff_flat`), the flat counterpart of Mathlib's
`Module.free_quotSMulTop_iff_free`.

For a local homomorphism `R → S` of Noetherian local rings and `x` in the maximal ideal of `R`, the
Jacobson hypothesis is automatic (`Module.Flat.of_flat_quotSMulTop_of_isLocalHom`). This is the
inductive step of miracle flatness (Stacks, Lemma 10.128.1 (00R4)): there `R` is regular,
`x ∈ 𝔪_R ∖ 𝔪_R²` is a nonzerodivisor on the Cohen–Macaulay ring `S`, and `S ⧸ x S` is flat over the
regular local ring `R ⧸ (x)` by induction on the dimension.

## Implementation notes

By Mathlib's ideal criterion it suffices that `M ⊗[R] J → M` is injective for every ideal `J`. Let
`t` be in its kernel.

1. Write `t = ∑ mᵢ ⊗ jᵢ`, so `∑ jᵢ mᵢ = 0`. The equational criterion for the flat
   `R ⧸ (x)`-module `M ⧸ x M` gives `aᵢₖ ∈ R` and `yₖ ∈ M` with `mᵢ ≡ ∑ₖ aᵢₖ yₖ` modulo `x M`
   and `∑ᵢ jᵢ aᵢₖ = x cₖ`. Then `cₖ ∈ (J : x)` and `t` is the image of an element `s` of
   `M ⊗[R] (J : x)` under multiplication by `x`; regularity of `x` on `M` puts `s` in the kernel
   of `M ⊗[R] (J : x) → M`.
2. Iterating, `t` comes from `M ⊗[R] (J ⊓ (x) ^ n)` for every `n`. This needs no Noetherian
   hypothesis.
3. By the Artin–Rees lemma `J ⊓ (x) ^ n ⊆ (x) ^ (n - c) J`, so `t ∈ x ^ (n - c) (M ⊗[R] J)` for
   all `n`. Since `M ⊗[R] J` is a finite `S`-module (`Module.Finite.tensor`), Krull's
   intersection theorem over `S` gives `t = 0`.

This replaces the `Tor` computations of the Stacks proof by the equational criterion and avoids
the general local criterion (Stacks, Lemma 10.99.7 (00MK)).

## Main results

* `Module.Flat.of_flat_quotSMulTop`: the criterion above.
* `Module.Flat.of_flat_quotSMulTop_of_isLocalHom`: the same for a local homomorphism of
  Noetherian local rings and `x` in the maximal ideal.
* `Module.Flat.quotSMulTop`: `M ⧸ x M` is flat over `R ⧸ (x)` when `M` is flat over `R`.
* `Module.flat_quotSMulTop_iff_flat`: for an `M`-regular `x` as above, `M ⧸ x M` is flat over
  `R ⧸ (x)` if and only if `M` is flat over `R`.

## References

* [The Stacks Project, Lemma 10.99.10](https://stacks.math.columbia.edu/tag/00ML) and the remark
  following it.
* [The Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4), whose proof
  uses this criterion.
* H. Matsumura, *Commutative Ring Theory*, Theorem 22.3.
-/

public section

open TensorProduct LinearMap

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `M` is flat over `R`, then `M ⧸ x M` is flat over `R ⧸ (x)`. -/
instance Flat.quotSMulTop [Flat R M] (x : R) : Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  .of_linearEquiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective)

variable {x : R}

open scoped Pointwise

/-- Multiplication by `x`, from an ideal `P` to an ideal `Q` with `x P ⊆ Q`. -/
private noncomputable def mulRestrict (x : R) {P Q : Ideal R} (h : ∀ c ∈ P, x * c ∈ Q) :
    P →ₗ[R] Q :=
  (mulLeft R x).restrict h

@[simp]
private theorem coe_mulRestrict_apply (x : R) {P Q : Ideal R} (h : ∀ c ∈ P, x * c ∈ Q) (c : P) :
    (mulRestrict x h c : R) = x * c := rfl

/-- Multiplication by `x`, from the colon ideal `(J : x)` to `J`. -/
private noncomputable def mulColon (J : Ideal R) (x : R) : J.colon {x} →ₗ[R] J :=
  mulRestrict x fun c hc ↦ by simpa [mul_comm] using Submodule.mem_colon_singleton.mp hc

@[simp]
private theorem coe_mulColon_apply (J : Ideal R) (x : R) (c : J.colon {x}) :
    (mulColon J x c : R) = x * c := rfl

/-- The `R ⧸ (x)`-action on `M ⧸ x M` is induced by the `R`-action on `M`. -/
@[simp]
private theorem quotient_mk_smul_mk (r : R) (m : M) :
    Ideal.Quotient.mk (Ideal.span {x}) r • (Submodule.Quotient.mk m : QuotSMulTop x M) =
      Submodule.Quotient.mk (r • m) := by
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, Submodule.Quotient.mk_smul]

/-- One step of the descent: an element of the kernel of `M ⊗[R] J → M` is `x` times an element
of the kernel of `M ⊗[R] (J : x) → M`. -/
private theorem exists_lTensor_mulColon_eq (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] {J : Ideal R} {t : M ⊗[R] J}
    (ht : J.subtype.lTensor M t = 0) :
    ∃ s : M ⊗[R] J.colon {x}, (mulColon J x).lTensor M s = t ∧
      (J.colon {x}).subtype.lTensor M s = 0 := by
  classical
  obtain ⟨T, rfl⟩ := TensorProduct.exists_finset t
  have h0 : ∑ i ∈ T, (i.2 : R) • i.1 = 0 := by
    simpa using congr(TensorProduct.rid R M $ht)
  -- The relation `∑ jᵢ mᵢ = 0` holds modulo `x`; apply the equational criterion over `R ⧸ (x)`.
  have h1 : ∑ i : T, (Ideal.Quotient.mk (Ideal.span {x}) (i.1.2 : R)) •
      (Submodule.Quotient.mk i.1.1 : QuotSMulTop x M) = 0 := by
    simp_rw [quotient_mk_smul_mk, ← Submodule.mkQ_apply, ← map_sum,
      Finset.sum_coe_sort T (fun i ↦ (i.2 : R) • i.1), h0, map_zero]
  obtain ⟨k, a, z, hy, ha⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero h1
  -- Lift to `R` and `M`: `mᵢ = ∑ₖ aᵢₖ yₖ + x m'ᵢ` and `∑ᵢ aᵢₖ jᵢ = x cₖ`.
  choose a' ha' using fun i j ↦ Ideal.Quotient.mk_surjective (a i j)
  choose z' hz' using fun j ↦ Submodule.Quotient.mk_surjective _ (z j)
  have hm (i : T) : ∃ m', i.1.1 = ∑ j, a' i j • z' j + x • m' := by
    have hi := hy i
    simp_rw [← ha', ← hz', quotient_mk_smul_mk, ← Submodule.mkQ_apply, ← map_sum,
      Submodule.mkQ_apply, Submodule.Quotient.eq] at hi
    obtain ⟨m', -, hm'⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hi
    exact ⟨m', by rw [hm']; abel⟩
  choose m' hm' using hm
  have hc (j : Fin k) : ∃ c, ∑ i : T, a' i j * (i.1.2 : R) = x * c := by
    have hj := ha j
    simp_rw [← ha', ← map_mul, ← map_sum, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hj
    obtain ⟨c, hc⟩ := hj
    exact ⟨c, by rw [mul_comm x, hc]; simp_rw [mul_comm]⟩
  choose c hc using hc
  have hcJ (j : Fin k) : c j ∈ J.colon {x} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm, ← hc]
    exact J.sum_mem fun i _ ↦ J.mul_mem_left _ i.1.2.2
  have hTJ (i : T) : (i.1.2 : R) ∈ J.colon {x} :=
    Submodule.mem_colon_singleton.mpr (J.mul_mem_right x i.1.2.2)
  -- Multiplication by `x` sends `s = ∑ₖ yₖ ⊗ cₖ + ∑ᵢ m'ᵢ ⊗ jᵢ` to `t`.
  set s := ∑ j, z' j ⊗ₜ[R] (⟨c j, hcJ j⟩ : J.colon {x}) +
    ∑ i : T, m' i ⊗ₜ[R] (⟨i.1.2, hTJ i⟩ : J.colon {x})
  have hs : (mulColon J x).lTensor M s = ∑ i ∈ T, i.1 ⊗ₜ i.2 := by
    have e1 (j : Fin k) : mulColon J x ⟨c j, hcJ j⟩ = ∑ i : T, a' i j • i.1.2 := by
      ext; simp [← hc, smul_eq_mul]
    have e2 (i : T) : mulColon J x ⟨i.1.2, hTJ i⟩ = x • i.1.2 := by
      ext; simp [smul_eq_mul]
    rw [← Finset.sum_coe_sort T (fun i ↦ i.1 ⊗ₜ[R] i.2)]
    simp only [s, map_add, map_sum, lTensor_tmul, e1, e2, tmul_sum, tmul_smul]
    conv_rhs => enter [2, i]; rw [hm' i, add_tmul, sum_tmul, smul_tmul]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp only [tmul_smul, smul_tmul']
  refine ⟨s, hs, ?_⟩
  -- The image of `s` in `M` is killed by `x`, so it vanishes by regularity.
  have hcomp : x • (J.colon {x}).subtype = J.subtype ∘ₗ mulColon J x := by ext; simp
  have key : x • (J.colon {x}).subtype.lTensor M s = 0 := by
    rw [← LinearMap.smul_apply, ← lTensor_smul, hcomp, lTensor_comp_apply, hs, ht]
  apply (TensorProduct.rid R M).injective
  refine reg ?_
  simp only [smul_zero, ← map_smul, key, map_zero]

/-- An element of the kernel of `M ⊗[R] J → M` comes from `M ⊗[R] (J ⊓ (x) ^ n)` for every `n`. -/
private theorem mem_range_lTensor_inclusion (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] (n : ℕ) {J : Ideal R} {t : M ⊗[R] J}
    (ht : J.subtype.lTensor M t = 0) :
    t ∈ range ((Submodule.inclusion (inf_le_left : J ⊓ Ideal.span {x} ^ n ≤ J)).lTensor M) := by
  induction n generalizing J t with
  | zero =>
    have hsurj : Function.Surjective
        (Submodule.inclusion (inf_le_left : J ⊓ Ideal.span {x} ^ 0 ≤ J)) :=
      fun j ↦ ⟨⟨j, j.2, by simp⟩, rfl⟩
    rw [range_eq_top.mpr (lTensor_surjective M hsurj)]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨s, rfl, hs⟩ := exists_lTensor_mulColon_eq reg ht
    obtain ⟨u, rfl⟩ := ih hs
    have hmul : ∀ c ∈ J.colon {x} ⊓ Ideal.span {x} ^ n, x * c ∈ J ⊓ Ideal.span {x} ^ (n + 1) :=
      fun c hc ↦ ⟨by simpa [mul_comm] using Submodule.mem_colon_singleton.mp hc.1,
        pow_succ' (Ideal.span {x}) n ▸ Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hc.2⟩
    let ψ := mulRestrict x hmul
    have hcomp : mulColon J x ∘ₗ Submodule.inclusion inf_le_left =
        Submodule.inclusion inf_le_left ∘ₗ ψ := by
      ext; simp [ψ]
    refine ⟨ψ.lTensor M u, ?_⟩
    rw [← lTensor_comp_apply, ← lTensor_comp_apply, hcomp]

/-- **Local criterion for flatness** along a regular element (Stacks, Lemma 10.99.10 (00ML), for
the ideal `(x)`). Let `R` and `S` be Noetherian, `M` a finite `S`-module and `x ∈ R` with image in
the Jacobson radical of `S`. If `x` is `M`-regular and `M ⧸ x M` is flat over `R ⧸ (x)`, then `M`
is flat over `R`. -/
@[stacks 00ML "the case of a principal ideal"]
theorem Flat.of_flat_quotSMulTop [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : algebraMap R S x ∈ (⊥ : Ideal S).jacobson) (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] : Flat R M := by
  refine Flat.iff_lTensor_injective'.mpr fun J ↦ (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  set I := Ideal.span {x}
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  -- By Artin–Rees, `t` is divisible by every power of `x` in `M ⊗[R] J`.
  have hmem (n : ℕ) : t ∈ (I ^ n • ⊤ : Submodule R (M ⊗[R] J)) := by
    obtain ⟨u, rfl⟩ := mem_range_lTensor_inclusion reg (n + k) ht
    clear ht
    induction u using TensorProduct.inductionOn with
    | add u v hu hv => rw [map_add]; exact add_mem hu hv
    | tmul m c =>
      have hc : (c : R) ∈ I ^ n • J := by
        have := hk (n + k) (Nat.le_add_left k n)
        rw [Nat.add_sub_cancel] at this
        have hc' : (c : R) ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ J :=
          ⟨by simpa [smul_eq_mul, Ideal.mul_top] using c.2.2, c.2.1⟩
        rw [this] at hc'
        exact Submodule.smul_mono le_rfl inf_le_right hc'
      exact range_lTensor_inclusion_smul_le (I ^ n) J
        ⟨m ⊗ₜ ⟨c, hc⟩, by simp [Submodule.inclusion_apply]⟩
  -- Krull's intersection theorem for the finite `S`-module `M ⊗[R] J`.
  set IS := I.map (algebraMap R S)
  have hle (n : ℕ) : (I ^ n • ⊤ : Submodule R (M ⊗[R] J)) ≤
      (IS ^ n • (⊤ : Submodule S (M ⊗[R] J))).restrictScalars R := by
    refine Submodule.smul_le.mpr fun r hr y _ ↦ ?_
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul S r y]
    have hr' : algebraMap R S r ∈ IS ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr
    exact Submodule.smul_mem_smul hr' Submodule.mem_top
  have hjac : IS ≤ (⊥ : Ideal S).jacobson := by
    simpa [IS, I, Ideal.map_span, Ideal.span_singleton_le_iff_mem] using hx
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson IS hjac (M := M ⊗[R] J)
  have : t ∈ ⨅ n : ℕ, IS ^ n • (⊤ : Submodule S (M ⊗[R] J)) :=
    Submodule.mem_iInf _ |>.mpr fun n ↦ hle n (hmem n)
  simpa [hbot] using this

/-- **Local criterion for flatness** along a regular element, for a local homomorphism `R → S` of
Noetherian local rings (Stacks, Lemma 10.99.10 (00ML), for the ideal `(x)`): if `x` lies in the
maximal ideal of `R`, is `M`-regular, and `M ⧸ x M` is flat over `R ⧸ (x)`, then the finite
`S`-module `M` is flat over `R`. -/
@[stacks 00ML "the case of a principal ideal"]
theorem Flat.of_flat_quotSMulTop_of_isLocalHom [IsLocalRing R] [IsNoetherianRing R] {S : Type*}
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : x ∈ IsLocalRing.maximalIdeal R) (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] : Flat R M :=
  of_flat_quotSMulTop (S := S) (by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact map_nonunit (algebraMap R S) x hx) reg

/-- For an `M`-regular element `x` as in `Module.Flat.of_flat_quotSMulTop`, `M ⧸ x M` is flat over
`R ⧸ (x)` if and only if `M` is flat over `R`. -/
theorem flat_quotSMulTop_iff_flat [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : algebraMap R S x ∈ (⊥ : Ideal S).jacobson) (reg : IsSMulRegular M x) :
    Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Flat R M :=
  ⟨fun _ ↦ Flat.of_flat_quotSMulTop hx reg, fun _ ↦ inferInstance⟩

end Module
