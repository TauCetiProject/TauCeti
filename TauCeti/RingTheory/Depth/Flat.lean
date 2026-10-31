/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.Basic
public import TauCeti.RingTheory.Flat.FiberRegular
public import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Depth along a flat local homomorphism

Let `R → S` be a local homomorphism of Noetherian local rings, with `𝔪` the maximal ideal of `R`,
and let `M` be a finite `S`-module that is flat over `R`. Then
`depth_S M = depth R + depth_S (M ⧸ 𝔪M)` (Stacks, Lemma 10.163.2 (0337), for `M = S`; Matsumura,
Theorem 23.3, for `N = R`). For `M = S` this reads `depth S = depth R + depth (S ⧸ 𝔪S)`: the depth
of the total space of a flat family is the depth of the base plus the depth of the closed fibre.
This is the input for the ascent of Serre's conditions `(S_n)`, and so of reducedness and
normality, along flat maps with well-behaved fibres.

More generally, for every ideal `J` of `R`,
`depth_S (M ⧸ JM) = depth_R (R ⧸ J) + depth_S (M ⧸ 𝔪M)`, which is Matsumura's Theorem 23.3 for
the cyclic module `N = R ⧸ J`, as `M ⧸ JM = (R ⧸ J) ⊗[R] M`.

## Main results

* `IsLocalRing.depth_quotient_map_smul_top_eq_add_of_flat`: for every ideal `J` of `R`,
  `depth_S (M ⧸ JM) = depth_R (R ⧸ J) + depth_S (M ⧸ 𝔪M)`.
* `IsLocalRing.depth_eq_add_depth_quotient_of_flat`: `depth_S M = depth R + depth_S (M ⧸ 𝔪M)`.
* `IsLocalRing.depth_eq_add_of_flat`: `depth S = depth R + depth (S ⧸ 𝔪S)` for a flat local
  homomorphism `R → S` of Noetherian local rings (Stacks, Lemma 10.163.2 (0337)).

## Proof

By induction on `depth_R (R ⧸ J)`. If it is positive, some `x ∈ 𝔪` is regular on `R ⧸ J`; by
flatness it is regular on `M ⧸ JM`, and passing from `J` to `J + (x)` lowers both
`depth_R (R ⧸ J)` and `depth_S (M ⧸ JM)` by one.

If it is zero, some `a ∉ J` has `𝔪 a ⊆ J`, and `M ⧸ JM` and `M ⧸ 𝔪M` have the same depth, by
induction on the depth of `M ⧸ 𝔪M`. Multiplication by `a` embeds `M ⧸ 𝔪M` into `M ⧸ JM`
(`Module.Flat.mem_smul_top_of_smul_mem_ideal_smul_top`), so the two have depth zero together.
Otherwise some `y` in the maximal ideal of `S` is a nonzerodivisor on `M ⧸ 𝔪M`. It is then regular
on `M ⧸ JM`, and `M ⧸ yM` is again flat over `R` (`Module.Flat.isSMulRegular_quotient_map_smul_top`,
`Module.Flat.flat_quotSMulTop_of_isSMulRegular_quotient_map_smul_top`), so dividing by `y` lowers
both depths by one.

## References

* [Stacks Project, Lemma 10.163.2](https://stacks.math.columbia.edu/tag/0337)
* H. Matsumura, *Commutative Ring Theory*, Theorem 23.3.
-/

public section

universe u v w

open IsLocalRing Pointwise

namespace IsLocalRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- For a local homomorphism, the extension of the maximal ideal lies in the Jacobson radical. -/
private theorem map_maximalIdeal_le_jacobson :
    (maximalIdeal R).map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap]
  exact fun x hx ↦ map_nonunit (algebraMap R S) x hx

section Module

variable [IsNoetherianRing R] [IsNoetherianRing S] {M : Type w} [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M] [Small.{w} S]

/-- If `a ∉ J` and `𝔪 a ⊆ J`, then `M ⧸ JM` and `M ⧸ 𝔪M` satisfy the same lower bounds on depth. -/
private theorem natCast_le_depth_quotient_iff [Module.Finite S M] [Module.Flat R M] {J : Ideal R}
    {a : R} (haJ : a ∉ J) (h𝔪a : ∀ r ∈ maximalIdeal R, r * a ∈ J) (n : ℕ) :
    (n : ℕ∞) ≤ depth (ModuleCat.of S (M ⧸ J.map (algebraMap R S) • (⊤ : Submodule S M))) ↔
      (n : ℕ∞) ≤ depth (ModuleCat.of S
        (M ⧸ (maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M))) := by
  induction n generalizing M with
  | zero => simp
  | succ n ih =>
    set 𝔪 := maximalIdeal R
    by_cases h0 : depth (ModuleCat.of S (M ⧸ 𝔪.map (algebraMap R S) • (⊤ : Submodule S M))) = 0
    · -- Multiplication by `a` embeds `M ⧸ 𝔪M` into `M ⧸ JM`, so `M ⧸ JM` has depth zero too.
      let ι := Submodule.mapQ (𝔪.map (algebraMap R S) • (⊤ : Submodule S M))
        (J.map (algebraMap R S) • (⊤ : Submodule S M)) (algebraMap R S a • LinearMap.id)
        fun v hv ↦ by
          rw [Ideal.mem_map_smul_top_iff] at hv
          rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, algebraMap_smul,
            Ideal.mem_map_smul_top_iff]
          refine Submodule.smul_induction_on hv (fun r hr w _ ↦ ?_) fun _ _ h₁ h₂ ↦ ?_
          · rw [smul_smul, mul_comm]
            exact Submodule.smul_mem_smul (h𝔪a r hr) trivial
          · rw [smul_add]
            exact add_mem h₁ h₂
      have hι : Function.Injective ι := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro q hq
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [LinearMap.mem_ker, Submodule.mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
          algebraMap_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_map_smul_top_iff] at hq
        rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Ideal.mem_map_smul_top_iff]
        exact Module.Flat.mem_smul_top_of_smul_mem_ideal_smul_top haJ h𝔪a hq
      have hJ0 : depth (ModuleCat.of S (M ⧸ J.map (algebraMap R S) • (⊤ : Submodule S M))) = 0 := by
        rw [depth_eq_zero_iff_nontrivial_linearMap] at h0 ⊢
        obtain ⟨g, hg⟩ := exists_ne
          (0 : S ⧸ maximalIdeal S →ₗ[S] M ⧸ 𝔪.map (algebraMap R S) • (⊤ : Submodule S M))
        exact ⟨ι ∘ₗ g, 0, fun h ↦ hg <| LinearMap.ext fun t ↦ hι <| by
          simpa using LinearMap.congr_fun h t⟩
      rw [h0, hJ0]
    -- Otherwise the maximal ideal of `S` contains a nonzerodivisor `y` on `M ⧸ 𝔪M`.
    obtain ⟨y, hy, reg⟩ := ((maximalIdeal S).exists_mem_isSMulRegular_iff
      (M := M ⧸ 𝔪.map (algebraMap R S) • (⊤ : Submodule S M))).2 fun p hp hle ↦ h0 <|
        depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.2 <|
          le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle ▸ hp
    -- Dividing by `y` lowers both depths by one and keeps the module flat over `R`.
    have hjac := map_maximalIdeal_le_jacobson (R := R) (S := S)
    have : Module.Flat R (QuotSMulTop y M) :=
      Module.Flat.flat_quotSMulTop_of_isSMulRegular_quotient_map_smul_top 𝔪 hjac reg
    have hJ := depth_quotSMulTop_succ_eq_depth
      (Module.Flat.isSMulRegular_quotient_map_smul_top 𝔪 hjac reg J) hy
    have h𝔪 := depth_quotSMulTop_succ_eq_depth reg hy
    rw [depth_eq_of_linearEquiv
      ((Submodule.quotSupSpanSingletonSMulTopEquivQuotSMulTopOuter M _ y).symm ≪≫ₗ
        Submodule.quotSupSpanSingletonSMulTopEquivQuotSMulTopInner M _ y)] at hJ h𝔪
    rw [← hJ, ← h𝔪, Nat.cast_succ, ENat.add_le_add_iff_right ENat.one_ne_top,
      ENat.add_le_add_iff_right ENat.one_ne_top]
    exact ih

variable [Module.Finite S M] [Module.Flat R M]

/-- **Depth along a flat local homomorphism, modulo an ideal of the base.** Let `R → S` be a
local homomorphism of Noetherian local rings, with `𝔪` the maximal ideal of `R`, and `M` a finite
`S`-module, flat over `R`. For every ideal `J` of `R`,
`depth_S (M ⧸ JM) = depth_R (R ⧸ J) + depth_S (M ⧸ 𝔪M)`. Matsumura, Theorem 23.3, for the
`R`-module `R ⧸ J`. -/
theorem depth_quotient_map_smul_top_eq_add_of_flat (J : Ideal R) :
    depth (ModuleCat.of S (M ⧸ J.map (algebraMap R S) • (⊤ : Submodule S M))) =
      depth (ModuleCat.of R (R ⧸ J)) + depth (ModuleCat.of S
        (M ⧸ (maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M))) := by
  set 𝔪 := maximalIdeal R
  by_cases hJ : J = ⊤
  · -- Both `M ⧸ M` and `R ⧸ R` are zero, of depth `⊤`.
    subst hJ
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.2 rfl
    have : Subsingleton (M ⧸ (⊤ : Ideal R).map (algebraMap R S) • (⊤ : Submodule S M)) := by
      rw [Ideal.map_top, Submodule.top_smul]
      infer_instance
    rw [depth_eq_top_of_subsingleton, depth_eq_top_of_subsingleton, top_add]
  -- Otherwise `R ⧸ J` is nonzero, so its depth is a natural number `n`; induct on `n`.
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (mt (depth_eq_top_iff (ModuleCat.of R (R ⧸ J))).1 (not_subsingleton _))
  clear hJ this
  induction n generalizing J with
  | zero =>
    -- Some `a ∉ J` has `𝔪 a ⊆ J`, so `M ⧸ JM` and `M ⧸ 𝔪M` have the same depth.
    have := depth_eq_zero_iff_nontrivial_linearMap.1 hn.symm
    obtain ⟨f, hf⟩ := exists_ne (0 : R ⧸ 𝔪 →ₗ[R] R ⧸ J)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (f 1)
    have hf1 (r : R) : f (Ideal.Quotient.mk 𝔪 r) = Ideal.Quotient.mk J (r * a) := by
      rw [← mul_one (Ideal.Quotient.mk 𝔪 r), ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def,
        map_smul, ← ha, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    have haJ : a ∉ J := fun h ↦ hf <| LinearMap.ext fun t ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
      rw [hf1, Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left r h), LinearMap.zero_apply]
    have h𝔪a (r : R) (hr : r ∈ 𝔪) : r * a ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hf1, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
    rw [← hn, Nat.cast_zero, zero_add]
    exact ENat.eq_of_forall_natCast_le_iff (natCast_le_depth_quotient_iff haJ h𝔪a)
  | succ n ih =>
    -- Some `x ∈ 𝔪` is regular on `R ⧸ J`.
    have h0 : depth (ModuleCat.of R (R ⧸ J)) ≠ 0 := by
      rw [← hn]
      exact_mod_cast n.succ_ne_zero
    obtain ⟨x, hx, reg⟩ := (𝔪.exists_mem_isSMulRegular_iff (M := R ⧸ J)).2 fun p hp hle ↦ h0 <|
      depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.2 <|
        le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle ▸ hp
    -- Passing to `J + (x)` lowers the depth of `R ⧸ J` by one.
    have hsmul (I : Ideal R) : I • (⊤ : Submodule R R) = I := by
      rw [smul_eq_mul, Ideal.mul_top]
    have eR : (R ⧸ (J ⊔ Ideal.span {x})) ≃ₗ[R] QuotSMulTop x (R ⧸ J) :=
      Submodule.quotEquivOfEq _ _ (hsmul _).symm ≪≫ₗ
        Submodule.quotSupSpanSingletonSMulTopEquivQuotSMulTopOuter R J x ≪≫ₗ
          QuotSMulTop.congr x (Submodule.quotEquivOfEq _ _ (hsmul J))
    have hR := depth_quotSMulTop_succ_eq_depth reg hx
    rw [← depth_eq_of_linearEquiv eR, ← hn, Nat.cast_succ] at hR
    have hn' := WithTop.add_right_cancel ENat.one_ne_top hR
    -- By flatness, the image `x'` of `x` in `S` is regular on `M ⧸ JM`.
    set x' := algebraMap R S x
    have hcolon : J.colon {x} = J := by
      refine le_antisymm (fun r hr ↦ ?_) fun r hr ↦ Submodule.mem_colon_singleton.2 ?_
      · refine Ideal.Quotient.eq_zero_iff_mem.1 (reg.right_eq_zero_of_smul ?_)
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem, mul_comm]
        simpa using Submodule.mem_colon_singleton.1 hr
      · simpa using J.mul_mem_right x hr
    have regS : IsSMulRegular (M ⧸ J.map (algebraMap R S) • (⊤ : Submodule S M)) x' := by
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
      intro v hv
      rw [algebraMap_smul, Ideal.mem_map_smul_top_iff, Module.Flat.smul_mem_ideal_smul_top_iff,
        hcolon] at hv
      rwa [Ideal.mem_map_smul_top_iff]
    have hx' : x' ∈ maximalIdeal S := map_nonunit (algebraMap R S) x hx
    -- Dividing `M ⧸ JM` by `x'` gives `M ⧸ (J + (x)) M`, of depth one less.
    have eS : (M ⧸ (J ⊔ Ideal.span {x}).map (algebraMap R S) • (⊤ : Submodule S M)) ≃ₗ[S]
        QuotSMulTop x' (M ⧸ J.map (algebraMap R S) • (⊤ : Submodule S M)) :=
      Submodule.quotEquivOfEq _ _ (by rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]) ≪≫ₗ
        Submodule.quotSupSpanSingletonSMulTopEquivQuotSMulTopOuter M _ x'
    rw [← depth_quotSMulTop_succ_eq_depth regS hx', ← depth_eq_of_linearEquiv eS, ih _ hn'.symm,
      hn', ← hn, Nat.cast_succ, add_right_comm]

/-- **Depth along a flat local homomorphism.** Let `R → S` be a local homomorphism of Noetherian
local rings, with `𝔪` the maximal ideal of `R`, and `M` a finite `S`-module, flat over `R`. Then
`depth_S M = depth R + depth_S (M ⧸ 𝔪M)`. Matsumura, Theorem 23.3, for the `R`-module `R`. -/
theorem depth_eq_add_depth_quotient_of_flat :
    depth (ModuleCat.of S M) = depth (ModuleCat.of R R) + depth (ModuleCat.of S
      (M ⧸ (maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M))) := by
  have h := depth_quotient_map_smul_top_eq_add_of_flat (R := R) (S := S) (M := M) ⊥
  rwa [depth_eq_of_linearEquiv (Submodule.quotEquivOfEqBot _
      (by rw [Ideal.map_bot, Submodule.bot_smul])),
    depth_eq_of_linearEquiv (Submodule.quotEquivOfEqBot (⊥ : Ideal R) rfl)] at h

end Module

/-- **Depth along a flat local homomorphism** (Stacks, Lemma 10.163.2 (0337)). Let `R → S` be a
flat local homomorphism of Noetherian local rings, with `𝔪` the maximal ideal of `R`. Then
`depth S = depth R + depth (S ⧸ 𝔪S)`, where `S ⧸ 𝔪S` is the closed fibre, as an `S`-module. -/
@[stacks 0337]
theorem depth_eq_add_of_flat [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] :
    depth (ModuleCat.of S S) = depth (ModuleCat.of R R) +
      depth (ModuleCat.of S (S ⧸ (maximalIdeal R).map (algebraMap R S))) := by
  rw [depth_eq_add_depth_quotient_of_flat (R := R) (M := S),
    depth_eq_of_linearEquiv (Submodule.quotEquivOfEq _ _ (by rw [smul_eq_mul, Ideal.mul_top]))]

end IsLocalRing
