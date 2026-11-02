/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.Flat.Extensions
public import TauCeti.RingTheory.Flat.FiniteLength
public import TauCeti.RingTheory.Length

/-!
# Regular elements on the closed fibre of a flat module

Let `R → S` be a local homomorphism of Noetherian local rings and `N` a finite `S`-module which
is flat over `R`. If `y` lies in `S` and is a nonzerodivisor on the closed fibre
`N ⧸ 𝔪_R N`, then `y` is a nonzerodivisor on `N ⊗[R] M` for every finite `R`-module `M`, in
particular on `N` itself, and `N ⧸ y N` is again flat over `R`.

This is the step that lets an induction on the depth of the closed fibre replace `N` by `N ⧸ y N`
while keeping it flat over `R`, as in the proof that depth is additive along flat local
homomorphisms.

The proof first treats `M` of finite length, by
`Module.Flat.injective_rTensor_of_isFiniteLength`: the residue field case is the hypothesis,
through the isomorphism `N ⊗[R] κ(R) ≃ N ⧸ 𝔪_R N` of
`TensorProduct.AlgebraTensorModule.tensorQuotEquivQuotMapSMul`. A general finite `M` is then
reached through its quotients `M ⧸ 𝔪_R ^ (k + 1) M`, which have finite length: an element of
`N ⊗[R] M` killed by `y` lies in `𝔪_S ^ k (N ⊗[R] M)` for every `k`, and so vanishes by Krull's
intersection theorem for the finite `S`-module `N ⊗[R] M`. Flatness of `N ⧸ y N` follows from
Tor-vanishing against the quotients `R ⧸ I`, in the form
`Module.Flat.of_exact_of_lTensor_quotient_injective`.

## Main results

* `Module.Flat.isSMulRegular_tensorProduct_of_isSMulRegular_quotient`: `y` is a nonzerodivisor
  on `N ⊗[R] M` for every finite `R`-module `M`.
* `Module.Flat.isSMulRegular_of_isSMulRegular_quotient`: `y` is a nonzerodivisor on `N`.
* `Module.Flat.quotSMulTop_of_isSMulRegular_quotient`: `N ⧸ y N` is flat over `R`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 22.5 and its Corollary.
-/

public section

open IsLocalRing TensorProduct Pointwise

namespace Module.Flat

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S] [IsNoetherianRing S]
  [IsLocalHom (algebraMap R S)]

/-- **A nonzerodivisor on the closed fibre stays one after tensoring.** Let `R → S` be a local
homomorphism of Noetherian local rings and `N` a finite `S`-module flat over `R`. If `y ∈ S` is a
nonzerodivisor on `N ⧸ 𝔪_R N`, then `y` is a nonzerodivisor on `N ⊗[R] M` for every finite
`R`-module `M`. -/
theorem isSMulRegular_tensorProduct_of_isSMulRegular_quotient [Module.Finite S N] [Flat R N]
    {y : S}
    (hy : IsSMulRegular (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)) y)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsSMulRegular (N ⊗[R] M) y := by
  let f := DistribSMul.toLinearMap R N y
  -- The residue field case is the hypothesis, through `N ⊗[R] κ(R) ≃ N ⧸ 𝔪_R N`.
  have hκ : Function.Injective (f.rTensor (R ⧸ maximalIdeal R)) := by
    rw [show ⇑(f.rTensor (R ⧸ maximalIdeal R)) = (y • ·) from
      funext fun z ↦ (AlgebraTensorModule.smul_eq_lsmul_rTensor y z).symm]
    exact ((AlgebraTensorModule.tensorQuotEquivQuotMapSMul (S := S) (N := N)
      (maximalIdeal R)).isSMulRegular_congr y).mpr hy
  have hfin (k : ℕ) := injective_rTensor_of_isFiniteLength hκ
    (Ideal.isFiniteLength_quotient_smul_top_of_radical_eq_maximalIdeal _
      (by rw [Ideal.radical_pow _ k.succ_ne_zero, (maximalIdeal.isMaximal R).isPrime.radical]) M)
  have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
  unfold IsSMulRegular
  rw [← show ⇑(f.rTensor M) = (y • ·) from
    funext fun z ↦ (AlgebraTensorModule.smul_eq_lsmul_rTensor y z).symm,
    injective_iff_map_eq_zero]
  intro z hz
  -- `z` dies in each `N ⊗[R] (M ⧸ 𝔪_R ^ (k + 1) M)`, so it lies in `𝔪_S ^ (k + 1) (N ⊗[R] M)`.
  have hmem (k : ℕ) : z ∈ (maximalIdeal S ^ k • ⊤ : Submodule S (N ⊗[R] M)) := by
    set P := (maximalIdeal R ^ (k + 1) • ⊤ : Submodule R M)
    have hq : P.mkQ.lTensor N z = 0 := (injective_iff_map_eq_zero _).mp (hfin k) _ <| by
      rw [← LinearMap.lTensor_rTensor_comm, hz, map_zero]
    obtain ⟨w, rfl⟩ := ((_root_.lTensor_exact N (LinearMap.exact_subtype_mkQ P)
      P.mkQ_surjective) z).mp hq
    refine Submodule.smul_mono_left (Ideal.pow_le_pow_right k.le_succ) <|
      AlgebraTensorModule.range_lTensor_subtype_smul_top_le ?_ ⟨w, rfl⟩
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le (algebraMap R S)) _
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N ⊗[R] M) (maximalIdeal S)
    (maximalIdeal.isMaximal S).ne_top
  rw [← Submodule.mem_bot S, ← hbot, Submodule.mem_iInf]
  exact hmem

/-- **A nonzerodivisor on the closed fibre is a nonzerodivisor.** Let `R → S` be a local
homomorphism of Noetherian local rings and `N` a finite `S`-module flat over `R`. If `y ∈ S` is a
nonzerodivisor on `N ⧸ 𝔪_R N`, then it is a nonzerodivisor on `N`. -/
theorem isSMulRegular_of_isSMulRegular_quotient [Module.Finite S N] [Flat R N] {y : S}
    (hy : IsSMulRegular (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)) y) :
    IsSMulRegular N y :=
  ((AlgebraTensorModule.rid R S N).isSMulRegular_congr y).mp
    (isSMulRegular_tensorProduct_of_isSMulRegular_quotient hy R)

/-- **Dividing by a nonzerodivisor on the closed fibre preserves flatness.** Let `R → S` be a local
homomorphism of Noetherian local rings and `N` a finite `S`-module flat over `R`. If `y ∈ S` is a
nonzerodivisor on `N ⧸ 𝔪_R N`, then `N ⧸ y N` is flat over `R`. -/
theorem quotSMulTop_of_isSMulRegular_quotient [Module.Finite S N] [Flat R N] {y : S}
    (hy : IsSMulRegular (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)) y) :
    Flat R (QuotSMulTop y N) := by
  let f := DistribSMul.toLinearMap R N y
  let g := (y • ⊤ : Submodule S N).mkQ.restrictScalars R
  have hexact : Function.Exact f g := fun n ↦ by
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [f]
  have hg : Function.Surjective g := by
    rw [LinearMap.coe_restrictScalars]
    exact Submodule.mkQ_surjective _
  refine of_exact_of_lTensor_quotient_injective f g hexact hg ?_
  intro I _
  rw [f.lTensor_inj_iff_rTensor_inj (R ⧸ I), show ⇑(f.rTensor (R ⧸ I)) = (y • ·) from
    funext fun z ↦ (AlgebraTensorModule.smul_eq_lsmul_rTensor y z).symm]
  exact isSMulRegular_tensorProduct_of_isSMulRegular_quotient hy (R ⧸ I)

end Module.Flat
