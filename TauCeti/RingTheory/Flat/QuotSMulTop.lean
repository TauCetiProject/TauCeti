/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.RingTheory.Flat.QuotientRegular

/-!
# Regular elements on the closed fibre of a flat module

Let `R → S` be a local homomorphism of Noetherian local rings and `N` a finite `S`-module which
is flat over `R`. If `y` lies in `S` and is a nonzerodivisor on the closed fibre
`N ⧸ 𝔪_R N`, then `y` is a nonzerodivisor on `N ⊗[R] M` for every finite `R`-module `M`, in
particular on `N` itself, and `N ⧸ y N` is again flat over `R`.

This is the step that lets an induction on the depth of the closed fibre replace `N` by `N ⧸ y N`
while keeping it flat over `R`, as in the proof that depth is additive along flat local
homomorphisms.

The proof first treats `M` of finite length, by induction on a composition series: the residue
field case is the hypothesis, and flatness of `N` makes `N ⊗[R] -` exact on the short exact
sequences of the series. A general finite `M` is then reached through its quotients
`M ⧸ 𝔪_R ^ (k + 1) M`, which have finite length: an element of `N ⊗[R] M` killed by `y` lies in
`𝔪_S ^ k (N ⊗[R] M)` for every `k`, and so vanishes by Krull's intersection theorem for the finite
`S`-module `N ⊗[R] M`. Flatness of `N ⧸ y N` follows from Tor-vanishing against the quotients
`R ⧸ I`, in the form `Module.Flat.of_exact_of_lTensor_quotient_injective`.

## Main results

* `TensorProduct.AlgebraTensorModule.tensorQuotEquivQuotMapSMul`: the `S`-linear isomorphism
  `N ⊗[R] (R ⧸ I) ≃ N ⧸ I S • N`.
* `Module.Flat.isSMulRegular_tensorProduct_of_isSMulRegular_quotient`: `y` is a nonzerodivisor
  on `N ⊗[R] M` for every finite `R`-module `M`.
* `Module.Flat.isSMulRegular_of_isSMulRegular_quotient`: `y` is a nonzerodivisor on `N`.
* `Module.Flat.quotSMulTop_of_isSMulRegular_quotient`: `N ⧸ y N` is flat over `R`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 22.5 and its Corollary.
-/

public section

open IsLocalRing TensorProduct Pointwise

namespace TensorProduct.AlgebraTensorModule

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The `S`-linear isomorphism `N ⊗[R] (R ⧸ I) ≃ N ⧸ I S • N` for an `S`-module `N` and an ideal
`I` of `R`. It upgrades Mathlib's `TensorProduct.tensorQuotEquivQuotSMul`, which is `R`-linear
with target `N ⧸ I • N`. -/
noncomputable def tensorQuotEquivQuotMapSMul (I : Ideal R) :
    N ⊗[R] (R ⧸ I) ≃ₗ[S] N ⧸ (I.map (algebraMap R S) • ⊤ : Submodule S N) where
  __ := tensorQuotEquivQuotSMul N I ≪≫ₗ
    Submodule.quotEquivOfEq _ _
      (by rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R _
  map_smul' s x := by
    induction x with
    | add x y hx hy => simp_all
    | tmul n r =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp only [smul_tmul']
      simp [smul_comm r s]

@[simp]
theorem tensorQuotEquivQuotMapSMul_tmul_mk (I : Ideal R) (n : N) (r : R) :
    tensorQuotEquivQuotMapSMul (S := S) I (n ⊗ₜ[R] Ideal.Quotient.mk I r) =
      Submodule.Quotient.mk (r • n) := by
  simp [tensorQuotEquivQuotMapSMul]

end TensorProduct.AlgebraTensorModule

namespace Module.Flat

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

section Tensor

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- On `N ⊗[R] M`, the `S`-action of `y` is `(y • ·) ⊗ id`. -/
@[simp]
theorem _root_.LinearMap.rTensor_distribSMul_toLinearMap_apply (y : S) (z : N ⊗[R] M) :
    (DistribSMul.toLinearMap R N y).rTensor M z = y • z := by
  induction z with
  | add x z hx hz => simp [hx, hz]
  | tmul n m => simp [smul_tmul']

/-- Injectivity of `(y • ·) ⊗ id_M` is invariant under isomorphisms of `M`. -/
private theorem injective_rTensor_of_linearEquiv {f : N →ₗ[R] N} (e : M ≃ₗ[R] M')
    (h : Function.Injective (f.rTensor M')) : Function.Injective (f.rTensor M) := by
  have hcomm : (e.toLinearMap.lTensor N) ∘ (f.rTensor M) =
      (f.rTensor M') ∘ (e.toLinearMap.lTensor N) := by
    rw [← LinearMap.coe_comp, ← LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  refine Function.Injective.of_comp (f := e.toLinearMap.lTensor N) ?_
  rw [hcomm]
  exact h.comp (e.lTensor N).injective

/-- Over a flat `N`, injectivity of `f ⊗ id` passes from a submodule `P` of `M` and the quotient
`M ⧸ P` to `M`, by exactness of `0 → N ⊗ P → N ⊗ M → N ⊗ (M ⧸ P) → 0`. -/
private theorem injective_rTensor_of_injective_rTensor_submodule_quotient [Flat R N]
    {f : N →ₗ[R] N} (P : Submodule R M) (hP : Function.Injective (f.rTensor P))
    (hQ : Function.Injective (f.rTensor (M ⧸ P))) : Function.Injective (f.rTensor M) := by
  rw [injective_iff_map_eq_zero] at hP hQ ⊢
  intro z hz
  have hq : P.mkQ.lTensor N z = 0 := hQ _ <| by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hz, map_zero]
  obtain ⟨w, rfl⟩ := ((_root_.lTensor_exact N (LinearMap.exact_subtype_mkQ P)
    P.mkQ_surjective) z).mp hq
  have hw : P.subtype.lTensor N (f.rTensor P w) = 0 := by
    rwa [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply]
  rw [hP w ((injective_iff_map_eq_zero _).mp
    (lTensor_preserves_injective_linearMap _ P.injective_subtype) _ hw), map_zero]

/-- The image of `N ⊗[R] I M` in `N ⊗[R] M` lies in `J • (N ⊗[R] M)` whenever `I S ≤ J`. -/
private theorem lTensor_subtype_mem_smul_top {M : Type*} [AddCommGroup M] [Module R M]
    {I : Ideal R} {J : Ideal S} (hIJ : I.map (algebraMap R S) ≤ J)
    (w : N ⊗[R] (I • ⊤ : Submodule R M)) :
    (I • ⊤ : Submodule R M).subtype.lTensor N w ∈ (J • ⊤ : Submodule S (N ⊗[R] M)) := by
  induction w with
  | add x z hx hz => rw [map_add]; exact add_mem hx hz
  | tmul n v =>
    obtain ⟨v, hv⟩ := v
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, Submodule.coe_mk]
    refine Submodule.smul_induction_on hv (fun a ha m _ ↦ ?_) (fun x z hx hz ↦ ?_)
    · rw [tmul_smul, ← algebraMap_smul S a]
      exact Submodule.smul_mem_smul (hIJ (Ideal.mem_map_of_mem _ ha)) trivial
    · rw [tmul_add]
      exact add_mem hx hz

end Tensor

variable [IsLocalRing R]

/-- Over a flat `N`, if `f ⊗ id` is injective on `N ⊗[R] κ(R)`, it is injective on `N ⊗[R] M`
for every `R`-module `M` of finite length. -/
private theorem injective_rTensor_of_isFiniteLength [Flat R N] {f : N →ₗ[R] N}
    (hκ : Function.Injective (f.rTensor (R ⧸ maximalIdeal R))) {M : Type*} [AddCommGroup M]
    [Module R M] (hM : IsFiniteLength R M) : Function.Injective (f.rTensor M) := by
  induction hM with
  | of_subsingleton => exact Function.injective_of_subsingleton _
  | @of_simple_quotient M _ _ P _ _ ih =>
    refine injective_rTensor_of_injective_rTensor_submodule_quotient P ih ?_
    -- A simple module over a local ring is the residue field.
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R (M ⧸ P)›
    obtain rfl := IsLocalRing.eq_maximalIdeal hI
    exact injective_rTensor_of_linearEquiv e hκ

variable [IsNoetherianRing R]

/-- A finite module over a Noetherian local ring, divided by a positive power of the maximal ideal,
has finite length. -/
private theorem isFiniteLength_quotient_maximalIdeal_pow_smul (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (k : ℕ) :
    IsFiniteLength R (M ⧸ (maximalIdeal R ^ (k + 1) • ⊤ : Submodule R M)) := by
  set I := maximalIdeal R ^ (k + 1)
  have hmin : maximalIdeal R ∈ I.minimalPrimes :=
    ⟨⟨inferInstance, Ideal.pow_le_self k.succ_ne_zero⟩, fun q hq _ ↦
      have := hq.1
      Ideal.IsPrime.le_of_pow_le hq.2⟩
  have := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  have : Module.Finite (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinian R (M ⧸ (I • ⊤ : Submodule R M)) :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ I) Ideal.Quotient.mk_surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, this⟩

variable [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)]

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
    let e := AlgebraTensorModule.tensorQuotEquivQuotMapSMul (S := S) (N := N) (maximalIdeal R)
    rw [show ⇑(f.rTensor (R ⧸ maximalIdeal R)) = (y • ·) from
      funext (LinearMap.rTensor_distribSMul_toLinearMap_apply y)]
    refine Function.Injective.of_comp (f := e) ?_
    have : (e ∘ (y • ·)) = (y • ·) ∘ e := funext fun z ↦ e.map_smul y z
    rw [this]
    exact hy.comp e.injective
  have hfin (k : ℕ) := injective_rTensor_of_isFiniteLength hκ
    (isFiniteLength_quotient_maximalIdeal_pow_smul M k)
  have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
  unfold IsSMulRegular
  rw [← show ⇑(f.rTensor M) = (y • ·) from
    funext (LinearMap.rTensor_distribSMul_toLinearMap_apply y), injective_iff_map_eq_zero]
  intro z hz
  -- `z` dies in each `N ⊗[R] (M ⧸ 𝔪_R ^ (k + 1) M)`, so it lies in `𝔪_S ^ (k + 1) (N ⊗[R] M)`.
  have hmem (k : ℕ) : z ∈ (maximalIdeal S ^ k • ⊤ : Submodule S (N ⊗[R] M)) := by
    set P := (maximalIdeal R ^ (k + 1) • ⊤ : Submodule R M)
    have hq : P.mkQ.lTensor N z = 0 := (injective_iff_map_eq_zero _).mp (hfin k) _ <| by
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hz, map_zero]
    obtain ⟨w, rfl⟩ := ((_root_.lTensor_exact N (LinearMap.exact_subtype_mkQ P)
      P.mkQ_surjective) z).mp hq
    refine Submodule.smul_mono_left (Ideal.pow_le_pow_right k.le_succ) ?_
    refine lTensor_subtype_mem_smul_top ?_ w
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
    IsSMulRegular N y := by
  let e := AlgebraTensorModule.rid R S N
  have := isSMulRegular_tensorProduct_of_isSMulRegular_quotient hy R
  refine Function.Injective.of_comp (f := e.symm) ?_
  have hcomm : (e.symm ∘ (y • ·)) = (y • ·) ∘ e.symm := funext fun z ↦ e.symm.map_smul y z
  rw [hcomm]
  exact this.comp e.symm.injective

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
  -- Transport the regularity of `y` on `N ⊗[R] (R ⧸ I)` across the symmetry of `⊗`.
  have hreg := isSMulRegular_tensorProduct_of_isSMulRegular_quotient hy (R ⧸ I)
  let e := TensorProduct.comm R (R ⧸ I) N
  have hcomm : e ∘ (f.lTensor (R ⧸ I)) = (y • · : N ⊗[R] (R ⧸ I) → _) ∘ e := by
    funext z
    simp only [Function.comp_apply, ← LinearMap.rTensor_distribSMul_toLinearMap_apply]
    induction z with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r n => simp [e, f]
  refine Function.Injective.of_comp (f := e) ?_
  rw [hcomm]
  exact hreg.comp e.injective

end Module.Flat
