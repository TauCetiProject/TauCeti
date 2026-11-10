/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Quotient.Basic
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Iterated adic completion

Let `I` and `J` be ideals of a commutative ring `R` and `M` an `R`-module. The `I`-adic completion
of the `J`-adic completion `M̂_J` maps canonically to the `(I ⊔ J)`-adic completion of `M`
(`AdicCompletion.iteratedToSup`): at level `n`, a class in `M̂_J ⧸ Iⁿ M̂_J` is sent to the image of
its `n`-th `J`-adic component in `M ⧸ (I ⊔ J)ⁿ M`.

For `I = (p)` principal, this map is an isomorphism as soon as `p` is regular on `M ⧸ Jᵐ M` for
every `m` (`AdicCompletion.iteratedEquivSup`). No Noetherian or finite-generation hypothesis is
needed. The two inputs are the following.

* Membership in `pⁿ M̂_J` is detected levelwise: if every component of `c ∈ M̂_J` is divisible by
  `pⁿ` in `M ⧸ Jᵐ M`, then `c` is divisible by `pⁿ` in `M̂_J`, since the quotients are unique
  (`AdicCompletion.exists_eq_smul_of_forall_exists_val_eq_smul`). Hence `pⁿ M̂_J` is the kernel
  of the maps `M̂_J → M ⧸ (pⁿ M + Jᵐ M)`, and the canonical map is injective.
* Every compatible system of classes modulo `pⁿ M + Jᵐ M` lifts to `M̂_J`: the differences of
  consecutive terms split into a part in `pⁿ M`, which is discarded, and a part in `Jᵐ M`, which
  is summed `J`-adically. Since `(I ⊔ J)ⁿ⁺ᵐ ≤ Iⁿ ⊔ Jᵐ`, the canonical map is surjective.

For a weakly regular pair `(p, v)` on `M`, the element `p` is regular on every `M ⧸ vᵐ M`
(`RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotient_pow_smul_top`), so the `p`-adic
completion of the `(v)`-adic completion of `M` is its `(p, v)`-adic completion, the ideal
`(p) ⊔ (v)` being `(p, v)` by `Ideal.span_insert`. For `v = v₁` on a chart of the moduli of
elliptic curves, this identifies the `p`-adically completed `v₁`-adic completion appearing in the
localization–completion square of `TauCeti.RingTheory.AdicCompletion.Fracture` with the
`(p, v₁)`-adic completion, the supersingular coefficients.

## Main definitions

* `AdicCompletion.iteratedToSup`: the canonical map from the `I`-adic completion of the
  `J`-adic completion to the `(I ⊔ J)`-adic completion.
* `AdicCompletion.iteratedEquivSup`: for `p` regular modulo every power of `J`, the canonical map
  for `I = (p)` as a linear equivalence.

## Main results

* `AdicCompletion.exists_eq_smul_of_forall_exists_val_eq_smul`: divisibility by an element regular
  modulo every `Jᵐ M` is detected on the components of the `J`-adic completion.
* `AdicCompletion.iteratedToSup_bijective`: the canonical map is bijective for `I = (p)`.
* `AdicCompletion.iteratedToSup_of_of`: the canonical map restricts to the identity of `M`.

## References

* Douglas–Francis–Henriques–Hill, *Topological Modular Forms*, Chapter 12, §8, for the
  `(p, v₁)`-adic completion as the supersingular coefficients.
-/

public noncomputable section

open Submodule

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The level-`n` component of the canonical map, on the `J`-adic completion. -/
private def iteratedToSupAux (n : ℕ) :
    AdicCompletion J M →ₗ[R] M ⧸ ((I ⊔ J) ^ n • ⊤ : Submodule R M) :=
  factor (smul_mono_left (Ideal.pow_right_mono le_sup_right n)) ∘ₗ eval J M n

private theorem le_ker_iteratedToSupAux (n : ℕ) :
    (I ^ n • ⊤ : Submodule R (AdicCompletion J M)) ≤
      LinearMap.ker (iteratedToSupAux I J M n) :=
  smul_le.2 fun r hr c _ ↦ by
    rw [LinearMap.mem_ker, map_smul]
    exact Module.isTorsionBySet_quotient_ideal_smul M ((I ⊔ J) ^ n)
      (a := ⟨r, Ideal.pow_right_mono le_sup_left n hr⟩)

/-- The level-`n` component of the canonical map, on `M̂_J ⧸ Iⁿ M̂_J`. -/
private def iteratedToSupQuot (n : ℕ) :
    AdicCompletion J M ⧸ (I ^ n • ⊤ : Submodule R (AdicCompletion J M)) →ₗ[R]
      M ⧸ ((I ⊔ J) ^ n • ⊤ : Submodule R M) :=
  (I ^ n • ⊤ : Submodule R (AdicCompletion J M)).liftQ (iteratedToSupAux I J M n)
    (le_ker_iteratedToSupAux I J M n)

private theorem iteratedToSupQuot_mk (n : ℕ) (c : AdicCompletion J M) :
    iteratedToSupQuot I J M n (Submodule.Quotient.mk c) =
      factor (smul_mono_left (Ideal.pow_right_mono le_sup_right n)) (c.val n) :=
  rfl

private theorem transitionMap_iteratedToSupQuot {m n : ℕ} (hmn : m ≤ n)
    (q : AdicCompletion J M ⧸ (I ^ n • ⊤ : Submodule R (AdicCompletion J M))) :
    transitionMap (I ⊔ J) M hmn (iteratedToSupQuot I J M n q) =
      iteratedToSupQuot I J M m (transitionMap I (AdicCompletion J M) hmn q) := by
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (c.val n)
    have hm : c.val m = Submodule.Quotient.mk a := by
      rw [← c.prop hmn, ← ha, transitionMap, mapQ_apply, LinearMap.id_apply]
    simp only [transitionMap, mapQ_apply, LinearMap.id_apply, iteratedToSupQuot_mk, ← ha, hm]

/-- The canonical map from the `I`-adic completion of the `J`-adic completion of `M` to the
`(I ⊔ J)`-adic completion of `M`. At level `n` it sends the class of `c ∈ M̂_J` modulo `Iⁿ M̂_J`
to the image of the `n`-th component of `c` in `M ⧸ (I ⊔ J)ⁿ M`. -/
def iteratedToSup : AdicCompletion I (AdicCompletion J M) →ₗ[R] AdicCompletion (I ⊔ J) M :=
  lift (I ⊔ J) (fun n ↦ iteratedToSupQuot I J M n ∘ₗ eval I (AdicCompletion J M) n)
    fun {m n} hmn ↦ LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, transitionMap_iteratedToSupQuot, eval_apply]
      congr 1
      exact x.prop hmn

/-- The `n`-th component of the image of `x` under `AdicCompletion.iteratedToSup` is the image of
the `n`-th component of `c` whenever `c ∈ M̂_J` represents the `n`-th component of `x`. -/
theorem iteratedToSup_val {n : ℕ} {x : AdicCompletion I (AdicCompletion J M)}
    {c : AdicCompletion J M} (hc : x.val n = Submodule.Quotient.mk c) :
    (iteratedToSup I J M x).val n =
      factor (smul_mono_left (Ideal.pow_right_mono le_sup_right n)) (c.val n) := by
  -- the components of a map built with `AdicCompletion.lift` are its defining family
  calc (iteratedToSup I J M x).val n = iteratedToSupQuot I J M n (x.val n) := rfl
    _ = _ := by rw [hc, iteratedToSupQuot_mk]

/-- The canonical map restricts to the identity on `M`. -/
@[simp]
theorem iteratedToSup_of_of (a : M) :
    iteratedToSup I J M (of I (AdicCompletion J M) (of J M a)) = of (I ⊔ J) M a := by
  ext n
  rw [iteratedToSup_val I J M (c := of J M a) (of_apply _ _ _ n), of_apply, of_apply, mkQ_apply,
    mkQ_apply, mapQ_apply, LinearMap.id_apply]

variable {I J M}

variable (M) in
/-- **The iterated completion is the completion at the sum.** If `p` is regular on `M ⧸ Jᵐ M` for
every `m`, the canonical map from the `p`-adic completion of the `J`-adic completion of `M` to the
`((p) ⊔ J)`-adic completion of `M` is bijective. -/
theorem iteratedToSup_bijective {p : R}
    (hp : ∀ m : ℕ, IsSMulRegular (M ⧸ (J ^ m • ⊤ : Submodule R M)) p) :
    Function.Bijective (iteratedToSup (Ideal.span {p}) J M) := by
  set I := Ideal.span {p}
  have hle (n m : ℕ) : ((I ⊔ J) ^ (n + m) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ ⊔ J ^ m • ⊤ :=
    (smul_mono_left (Ideal.sup_pow_add_le_pow_sup_pow)).trans (sup_smul _ _ _).le
  constructor
  · -- Injectivity: a class `c` in the kernel at level `n` dies modulo every `pⁿ M + Jᵐ M`.
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ext fun n ↦ ?_
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [val_zero_apply, ← hc, Submodule.Quotient.mk_eq_zero]
    refine (mem_span_singleton_pow_smul_top_iff hp).2 fun m ↦ ?_
    obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + m))
    -- `c' ≡ c` modulo `pⁿ M̂_J`
    have hcc' : c' - c ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion J M)) := by
      rw [← Submodule.Quotient.eq, hc, ← x.prop (Nat.le_add_right n m), ← hc']
      rw [transitionMap, mapQ_apply, LinearMap.id_apply]
    -- and the image of `c'` vanishes at level `n + m`.
    have h0 := iteratedToSup_val I J M hc'.symm
    rw [hx, val_zero_apply] at h0
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (c'.val (n + m))
    rw [← ha, mapQ_apply, LinearMap.id_apply, eq_comm, Submodule.Quotient.mk_eq_zero] at h0
    have hc'm : c'.val m = Submodule.Quotient.mk a := by
      rw [← c'.prop (Nat.le_add_right m n |>.trans_eq (Nat.add_comm m n)), ← ha, transitionMap,
        mapQ_apply, LinearMap.id_apply]
    have h1 := factor_val_eq_zero_of_mem hcc' m
    rw [val_sub_apply, map_sub, hc'm, mapQ_apply, LinearMap.id_apply,
      (Submodule.Quotient.mk_eq_zero _).2 (hle n m h0), zero_sub, neg_eq_zero] at h1
    exact h1
  · -- Surjectivity: lift the classes of a Cauchy sequence modulo `pⁿ M + Jᵐ M` level by level.
    intro y
    obtain ⟨t, rfl⟩ := mk_surjective (I ⊔ J) M y
    have hts (n m : ℕ) :
        t (n + m) ≡ t (n + (m + 1)) [SMOD (I ^ n • ⊤ ⊔ J ^ m • ⊤ : Submodule R M)] :=
      SModEq.mono (hle n m) (t.prop (Nat.le_succ _))
    choose c hc using fun n ↦ exists_forall_factor_val_eq n (fun m ↦ t (n + m)) (hts n)
    -- Consecutive lifts agree modulo `pⁿ M̂_J`.
    let g : AdicCauchySequence I (AdicCompletion J M) := AdicCauchySequence.mk I _ c fun n ↦ by
      rw [SModEq.sub_mem]
      refine (mem_span_singleton_pow_smul_top_iff hp).2 fun m ↦ ?_
      have hn1 := congrArg (factor (sup_le_sup_right
        (smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) _)) (hc (n + 1) m)
      rw [factor_comp_apply, mapQ_apply, LinearMap.id_apply] at hn1
      rw [val_sub_apply, map_sub, hc n m, hn1, sub_eq_zero, Submodule.Quotient.eq,
        show n + 1 + m = n + (m + 1) by omega]
      exact SModEq.sub_mem.1 (hts n m)
    refine ⟨mk I _ g, ext fun n ↦ ?_⟩
    rw [iteratedToSup_val I J M (c := c n) rfl]
    have h2 := congrArg (factor (sup_le (smul_mono_left (Ideal.pow_right_mono le_sup_left n))
      (smul_mono_left (Ideal.pow_right_mono le_sup_right n)))) (hc n n)
    rw [factor_comp_apply, mapQ_apply, LinearMap.id_apply] at h2
    rw [h2, mk_apply_coe, mkQ_apply, Submodule.Quotient.eq]
    exact SModEq.sub_mem.1 (t.prop (Nat.le_add_right n n)).symm

variable (M) in
/-- **The iterated completion is the completion at the sum.** If `p` is regular on `M ⧸ Jᵐ M` for
every `m`, the `p`-adic completion of the `J`-adic completion of `M` is the `((p) ⊔ J)`-adic
completion of `M`, by the canonical map `AdicCompletion.iteratedToSup`. -/
def iteratedEquivSup {p : R}
    (hp : ∀ m : ℕ, IsSMulRegular (M ⧸ (J ^ m • ⊤ : Submodule R M)) p) :
    AdicCompletion (Ideal.span {p}) (AdicCompletion J M) ≃ₗ[R]
      AdicCompletion (Ideal.span {p} ⊔ J) M :=
  LinearEquiv.ofBijective _ (iteratedToSup_bijective M hp)

@[simp]
theorem iteratedEquivSup_apply {p : R}
    (hp : ∀ m : ℕ, IsSMulRegular (M ⧸ (J ^ m • ⊤ : Submodule R M)) p)
    (x : AdicCompletion (Ideal.span {p}) (AdicCompletion J M)) :
    iteratedEquivSup M hp x = iteratedToSup (Ideal.span {p}) J M x :=
  (rfl)

end AdicCompletion
