/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.Depth.Basic
public import TauCeti.RingTheory.Depth.WeaklyRegular
public import TauCeti.RingTheory.Regular.RegularSequence
public import TauCeti.RingTheory.Flat.QuotSMulTop
public import TauCeti.RingTheory.QuotSMulTop

/-!
# Depth along flat local homomorphisms

Let `R → S` be a local homomorphism of Noetherian local rings, `M` a finite `R`-module and `N` a
finite `S`-module which is flat over `R`. Then the depth of `N ⊗[R] M` over `S` is the depth of
`M` over `R` plus the depth over `S` of the closed fibre `N ⧸ 𝔪_R N`. For `N = S` and `M = R`,
the depth of `S` is the depth of `R` plus the depth of `S ⧸ 𝔪_R S`.

This is the depth half of the dimension and depth formulas for flat local homomorphisms. It is
what makes Cohen–Macaulayness and the conditions `(S_n)` ascend and descend along flat local
homomorphisms with well-behaved closed fibres.

The proof is by induction on the two depths. An `M`-regular element `x ∈ 𝔪_R` stays regular on
`N ⊗[R] M`, since tensoring the injective multiplication by `x` on `M` with the flat module `N`
keeps it injective, and `N ⊗[R] (M ⧸ x M) = (N ⊗[R] M) ⧸ x (N ⊗[R] M)`. When `M` has depth
zero, an element `y ∈ 𝔪_S` regular on the closed fibre is regular on `N ⊗[R] M`, and `N ⧸ y N` is
again flat over `R` (`Module.Flat.quotSMulTop_of_isSMulRegular_quotient`), with closed fibre
`(N ⧸ 𝔪_R N) ⧸ y (N ⧸ 𝔪_R N)`. When both depths vanish, the residue field of `S` embeds in the
closed fibre, which embeds in `N ⊗[R] M` by flatness, so `N ⊗[R] M` has depth zero.

## Main results

* `IsLocalRing.depth_tensorProduct_eq_add_of_flat`:
  `depth (N ⊗[R] M) = depth M + depth (N ⧸ 𝔪_R N)`.
* `IsLocalRing.depth_eq_add_of_flat`: `depth S = depth R + depth (S ⧸ 𝔪_R S)` for a flat local
  homomorphism `R → S`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.3.
* The Stacks Project, Tag 0337, for the ring version.
-/

public section

universe u u' v

open IsLocalRing TensorProduct Pointwise

namespace IsLocalRing

section Depth

variable {S : Type u} [CommRing S] [IsLocalRing S] [Small.{v} S] [IsNoetherianRing S]

section Flat

variable {R : Type u'} [CommRing R] [Algebra R S] [IsLocalRing R] [IsNoetherianRing R]
  [IsLocalHom (algebraMap R S)] [Small.{v} R]
  {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  {M : Type v} [AddCommGroup M] [Module R M]

omit [IsNoetherianRing S] [IsNoetherianRing R] [IsLocalHom (algebraMap R S)] in
/-- If `M` and the closed fibre `N ⧸ 𝔪_R N` have depth zero, so does `N ⊗[R] M`: the residue field
of `S` embeds in the closed fibre `N ⊗[R] κ(R)`, which embeds in `N ⊗[R] M` by flatness. -/
private theorem depth_tensorProduct_eq_zero [Module.Flat R N]
    (hM : depth (ModuleCat.of R M) = 0)
    (hN : depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
      Submodule S N))) = 0) :
    depth (ModuleCat.of S (N ⊗[R] M)) = 0 := by
  rw [depth_eq_zero_iff_nontrivial_linearMap] at hM hN ⊢
  obtain ⟨f, hf⟩ := exists_ne (0 : R ⧸ maximalIdeal R →ₗ[R] M)
  obtain ⟨g, hg⟩ := exists_ne (0 : S ⧸ maximalIdeal S →ₗ[S]
    N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N))
  have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_quot_maximal.2 ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
  have hfi : Function.Injective f := f.injective_or_eq_zero.resolve_right hf
  let e := AlgebraTensorModule.tensorQuotEquivQuotMapSMul (S := S) (N := N) (maximalIdeal R)
  let h := AlgebraTensorModule.lTensor S N f ∘ₗ e.symm.toLinearMap
  have hh : Function.Injective h :=
    (Module.Flat.lTensor_preserves_injective_linearMap f hfi).comp e.symm.injective
  refine nontrivial_of_ne (h ∘ₗ g) 0 fun H ↦ hg (LinearMap.ext fun q ↦ hh ?_)
  simpa using LinearMap.congr_fun H q

/-- When `M` has depth zero, the depth of `N ⊗[R] M` is that of the closed fibre of `N`. The
induction on the depth of the closed fibre divides `N` by an element of `𝔪_S` regular on it. -/
private theorem depth_tensorProduct_eq_of_depth_eq_zero [Module.Finite R M]
    (hM : depth (ModuleCat.of R M) = 0) (e : ℕ) :
    ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
      [Module.Finite S N] [Module.Flat R N],
      depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
        Submodule S N))) = e →
      depth (ModuleCat.of S (N ⊗[R] M)) = e := by
  induction e with
  | zero => exact fun N _ _ _ _ _ _ hN ↦ depth_tensorProduct_eq_zero hM hN
  | succ e ih =>
    intro N _ _ _ _ _ _ hN
    obtain ⟨y, hy, reg⟩ := exists_isSMulRegular_of_depth_ne_zero (R := S) <| by
      rw [hN]
      exact_mod_cast e.succ_ne_zero
    have := Module.Flat.quotSMulTop_of_isSMulRegular_quotient reg
    have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
    have hfib := depth_eq_add_one_of_surjective hy reg _ (QuotSMulTop.mapQ_mkQ_surjective _ y)
      (QuotSMulTop.ker_mapQ_mkQ _ y)
    rw [hN, Nat.cast_succ] at hfib
    rw [depth_eq_add_one_of_surjective hy
      (Module.Flat.isSMulRegular_tensorProduct_of_isSMulRegular_quotient reg M) _
      (AlgebraTensorModule.rTensor_mkQ_surjective _)
      (AlgebraTensorModule.ker_rTensor_mkQ_smul_top y),
      ih (QuotSMulTop y N) (ENat.add_left_injective_of_ne_top ENat.one_ne_top hfib).symm,
      Nat.cast_succ]

/-- The depth formula when both depths are finite, by induction on the depth of `M`, dividing `M`
by an element of `𝔪_R` regular on it. -/
private theorem depth_tensorProduct_eq_add_of_eq [Module.Finite S N] [Module.Flat R N] {e : ℕ}
    (hN : depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
      Submodule S N))) = e) (d : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      depth (ModuleCat.of R M) = d → depth (ModuleCat.of S (N ⊗[R] M)) = d + e := by
  induction d with
  | zero =>
    intro M _ _ _ hM
    rw [Nat.cast_zero, zero_add]
    exact depth_tensorProduct_eq_of_depth_eq_zero hM e N hN
  | succ d ih =>
    intro M _ _ _ hM
    obtain ⟨x, hx, reg⟩ := exists_isSMulRegular_of_depth_ne_zero (R := R) <| by
      rw [hM]
      exact_mod_cast d.succ_ne_zero
    have hM' := depth_quotSMulTop_succ_eq_depth reg hx
    rw [hM, Nat.cast_succ] at hM'
    have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
    rw [depth_eq_add_one_of_surjective (map_maximalIdeal_le _ (Ideal.mem_map_of_mem _ hx))
      (isSMulRegular_algebraMap_iff S |>.mpr (reg.lTensor N)) _
      (AlgebraTensorModule.lTensor_mkQ_surjective _)
      (AlgebraTensorModule.ker_lTensor_mkQ_smul_top x),
      ih (QuotSMulTop x M) (ENat.add_left_injective_of_ne_top ENat.one_ne_top hM'),
      Nat.cast_succ, add_right_comm]

/-- **Depth along a flat local homomorphism.** Let `R → S` be a local homomorphism of Noetherian
local rings, `M` a finite `R`-module and `N` a finite `S`-module which is flat over `R`. Then the
depth of `N ⊗[R] M` over `S` is the depth of `M` over `R` plus the depth over `S` of the closed
fibre `N ⧸ 𝔪_R N`. -/
theorem depth_tensorProduct_eq_add_of_flat [Module.Finite S N] [Module.Flat R N]
    [Module.Finite R M] :
    depth (ModuleCat.of S (N ⊗[R] M)) = depth (ModuleCat.of R M) +
      depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
        Submodule S N))) := by
  have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
  rcases subsingleton_or_nontrivial
    (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)) with hN | hN
  · -- By Nakayama's lemma, `N` vanishes with its closed fibre.
    have : Subsingleton N := by
      by_contra hN'
      rw [not_subsingleton_iff_nontrivial] at hN'
      exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        ((map_maximalIdeal_le _).trans (maximalIdeal_le_jacobson _))
        (Submodule.Quotient.subsingleton_iff.mp hN).symm
    rw [depth_eq_top_of_subsingleton (ModuleCat.of S (N ⊗[R] M)),
      depth_eq_top_of_subsingleton (ModuleCat.of S
        (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N))), add_top]
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [depth_eq_top_of_subsingleton (ModuleCat.of S (N ⊗[R] M)),
      depth_eq_top_of_subsingleton (ModuleCat.of R M), top_add]
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    ((depth_eq_top_iff (ModuleCat.of R M)).not.mpr (not_subsingleton M))
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp
    ((depth_eq_top_iff (ModuleCat.of S
      (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)))).not.mpr
      (not_subsingleton _))
  rw [← hd, ← he]
  exact depth_tensorProduct_eq_add_of_eq he.symm d M hd.symm

end Flat

end Depth

/-- **Depth along a flat local homomorphism of rings.** For a flat local homomorphism `R → S` of
Noetherian local rings, the depth of `S` is the depth of `R` plus the depth of the closed fibre
`S ⧸ 𝔪_R S`, as a module over `S`. -/
@[stacks 0337]
theorem depth_eq_add_of_flat {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    depth (ModuleCat.of S S) = depth (ModuleCat.of R R) +
      depth (ModuleCat.of S (S ⧸ (maximalIdeal R).map (algebraMap R S))) := by
  have h := depth_tensorProduct_eq_add_of_flat (R := R) (S := S) (N := S) (M := R)
  rwa [depth_eq_of_linearEquiv (AlgebraTensorModule.rid R S S),
    depth_eq_of_linearEquiv (Submodule.quotEquivOfEq _ _ (by simp) :
      (S ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S S)) ≃ₗ[S]
        (S ⧸ (maximalIdeal R).map (algebraMap R S)))] at h

end IsLocalRing
