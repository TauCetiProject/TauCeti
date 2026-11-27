/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.ZMod.Basic
import TauCeti.LinearAlgebra.Dual.Divisibility

/-!
# Reduction modulo `n` of an integral pairing

Let `B : M × N → ℤ` be a bilinear pairing of abelian groups. Reducing its values modulo `n`
gives a pairing `M / nM × N → ℤ / n`, since `B (n x) y = n B x y` vanishes modulo `n`
(`ModN.pairing`). If `B` identifies `M` with the dual `Hom(N, ℤ)` of a free abelian group `N`, the
reduced pairing identifies `M / nM` with `Hom(N, ℤ / n)` (`ModN.pairingEquiv`): every homomorphism
`N → ℤ / n` lifts along a basis of `N` to a homomorphism `N → ℤ`, which is `B x` for some `x`, and
if `B x` has all its values divisible by `n` then `B x = n B x'` for some `x'`, so `x = n x'`.
This is the extension of scalars of `B` to `ℤ / n` (`LinearMap.isPerfPair_baseChangePairing`),
stated on `M / nM` and on the homomorphisms to `ℤ / n` rather than on tensor products.

For `n = 2` and the intersection pairing of a closed oriented surface `C` on `M = N = H₁(C; ℤ)`
this identifies the classes in `H₁(C; ℤ / 2)` with the homomorphisms `H₁(C; ℤ) → ℤ / 2`, which
are the real flat line bundles of `C`: a class is sent to the homomorphism counting
intersections with it modulo two.

## Main definitions

* `ModN.pairing n B`: the pairing `M / nM × N → ℤ / n` induced by `B`.
* `ModN.pairingEquiv n B hB`: for `B` bijective onto the dual of a free `N`, the identification
  `M / nM ≃ Hom(N, ℤ / n)`.
-/

public section

open Module

namespace ModN

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] (n : ℕ)

/-- The **reduction modulo `n`** of a pairing `B : M × N → ℤ`: the class of `x` in `M / nM`
pairs with `y` to `B x y` modulo `n` (`ModN.pairing_mkQ_apply`). -/
noncomputable def pairing (B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ) : ModN M n →+ N →+ ZMod n :=
  ModN.liftEquiv.symm
    ⟨{ toFun x := (Int.castAddHom (ZMod n)).comp (B x).toAddMonoidHom
       map_zero' := by ext; simp
       map_add' x y := by ext; simp },
     fun x ↦ by ext; simp⟩

@[simp]
theorem pairing_mkQ_apply (B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ) (x : M) (y : N) :
    pairing n B (mkQ n x) y = (B x y : ZMod n) := (rfl)

@[simp]
theorem pairing_mk_apply (B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ) (x : M) (y : N) :
    pairing n B (Submodule.Quotient.mk x : ModN M n) y = (B x y : ZMod n) := (rfl)

variable {n}

/-- If `B` identifies `M` with the dual of `N`, the reduction modulo `n ≠ 0` of `B` is injective:
a vector all of whose pairings are divisible by `n` is a multiple of `n`. -/
theorem injective_pairing [NeZero n] {B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ} (hB : Function.Bijective B) :
    Function.Injective (pairing n B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with | H x => ?_
  have hdvd : ∀ y, (n : ℤ) ∣ B x y := fun y ↦ by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact DFunLike.congr_fun hx y
  obtain ⟨g, hg⟩ := LinearMap.exists_smul_eq_of_forall_dvd
    (IsRegular.of_ne_zero (Int.natCast_ne_zero.2 (NeZero.ne n))).left hdvd
  obtain ⟨x', rfl⟩ := hB.2 g
  have hx' : x = (n : ℤ) • x' := hB.1 (by rw [map_zsmul, hg])
  refine (QuotientAddGroup.eq_zero_iff _).2 ⟨x', ?_⟩
  simp [hx']

/-- If `N` is free, the reduction modulo `n` of a pairing `B` with `B` onto the dual of `N` is
surjective: every homomorphism `N → ℤ / n` lifts along a basis of `N` to a homomorphism `N → ℤ`,
which is `B x` for some `x`. -/
theorem surjective_pairing [Module.Free ℤ N] {B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ}
    (hB : Function.Surjective B) : Function.Surjective (pairing n B) := by
  intro χ
  let b := Module.Free.chooseBasis ℤ N
  choose c hc using fun i ↦ ZMod.intCast_surjective (χ (b i))
  obtain ⟨x, hx⟩ := hB (b.constr ℤ c)
  refine ⟨mkQ n x, ?_⟩
  -- Both sides are additive in `y` and agree on the basis `b`.
  refine AddMonoidHom.toIntLinearMap_injective (b.ext fun i ↦ ?_)
  simp [hx, hc]

/-- If `N` is free and `B` identifies `M` with the dual of `N`, the reduction modulo `n ≠ 0` of
`B` identifies `M / nM` with the homomorphisms `N → ℤ / n`. -/
theorem bijective_pairing [NeZero n] [Module.Free ℤ N] {B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ}
    (hB : Function.Bijective B) : Function.Bijective (pairing n B) :=
  ⟨injective_pairing hB, surjective_pairing hB.2⟩

variable (n) in
/-- For a free `N` and a pairing `B : M × N → ℤ` identifying `M` with the dual of `N`, the
identification of `M / nM` with the homomorphisms `N → ℤ / n` given by reducing `B` modulo `n`. -/
noncomputable def pairingEquiv [NeZero n] [Module.Free ℤ N] (B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ)
    (hB : Function.Bijective B) : ModN M n ≃+ (N →+ ZMod n) :=
  AddEquiv.ofBijective (pairing n B) (bijective_pairing hB)

@[simp]
theorem coe_pairingEquiv [NeZero n] [Module.Free ℤ N] (B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ)
    (hB : Function.Bijective B) : ⇑(pairingEquiv n B hB) = pairing n B := (rfl)

end ModN
