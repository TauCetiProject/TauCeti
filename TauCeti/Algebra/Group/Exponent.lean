/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import TauCeti.Algebra.Group.Coprime

/-!
# Multiplication by a natural number coprime to an exponent

Let `M` be an additive group and `p` a natural number killing every element of `M`. Multiplication
by a natural number `n` coprime to `p` is then **bijective**
(`TauCeti.nsmul_right_bijective_of_coprime`): the Bézout decomposition
`TauCeti.exists_zsmul_add_zsmul_eq_of_coprime` writes every `m` as `i • (n • m) + j • (p • m)`, the
second summand vanishes, and the coefficient `i` is independent of `m`, so `m ↦ i • m` is a
two-sided inverse. No finiteness and no commutativity are involved. Two coprime exponents therefore
leave nothing (`TauCeti.subsingleton_of_forall_nsmul_eq_zero_of_coprime`), so a nontrivial group has
at most one prime exponent (`TauCeti.eq_of_prime_forall_nsmul_eq_zero`).

For a commutative `M` this computes the torsion subgroups and the reductions of `M` at every
natural number at once. Away from the exponent, injectivity makes the torsion subgroup `M[n]` —
Mathlib's `AddSubgroup.torsionBy M (n : ℤ)` — trivial and surjectivity makes `nM = M`, so the
reduction `M / nM` — Mathlib's `ModN M n` — is trivial. At the exponent the two computations are the
opposite ones: `M[p] = ⊤` (`TauCeti.torsionBy_eq_top_of_forall_nsmul_eq_zero`) and `pM = ⊥`, the
latter making the reduction `M` itself (`TauCeti.modNEquiv`).

## Main definitions

* `TauCeti.modNEquiv`: at the exponent, the reduction `M / pM` is `M` again.

## Main results

* `TauCeti.nsmul_right_bijective_of_coprime`: multiplication by a natural number coprime to an
  exponent is bijective, with `TauCeti.subsingleton_of_forall_nsmul_eq_zero_of_coprime` and
  `TauCeti.eq_of_prime_forall_nsmul_eq_zero` the uniqueness consequences.
* `TauCeti.torsionBy_eq_bot_of_coprime`, `TauCeti.subsingleton_modN_of_coprime`: away from the
  exponent both the torsion subgroup and the reduction vanish.
* `TauCeti.torsionBy_eq_top_of_forall_nsmul_eq_zero`,
  `TauCeti.range_lsmul_eq_bot_of_forall_nsmul_eq_zero`: at the exponent itself everything is torsion
  and multiplication is zero.
-/

public section

namespace TauCeti

/-! ### Multiplication by a coprime natural number -/

section AddGroup

variable {M : Type*} [AddGroup M] {p q n : ℕ}

/-- **Multiplication by a natural number coprime to an exponent is bijective.** If `p` kills every
element of `M` and `n` is coprime to `p`, the Bézout decomposition
`TauCeti.exists_zsmul_add_zsmul_eq_of_coprime` exhibits `m ↦ i • m` as a two-sided inverse of
`m ↦ n • m`, because its `p`-multiple summand vanishes.

Mathlib's `Nat.Coprime.nsmul_right_bijective` is the same conclusion from a different hypothesis,
coprimality with `Nat.card M` for a finite `M`. The hypothesis here asks for no finiteness: an
infinite `𝔽_p`-vector space is covered. -/
theorem nsmul_right_bijective_of_coprime (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    Function.Bijective fun m : M ↦ n • m := by
  obtain ⟨i, j, hij⟩ := exists_zsmul_add_zsmul_eq_of_coprime (G := M) h
  have key : ∀ m : M, i • (n • m) = m := fun m ↦ by
    simpa only [hp m, smul_zero, add_zero] using hij m
  refine ⟨fun x y hxy ↦ ?_, fun m ↦ ⟨i • m, ?_⟩⟩
  · simpa only [key] using congrArg (fun z : M ↦ i • z) hxy
  · simpa only [natCast_zsmul, key] using zsmul_comm m i (n : ℤ)

/-- **Two coprime exponents leave nothing.** If coprime naturals `p` and `q` both kill every
element of `M` then `M` is trivial: multiplication by `q` is bijective by
`TauCeti.nsmul_right_bijective_of_coprime` and is also the zero map. -/
theorem subsingleton_of_forall_nsmul_eq_zero_of_coprime (hp : ∀ m : M, p • m = 0)
    (hq : ∀ m : M, q • m = 0) (h : Nat.Coprime p q) : Subsingleton M := by
  have hinj := (nsmul_right_bijective_of_coprime hp h.symm).injective
  refine ⟨fun x y ↦ hinj ?_⟩
  simp only [hq]

/-- **A nontrivial group has at most one prime exponent.** Two primes both killing a nontrivial
group are coprime unless equal, and coprime exponents leave nothing
(`TauCeti.subsingleton_of_forall_nsmul_eq_zero_of_coprime`). -/
theorem eq_of_prime_forall_nsmul_eq_zero [Nontrivial M] (hp : p.Prime) (hq : q.Prime)
    (hp' : ∀ m : M, p • m = 0) (hq' : ∀ m : M, q • m = 0) : p = q := by
  by_contra hne
  exact (not_subsingleton M)
    (subsingleton_of_forall_nsmul_eq_zero_of_coprime hp' hq' ((Nat.coprime_primes hp hq).mpr hne))

end AddGroup

/-! ### Torsion and reduction -/

section Torsion

variable {M : Type*} [AddCommGroup M] {p n : ℕ}

/-- **Away from the exponent there is no torsion.** If `p` kills `M` and `n` is coprime to `p`,
multiplication by `n` is injective, so the `n`-torsion subgroup `M[n]` is trivial. -/
theorem torsionBy_eq_bot_of_coprime (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    AddSubgroup.torsionBy M (n : ℤ) = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun m hm ↦ ?_
  have hinj := (nsmul_right_bijective_of_coprime hp h).injective
  exact hinj (by simpa only [smul_zero] using AddSubgroup.torsionBy.nsmul_iff.mp hm)

/-- **Away from the exponent multiplication is onto.** If `p` kills `M` and `n` is coprime to `p`
then `n M = M`, which is the statement that `TauCeti.subsingleton_modN_of_coprime` quotients by. -/
theorem range_lsmul_eq_top_of_coprime (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    LinearMap.range (LinearMap.lsmul ℤ M (n : ℤ)) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun m ↦ ?_
  obtain ⟨x, hx⟩ := (nsmul_right_bijective_of_coprime hp h).surjective m
  exact ⟨x, by rw [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul]; exact hx⟩

/-- **Away from the exponent the reduction vanishes.** If `p` kills `M` and `n` is coprime to `p`
then `M / nM` — Mathlib's `ModN M n` — is trivial. -/
theorem subsingleton_modN_of_coprime (hp : ∀ m : M, p • m = 0) (h : Nat.Coprime n p) :
    Subsingleton (ModN M n) := by
  obtain ⟨hu⟩ :=
    Submodule.unique_quotient_iff_eq_top.mpr (range_lsmul_eq_top_of_coprime hp h)
  exact @Unique.instSubsingleton _ hu

/-- **At the exponent everything is torsion.** If `p` kills `M` then the `p`-torsion subgroup
`M[p]` — Mathlib's `AddSubgroup.torsionBy M (p : ℤ)` — is everything. -/
theorem torsionBy_eq_top_of_forall_nsmul_eq_zero (hp : ∀ m : M, p • m = 0) :
    AddSubgroup.torsionBy M (p : ℤ) = ⊤ :=
  eq_top_iff.mpr fun m _ ↦ AddSubgroup.torsionBy.nsmul_iff.mpr (hp m)

/-- **At the exponent multiplication is zero.** -/
theorem range_lsmul_eq_bot_of_forall_nsmul_eq_zero (hp : ∀ m : M, p • m = 0) :
    LinearMap.range (LinearMap.lsmul ℤ M (p : ℤ)) = ⊥ := by
  refine LinearMap.range_eq_bot.mpr (LinearMap.ext fun m ↦ ?_)
  rw [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, hp m, LinearMap.zero_apply]

/-- **At the exponent the reduction is the module itself.** Since `pM = 0`, the quotient
`ModN M p = M / pM` is `M`, linearly over `ℤ`. -/
noncomputable def modNEquiv (hp : ∀ m : M, p • m = 0) : ModN M p ≃ₗ[ℤ] M :=
  Submodule.quotEquivOfEqBot _ (range_lsmul_eq_bot_of_forall_nsmul_eq_zero hp)

/-- `TauCeti.modNEquiv` undoes Mathlib's quotient map `ModN.mkQ`. Mathlib's
`Submodule.quotEquivOfEqBot_apply_mk` is this statement for the `Submodule.Quotient.mk` spelling,
which `ModN.mkQ` is definitionally but not syntactically, so it never fires here. -/
@[simp]
theorem modNEquiv_apply_mkQ (hp : ∀ m : M, p • m = 0) (m : M) :
    modNEquiv hp (ModN.mkQ p m) = m :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ m

/-- The inverse of `TauCeti.modNEquiv` is the quotient map `ModN.mkQ`, the `ModN` spelling that
Mathlib's `Submodule.quotEquivOfEqBot_symm_apply` does not match. -/
@[simp]
theorem modNEquiv_symm_apply (hp : ∀ m : M, p • m = 0) (m : M) :
    (modNEquiv hp).symm m = ModN.mkQ p m :=
  Submodule.quotEquivOfEqBot_symm_apply _ _ m

end Torsion

end TauCeti
