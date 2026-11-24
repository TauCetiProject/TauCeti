/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.PerfectPairing.Prod

/-!
# Extending a root datum by a central rank-one torus

Let `P` be a root datum on character and cocharacter lattices `M` and `N`. This file builds root
data on `M × ℤ` and `N × ℤ`, paired by `⟨(x, a), (y, b)⟩ = ⟨x, y⟩ + a b`, with the same roots and
an extra coordinate on the coroots:

```text
roots  (αᵢ, 0),    coroots  (αᵢ∨, dᵢ).
```

Writing `ε₀` and `ε₀∨` for the new basis vectors `(0, 1)`, the cocharacter `ε₀∨` pairs to zero with
every root, so it is central. The coordinates `dᵢ` are prescribed by a linear form `δ` on `N`
through `2 dᵢ = δ(αᵢ∨)`. This makes `i ↦ (αᵢ∨, dᵢ)` compatible with the reflections, so the
reflections of the extension permute the indices exactly as those of `P` do, and it transfers every
base of `P` to the extension. When `δ = -⟨υ, ·⟩` for a character `υ` of `P`, the character
`υ + 2ε₀` pairs to zero with every coroot of the extension.

When `P` is semisimple, the extension is the root datum of a reductive group `(𝔾_m × G)/μ`, with
`𝔾_m` the image of `ε₀∨`, `G` the derived group of the extension and `μ` a finite central subgroup.
In general `G` is not the semisimple group of `P` but a cover of it, since only the cocharacters
`y` of `P` with `δ(y)` even lift to the cocharacters `(y, δ(y)/2)` of `G`. For the general spin
groups, `P` is the root datum of `SO_{2n+1}` or `SO_{2n}`, while `G` is `Spin_{2n+1}` or
`Spin_{2n}`.

The dual construction `RootPairing.extendRoot` puts the extra coordinate on the roots instead:
roots `(αᵢ, dᵢ)` and coroots `(αᵢ∨, 0)`. It is the flip of `extendCoroot` applied to the flip of
`P`, so the two constructions are dual to one another by definition.

## Main declarations

* `RootPairing.extendPairing`: the pairing of `M × ℤ` with `N × ℤ`, a perfect pairing when the
  pairing of `M` with `N` is; its flip is the extended pairing of the flip
  (`RootPairing.flip_extendPairing`).
* `RootPairing.extendCoroot` and `RootPairing.extendRoot`: the two extensions, dual to one another
  (`RootPairing.flip_extendCoroot`, `RootPairing.flip_extendRoot`).
* `RootPairing.extendCoroot_reflectionPerm`: the extension has the reflection permutations of `P`.
* `RootPairing.extendCoroot_toLinearMap_root_inr`: `ε₀∨` pairs to zero with every root.
* `RootPairing.extendCoroot_toLinearMap_coroot_of_eq_neg`: `υ + 2ε₀` pairs to zero with every
  coroot.
* `RootPairing.Base.extendCoroot` and `RootPairing.Base.extendRoot`: a base of `P` is a base of
  each extension, on the same support.

## References

* M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002), §2, for the
  root datum of the general spin groups as such an extension.
* M. Demazure, A. Grothendieck, *SGA 3*, Exp. XXI, for root data.
-/

public section

open Set Function Module

namespace RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-! ### The extended pairing -/

section Pairing

variable (p : M →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-- The pairing of `M × ℤ` with `N × ℤ` extending `p` orthogonally by the product pairing of `ℤ`:
`⟨(x, a), (y, b)⟩ = p x y + a b`. -/
def extendPairing : (M × ℤ) →ₗ[ℤ] (N × ℤ) →ₗ[ℤ] ℤ :=
  p.compl₁₂ (LinearMap.fst ℤ M ℤ) (LinearMap.fst ℤ N ℤ) +
    (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.snd ℤ M ℤ) (LinearMap.snd ℤ N ℤ)

@[simp]
theorem extendPairing_apply (x : M × ℤ) (y : N × ℤ) :
    extendPairing p x y = p x.1 y.1 + x.2 * y.2 :=
  (rfl)

/-- The flip of the extended pairing is the extended pairing of the flip. -/
@[simp]
theorem flip_extendPairing : (extendPairing p).flip = extendPairing p.flip := by
  ext <;> simp [mul_comm]

/-- The extended pairing is perfect when `p` is. -/
instance [p.IsPerfPair] : (extendPairing p).IsPerfPair :=
  inferInstanceAs (p.compl₁₂ (LinearMap.fst ℤ M ℤ) (LinearMap.fst ℤ N ℤ) +
    (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.snd ℤ M ℤ) (LinearMap.snd ℤ N ℤ)).IsPerfPair

end Pairing

/-! ### The extension on the coroots -/

variable (P : RootDatum ι M N) (δ : N →ₗ[ℤ] ℤ) (δ' : M →ₗ[ℤ] ℤ) (d : ι → ℤ)
  (hd : ∀ i, 2 * d i = δ (P.coroot i))

include hd in
/-- The extra coordinates are compatible with the reflections:
`d (s_i j) = d j - ⟨αᵢ, αⱼ∨⟩ dᵢ`. -/
private theorem extendCoroot_aux (i j : ι) :
    d (P.reflectionPerm i j) = d j - P.pairing i j * d i := by
  have h := hd (P.reflectionPerm i j)
  rw [← P.reflectionPerm_coroot, map_sub, map_smul, smul_eq_mul, ← hd, ← hd,
    RootPairing.root_coroot_eq_pairing] at h
  linarith

/-- The roots `(αᵢ, 0)` of the extension on the coroots. -/
private def extendCorootRoot : ι ↪ M × ℤ :=
  ⟨fun i => (P.root i, 0), fun _ _ h => P.root.injective (Prod.ext_iff.mp h).1⟩

private theorem extendCorootRoot_apply (i : ι) : extendCorootRoot P i = (P.root i, 0) :=
  (rfl)

/-- The coroots `(αᵢ∨, dᵢ)` of the extension on the coroots. -/
private def extendCorootCoroot : ι ↪ N × ℤ :=
  ⟨fun i => (P.coroot i, d i), fun _ _ h => P.coroot.injective (Prod.ext_iff.mp h).1⟩

private theorem extendCorootCoroot_apply (i : ι) :
    extendCorootCoroot P d i = (P.coroot i, d i) :=
  (rfl)

/-- **The extension of a root datum by a central rank-one torus**, with the extra coordinate on
the coroots: roots `(αᵢ, 0)` and coroots `(αᵢ∨, dᵢ)` in `M × ℤ` and `N × ℤ`, where
`2 dᵢ = δ(αᵢ∨)`. -/
def extendCoroot : RootDatum ι (M × ℤ) (N × ℤ) where
  toLinearMap := extendPairing P.toLinearMap
  root := extendCorootRoot P
  coroot := extendCorootCoroot P d
  root_coroot_two i := by
    simp only [extendCorootRoot_apply, extendCorootCoroot_apply, extendPairing_apply, zero_mul,
      add_zero]
    exact P.root_coroot_two i
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    simp only [extendCorootRoot_apply, extendCorootCoroot_apply, extendPairing_apply, zero_mul,
      add_zero]
    ext
    · exact P.reflectionPerm_root i j
    · simp
  reflectionPerm_coroot i j := by
    simp only [extendCorootRoot_apply, extendCorootCoroot_apply, extendPairing_apply, zero_mul,
      add_zero]
    ext
    · exact P.reflectionPerm_coroot i j
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      rw [extendCoroot_aux P δ d hd, RootPairing.root_coroot_eq_pairing]

@[simp]
theorem extendCoroot_toLinearMap :
    (P.extendCoroot δ d hd).toLinearMap = extendPairing P.toLinearMap :=
  (rfl)

@[simp]
theorem extendCoroot_root (i : ι) : (P.extendCoroot δ d hd).root i = (P.root i, 0) :=
  (rfl)

@[simp]
theorem extendCoroot_coroot (i : ι) : (P.extendCoroot δ d hd).coroot i = (P.coroot i, d i) :=
  (rfl)

@[simp]
theorem extendCoroot_reflectionPerm (i : ι) :
    (P.extendCoroot δ d hd).reflectionPerm i = P.reflectionPerm i :=
  (rfl)

/-- The extension has the Cartan integers of `P`. -/
@[simp]
theorem extendCoroot_pairing (i j : ι) :
    (P.extendCoroot δ d hd).pairing i j = P.pairing i j := by
  rw [← RootPairing.root_coroot_eq_pairing, ← RootPairing.root_coroot_eq_pairing,
    extendCoroot_toLinearMap, extendCoroot_root, extendCoroot_coroot, extendPairing_apply,
    zero_mul, add_zero]

/-- **The new cocharacter `ε₀∨ = (0, 1)` is central**: it pairs to zero with every root. -/
theorem extendCoroot_toLinearMap_root_inr (i : ι) :
    (P.extendCoroot δ d hd).toLinearMap ((P.extendCoroot δ d hd).root i) (0, 1) = 0 := by
  simp

/-- **A character orthogonal to every coroot.** If `δ = -⟨υ, ·⟩`, then `υ + 2ε₀` pairs to zero
with every coroot `(αᵢ∨, dᵢ)` of the extension. -/
theorem extendCoroot_toLinearMap_coroot_of_eq_neg {υ : M} (hυ : ∀ y, P.toLinearMap υ y = -δ y)
    (i : ι) :
    (P.extendCoroot δ d hd).toLinearMap (υ, 2) ((P.extendCoroot δ d hd).coroot i) = 0 := by
  rw [extendCoroot_toLinearMap, extendCoroot_coroot, extendPairing_apply, hυ, ← hd]
  ring

/-- A character `(x, a)` pairs with the central cocharacter `ε₀∨` to its `ε₀`-coordinate `a`. -/
theorem extendCoroot_toLinearMap_inr (x : M × ℤ) :
    (P.extendCoroot δ d hd).toLinearMap x (0, 1) = x.2 := by
  simp

/-! ### Bases -/

/-- Every element `(y, e)` of the additive monoid generated by some coroots of the extension
satisfies `2 e = δ(y)`. -/
private theorem two_mul_snd_eq_of_mem_closure (s : Set ι) {z : N × ℤ}
    (hz : z ∈ AddSubmonoid.closure ((P.extendCoroot δ d hd).coroot '' s)) :
    2 * z.2 = δ z.1 := by
  induction hz using AddSubmonoid.closure_induction with
  | mem z hz =>
    obtain ⟨i, -, rfl⟩ := hz
    exact hd i
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Prod.snd_add, Prod.fst_add, map_add, mul_add, hx, hy]

/-- The first projection maps the additive monoid generated by some coroots of the extension onto
the one generated by the same coroots of `P`. -/
private theorem map_fst_closure_extendCoroot_coroot (s : Set ι) :
    (AddSubmonoid.closure ((P.extendCoroot δ d hd).coroot '' s)).map (AddMonoidHom.fst N ℤ) =
      AddSubmonoid.closure (P.coroot '' s) := by
  rw [AddMonoidHom.map_mclosure, ← image_comp]
  exact congrArg AddSubmonoid.closure (image_congr fun i _ => by simp)

/-- The inclusion `x ↦ (x, 0)` maps the additive monoid generated by some roots of `P` onto the
one generated by the same roots of the extension. -/
private theorem map_inl_closure_root (s : Set ι) :
    (AddSubmonoid.closure (P.root '' s)).map (AddMonoidHom.inl M ℤ) =
      AddSubmonoid.closure ((P.extendCoroot δ d hd).root '' s) := by
  rw [AddMonoidHom.map_mclosure, ← image_comp]
  exact congrArg AddSubmonoid.closure (image_congr fun i _ => by simp)

/-- A sum of coroots of `P` lifts to the same sum of coroots of the extension. -/
private theorem mem_closure_extendCoroot_coroot (s : Set ι) {y : N} {e : ℤ}
    (hy : y ∈ AddSubmonoid.closure (P.coroot '' s)) (he : 2 * e = δ y) :
    (y, e) ∈ AddSubmonoid.closure ((P.extendCoroot δ d hd).coroot '' s) := by
  rw [← map_fst_closure_extendCoroot_coroot P δ d hd] at hy
  obtain ⟨z, hz, hzy⟩ := AddSubmonoid.mem_map.mp hy
  rw [AddMonoidHom.coe_fst] at hzy
  have hz2 := two_mul_snd_eq_of_mem_closure P δ d hd s hz
  rw [hzy, ← he] at hz2
  have hze : z.2 = e := by omega
  rwa [← hzy, ← hze]

variable {P} in
/-- **A base of `P` is a base of the extension**, on the same support. -/
def Base.extendCoroot (b : P.Base) : (P.extendCoroot δ d hd).Base where
  support := b.support
  linearIndepOn_root :=
    LinearIndependent.map' b.linearIndepOn_root (LinearMap.inl ℤ M ℤ)
      (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
  linearIndepOn_coroot := LinearIndepOn.of_comp (LinearMap.fst ℤ N ℤ) b.linearIndepOn_coroot
  root_mem_or_neg_mem i := by
    rw [← map_inl_closure_root P δ d hd]
    refine (b.root_mem_or_neg_mem i).imp (fun h => ?_) (fun h => ?_)
    · exact AddSubmonoid.mem_map_of_mem _ h
    · have := AddSubmonoid.mem_map_of_mem (AddMonoidHom.inl M ℤ) h
      simpa using this
  coroot_mem_or_neg_mem i := by
    refine (b.coroot_mem_or_neg_mem i).imp (fun h => ?_) (fun h => ?_)
    · exact mem_closure_extendCoroot_coroot P δ d hd _ h (hd i)
    · have := mem_closure_extendCoroot_coroot P δ d hd _ h (e := -d i) (by rw [map_neg, ← hd]; ring)
      simpa using this

variable {P} in
@[simp]
theorem Base.extendCoroot_support (b : P.Base) : (b.extendCoroot δ d hd).support = b.support :=
  (rfl)

/-! ### The extension on the roots -/

variable (hd' : ∀ i, 2 * d i = δ' (P.root i))

/-- **The extension of a root datum by a central rank-one torus**, with the extra coordinate on
the roots: roots `(αᵢ, dᵢ)` and coroots `(αᵢ∨, 0)` in `M × ℤ` and `N × ℤ`, where
`2 dᵢ = δ'(αᵢ)`. It is the flip of `extendCoroot` applied to the flip of `P`. -/
def extendRoot : RootDatum ι (M × ℤ) (N × ℤ) :=
  (P.flip.extendCoroot δ' d hd').flip

/-- The extension on the roots is the flip of the extension on the coroots of the flip. -/
theorem extendRoot_def : P.extendRoot δ' d hd' = (P.flip.extendCoroot δ' d hd').flip :=
  (rfl)

/-- The extension on the coroots is dual to the extension on the roots of the dual root datum. -/
theorem flip_extendCoroot : (P.extendCoroot δ d hd).flip = P.flip.extendRoot δ d hd :=
  (rfl)

/-- The extension on the roots is dual to the extension on the coroots of the dual root datum. -/
theorem flip_extendRoot : (P.extendRoot δ' d hd').flip = P.flip.extendCoroot δ' d hd' :=
  P.flip.extendCoroot δ' d hd' |>.flip_flip

@[simp]
theorem extendRoot_root (i : ι) : (P.extendRoot δ' d hd').root i = (P.root i, d i) :=
  (rfl)

@[simp]
theorem extendRoot_coroot (i : ι) : (P.extendRoot δ' d hd').coroot i = (P.coroot i, 0) :=
  (rfl)

@[simp]
theorem extendRoot_reflectionPerm (i : ι) :
    (P.extendRoot δ' d hd').reflectionPerm i = P.reflectionPerm i :=
  (rfl)

@[simp]
theorem extendRoot_toLinearMap_apply (x : M × ℤ) (y : N × ℤ) :
    (P.extendRoot δ' d hd').toLinearMap x y = P.toLinearMap x.1 y.1 + x.2 * y.2 := by
  rw [extendRoot_def, flip_toLinearMap, LinearMap.flip_apply]
  exact (LinearMap.congr_fun₂ (extendCoroot_toLinearMap P.flip δ' d hd') y x).trans <| by
    rw [extendPairing_apply, flip_toLinearMap, LinearMap.flip_apply, mul_comm]

/-- The extension on the roots has the Cartan integers of `P`. -/
@[simp]
theorem extendRoot_pairing (i j : ι) : (P.extendRoot δ' d hd').pairing i j = P.pairing i j := by
  rw [← RootPairing.root_coroot_eq_pairing, ← RootPairing.root_coroot_eq_pairing,
    extendRoot_toLinearMap_apply, extendRoot_root, extendRoot_coroot, mul_zero, add_zero]

variable {P} in
/-- A base of `P` is a base of the extension on the roots, on the same support. -/
def Base.extendRoot (b : P.Base) : (P.extendRoot δ' d hd').Base :=
  (b.flip.extendCoroot δ' d hd').flip

variable {P} in
@[simp]
theorem Base.extendRoot_support (b : P.Base) : (b.extendRoot δ' d hd').support = b.support :=
  (rfl)

end RootPairing
