/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Constructions

/-!
# Frobenius orders and the modified Cartan datum

Let `D` be a Cartan datum with weight lattice `X`, coweight lattice `Y` and symmetrizer `d`, and
let `ζ` be an element whose square has order `L`. The element `ζ ^ (2 dᵢ)` then has order
`ℓᵢ = L / gcd(L, dᵢ)`, the *Frobenius order* `TauCeti.CartanDatum.frobeniusOrder` of the node `i`.
Lusztig's quantum Frobenius map at `ζ` lands in the quantum group of a new datum built from
these orders, the *modified datum* `TauCeti.CartanDatum.modified`:

* its weight lattice is `X* = {λ ∈ X : ℓᵢ ∣ ⟨λ, hᵢ⟩ for all i}`
  (`TauCeti.CartanDatum.modifiedWeight`), and its coweight lattice is `Y* = Hom(X*, ℤ)`;
* its simple roots are `αᵢ* = ℓᵢ αᵢ` and its simple coroots are `hᵢ* = ⟨-, hᵢ⟩ / ℓᵢ`
  (`TauCeti.CartanDatum.modifiedCoroot`);
* its Cartan matrix is `aᵢⱼ* = ℓⱼ aᵢⱼ / ℓᵢ` and its symmetrizer is `dᵢ* = ℓᵢ² dᵢ`.

The lattice `X*` contains `L • X`, and restricting coweights to it gives a map `Y → Y*` sending
`hᵢ` to `ℓᵢ hᵢ*` (`TauCeti.CartanDatum.restrictCoweight`). The integrality of `aᵢⱼ*`, that is
`ℓᵢ ∣ ℓⱼ aᵢⱼ`, uses the symmetrizer (`TauCeti.CartanDatum.frobeniusOrder_dvd_mul_cartan`). The
parameters `ζ ^ (dᵢ ℓᵢ²)` of the new datum square to `1`, so they are `±1` in a domain.

The orders only see the symmetrizer up to a common factor: if `d = c d'` then the orders of `d`
at `L` are those of `d'` at `L / gcd(L, c)`, the order of `(ζ ^ c) ^ 2`
(`TauCeti.CartanDatum.frobeniusOrder_eq_of_symmetrizer_eq_mul`). This reduces Frobenius maps for
an arbitrary symmetrizer to the normalized one.

## Main definitions

* `TauCeti.CartanDatum.frobeniusOrder D L i`: the order `ℓᵢ = L / gcd(L, dᵢ)`.
* `TauCeti.CartanDatum.modifiedWeight D L`: the weight lattice `X*`.
* `TauCeti.CartanDatum.modifiedRoot D L i`: the root `αᵢ* = ℓᵢ αᵢ ∈ X*`.
* `TauCeti.CartanDatum.modifiedCoroot D L i`: the coroot `hᵢ* ∈ Hom(X*, ℤ)`.
* `TauCeti.CartanDatum.restrictCoweight D L`: the restriction map `Y → Hom(X*, ℤ)`.
* `TauCeti.CartanDatum.modified D L`: the modified Cartan datum on `(X*, Hom(X*, ℤ))`.

## Main results

* `TauCeti.CartanDatum.isPrimitiveRoot_pow_two_mul_symmetrizer`: if `ζ ^ 2` is a primitive
  `L`-th root of unity, then `ζ ^ (2 dᵢ)` is a primitive `ℓᵢ`-th root of unity.
* `TauCeti.CartanDatum.frobeniusOrder_eq_self_iff`: `ℓᵢ = L` exactly when `L` is coprime to `dᵢ`.
* `TauCeti.CartanDatum.frobeniusOrder_dvd_mul_cartan`: `ℓᵢ ∣ ℓⱼ aᵢⱼ`.
* `TauCeti.CartanDatum.frobeniusOrder_mul_cartan_modified`: `ℓᵢ aᵢⱼ* = ℓⱼ aᵢⱼ`, and
  `TauCeti.CartanDatum.cartan_modified_of_coprime`: `A* = A` when `L` is coprime to every `dᵢ`.
* `TauCeti.CartanDatum.frobeniusOrder_eq_of_symmetrizer_eq_mul`: reduction of the symmetrizer.
* `TauCeti.CartanDatum.modified_symmetrizer`: `dᵢ* = ℓᵢ² dᵢ`.
* `TauCeti.CartanDatum.pow_symmetrizer_mul_frobeniusOrder_sq_eq_one_or_eq_neg_one`: the new
  parameters `ζ ^ (dᵢ ℓᵢ²)` are `±1` in a domain.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  Chapter 35 (the quantum Frobenius homomorphism and its root datum).
* K. McGerty, *Hall algebras and quantum Frobenius*, arXiv:math/0601150, §2 (the orders `ℓᵢ` and
  the modified datum `i ∘ j = ℓᵢ ℓⱼ (i · j)`).
* S. Lentner, *A Frobenius homomorphism for Lusztig's quantum groups over arbitrary roots of
  unity*, arXiv:1406.0865, Definition 2.3 (the orders `ℓᵢ`).
-/

public section

namespace TauCeti

namespace CartanDatum

open Module

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-! ### Frobenius orders -/

/-- The **Frobenius order** `ℓᵢ = L / gcd(L, dᵢ)` of the node `i` at `L`: the order of
`ζ ^ (2 dᵢ)` when `ζ ^ 2` has order `L`
(`TauCeti.CartanDatum.isPrimitiveRoot_pow_two_mul_symmetrizer`). -/
def frobeniusOrder (L : ℕ) (i : ι) : ℕ :=
  L / L.gcd (D.symmetrizer i)

lemma frobeniusOrder_def (L : ℕ) (i : ι) :
    D.frobeniusOrder L i = L / L.gcd (D.symmetrizer i) := (rfl)

lemma frobeniusOrder_mul_gcd (L : ℕ) (i : ι) :
    D.frobeniusOrder L i * L.gcd (D.symmetrizer i) = L :=
  Nat.div_mul_cancel (L.gcd_dvd_left _)

lemma frobeniusOrder_dvd (L : ℕ) (i : ι) : D.frobeniusOrder L i ∣ L :=
  Nat.div_dvd_of_dvd (L.gcd_dvd_left _)

lemma frobeniusOrder_pos {L : ℕ} (hL : L ≠ 0) (i : ι) : 0 < D.frobeniusOrder L i :=
  Nat.div_pos (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hL)) (Nat.gcd_pos_of_pos_right _
    (D.symmetrizer_pos i))

@[simp]
lemma frobeniusOrder_zero (i : ι) : D.frobeniusOrder 0 i = 0 := by
  simp [frobeniusOrder]

@[simp]
lemma frobeniusOrder_one (i : ι) : D.frobeniusOrder 1 i = 1 := by
  simp [frobeniusOrder]

/-- `ℓᵢ dᵢ = L (dᵢ / gcd(L, dᵢ))`: the product `ℓᵢ dᵢ` is a multiple of `L`. -/
lemma frobeniusOrder_mul_symmetrizer (L : ℕ) (i : ι) :
    D.frobeniusOrder L i * D.symmetrizer i = L * (D.symmetrizer i / L.gcd (D.symmetrizer i)) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_right L (D.symmetrizer_pos i))
  rw [mul_right_comm, frobeniusOrder_mul_gcd, mul_assoc, Nat.div_mul_cancel (L.gcd_dvd_right _)]

/-- `ℓᵢ = L` exactly when `L` is coprime to `dᵢ`, for `L ≠ 0`. -/
lemma frobeniusOrder_eq_self_iff {L : ℕ} (hL : L ≠ 0) (i : ι) :
    D.frobeniusOrder L i = L ↔ L.Coprime (D.symmetrizer i) := by
  rw [frobeniusOrder, Nat.div_eq_self, Nat.Coprime]
  simp [hL]

/-- If `L` is coprime to `dᵢ`, then `ℓᵢ = L`. -/
lemma frobeniusOrder_of_coprime {L : ℕ} {i : ι} (h : L.Coprime (D.symmetrizer i)) :
    D.frobeniusOrder L i = L := by
  rw [frobeniusOrder, h.gcd_eq_one, Nat.div_one]

/-- If `ζ ^ 2` is a primitive `L`-th root of unity, then `ζ ^ (2 dᵢ)` is a primitive `ℓᵢ`-th root
of unity. -/
lemma isPrimitiveRoot_pow_two_mul_symmetrizer {M : Type*} [CommMonoid M] {ζ : M} {L : ℕ}
    (hζ : IsPrimitiveRoot (ζ ^ 2) L) (i : ι) :
    IsPrimitiveRoot (ζ ^ (2 * D.symmetrizer i)) (D.frobeniusOrder L i) := by
  rw [pow_mul]
  exact hζ.pow_div_gcd _ (Nat.gcd_pos_of_pos_right _ (D.symmetrizer_pos i)).ne'

/-- The parameter `ζ ^ (dᵢ ℓᵢ²)` of the modified datum squares to `1` when `(ζ ^ 2) ^ L = 1`. -/
lemma pow_symmetrizer_mul_frobeniusOrder_sq_sq_eq_one {M : Type*} [Monoid M] {ζ : M} {L : ℕ}
    (hζ : (ζ ^ 2) ^ L = 1) (i : ι) :
    (ζ ^ (D.symmetrizer i * D.frobeniusOrder L i ^ 2)) ^ 2 = 1 := by
  have h : D.symmetrizer i * D.frobeniusOrder L i ^ 2 * 2 =
      2 * L * ((D.symmetrizer i / L.gcd (D.symmetrizer i)) * D.frobeniusOrder L i) := by
    rw [sq, ← mul_assoc, mul_comm (D.symmetrizer i), D.frobeniusOrder_mul_symmetrizer]
    ring
  rw [← pow_mul, h, pow_mul, pow_mul ζ 2 L, hζ, one_pow]

/-- In a domain, the parameter `ζ ^ (dᵢ ℓᵢ²)` of the modified datum is `1` or `-1` when
`(ζ ^ 2) ^ L = 1`. -/
lemma pow_symmetrizer_mul_frobeniusOrder_sq_eq_one_or_eq_neg_one {R : Type*} [Ring R]
    [NoZeroDivisors R] {ζ : R} {L : ℕ} (hζ : (ζ ^ 2) ^ L = 1) (i : ι) :
    ζ ^ (D.symmetrizer i * D.frobeniusOrder L i ^ 2) = 1 ∨
      ζ ^ (D.symmetrizer i * D.frobeniusOrder L i ^ 2) = -1 :=
  sq_eq_one_iff.mp (D.pow_symmetrizer_mul_frobeniusOrder_sq_sq_eq_one hζ i)

/-- `ℓᵢ ∣ ℓⱼ aᵢⱼ`: the modified Cartan entry `ℓⱼ aᵢⱼ / ℓᵢ` is an integer. -/
lemma frobeniusOrder_dvd_mul_cartan (L : ℕ) (i j : ι) :
    (D.frobeniusOrder L i : ℤ) ∣ D.frobeniusOrder L j * D.cartan i j := by
  set gi := L.gcd (D.symmetrizer i)
  set gj := L.gcd (D.symmetrizer j)
  -- `gcd(L, dⱼ)` divides `gcd(L, dᵢ) aᵢⱼ = L aᵢⱼ x + dᵢ aᵢⱼ y` (Bézout), because
  -- `dᵢ aᵢⱼ = dⱼ aⱼᵢ`; then multiply by `ℓᵢ ℓⱼ` and use `ℓᵢ gcd(L, dᵢ) = L = ℓⱼ gcd(L, dⱼ)`.
  obtain ⟨k, hk⟩ : (gj : ℤ) ∣ gi * D.cartan i j := by
    rw [Nat.gcd_eq_gcd_ab L (D.symmetrizer i), add_mul, mul_assoc, mul_right_comm,
      D.symmetrizer_mul_cartan]
    refine dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (L.gcd_dvd_left _)) _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (Int.natCast_dvd_natCast.mpr (L.gcd_dvd_right _)) _) _)
  refine ⟨k, mul_right_cancel₀ (b := (gi : ℤ))
    (Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_right _ (D.symmetrizer_pos i)).ne') ?_⟩
  have hi : (D.frobeniusOrder L i : ℤ) * gi = L := by exact_mod_cast D.frobeniusOrder_mul_gcd L i
  have hj : (D.frobeniusOrder L j : ℤ) * gj = L := by exact_mod_cast D.frobeniusOrder_mul_gcd L j
  linear_combination (D.frobeniusOrder L j : ℤ) * hk + k * hj - k * hi

/-- **Reduction of the symmetrizer.** If `dᵢ = c d'ᵢ` for every `i`, the Frobenius orders of `d`
at `L` are those of `d'` at `L / gcd(L, c)`; when `ζ ^ 2` has order `L`, the latter is the order
of `(ζ ^ c) ^ 2`. -/
lemma frobeniusOrder_eq_of_symmetrizer_eq_mul {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} {c : ℕ} (h : ∀ i, D.symmetrizer i = c * D'.symmetrizer i)
    (L : ℕ) (i : ι) :
    D.frobeniusOrder L i = D'.frobeniusOrder (L / L.gcd c) i := by
  rw [frobeniusOrder, frobeniusOrder, h, Nat.div_div_eq_div_mul]
  congr 1
  -- `gcd(L, c d') = gcd(L, c) gcd(L', d')` with `L = gcd(L, c) L'`, since `L'` is coprime to
  -- `c / gcd(L, c)`.
  rcases Nat.eq_zero_or_pos (L.gcd c) with hg | hg
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hg
    simp
  obtain ⟨L', hL'⟩ := L.gcd_dvd_left c
  obtain ⟨c', hc'⟩ := L.gcd_dvd_right c
  have hL'' : L / L.gcd c = L' := Nat.div_eq_of_eq_mul_right hg hL'
  have hcop : L'.Coprime c' := by
    simpa [hL'', Nat.div_eq_of_eq_mul_right hg hc'] using Nat.coprime_div_gcd_div_gcd hg
  rw [hL'']
  calc L.gcd (c * D'.symmetrizer i)
      = (L.gcd c * L').gcd (L.gcd c * (c' * D'.symmetrizer i)) := by
        rw [← hL', ← mul_assoc, ← hc']
    _ = L.gcd c * L'.gcd (D'.symmetrizer i) := by
        rw [Nat.gcd_mul_left, hcop.symm.gcd_mul_left_cancel_right]

/-! ### The modified weight lattice -/

/-- The **modified weight lattice** `X* = {λ ∈ X : ℓᵢ ∣ ⟨λ, hᵢ⟩ for all i}`, the kernel of
`X → ∏ᵢ ℤ/ℓᵢ`, `λ ↦ (⟨λ, hᵢ⟩ mod ℓᵢ)ᵢ`. -/
def modifiedWeight (L : ℕ) : Submodule ℤ X where
  carrier := {x | ∀ i, (D.frobeniusOrder L i : ℤ) ∣ D.pairing x (D.coroot i)}
  add_mem' hx hy i := by
    rw [map_add, LinearMap.add_apply]
    exact dvd_add (hx i) (hy i)
  zero_mem' i := by simp
  smul_mem' c x hx i := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hx i) c

@[simp]
lemma mem_modifiedWeight {L : ℕ} {x : X} :
    x ∈ D.modifiedWeight L ↔ ∀ i, (D.frobeniusOrder L i : ℤ) ∣ D.pairing x (D.coroot i) :=
  Iff.rfl

/-- `X*` contains `L • X`. -/
lemma smul_mem_modifiedWeight (L : ℕ) (x : X) : L • x ∈ D.modifiedWeight L := fun i ↦ by
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (D.frobeniusOrder_dvd L i)) _

/-- The modified root `αⱼ* = ℓⱼ αⱼ` lies in `X*`, by `ℓᵢ ∣ ℓⱼ aᵢⱼ`. -/
lemma frobeniusOrder_smul_root_mem_modifiedWeight (L : ℕ) (j : ι) :
    D.frobeniusOrder L j • D.root j ∈ D.modifiedWeight L := fun i ↦ by
  rw [map_nsmul, LinearMap.smul_apply, pairing_root_coroot, nsmul_eq_mul]
  exact D.frobeniusOrder_dvd_mul_cartan L i j

/-! ### Modified coroots and the restriction of coweights -/

/-- The **modified coroot** `hᵢ* = ⟨-, hᵢ⟩ / ℓᵢ`, a linear form on `X*`. -/
def modifiedCoroot (L : ℕ) (i : ι) : Dual ℤ (D.modifiedWeight L) where
  toFun x := D.pairing x (D.coroot i) / D.frobeniusOrder L i
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
    exact Int.add_ediv_of_dvd_right (y.2 i)
  map_smul' c x := by
    simp only [SetLike.val_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact Int.mul_ediv_assoc _ (x.2 i)

lemma modifiedCoroot_apply (L : ℕ) (i : ι) (x : D.modifiedWeight L) :
    D.modifiedCoroot L i x = D.pairing x (D.coroot i) / D.frobeniusOrder L i := (rfl)

/-- `ℓᵢ ⟨λ, hᵢ*⟩ = ⟨λ, hᵢ⟩` for `λ ∈ X*`. -/
lemma frobeniusOrder_mul_modifiedCoroot (L : ℕ) (i : ι) (x : D.modifiedWeight L) :
    D.frobeniusOrder L i * D.modifiedCoroot L i x = D.pairing x (D.coroot i) :=
  Int.mul_ediv_cancel' (x.2 i)

/-- The restriction `Y → Hom(X*, ℤ)` of coweights to the modified weight lattice. -/
def restrictCoweight (L : ℕ) : Y →ₗ[ℤ] Dual ℤ (D.modifiedWeight L) :=
  (D.modifiedWeight L).dualRestrict ∘ₗ D.pairing.flip

@[simp]
lemma restrictCoweight_apply (L : ℕ) (y : Y) (x : D.modifiedWeight L) :
    D.restrictCoweight L y x = D.pairing x y := (rfl)

/-- The restriction of `hᵢ` to `X*` is `ℓᵢ hᵢ*`. -/
lemma restrictCoweight_coroot (L : ℕ) (i : ι) :
    D.restrictCoweight L (D.coroot i) = D.frobeniusOrder L i • D.modifiedCoroot L i := by
  ext x
  rw [restrictCoweight_apply, LinearMap.smul_apply, nsmul_eq_mul,
    frobeniusOrder_mul_modifiedCoroot]

/-! ### The modified datum -/

/-- The **modified root** `αⱼ* = ℓⱼ αⱼ`, an element of `X*`. -/
def modifiedRoot (L : ℕ) (j : ι) : D.modifiedWeight L :=
  ⟨D.frobeniusOrder L j • D.root j, D.frobeniusOrder_smul_root_mem_modifiedWeight L j⟩

@[simp]
lemma coe_modifiedRoot (L : ℕ) (j : ι) :
    (D.modifiedRoot L j : X) = D.frobeniusOrder L j • D.root j := (rfl)

/-- `ℓᵢ ⟨αⱼ*, hᵢ*⟩ = ℓⱼ aᵢⱼ`. -/
lemma frobeniusOrder_mul_modifiedCoroot_modifiedRoot (L : ℕ) (i j : ι) :
    D.frobeniusOrder L i * D.modifiedCoroot L i (D.modifiedRoot L j) =
      D.frobeniusOrder L j * D.cartan i j := by
  rw [frobeniusOrder_mul_modifiedCoroot, coe_modifiedRoot, map_nsmul, LinearMap.smul_apply,
    pairing_root_coroot, nsmul_eq_mul]

variable (L : ℕ) [NeZero L]

/-- The modified roots `αᵢ* = ℓᵢ αᵢ` are linearly independent. -/
lemma linearIndependent_modifiedRoot : LinearIndependent ℤ (D.modifiedRoot L) := by
  refine LinearIndependent.of_comp (D.modifiedWeight L).subtype ?_
  have : (D.modifiedWeight L).subtype ∘ D.modifiedRoot L =
      (fun j ↦ (D.frobeniusOrder L j : ℤ)) • D.root := by
    ext j
    simp
  rw [this]
  exact D.linearIndependent_root.smul_of_isRightRegular fun j ↦
    (IsRegular.of_ne_zero (by exact_mod_cast (D.frobeniusOrder_pos (NeZero.ne L) j).ne')).right

/-- The modified coroots `hᵢ* = ⟨-, hᵢ⟩ / ℓᵢ` are linearly independent. -/
lemma linearIndependent_modifiedCoroot : LinearIndependent ℤ (D.modifiedCoroot L) := by
  -- Precomposing with `φ : x ↦ L • x` sends `hᵢ*` to `gcd(L, dᵢ) ⟨-, hᵢ⟩`, and the forms
  -- `⟨-, hᵢ⟩` on `X` are independent because the pairing is perfect.
  let φ : X →ₗ[ℤ] D.modifiedWeight L :=
    ((L : ℤ) • LinearMap.id).codRestrict _ fun x ↦ by
      simpa [natCast_zsmul] using D.smul_mem_modifiedWeight L x
  have hcomp : φ.dualMap ∘ D.modifiedCoroot L =
      (fun i ↦ (L.gcd (D.symmetrizer i) : ℤ)) • (D.pairing.flip ∘ D.coroot) := by
    ext i x
    have hi : (D.frobeniusOrder L i : ℤ) ≠ 0 := by
      exact_mod_cast (D.frobeniusOrder_pos (NeZero.ne L) i).ne'
    have hL : (L : ℤ) = D.frobeniusOrder L i * L.gcd (D.symmetrizer i) := by
      exact_mod_cast (D.frobeniusOrder_mul_gcd L i).symm
    have hφ : (φ x : X) = (L : ℤ) • x := (rfl)
    rw [Function.comp_apply, LinearMap.dualMap_apply, modifiedCoroot_apply, hφ, map_zsmul,
      LinearMap.smul_apply, smul_eq_mul, hL, mul_assoc, Int.mul_ediv_cancel_left _ hi]
    simp
  refine LinearIndependent.of_comp φ.dualMap ?_
  rw [hcomp]
  refine (D.linearIndependent_coroot.map' D.pairing.flip ?_).smul_of_isRightRegular fun i ↦ ?_
  · exact LinearMap.ker_eq_bot.mpr (LinearMap.IsPerfPair.bijective_right D.pairing).injective
  · exact (IsRegular.of_ne_zero (by exact_mod_cast
      (Nat.gcd_pos_of_pos_right _ (D.symmetrizer_pos i)).ne')).right

variable [Module.Finite ℤ X]

/-- The **modified Cartan datum** at `L ≠ 0`: weight lattice `X*`, coweight lattice
`Y* = Hom(X*, ℤ)` with the evaluation pairing, simple roots `αᵢ* = ℓᵢ αᵢ`, simple coroots
`hᵢ* = ⟨-, hᵢ⟩ / ℓᵢ` and symmetrizer `dᵢ* = ℓᵢ² dᵢ`. Its Cartan matrix is `aᵢⱼ* = ℓⱼ aᵢⱼ / ℓᵢ`
(`TauCeti.CartanDatum.frobeniusOrder_mul_cartan_modified`). -/
noncomputable def modified : CartanDatum ι (D.modifiedWeight L) (Dual ℤ (D.modifiedWeight L)) :=
  -- `X` embeds in `Hom(Y, ℤ)`, so it is torsion-free; being finite, its sublattice `X*` is then
  -- free of finite rank, hence reflexive, which makes the evaluation pairing perfect.
  haveI : IsTorsionFree ℤ X := Function.Injective.moduleIsTorsionFree D.pairing
    (LinearMap.IsPerfPair.bijective_left D.pairing).injective (map_smul D.pairing)
  { pairing := Dual.eval ℤ _
    root := D.modifiedRoot L
    coroot := D.modifiedCoroot L
    linearIndependent_root := D.linearIndependent_modifiedRoot L
    linearIndependent_coroot := D.linearIndependent_modifiedCoroot L
    pairing_root_coroot_self i := by
      have hi : (D.frobeniusOrder L i : ℤ) ≠ 0 := by
        exact_mod_cast (D.frobeniusOrder_pos (NeZero.ne L) i).ne'
      have := D.frobeniusOrder_mul_modifiedCoroot_modifiedRoot L i i
      rw [cartan_apply_self] at this
      rw [Dual.eval_apply]
      exact mul_left_cancel₀ hi this
    pairing_root_coroot_nonpos {i j} hij := by
      have hi : (0 : ℤ) < D.frobeniusOrder L i := by
        exact_mod_cast D.frobeniusOrder_pos (NeZero.ne L) i
      have h := D.frobeniusOrder_mul_modifiedCoroot_modifiedRoot L i j
      have : (D.frobeniusOrder L j : ℤ) * D.cartan i j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (D.cartan_nonpos hij)
      simp only [Dual.eval_apply]
      nlinarith
    symmetrizer i := D.frobeniusOrder L i ^ 2 * D.symmetrizer i
    symmetrizer_pos i := Nat.mul_pos (pow_pos (D.frobeniusOrder_pos (NeZero.ne L) i) 2)
      (D.symmetrizer_pos i)
    symmetrizer_mul_pairing i j := by
      simp only [Dual.eval_apply]
      have hi := D.frobeniusOrder_mul_modifiedCoroot_modifiedRoot L i j
      have hj := D.frobeniusOrder_mul_modifiedCoroot_modifiedRoot L j i
      have hs := D.symmetrizer_mul_cartan i j
      push_cast
      linear_combination (D.frobeniusOrder L i * D.symmetrizer i : ℤ) * hi -
        (D.frobeniusOrder L j * D.symmetrizer j : ℤ) * hj +
        (D.frobeniusOrder L i * D.frobeniusOrder L j : ℤ) * hs }

@[simp]
lemma modified_pairing (x : D.modifiedWeight L) (f : Dual ℤ (D.modifiedWeight L)) :
    (D.modified L).pairing x f = f x := (rfl)

@[simp]
lemma modified_root : (D.modified L).root = D.modifiedRoot L := (rfl)

@[simp]
lemma modified_coroot : (D.modified L).coroot = D.modifiedCoroot L := (rfl)

@[simp]
lemma modified_symmetrizer (i : ι) :
    (D.modified L).symmetrizer i = D.frobeniusOrder L i ^ 2 * D.symmetrizer i := (rfl)

/-- The Cartan matrix of the modified datum: `ℓᵢ aᵢⱼ* = ℓⱼ aᵢⱼ`. -/
lemma frobeniusOrder_mul_cartan_modified (i j : ι) :
    D.frobeniusOrder L i * (D.modified L).cartan i j = D.frobeniusOrder L j * D.cartan i j := by
  rw [cartan_apply, modified_pairing, modified_root, modified_coroot,
    frobeniusOrder_mul_modifiedCoroot_modifiedRoot]

/-- The Cartan matrix of the modified datum: `aᵢⱼ* = ℓⱼ aᵢⱼ / ℓᵢ`. -/
lemma cartan_modified (i j : ι) :
    (D.modified L).cartan i j = D.frobeniusOrder L j * D.cartan i j / D.frobeniusOrder L i := by
  rw [← frobeniusOrder_mul_cartan_modified, Int.mul_ediv_cancel_left]
  exact_mod_cast (D.frobeniusOrder_pos (NeZero.ne L) i).ne'

/-- If `L` is coprime to every `dᵢ`, then every `ℓᵢ` is `L` and the modified datum has the same
Cartan matrix as `D`. -/
lemma cartan_modified_of_coprime (h : ∀ i, L.Coprime (D.symmetrizer i)) :
    (D.modified L).cartan = D.cartan := by
  ext i j
  rw [cartan_modified, D.frobeniusOrder_of_coprime (h i), D.frobeniusOrder_of_coprime (h j),
    Int.mul_ediv_cancel_left]
  exact_mod_cast NeZero.ne L

/-! ### Checks -/

section Checks

/-- `G₂` with `a₁₂ = −3`, `a₂₁ = −1` and symmetrizer `(1, 3)` at `L = 3`: the Frobenius orders are
`(3, 1)`, not the uniform `3`, the modified Cartan matrix is the dual `G₂` matrix
`[[2, −1], [−3, 2]]`, and the modified symmetrizer is `(9, 3)`. -/
example :
    let D := simplyConnected !![2, -3; -1, 2] ![1, 3] (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two])
      (by simp [Matrix.det_fin_two_of])
    D.frobeniusOrder 3 0 = 3 ∧ D.frobeniusOrder 3 1 = 1 ∧
      (D.modified 3).cartan = !![2, -1; -3, 2] ∧ (D.modified 3).symmetrizer = ![9, 3] := by
  intro D
  have h0 : D.frobeniusOrder 3 0 = 3 := by simp [D, frobeniusOrder_def]
  have h1 : D.frobeniusOrder 3 1 = 1 := by simp [D, frobeniusOrder_def]
  refine ⟨h0, h1, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cartan_modified, h0, h1, D]
  · ext i
    fin_cases i <;> simp [h0, h1, D]

/-- `B₂` with `a₁₂ = −2`, `a₂₁ = −1` and symmetrizer `(1, 2)` at `L = 2`: the Frobenius orders
are `(2, 1)` and the modified Cartan matrix `[[2, −1], [−2, 2]]` is of the dual type `C₂`. -/
example :
    let D := simplyConnected !![2, -2; -1, 2] ![1, 2] (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two])
      (by simp [Matrix.det_fin_two_of])
    (D.modified 2).cartan = !![2, -1; -2, 2] := by
  intro D
  have h0 : D.frobeniusOrder 2 0 = 2 := by simp [D, frobeniusOrder_def]
  have h1 : D.frobeniusOrder 2 1 = 1 := by simp [D, frobeniusOrder_def]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cartan_modified, h0, h1, D]

end Checks

end CartanDatum

end TauCeti
