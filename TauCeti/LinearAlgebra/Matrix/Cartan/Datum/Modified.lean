/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Data.Nat.GCD
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Constructions

/-!
# Frobenius orders and the modified Cartan datum

Let `D` be a Cartan datum with weight lattice `X`, coweight lattice `Y` and symmetrizer `d`, and
let `ζ` be an element whose square has order `L`. The element `ζ ^ (2 dᵢ)` then has order
`ℓᵢ = L / gcd(L, dᵢ)`, the *Frobenius order* `TauCeti.CartanDatum.frobeniusOrder` of the node `i`.
Lusztig's quantum Frobenius map at `ζ` lands in the quantum group of a new datum built from
these orders, the *modified datum* `TauCeti.CartanDatum.modified`:

* its weight lattice is `X* = {λ ∈ X : ℓᵢ ∣ ⟨λ, hᵢ⟩ for all i}`
  (`TauCeti.CartanDatum.modifiedWeightLattice`), and its coweight lattice is `Y* = Hom(X*, ℤ)`;
* its simple roots are `αᵢ* = ℓᵢ αᵢ` and its simple coroots are `hᵢ* = ⟨-, hᵢ⟩ / ℓᵢ`
  (`TauCeti.CartanDatum.modifiedCoroot`);
* its Cartan matrix is `aᵢⱼ* = ℓⱼ aᵢⱼ / ℓᵢ` and its symmetrizer is `dᵢ* = ℓᵢ² dᵢ`.

The lattice `X*` contains `L • X`, and restricting coweights to it gives a map `Y → Y*`,
injective for `L ≠ 0`, sending `hᵢ` to `ℓᵢ hᵢ*` (`TauCeti.CartanDatum.restrictCoweight`). As `X`
is reflexive (its pairing with `Y` is perfect) and `X*` contains `L • X`, the lattice `X*` is
reflexive too, with no finiteness assumption, so the evaluation pairing on `(X*, Y*)` is perfect.
The integrality of `aᵢⱼ*`, that is `ℓᵢ ∣ ℓⱼ aᵢⱼ`, uses the symmetrizer
(`TauCeti.CartanDatum.frobeniusOrder_dvd_frobeniusOrder_mul_cartan`). The parameters
`ζ ^ (ℓᵢ² dᵢ)` of the new datum square to `1`, so they are `±1` in a domain. The modified datum
has the same Cartan products `aᵢⱼ aⱼᵢ`, hence the same braid lengths, and its simple reflections
are the restrictions of those of `D`.

The orders only see the symmetrizer up to a common factor: if `dᵢ = c d'ᵢ` then the order of `d`
at `L` and `i` is that of `d'` at `L / gcd(L, c)`, the order of `(ζ ^ c) ^ 2`
(`TauCeti.CartanDatum.frobeniusOrder_eq_of_symmetrizer_eq_mul`). This reduces Frobenius maps for
an arbitrary symmetrizer to the normalized one.

## Main definitions

* `TauCeti.CartanDatum.frobeniusOrder D L i`: the order `ℓᵢ = L / gcd(L, dᵢ)`.
* `TauCeti.CartanDatum.modifiedWeightLattice D L`: the weight lattice `X*`.
* `TauCeti.CartanDatum.modifiedRoot D L i`: the root `αᵢ* = ℓᵢ αᵢ ∈ X*`.
* `TauCeti.CartanDatum.modifiedCoroot D L i`: the coroot `hᵢ* ∈ Hom(X*, ℤ)`.
* `TauCeti.CartanDatum.restrictCoweight D L`: the restriction map `Y → Hom(X*, ℤ)`.
* `TauCeti.CartanDatum.modified D L`: the modified Cartan datum on `(X*, Hom(X*, ℤ))`.

## Main results

* `TauCeti.CartanDatum.isPrimitiveRoot_pow_two_mul_symmetrizer`: if `ζ ^ 2` is a primitive
  `L`-th root of unity, then `ζ ^ (2 dᵢ)` is a primitive `ℓᵢ`-th root of unity.
* `TauCeti.CartanDatum.frobeniusOrder_eq_self_iff`: `ℓᵢ = L` exactly when `L` is coprime to `dᵢ`.
* `TauCeti.CartanDatum.frobeniusOrder_dvd_frobeniusOrder_mul_cartan`: `ℓᵢ ∣ ℓⱼ aᵢⱼ`.
* `TauCeti.CartanDatum.frobeniusOrder_mul_cartan_modified`: `ℓᵢ aᵢⱼ* = ℓⱼ aᵢⱼ`, and
  `TauCeti.CartanDatum.cartan_modified_of_coprime`: `A* = A` when `L` is coprime to every `dᵢ`.
* `TauCeti.CartanDatum.frobeniusOrder_eq_of_symmetrizer_eq_mul`: reduction of the symmetrizer.
* `TauCeti.CartanDatum.modified_symmetrizer`: `dᵢ* = ℓᵢ² dᵢ`.
* `TauCeti.CartanDatum.isReflexive_modifiedWeightLattice`: `X*` is reflexive for `L ≠ 0`.
* `TauCeti.CartanDatum.restrictCoweight_injective`: `Y → Hom(X*, ℤ)` is injective for `L ≠ 0`.
* `TauCeti.CartanDatum.coxeterMatrixOfGeneralizedCartanMatrix_cartan_modified`: the modified datum
  has the braid lengths of `D`.
* `TauCeti.CartanDatum.coe_modified_reflection` and
  `TauCeti.CartanDatum.restrictCoweight_coreflection`: the simple reflections of the modified
  datum are those of `D`.
* `TauCeti.CartanDatum.pow_frobeniusOrder_sq_mul_symmetrizer_eq_one_or_eq_neg_one`: the new
  parameters `ζ ^ (ℓᵢ² dᵢ)` are `±1` in a domain.

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
lemma frobeniusOrder_eq_zero_iff {L : ℕ} {i : ι} : D.frobeniusOrder L i = 0 ↔ L = 0 := by
  refine ⟨fun h ↦ by_contra fun hL ↦ (D.frobeniusOrder_pos hL i).ne' h, ?_⟩
  rintro rfl
  simp [frobeniusOrder]

instance neZero_frobeniusOrder (L : ℕ) [NeZero L] (i : ι) : NeZero (D.frobeniusOrder L i) :=
  ⟨(D.frobeniusOrder_pos (NeZero.ne L) i).ne'⟩

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

/-- The parameter `ζ ^ (ℓᵢ² dᵢ)` of the modified datum squares to `1` when `(ζ ^ 2) ^ L = 1`. -/
lemma pow_frobeniusOrder_sq_mul_symmetrizer_sq_eq_one {M : Type*} [Monoid M] {ζ : M} {L : ℕ}
    (hζ : (ζ ^ 2) ^ L = 1) (i : ι) :
    (ζ ^ (D.frobeniusOrder L i ^ 2 * D.symmetrizer i)) ^ 2 = 1 := by
  have h : D.frobeniusOrder L i ^ 2 * D.symmetrizer i * 2 =
      2 * L * ((D.symmetrizer i / L.gcd (D.symmetrizer i)) * D.frobeniusOrder L i) := by
    rw [sq, mul_assoc (D.frobeniusOrder L i), D.frobeniusOrder_mul_symmetrizer]
    ring
  rw [← pow_mul, h, pow_mul, pow_mul ζ 2 L, hζ, one_pow]

/-- In a domain, the parameter `ζ ^ (ℓᵢ² dᵢ)` of the modified datum is `1` or `-1` when
`(ζ ^ 2) ^ L = 1`. -/
lemma pow_frobeniusOrder_sq_mul_symmetrizer_eq_one_or_eq_neg_one {R : Type*} [Ring R]
    [NoZeroDivisors R] {ζ : R} {L : ℕ} (hζ : (ζ ^ 2) ^ L = 1) (i : ι) :
    ζ ^ (D.frobeniusOrder L i ^ 2 * D.symmetrizer i) = 1 ∨
      ζ ^ (D.frobeniusOrder L i ^ 2 * D.symmetrizer i) = -1 :=
  sq_eq_one_iff.mp (D.pow_frobeniusOrder_sq_mul_symmetrizer_sq_eq_one hζ i)

/-- `ℓᵢ ∣ ℓⱼ aᵢⱼ`: the modified Cartan entry `ℓⱼ aᵢⱼ / ℓᵢ` is an integer. -/
lemma frobeniusOrder_dvd_frobeniusOrder_mul_cartan (L : ℕ) (i j : ι) :
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

/-- **Reduction of the symmetrizer.** If `dᵢ = c d'ᵢ`, the Frobenius order of `d` at `L` and `i`
is that of `d'` at `L / gcd(L, c)`; when `ζ ^ 2` has order `L`, the latter is the order
of `(ζ ^ c) ^ 2`. -/
lemma frobeniusOrder_eq_of_symmetrizer_eq_mul {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} {c : ℕ} {i : ι} (h : D.symmetrizer i = c * D'.symmetrizer i)
    (L : ℕ) :
    D.frobeniusOrder L i = D'.frobeniusOrder (L / L.gcd c) i := by
  rw [frobeniusOrder, frobeniusOrder, h, Nat.div_div_eq_div_mul, Nat.gcd_mul_right_div_gcd]

/-! ### The modified weight lattice -/

/-- The **modified weight lattice** `X* = {λ ∈ X : ℓᵢ ∣ ⟨λ, hᵢ⟩ for all i}`, the kernel of
`X → ∏ᵢ ℤ/ℓᵢ`, `λ ↦ (⟨λ, hᵢ⟩ mod ℓᵢ)ᵢ`. -/
def modifiedWeightLattice (L : ℕ) : Submodule ℤ X where
  carrier := {x | ∀ i, (D.frobeniusOrder L i : ℤ) ∣ D.pairing x (D.coroot i)}
  add_mem' hx hy i := by
    rw [map_add, LinearMap.add_apply]
    exact dvd_add (hx i) (hy i)
  zero_mem' i := by simp
  smul_mem' c x hx i := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hx i) c

@[simp]
lemma mem_modifiedWeightLattice {L : ℕ} {x : X} :
    x ∈ D.modifiedWeightLattice L ↔ ∀ i, (D.frobeniusOrder L i : ℤ) ∣ D.pairing x (D.coroot i) :=
  Iff.rfl

@[simp]
lemma modifiedWeightLattice_one : D.modifiedWeightLattice 1 = ⊤ :=
  eq_top_iff.mpr fun x _ i ↦ by simp

/-- `X*` contains `L • X`. -/
lemma smul_mem_modifiedWeightLattice (L : ℕ) (x : X) :
    L • x ∈ D.modifiedWeightLattice L := fun i ↦ by
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (D.frobeniusOrder_dvd L i)) _

/-- The modified root `αⱼ* = ℓⱼ αⱼ` lies in `X*`, by `ℓᵢ ∣ ℓⱼ aᵢⱼ`. -/
lemma frobeniusOrder_smul_root_mem_modifiedWeightLattice (L : ℕ) (j : ι) :
    D.frobeniusOrder L j • D.root j ∈ D.modifiedWeightLattice L := fun i ↦ by
  rw [map_nsmul, LinearMap.smul_apply, pairing_root_coroot, nsmul_eq_mul]
  exact D.frobeniusOrder_dvd_frobeniusOrder_mul_cartan L i j

/-- The simple reflections preserve `X*`: `sᵢ λ = λ − ⟨λ, hᵢ⟩ αᵢ`, and `ℓⱼ ∣ ℓᵢ aⱼᵢ`. -/
lemma reflection_mem_modifiedWeightLattice {L : ℕ} {x : X} (hx : x ∈ D.modifiedWeightLattice L)
    (i : ι) : D.reflection i x ∈ D.modifiedWeightLattice L := fun j ↦ by
  obtain ⟨m, hm⟩ := hx i
  rw [reflection_apply, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    pairing_root_coroot, hm, smul_eq_mul, mul_right_comm]
  exact dvd_sub (hx j)
    (dvd_mul_of_dvd_left (D.frobeniusOrder_dvd_frobeniusOrder_mul_cartan L j i) _)

/-! ### Modified coroots and the restriction of coweights -/

/-- The **modified coroot** `hᵢ* = ⟨-, hᵢ⟩ / ℓᵢ`, a linear form on `X*`. -/
def modifiedCoroot (L : ℕ) (i : ι) : Dual ℤ (D.modifiedWeightLattice L) where
  toFun x := D.pairing x (D.coroot i) / D.frobeniusOrder L i
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
    exact Int.add_ediv_of_dvd_right (y.property i)
  map_smul' c x := by
    simp only [SetLike.val_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact Int.mul_ediv_assoc _ (x.property i)

lemma modifiedCoroot_apply (L : ℕ) (i : ι) (x : D.modifiedWeightLattice L) :
    D.modifiedCoroot L i x = D.pairing x (D.coroot i) / D.frobeniusOrder L i := (rfl)

/-- `ℓᵢ ⟨λ, hᵢ*⟩ = ⟨λ, hᵢ⟩` for `λ ∈ X*`. -/
lemma frobeniusOrder_mul_modifiedCoroot (L : ℕ) (i : ι) (x : D.modifiedWeightLattice L) :
    D.frobeniusOrder L i * D.modifiedCoroot L i x = D.pairing x (D.coroot i) :=
  Int.mul_ediv_cancel' (x.property i)

/-- The restriction `Y → Hom(X*, ℤ)` of coweights to the modified weight lattice. -/
def restrictCoweight (L : ℕ) : Y →ₗ[ℤ] Dual ℤ (D.modifiedWeightLattice L) :=
  (D.modifiedWeightLattice L).dualRestrict ∘ₗ D.pairing.flip

@[simp]
lemma restrictCoweight_apply (L : ℕ) (y : Y) (x : D.modifiedWeightLattice L) :
    D.restrictCoweight L y x = D.pairing x y := by
  simp [restrictCoweight]

/-- The restriction of `hᵢ` to `X*` is `ℓᵢ hᵢ*`. -/
lemma restrictCoweight_coroot (L : ℕ) (i : ι) :
    D.restrictCoweight L (D.coroot i) = D.frobeniusOrder L i • D.modifiedCoroot L i := by
  ext x
  rw [restrictCoweight_apply, LinearMap.smul_apply, nsmul_eq_mul,
    frobeniusOrder_mul_modifiedCoroot]

/-! ### The modified datum -/

/-- The **modified root** `αⱼ* = ℓⱼ αⱼ`, an element of `X*`. -/
def modifiedRoot (L : ℕ) (j : ι) : D.modifiedWeightLattice L :=
  ⟨D.frobeniusOrder L j • D.root j, D.frobeniusOrder_smul_root_mem_modifiedWeightLattice L j⟩

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
  refine LinearIndependent.of_comp (D.modifiedWeightLattice L).subtype ?_
  have : (D.modifiedWeightLattice L).subtype ∘ D.modifiedRoot L =
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
  let φ : X →ₗ[ℤ] D.modifiedWeightLattice L :=
    ((L : ℤ) • LinearMap.id).codRestrict _ fun x ↦ by
      simpa [natCast_zsmul] using D.smul_mem_modifiedWeightLattice L x
  have hcomp : φ.dualMap ∘ D.modifiedCoroot L =
      (fun i ↦ (L.gcd (D.symmetrizer i) : ℤ)) • (D.pairing.flip ∘ D.coroot) := by
    ext i x
    have hi : (D.frobeniusOrder L i : ℤ) ≠ 0 := by
      exact_mod_cast (D.frobeniusOrder_pos (NeZero.ne L) i).ne'
    have hL : (L : ℤ) = D.frobeniusOrder L i * L.gcd (D.symmetrizer i) := by
      exact_mod_cast (D.frobeniusOrder_mul_gcd L i).symm
    simp [φ, modifiedCoroot_apply, hL, mul_assoc, Int.mul_ediv_cancel_left _ hi]
  refine LinearIndependent.of_comp φ.dualMap ?_
  rw [hcomp]
  refine (D.linearIndependent_coroot.map' D.pairing.flip ?_).smul_of_isRightRegular fun i ↦ ?_
  · exact LinearMap.ker_eq_bot.mpr (LinearMap.IsPerfPair.bijective_right D.pairing).injective
  · exact (IsRegular.of_ne_zero (by exact_mod_cast
      (Nat.gcd_pos_of_pos_right _ (D.symmetrizer_pos i)).ne')).right

/-- The restriction `Y → Hom(X*, ℤ)` is injective for `L ≠ 0`, since `X*` contains `L • X`. -/
lemma restrictCoweight_injective : Function.Injective (D.restrictCoweight L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  refine (LinearMap.IsPerfPair.bijective_right D.pairing).injective (LinearMap.ext fun x ↦ ?_)
  have h := congr($hy ⟨L • x, D.smul_mem_modifiedWeightLattice L x⟩)
  rw [restrictCoweight_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h
  simpa [NeZero.ne L] using h

/-- `X*` is reflexive for `L ≠ 0`. A form `Φ` on `Hom(X*, ℤ)` is evaluation at the weight `x ∈ X`
representing `Φ` composed with restriction: `x` lies in `X*` because `hᵢ` restricts to `ℓᵢ hᵢ*`,
and testing against `f (L • -)` identifies `Φ f` with `f x` after cancelling `L`. -/
instance isReflexive_modifiedWeightLattice : IsReflexive ℤ (D.modifiedWeightLattice L) where
  bijective_dual_eval' := by
    have := IsReflexive.of_isPerfPair D.pairing
    set W := D.modifiedWeightLattice L
    refine ⟨fun x y hxy ↦ Subtype.ext <| (bijective_dual_eval ℤ X).injective <|
      LinearMap.ext fun g ↦ by simpa using congr($hxy (W.dualRestrict g)), fun Φ ↦ ?_⟩
    obtain ⟨x, hx⟩ := (bijective_dual_eval ℤ X).surjective (Φ ∘ₗ W.dualRestrict)
    have hmem : x ∈ W := fun i ↦ ⟨Φ (D.modifiedCoroot L i), by
      have hres :
          W.dualRestrict (D.pairing.flip (D.coroot i)) = D.restrictCoweight L (D.coroot i) :=
        LinearMap.ext fun y ↦ (D.restrictCoweight_apply L _ y).symm
      have := congr($hx (D.pairing.flip (D.coroot i)))
      rw [Dual.eval_apply, LinearMap.flip_apply, LinearMap.comp_apply, hres,
        restrictCoweight_coroot, map_nsmul, nsmul_eq_mul] at this
      exact this⟩
    refine ⟨⟨x, hmem⟩, LinearMap.ext fun f ↦ ?_⟩
    -- Test `Φ` against `f ∘ φ`, where `φ : X → X*` is `x ↦ L • x`.
    let φ : X →ₗ[ℤ] W := (L • LinearMap.id).codRestrict W (D.smul_mem_modifiedWeightLattice L)
    have hφ (y : X) (hy : y ∈ W) : φ y = L • ⟨y, hy⟩ := Subtype.ext (by simp [φ])
    have hres : W.dualRestrict (f ∘ₗ φ) = L • f := LinearMap.ext fun y ↦ by
      rw [Submodule.dualRestrict_apply, LinearMap.comp_apply, hφ _ y.property, map_nsmul,
        LinearMap.smul_apply]
    have := congr($hx (f ∘ₗ φ))
    rw [Dual.eval_apply, LinearMap.comp_apply, LinearMap.comp_apply, hres, map_nsmul, hφ _ hmem,
      map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at this
    rw [Dual.eval_apply]
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L)) this

/-- `⟨αᵢ*, hᵢ*⟩ = 2`. For `simp`, `TauCeti.CartanDatum.modifiedCoroot_modifiedRoot` and
`TauCeti.CartanDatum.cartan_apply_self` already give this. -/
lemma modifiedCoroot_modifiedRoot_self (i : ι) :
    D.modifiedCoroot L i (D.modifiedRoot L i) = 2 := by
  have := D.frobeniusOrder_mul_modifiedCoroot_modifiedRoot L i i
  rw [cartan_apply_self] at this
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne _)) this

/-- The **modified Cartan datum** at `L ≠ 0`: weight lattice `X*`, coweight lattice
`Y* = Hom(X*, ℤ)` with the evaluation pairing, simple roots `αᵢ* = ℓᵢ αᵢ`, simple coroots
`hᵢ* = ⟨-, hᵢ⟩ / ℓᵢ` and symmetrizer `dᵢ* = ℓᵢ² dᵢ`. Its Cartan matrix is `aᵢⱼ* = ℓⱼ aᵢⱼ / ℓᵢ`
(`TauCeti.CartanDatum.frobeniusOrder_mul_cartan_modified`). -/
noncomputable def modified :
    CartanDatum ι (D.modifiedWeightLattice L) (Dual ℤ (D.modifiedWeightLattice L)) :=
  -- `X*` is reflexive (`isReflexive_modifiedWeightLattice`), so the evaluation pairing is perfect.
  { pairing := Dual.eval ℤ _
    root := D.modifiedRoot L
    coroot := D.modifiedCoroot L
    linearIndependent_root := D.linearIndependent_modifiedRoot L
    linearIndependent_coroot := D.linearIndependent_modifiedCoroot L
    pairing_root_coroot_self i := by
      rw [Dual.eval_apply, modifiedCoroot_modifiedRoot_self]
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
lemma modified_pairing_apply (x : D.modifiedWeightLattice L)
    (f : Dual ℤ (D.modifiedWeightLattice L)) :
    (D.modified L).pairing x f = f x :=
  Dual.eval_apply ℤ _ x f

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
  rw [cartan_apply, modified_pairing_apply, modified_root, modified_coroot,
    frobeniusOrder_mul_modifiedCoroot_modifiedRoot]

/-- The Cartan matrix of the modified datum: `aᵢⱼ* = ℓⱼ aᵢⱼ / ℓᵢ`. -/
lemma cartan_modified (i j : ι) :
    (D.modified L).cartan i j = D.frobeniusOrder L j * D.cartan i j / D.frobeniusOrder L i := by
  rw [← frobeniusOrder_mul_cartan_modified, Int.mul_ediv_cancel_left]
  exact_mod_cast (D.frobeniusOrder_pos (NeZero.ne L) i).ne'

/-- `⟨αⱼ*, hᵢ*⟩ = aᵢⱼ*`, so that `simp` reaches the Cartan matrix of the modified datum whether or
not it first unfolds its roots and coroots. -/
@[simp]
lemma modifiedCoroot_modifiedRoot (i j : ι) :
    D.modifiedCoroot L i (D.modifiedRoot L j) = (D.modified L).cartan i j := by
  rw [cartan_apply, modified_pairing_apply, modified_root, modified_coroot]

/-- The Cartan products agree: `aᵢⱼ* aⱼᵢ* = aᵢⱼ aⱼᵢ`. -/
lemma cartan_mul_cartan_modified (i j : ι) :
    (D.modified L).cartan i j * (D.modified L).cartan j i = D.cartan i j * D.cartan j i := by
  have hi := D.frobeniusOrder_mul_cartan_modified L i j
  have hj := D.frobeniusOrder_mul_cartan_modified L j i
  refine mul_left_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne (D.frobeniusOrder L i)))
    (Nat.cast_ne_zero.mpr (NeZero.ne (D.frobeniusOrder L j)))) ?_
  linear_combination (D.frobeniusOrder L j * (D.modified L).cartan j i : ℤ) * hi +
    (D.frobeniusOrder L j * D.cartan i j : ℤ) * hj

/-- The braid lengths of the modified datum are those of `D`: both Coxeter matrices only see the
Cartan products `aᵢⱼ aⱼᵢ`. -/
@[simp]
lemma coxeterMatrixOfGeneralizedCartanMatrix_cartan_modified [DecidableEq ι] :
    coxeterMatrixOfGeneralizedCartanMatrix (D.modified L).cartan =
      coxeterMatrixOfGeneralizedCartanMatrix D.cartan := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ hij,
      coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ hij, cartan_mul_cartan_modified]

/-- The reflections of the modified datum are the restrictions of those of `D`. -/
@[simp]
lemma coe_modified_reflection (i : ι) (x : D.modifiedWeightLattice L) :
    ((D.modified L).reflection i x : X) = D.reflection i x := by
  rw [reflection_apply, reflection_apply, Submodule.coe_sub, Submodule.coe_smul,
    modified_pairing_apply, modified_root, modified_coroot, coe_modifiedRoot, smul_comm,
    ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, frobeniusOrder_mul_modifiedCoroot]

/-- Restricting coweights intertwines the reflections of `D` and of the modified datum. -/
lemma restrictCoweight_coreflection (i : ι) (y : Y) :
    D.restrictCoweight L (D.coreflection i y) =
      (D.modified L).coreflection i (D.restrictCoweight L y) := by
  rw [coreflection_apply, coreflection_apply, map_sub, map_zsmul, restrictCoweight_coroot,
    modified_pairing_apply, modified_root, modified_coroot, restrictCoweight_apply,
    coe_modifiedRoot, map_nsmul, LinearMap.smul_apply, smul_comm, ← Nat.cast_smul_eq_nsmul ℤ,
    smul_smul, nsmul_eq_mul, mul_comm]

/-- The toral directions of the modified datum: `ℓᵢ² dᵢ hᵢ* = ℓᵢ (dᵢ hᵢ)|_{X*}`. -/
lemma modified_simpleTorus (i : ι) :
    (D.modified L).simpleTorus i =
      D.frobeniusOrder L i • D.restrictCoweight L (D.simpleTorus i) := by
  rw [simpleTorus_def, simpleTorus_def, modified_symmetrizer, modified_coroot, map_nsmul,
    restrictCoweight_coroot, smul_smul, smul_smul, sq, mul_right_comm _ (D.symmetrizer i)]

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
