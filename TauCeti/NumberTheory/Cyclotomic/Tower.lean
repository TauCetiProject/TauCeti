/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# The full `p`-power cyclotomic extension `K(μ_{p^∞})`

For a field extension `L/K` and a natural number `p`, `cyclotomicTower p K L` is the subfield of
`L` generated over `K` by the roots of unity of `p`-power order in `L`. It is the increasing
union of the finite levels `K(μ_{p^n}) = K({x | x ^ p ^ n = 1})`.

When `L` contains primitive `p ^ n`-th roots of unity for all `n` (for instance when `L` is
algebraically closed of characteristic different from `p`), it is a cyclotomic extension of `K`
for the powers of `p`, hence abelian Galois over `K`. For a prime `p` its Galois group then embeds
into `ℤ_pˣ` by the `p`-adic cyclotomic character `cyclotomicTowerCharacter`, the fixing subgroup of
`K(μ_{p^∞})` in `Gal(L/K)` is the kernel of the cyclotomic character, and the image of the
embedding is the image of the cyclotomic character of the absolute Galois group of `K`, whatever
`L` is. For a finite extension `K` of `ℚ_p` this image is open.

This is the extension `K_∞` of Tate's normalized traces and of the Tate–Sen calculation of the
Galois cohomology of `ℂ_p`, whose Galois group `Γ_K` is identified with an open subgroup of
`ℤ_pˣ`.

## Main definitions

* `TauCeti.cyclotomicTower p K L`: the intermediate field `K(μ_{p^∞})` of `L/K`.
* `TauCeti.cyclotomicTowerCharacter p K L`: the cyclotomic character
  `Gal(K(μ_{p^∞})/K) →* ℤ_pˣ`.

## Main results

* `TauCeti.mem_cyclotomicTower_of_pow_eq_one`, `TauCeti.cyclotomicTower_le_iff`: `K(μ_{p^∞})` is
  the least intermediate field containing the roots of unity of `p`-power order.
* `TauCeti.apply_mem_cyclotomicTower`: the automorphisms of `L/K` map `K(μ_{p^∞})` into itself.
* `TauCeti.cyclotomicTower_eq_iSup`, `TauCeti.mem_cyclotomicTower_iff`: `K(μ_{p^∞})` is the
  increasing union of the levels `K(μ_{p^n})`.
* `TauCeti.isGalois_cyclotomicTower`, `TauCeti.isAbelianGalois_cyclotomicTower`: `K(μ_{p^∞})` is
  abelian Galois over `K`.
* `TauCeti.cyclotomicTowerCharacter_injective`: the cyclotomic character embeds `Gal(K(μ_{p^∞})/K)`
  into `ℤ_pˣ`.
* `TauCeti.fixingSubgroup_cyclotomicTower`: the automorphisms of `L/K` fixing `K(μ_{p^∞})` form the
  kernel of the cyclotomic character; `TauCeti.apply_eq_of_cyclotomicCharacter_eq_one` is its
  pointwise form.
* `TauCeti.range_cyclotomicTowerCharacter`: the image of `cyclotomicTowerCharacter` is that of the
  cyclotomic character of the absolute Galois group of `K`.
* `TauCeti.isOpen_range_cyclotomicTowerCharacter`: for `K` finite over `ℚ_p` the image is open.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §4.
* O. Brinon and B. Conrad, *CMI summer school notes on `p`-adic Hodge theory*, §1.3.
-/

public section

open IntermediateField

namespace TauCeti

variable (p : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The full `p`-power cyclotomic extension `K(μ_{p^∞})` of `K` inside `L`: the subfield generated
over `K` by the roots of unity of `p`-power order in `L`. -/
noncomputable def cyclotomicTower : IntermediateField K L :=
  adjoin K {x : L | ∃ n : ℕ, x ^ p ^ n = 1}

/-- `K(μ_{p^∞})` is generated over `K` by the roots of unity of `p`-power order. -/
theorem cyclotomicTower_def :
    cyclotomicTower p K L = adjoin K {x : L | ∃ n : ℕ, x ^ p ^ n = 1} :=
  (rfl)

variable {p K L}

/-- A root of unity of `p`-power order lies in `K(μ_{p^∞})`. -/
theorem mem_cyclotomicTower_of_pow_eq_one {x : L} {n : ℕ} (hx : x ^ p ^ n = 1) :
    x ∈ cyclotomicTower p K L :=
  subset_adjoin K _ ⟨n, hx⟩

/-- `K(μ_{p^∞})` is the least intermediate field containing every root of unity of `p`-power
order. -/
theorem cyclotomicTower_le_iff {E : IntermediateField K L} :
    cyclotomicTower p K L ≤ E ↔ ∀ (n : ℕ) (x : L), x ^ p ^ n = 1 → x ∈ E := by
  rw [cyclotomicTower_def, adjoin_le_iff]
  exact ⟨fun h n x hx ↦ h ⟨n, hx⟩, fun h x ⟨n, hx⟩ ↦ h n x hx⟩

/-- Every automorphism of `L/K` maps `K(μ_{p^∞})` into itself. -/
theorem apply_mem_cyclotomicTower (σ : L ≃ₐ[K] L) {x : L} (hx : x ∈ cyclotomicTower p K L) :
    σ x ∈ cyclotomicTower p K L :=
  have h : cyclotomicTower p K L ≤ (cyclotomicTower p K L).comap (σ : L →ₐ[K] L) :=
    cyclotomicTower_le_iff.2 fun n y hy ↦ mem_comap.2 <|
      mem_cyclotomicTower_of_pow_eq_one (n := n) <| by
        rw [AlgEquiv.coe_toAlgHom, ← map_pow, hy, map_one]
  h hx

variable (p K L)

/-- The levels `K(μ_{p^n})` increase with `n`. -/
theorem monotone_adjoin_pow_eq_one : Monotone fun n : ℕ ↦ adjoin K {x : L | x ^ p ^ n = 1} :=
  fun m n hmn ↦ adjoin.mono K _ _ fun x (hx : x ^ p ^ m = 1) ↦ by
    obtain ⟨k, hk⟩ := pow_dvd_pow p hmn
    rw [Set.mem_ofPred_eq, hk, pow_mul, hx, one_pow]

/-- Each level `K(μ_{p^n})` lies in `K(μ_{p^∞})`. -/
theorem adjoin_pow_eq_one_le_cyclotomicTower (n : ℕ) :
    adjoin K {x : L | x ^ p ^ n = 1} ≤ cyclotomicTower p K L :=
  adjoin_le_iff.2 fun _ hx ↦ mem_cyclotomicTower_of_pow_eq_one hx

/-- `K(μ_{p^∞})` is the supremum of the levels `K(μ_{p^n})`. -/
theorem cyclotomicTower_eq_iSup :
    cyclotomicTower p K L = ⨆ n : ℕ, adjoin K {x : L | x ^ p ^ n = 1} := by
  rw [cyclotomicTower_def, ← adjoin_iUnion, Set.ofPred_exists]

/-- `K(μ_{p^∞})` is the increasing union of the levels `K(μ_{p^n})`. -/
theorem coe_cyclotomicTower :
    (cyclotomicTower p K L : Set L) = ⋃ n : ℕ, (adjoin K {x : L | x ^ p ^ n = 1} : Set L) := by
  rw [cyclotomicTower_eq_iSup, coe_iSup_of_directed (monotone_adjoin_pow_eq_one p K L).directed_le]

variable {p K L} in
/-- An element lies in `K(μ_{p^∞})` exactly when it lies in some level `K(μ_{p^n})`. -/
theorem mem_cyclotomicTower_iff {x : L} :
    x ∈ cyclotomicTower p K L ↔ ∃ n : ℕ, x ∈ adjoin K {y : L | y ^ p ^ n = 1} := by
  rw [← SetLike.mem_coe, coe_cyclotomicTower, Set.mem_iUnion]
  simp only [SetLike.mem_coe]

/-- `K(μ_{p^∞})` contains a primitive `p ^ i`-th root of unity when `L` does. -/
instance hasEnoughRootsOfUnity_cyclotomicTower (i : ℕ) [HasEnoughRootsOfUnity L (p ^ i)] :
    HasEnoughRootsOfUnity (cyclotomicTower p K L) (p ^ i) where
  prim :=
    let ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L (p ^ i)
    ⟨⟨ζ, mem_cyclotomicTower_of_pow_eq_one hζ.pow_eq_one⟩,
      hζ.of_map_of_injective (f := (cyclotomicTower p K L).val) Subtype.val_injective⟩
  -- The roots of unity of `K(μ_{p^∞})` form a subgroup of those of `L`, which are cyclic.
  cyc := isCyclic_of_injective (restrictRootsOfUnity (cyclotomicTower p K L).val (p ^ i))
    fun _ _ h ↦ rootsOfUnity.coe_injective <| Subtype.val_injective <| by
      simpa using congrArg (fun u : rootsOfUnity (p ^ i) L ↦ ((u : Lˣ) : L)) h

section Cyclotomic

variable [NeZero p] [∀ i, HasEnoughRootsOfUnity L (p ^ i)]

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- For `p ≠ 0` the generators of `K(μ_{p^∞})` are the roots of unity of order in the set of
powers of `p`, in the form used by `IsCyclotomicExtension`. -/
private theorem setOf_pow_eq_one_eq :
    {x : L | ∃ n : ℕ, x ^ p ^ n = 1} =
      {x : L | ∃ n ∈ Set.range (p ^ · : ℕ → ℕ), n ≠ 0 ∧ x ^ n = 1} := by
  ext x
  simp [NeZero.ne p]

/-- `K(μ_{p^∞})` is a cyclotomic extension of `K` for the set of powers of `p`. -/
instance isCyclotomicExtension_cyclotomicTower :
    IsCyclotomicExtension (Set.range (p ^ · : ℕ → ℕ)) K (cyclotomicTower p K L) := by
  rw [cyclotomicTower_def, setOf_pow_eq_one_eq]
  refine isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot (K := K) (L := L) _ ?_
  rintro _ ⟨i, rfl⟩ -
  exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot L (p ^ i)

/-- `K(μ_{p^∞})` is Galois over `K`. -/
instance isGalois_cyclotomicTower : IsGalois K (cyclotomicTower p K L) :=
  IsCyclotomicExtension.isGalois (Set.range (p ^ · : ℕ → ℕ)) K (cyclotomicTower p K L)

/-- `K(μ_{p^∞})` is abelian Galois over `K`. -/
instance isAbelianGalois_cyclotomicTower : IsAbelianGalois K (cyclotomicTower p K L) :=
  IsCyclotomicExtension.isAbelianGalois (Set.range (p ^ · : ℕ → ℕ)) K _

end Cyclotomic

section Character

variable [Fact p.Prime]

/-- The `p`-adic cyclotomic character of `Gal(K(μ_{p^∞})/K)`, recording the action on the roots
of unity of `p`-power order. -/
noncomputable def cyclotomicTowerCharacter : Gal(cyclotomicTower p K L/K) →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (cyclotomicTower p K L) p).comp
    (MulSemiringAction.toRingAut Gal(cyclotomicTower p K L/K) (cyclotomicTower p K L))

variable {p K L}

/-- `cyclotomicTowerCharacter` is Mathlib's cyclotomic character of the underlying ring
automorphism. -/
@[simp]
theorem cyclotomicTowerCharacter_apply (σ : Gal(cyclotomicTower p K L/K)) :
    cyclotomicTowerCharacter p K L σ =
      cyclotomicCharacter (cyclotomicTower p K L) p σ.toRingEquiv :=
  (rfl)

/-- An automorphism `σ` of `K(μ_{p^∞})` raises each root of unity of order `p ^ n` to the power
`χ(σ) mod p ^ n`. -/
theorem cyclotomicTowerCharacter_spec [∀ i, HasEnoughRootsOfUnity L (p ^ i)]
    (σ : Gal(cyclotomicTower p K L/K)) {n : ℕ} {x : cyclotomicTower p K L} (hx : x ^ p ^ n = 1) :
    σ x = x ^ ((cyclotomicTowerCharacter p K L σ).val.toZModPow n).val :=
  cyclotomicCharacter.spec p σ.toRingEquiv x hx

variable (p K L) in
/-- `cyclotomicTowerCharacter` is continuous for the Krull topology. -/
theorem continuous_cyclotomicTowerCharacter : Continuous (cyclotomicTowerCharacter p K L) :=
  cyclotomicCharacter.continuous p K _

variable (p K L) in
/-- **The cyclotomic character embeds `Gal(K(μ_{p^∞})/K)` into `ℤ_pˣ`.** -/
theorem cyclotomicTowerCharacter_injective [∀ i, HasEnoughRootsOfUnity L (p ^ i)] :
    Function.Injective (cyclotomicTowerCharacter p K L) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine (injective_iff_map_eq_one _).2 fun σ hσ ↦ ?_
  refine IsCyclotomicExtension.algEquiv_eq_of_apply_eq (Set.range (p ^ · : ℕ → ℕ)) K
    (cyclotomicTower p K L) ?_
  rintro _ ⟨n, rfl⟩ -
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (cyclotomicTower p K L) (p ^ n)
  exact ⟨ζ, hζ, (cyclotomicCharacter_eq_one_iff p).1 hσ n ζ hζ.pow_eq_one⟩

/-- The cyclotomic character of the restriction to `K(μ_{p^∞})` of an automorphism of `L/K` is the
cyclotomic character of that automorphism. -/
theorem cyclotomicTowerCharacter_restrictNormalHom [∀ i, HasEnoughRootsOfUnity L (p ^ i)]
    (σ : Gal(L/K)) :
    cyclotomicTowerCharacter p K L (AlgEquiv.restrictNormalHom (cyclotomicTower p K L) σ) =
      cyclotomicCharacter L p σ.toRingEquiv :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (cyclotomicCharacter_eq_of_injective p (f := (cyclotomicTower p K L).val.toRingHom)
    Subtype.val_injective (fun _ t _ ↦ (AlgEquiv.restrictNormalHom_apply _ σ t).symm)
    fun _ i ↦ HasEnoughRootsOfUnity.exists_isPrimitiveRoot _ (p ^ i)).symm

variable (K) in
/-- **The automorphisms of `L/K` fixing `K(μ_{p^∞})` form the kernel of the cyclotomic
character.** -/
theorem fixingSubgroup_cyclotomicTower [∀ i, HasEnoughRootsOfUnity L (p ^ i)] :
    (cyclotomicTower p K L).fixingSubgroup =
      ((cyclotomicCharacter L p).comp (MulSemiringAction.toRingAut Gal(L/K) L)).ker := by
  ext σ
  rw [cyclotomicTower_def]
  exact mem_fixingSubgroup_adjoin_iff_cyclotomicCharacter_eq_one p

/-- An automorphism of `L/K` with trivial cyclotomic character fixes `K(μ_{p^∞})` pointwise. -/
theorem apply_eq_of_cyclotomicCharacter_eq_one [∀ i, HasEnoughRootsOfUnity L (p ^ i)]
    {σ : Gal(L/K)} (hσ : cyclotomicCharacter L p σ.toRingEquiv = 1) {x : L}
    (hx : x ∈ cyclotomicTower p K L) : σ x = x :=
  (mem_fixingSubgroup_iff _ σ).1
    (by rw [fixingSubgroup_cyclotomicTower]; exact MonoidHom.mem_ker.2 hσ) x hx

variable (p K L)

/-- For a normal extension `L/K`, the image of `cyclotomicTowerCharacter` is the image of the
cyclotomic character of `Gal(L/K)`, since every automorphism of `K(μ_{p^∞})` extends to `L`. -/
theorem range_cyclotomicTowerCharacter_eq_of_normal [Normal K L]
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] :
    (cyclotomicTowerCharacter p K L).range =
      ((cyclotomicCharacter L p).comp (MulSemiringAction.toRingAut Gal(L/K) L)).range := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h : (cyclotomicTowerCharacter p K L).comp (AlgEquiv.restrictNormalHom _) =
      (cyclotomicCharacter L p).comp (MulSemiringAction.toRingAut Gal(L/K) L) :=
    MonoidHom.ext fun σ ↦ cyclotomicTowerCharacter_restrictNormalHom σ
  rw [← h, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (AlgEquiv.restrictNormalHom_surjective L), ← MonoidHom.range_eq_map]

/-- **The image of `cyclotomicTowerCharacter` is the image of the cyclotomic character of the
absolute Galois group of `K`**, for every `L` containing all roots of unity of `p`-power order. -/
theorem range_cyclotomicTowerCharacter [∀ i, HasEnoughRootsOfUnity L (p ^ i)] :
    (cyclotomicTowerCharacter p K L).range = (localCyclotomicCharacter p K).range := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- `p` is invertible in `K` since `L` contains a primitive `p`-th root of unity.
  have : NeZero (p : K) := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L (p ^ 1)
    have := (pow_one p ▸ hζ).neZero'
    exact .of_map (algebraMap K L) (neZero := by rwa [map_natCast])
  -- The towers in `L` and in `AlgebraicClosure K` are isomorphic over `K`, so their characters
  -- have equal images.
  obtain ⟨e⟩ := IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_isSepClosed
    (Set.range (p ^ · : ℕ → ℕ)) K (cyclotomicTower p K L) (AlgebraicClosure K)
  let e' : cyclotomicTower p K L ≃ₐ[K] cyclotomicTower p K (AlgebraicClosure K) :=
    e.trans (equivOfEq (by rw [cyclotomicTower_def, setOf_pow_eq_one_eq]))
  have he : (cyclotomicTowerCharacter p K (AlgebraicClosure K)).comp
      (AlgEquiv.autCongr e').toMonoidHom = cyclotomicTowerCharacter p K L :=
    MonoidHom.ext fun σ ↦ cyclotomicCharacter_autCongr p e' σ
  rw [← he, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (AlgEquiv.autCongr e').surjective,
    ← MonoidHom.range_eq_map, range_cyclotomicTowerCharacter_eq_of_normal]
  -- The absolute Galois group of `K` is `Gal(AlgebraicClosure K/K)`.
  exact congrArg MonoidHom.range (MonoidHom.ext fun σ ↦ (localCyclotomicCharacter_apply p K σ).symm)

/-- **For `K` finite over `ℚ_p`, the cyclotomic character identifies `Gal(K(μ_{p^∞})/K)` with an
open subgroup of `ℤ_pˣ`.** -/
theorem isOpen_range_cyclotomicTowerCharacter [∀ i, HasEnoughRootsOfUnity L (p ^ i)]
    [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    IsOpen ((cyclotomicTowerCharacter p K L).range : Set ℤ_[p]ˣ) := by
  rw [range_cyclotomicTowerCharacter]
  exact isOpen_range_localCyclotomicCharacter p K

end Character

end TauCeti
