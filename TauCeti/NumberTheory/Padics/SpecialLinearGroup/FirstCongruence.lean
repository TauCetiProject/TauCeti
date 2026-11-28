/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.Matrix.SpecialLinearGroup
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Lift

/-!
# The first congruence subgroup of `SL_n(ℤ_p)`

The **first congruence subgroup** `G₁ = ker(SL_n(ℤ_p) → SL_n(𝔽_p))` is the kernel of reduction
modulo `p`, equivalently the subgroup `SL_n(ℤ_p) ∩ (1 + p M_n(ℤ_p))` of matrices congruent to the
identity modulo `p`. For `n = 2` and `p` odd it is the group whose Iwasawa algebra `ℤ_p[[G₁]]`
and its microlocalisation appear in Ardakov–Wadsley's semisimplicity theorem for
finite-dimensional Iwasawa modules and in Fu's injectivity theorem for central specialisations;
there the group `G = G₁^m` is the product of `m` copies of it.

This file sets up these groups as compact open normal subgroups of `SL_n(ℤ_p)` and, for finite
`ι`, of `SL_n(ℤ_p)^ι`, and computes their indices: reduction modulo `p` is surjective on `SL_n`,
since `ℤ_p` is local, so `[SL_n(ℤ_p) : G₁] = |SL_n(𝔽_p)|`, which is `p(p² - 1)` for `n = 2`. As
compact topological groups, `G₁` and `G₁^ι` are the groups whose completed group algebras
`TauCeti.completedGroupAlgebra ℤ_[p] G₁` are the Iwasawa algebras above.

## Main definitions

* `TauCeti.firstCongruenceSubgroup n p`: the kernel `G₁` of reduction modulo `p` on
  `SL n ℤ_[p]`.
* `TauCeti.firstCongruenceProduct n p ι`: the product `G₁^ι ≤ SL_n(ℤ_p)^ι`, as `Subgroup.pi`.
* `TauCeti.firstCongruenceProduct.continuousMulEquivPi`: `G₁^ι`, with its topology as a subgroup
  of the product `SL_n(ℤ_p)^ι`, is the product of copies of `G₁`.

## Main results

* `TauCeti.ker_specialLinearGroupMap_toZMod`,
  `TauCeti.mem_firstCongruenceSubgroup_iff_map_eq_one`: `G₁` is the kernel of reduction modulo
  `p`.
* `TauCeti.mem_firstCongruenceSubgroup_iff`: `g ∈ G₁` exactly when `p` divides every entry of
  `g - 1`; `TauCeti.transvection_mem_firstCongruenceSubgroup_iff`: an elementary transvection
  is in `G₁` exactly when its off-diagonal coefficient is divisible by `p`.
* `TauCeti.isOpen_firstCongruenceSubgroup`, `TauCeti.isClosed_firstCongruenceSubgroup` and the
  instances `CompactSpace (firstCongruenceSubgroup n p)` and
  `(firstCongruenceSubgroup n p).Normal`: `G₁` is a compact open normal subgroup.
* `TauCeti.exists_setOf_pow_dvd_sub_one_subset`: every neighbourhood of `1` in `SL_n(ℤ_p)`, for
  instance an open subgroup, contains all matrices congruent to the identity modulo some power of
  `p`.
* `TauCeti.firstCongruenceSubgroupQuotientEquiv`: reduction gives `SL_n(ℤ_p) / G₁ ≃* SL_n(𝔽_p)`.
* `TauCeti.index_firstCongruenceSubgroup`: `[SL_n(ℤ_p) : G₁] = |SL_n(𝔽_p)|`;
  `TauCeti.index_firstCongruenceSubgroup_fin_two`: `[SL₂(ℤ_p) : G₁] = p(p² - 1)`.
* `TauCeti.ker_compLeft_specialLinearGroupMap_toZMod`: `G₁^ι` is the kernel of reduction
  modulo `p` on `SL_n(ℤ_p)^ι`; `TauCeti.isOpen_firstCongruenceProduct` (for finite `ι`),
  `TauCeti.isClosed_firstCongruenceProduct`, `TauCeti.index_firstCongruenceProduct` and the
  compactness and normality instances.
* `TauCeti.neg_one_mem_firstCongruenceSubgroup_iff`: `-1 ∈ G₁ ≤ SL₂(ℤ_p)` exactly when `p = 2`;
  so for `p = 2` the group `G₁` has an element of order two.

## References

* K. Ardakov and S. Wadsley, *On irreducible representations of compact `p`-adic analytic
  groups*, Ann. of Math. (2) 178 (2013), 453–557, §10 (microlocalisation) and §11.1,
  Theorem (a) (semisimplicity).
* W. Fu, *Sharp bounds for multiplicities of Bianchi modular forms*, Ann. of Math. (2) 200
  (2024), 123–152, §1 (before Theorem 1.4) and §5 (before Lemma 5.6).
-/

public section

open Matrix PadicInt

namespace TauCeti

variable (n : Type*) [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]

/-! ### The first congruence subgroup -/

/-- The **first congruence subgroup** `G₁` of `SL_n(ℤ_p)`: the kernel of reduction modulo `p`,
`SL_n(ℤ_p) → SL_n(𝔽_p)`, that is the determinant-one matrices congruent to the identity
modulo `p` (`mem_firstCongruenceSubgroup_iff`). For `n = Fin 2` this is the group `G₁` of
Ardakov–Wadsley and Fu. -/
noncomputable def firstCongruenceSubgroup : Subgroup (SpecialLinearGroup n ℤ_[p]) :=
  (SpecialLinearGroup.map (toZMod (p := p))).ker

/-- The first congruence subgroup is the kernel of reduction modulo `p`. -/
theorem ker_specialLinearGroupMap_toZMod :
    (SpecialLinearGroup.map (n := n) (toZMod (p := p))).ker = firstCongruenceSubgroup n p :=
  (rfl)

variable {n p}

/-- A determinant-one matrix lies in the first congruence subgroup exactly when it reduces to the
identity modulo `p`. -/
theorem mem_firstCongruenceSubgroup_iff_map_eq_one {g : SpecialLinearGroup n ℤ_[p]} :
    g ∈ firstCongruenceSubgroup n p ↔ SpecialLinearGroup.map toZMod g = 1 := by
  rw [← ker_specialLinearGroupMap_toZMod, MonoidHom.mem_ker]

/-- A determinant-one matrix `g` lies in the first congruence subgroup exactly when `p` divides
every entry of `g - 1`. -/
theorem mem_firstCongruenceSubgroup_iff {g : SpecialLinearGroup n ℤ_[p]} :
    g ∈ firstCongruenceSubgroup n p ↔
      ∀ i j, (p : ℤ_[p]) ∣ ((g : Matrix n n ℤ_[p]) - 1) i j := by
  rw [mem_firstCongruenceSubgroup_iff_map_eq_one, SpecialLinearGroup.ext_iff]
  refine forall₂_congr fun i j ↦ ?_
  rcases eq_or_ne i j with rfl | hij <;> simp [← toZMod_eq_zero_iff_dvd, sub_eq_zero, *]

/-- An elementary transvection is in the first congruence subgroup exactly when its
off-diagonal coefficient is divisible by `p`. -/
@[simp]
theorem transvection_mem_firstCongruenceSubgroup_iff {i j : n} (hij : i ≠ j) (a : ℤ_[p]) :
    SpecialLinearGroup.transvection hij a ∈ firstCongruenceSubgroup n p ↔ (p : ℤ_[p]) ∣ a := by
  rw [mem_firstCongruenceSubgroup_iff, SpecialLinearGroup.transvection_coe, add_sub_cancel_left]
  refine ⟨fun h ↦ by simpa using h i j, fun h k l ↦ ?_⟩
  by_cases hkl : i = k ∧ j = l <;> simp [hkl, h]

variable (n p)

instance : (firstCongruenceSubgroup n p).Normal :=
  ker_specialLinearGroupMap_toZMod n p ▸ MonoidHom.normal_ker _

/-- The first congruence subgroup is open: it is the preimage of `1` under the continuous
reduction to the discrete group `SL_n(𝔽_p)`. -/
theorem isOpen_firstCongruenceSubgroup :
    IsOpen (firstCongruenceSubgroup n p : Set (SpecialLinearGroup n ℤ_[p])) := by
  rw [← ker_specialLinearGroupMap_toZMod, MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage continuous_toZMod.specialLinearGroup_map

/-- The first congruence subgroup is closed. -/
instance isClosed_firstCongruenceSubgroup :
    IsClosed (firstCongruenceSubgroup n p : Set (SpecialLinearGroup n ℤ_[p])) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_firstCongruenceSubgroup n p)

open Filter Topology in
variable {n p} in
/-- Every neighbourhood of `1` in `SL_n(ℤ_p)`, for instance an open subgroup, contains every matrix
congruent to the identity modulo a suitable power of `p`. -/
theorem exists_setOf_pow_dvd_sub_one_subset {s : Set (SpecialLinearGroup n ℤ_[p])}
    (hs : s ∈ 𝓝 1) :
    ∃ m : ℕ, {g : SpecialLinearGroup n ℤ_[p] |
      ∀ i j, (p : ℤ_[p]) ^ m ∣ ((g : Matrix n n ℤ_[p]) - 1) i j} ⊆ s := by
  by_contra! h
  choose g hg hgs using fun m ↦ Set.not_subset.mp (h m)
  have hlim : Tendsto g atTop (𝓝 1) := by
    rw [SpecialLinearGroup.tendsto_iff_tendsto_apply]
    intro i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hp : ‖(p : ℤ_[p])‖ < 1 := by
      rw [norm_p]
      exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp)
    obtain ⟨c, hc⟩ := hg m i j
    rw [SpecialLinearGroup.coe_one, ← Matrix.sub_apply, hc, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (norm_le_one c)
  obtain ⟨m, hm⟩ := (hlim.eventually hs).exists
  exact hgs m hm

/-- Reduction modulo `p` identifies the quotient by the first congruence subgroup with
`SL_n(𝔽_p)`. -/
noncomputable def firstCongruenceSubgroupQuotientEquiv :
    (SpecialLinearGroup n ℤ_[p] ⧸ firstCongruenceSubgroup n p) ≃*
      SpecialLinearGroup n (ZMod p) :=
  QuotientGroup.quotientKerEquivOfSurjective _
    (SpecialLinearGroup.map_surjective _ (ZMod.ringHom_surjective _))

/-- The quotient equivalence sends the class of a matrix to its reduction modulo `p`. -/
@[simp]
theorem firstCongruenceSubgroupQuotientEquiv_mk (g : SpecialLinearGroup n ℤ_[p]) :
    firstCongruenceSubgroupQuotientEquiv n p (QuotientGroup.mk g) =
      SpecialLinearGroup.map toZMod g := by
  rfl

/-- The index of the first congruence subgroup of `SL_n(ℤ_p)` is the order of `SL_n(𝔽_p)`:
reduction modulo `p` maps `SL_n(ℤ_p)` onto `SL_n(𝔽_p)`, since `ℤ_p` is local. -/
theorem index_firstCongruenceSubgroup :
    (firstCongruenceSubgroup n p).index = Nat.card (SpecialLinearGroup n (ZMod p)) := by
  rw [Subgroup.index_eq_card, Nat.card_congr (firstCongruenceSubgroupQuotientEquiv n p).toEquiv]

/-- The first congruence subgroup of `SL₂(ℤ_p)` has index `|SL₂(𝔽_p)| = p(p² - 1)`. -/
theorem index_firstCongruenceSubgroup_fin_two :
    (firstCongruenceSubgroup (Fin 2) p).index = p * (p ^ 2 - 1) := by
  rw [index_firstCongruenceSubgroup, natCard_SL_fin_two_zmod]

/-! ### Products of first congruence subgroups -/

variable (ι : Type*)

/-- The product `G₁^ι` of copies of the first congruence subgroup, as the subgroup of
`ι → SL_n(ℤ_p)` whose every coordinate lies in `G₁`. For `ι = Fin m` and `n = Fin 2` this is the
group `G = G₁^m` of Fu. -/
noncomputable def firstCongruenceProduct : Subgroup (ι → SpecialLinearGroup n ℤ_[p]) :=
  Subgroup.pi Set.univ fun _ ↦ firstCongruenceSubgroup n p

/-- The product of first congruence subgroups is `Subgroup.pi` of copies of `G₁`. -/
theorem firstCongruenceProduct_def :
    firstCongruenceProduct n p ι = Subgroup.pi Set.univ fun _ ↦ firstCongruenceSubgroup n p :=
  (rfl)

variable {n p ι} in
/-- A family of determinant-one matrices lies in `G₁^ι` exactly when each of them lies in `G₁`. -/
@[simp]
theorem mem_firstCongruenceProduct_iff {g : ι → SpecialLinearGroup n ℤ_[p]} :
    g ∈ firstCongruenceProduct n p ι ↔ ∀ i, g i ∈ firstCongruenceSubgroup n p := by
  simp [firstCongruenceProduct_def, Subgroup.mem_pi]

/-- The product `G₁^ι` is the kernel of reduction modulo `p`, coordinatewise, from
`SL_n(ℤ_p)^ι` to `SL_n(𝔽_p)^ι`. -/
theorem ker_compLeft_specialLinearGroupMap_toZMod :
    (MonoidHom.compLeft (SpecialLinearGroup.map (n := n) (toZMod (p := p))) ι).ker =
      firstCongruenceProduct n p ι := by
  ext g
  simp [funext_iff, mem_firstCongruenceSubgroup_iff_map_eq_one]

instance : (firstCongruenceProduct n p ι).Normal :=
  ker_compLeft_specialLinearGroupMap_toZMod n p ι ▸ MonoidHom.normal_ker _

/-- A product of finitely many copies of the first congruence subgroup is open. -/
theorem isOpen_firstCongruenceProduct [Finite ι] :
    IsOpen (firstCongruenceProduct n p ι : Set (ι → SpecialLinearGroup n ℤ_[p])) := by
  rw [firstCongruenceProduct_def, Subgroup.coe_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_firstCongruenceSubgroup n p

/-- A product of copies of the first congruence subgroup is closed. -/
instance isClosed_firstCongruenceProduct :
    IsClosed (firstCongruenceProduct n p ι : Set (ι → SpecialLinearGroup n ℤ_[p])) := by
  rw [firstCongruenceProduct_def, Subgroup.coe_pi]
  exact isClosed_set_pi fun _ _ ↦ isClosed_firstCongruenceSubgroup n p

/-- The index of `G₁^ι` in `SL_n(ℤ_p)^ι` is `|SL_n(𝔽_p)| ^ |ι|`. -/
theorem index_firstCongruenceProduct [Fintype ι] :
    (firstCongruenceProduct n p ι).index =
      Nat.card (SpecialLinearGroup n (ZMod p)) ^ Fintype.card ι := by
  rw [firstCongruenceProduct_def, Subgroup.index_pi, index_firstCongruenceSubgroup,
    Finset.prod_const, Finset.card_univ]

/-- The index of `G₁^ι` in `SL₂(ℤ_p)^ι` is `(p(p² - 1)) ^ |ι|`. -/
theorem index_firstCongruenceProduct_fin_two [Fintype ι] :
    (firstCongruenceProduct (Fin 2) p ι).index = (p * (p ^ 2 - 1)) ^ Fintype.card ι := by
  rw [index_firstCongruenceProduct, ← index_firstCongruenceSubgroup,
    index_firstCongruenceSubgroup_fin_two]

/-- The product `G₁^ι`, with its topology as a subgroup of `SL_n(ℤ_p)^ι`, is isomorphic as a
topological group to the product of copies of `G₁`, each with its topology as a subgroup of
`SL_n(ℤ_p)`. -/
noncomputable def firstCongruenceProduct.continuousMulEquivPi :
    firstCongruenceProduct n p ι ≃ₜ* (ι → firstCongruenceSubgroup n p) :=
  -- `firstCongruenceProduct n p ι` is by definition this `Subgroup.pi`, as
  -- `firstCongruenceProduct_def` records
  Subgroup.piContinuousMulEquiv fun _ ↦ firstCongruenceSubgroup n p

/-- The `i`-th coordinate of the image of `g ∈ G₁^ι` in `ι → G₁` is the `i`-th coordinate of
`g`. -/
@[simp]
theorem firstCongruenceProduct.coe_continuousMulEquivPi_apply (g : firstCongruenceProduct n p ι)
    (i : ι) :
    (continuousMulEquivPi n p ι g i : SpecialLinearGroup n ℤ_[p]) =
      (g : ι → SpecialLinearGroup n ℤ_[p]) i :=
  Subgroup.coe_piContinuousMulEquiv_apply _ g i

/-- The inverse of `firstCongruenceProduct.continuousMulEquivPi` assembles the coordinates into an
element of `G₁^ι`. -/
@[simp]
theorem firstCongruenceProduct.coe_continuousMulEquivPi_symm_apply
    (g : ι → firstCongruenceSubgroup n p) :
    ((continuousMulEquivPi n p ι).symm g : ι → SpecialLinearGroup n ℤ_[p]) =
      fun i ↦ (g i : SpecialLinearGroup n ℤ_[p]) :=
  Subgroup.coe_piContinuousMulEquiv_symm_apply _ g

/-! ### Degenerate products and particular elements -/

/-- An empty product of first congruence subgroups is the whole of the trivial group
`SL_n(ℤ_p)^ι`. -/
theorem firstCongruenceProduct_eq_top_of_isEmpty [IsEmpty ι] : firstCongruenceProduct n p ι = ⊤ :=
  Subsingleton.elim _ _

variable {p}

/-- The unipotent matrix `!![1, a; 0, 1]` lies in the first congruence subgroup of `SL₂(ℤ_p)`
exactly when `p ∣ a`. So `!![1, p; 0, 1] ∈ G₁` while `!![1, 1; 0, 1] ∉ G₁`: membership constrains
all entries of `g - 1`, not only the determinant. -/
theorem mk_upperRight_mem_firstCongruenceSubgroup_iff (a : ℤ_[p]) :
    SpecialLinearGroup.mk !![1, a; 0, 1] (by simp) ∈ firstCongruenceSubgroup (Fin 2) p ↔
      (p : ℤ_[p]) ∣ a := by
  simp [mem_firstCongruenceSubgroup_iff, Fin.forall_fin_two, one_fin_two]

/-- The matrix `-1` lies in the first congruence subgroup of `SL₂(ℤ_p)` exactly when `p = 2`. So
for odd `p` the group `G₁` does not contain `-1`, while `G₁ ≤ SL₂(ℤ₂)` has an element of order
two. -/
theorem neg_one_mem_firstCongruenceSubgroup_iff :
    (-1 : SpecialLinearGroup (Fin 2) ℤ_[p]) ∈ firstCongruenceSubgroup (Fin 2) p ↔ p = 2 := by
  have h2 : (p : ℤ_[p]) ∣ 2 ↔ p = 2 := by
    rw [← toZMod_eq_zero_iff_dvd, map_ofNat, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff,
      Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two]
  have hneg : (-1 - 1 : ℤ_[p]) = -2 := by norm_num
  simp [mem_firstCongruenceSubgroup_iff, Fin.forall_fin_two, one_fin_two, hneg, ← h2]

end TauCeti
