/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Height and integral relations among roots

The height of a root relative to a base of a root pairing is the sum of the coefficients of its
expansion in the simple roots. This file records that height respects every integral relation
among the roots: a vanishing integral combination of roots has a vanishing combination of heights,
so two integral combinations with the same value have the same combination of heights. When the
roots span the weight space, it also extends height to the linear functional which sums the
coordinates in the simple-root basis. Over a field, a form taking value one on the simple roots
exists even when they do not span the weight space. Ahead of all this, it records the
extensionality of bases (a base is determined by the indices of its simple roots), how bases,
heights and positivity are transported along equivalences of root pairings (in particular an
automorphism permuting the simple roots preserves heights), and how reflection in a root changes
height: reflection in a simple root subtracts the corresponding Cartan integer.

## Main definitions

* `TauCeti.heightLinearMap` is the linear extension of root height to the weight
  space of a root system.

## Main results

* `RootPairing.Base.ext`: a base is determined by its support, the indices of its simple roots.
* `RootPairing.Base.map_one` and `RootPairing.Base.map_mul`: transporting bases is an action of the
  automorphism group, and `RootPairing.Base.map_eq_of_forall_mem_support` says an automorphism
  permuting the simple roots fixes the base.
* `RootPairing.Base.height_map` and `RootPairing.Base.isPos_map_iff`: an equivalence of root
  pairings carries the height and the positivity of a root relative to a base to those of its
  image relative to the transported base; `RootPairing.Base.height_indexEquiv` and
  `RootPairing.Base.isPos_indexEquiv_iff` say an automorphism permuting the simple roots preserves
  both.
* `RootPairing.Base.height_eq_one_iff`: the roots of height one are exactly the simple roots.
* `RootPairing.Base.height_reflectionPerm` computes the height after an arbitrary root reflection;
  `RootPairing.Base.height_reflectionPerm_lt_iff` characterizes strict height decrease under a
  simple reflection by positivity of the corresponding Cartan integer.
* `RootPairing.pairingIn_eq_sum_of_root_eq_sum` reads the Cartan integers of an integral
  combination of roots off those of its summands.
* `TauCeti.apply_root_eq_height_zsmul` says that an additive map taking the constant value `c`
  on the simple roots takes the value `ht(α) • c` on every root.
* `TauCeti.sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero` says that height respects integral
  relations among roots.
* `TauCeti.sum_mul_height_eq_of_sum_zsmul_root_eq` compares the heights of two integral
  combinations of roots with the same value.
* `RootPairing.Base.height_indexEquiv` says that an automorphism of a root pairing permuting the
  simple roots preserves heights.

## References

The argument follows Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- **A base is determined by its simple roots.** The other fields of a base are propositions about
its support. -/
@[ext]
theorem ext {b b' : P.Base} (h : b.support = b'.support) : b = b' := by
  cases b
  cases b'
  subst h
  rfl

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P₂ : RootPairing ι₂ R M₂ N₂}

/-- Transporting a base along the identity automorphism does nothing. -/
@[simp]
protected theorem map_one (b : P.Base) : b.map (1 : P.Aut) = b := by
  classical
  ext i
  simp

/-- Transporting a base along a product of automorphisms transports it along each factor in turn,
the right-hand factor first. -/
protected theorem map_mul (b : P.Base) (g h : P.Aut) : b.map (g * h) = (b.map h).map g := by
  classical
  ext i
  simp [Finset.image_image]

/-- An automorphism carrying every simple root of `b` to a simple root fixes `b`. -/
theorem map_eq_of_forall_mem_support {b : P.Base} {u : P.Aut}
    (hu : ∀ j ∈ b.support, u.indexEquiv j ∈ b.support) : b.map u = b := by
  classical
  exact ext <| Finset.eq_of_subset_of_card_le (by simpa [Finset.image_subset_iff] using hu)
    (by rw [support_map_eq, Finset.card_image_of_injective _ u.indexEquiv.injective])

/-- **Heights are transported along equivalences of root pairings.** The image of a root under an
equivalence `e` has, relative to the transported base `b.map e`, the height of the original root
relative to `b`. -/
@[simp]
theorem height_map [CharZero R] (b : P.Base) (e : P.Equiv P₂) (i : ι) :
    (b.map e).height (e.indexEquiv i) = b.height i := by
  classical
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  have h : P₂.root (e.indexEquiv i) =
      ∑ j ∈ (b.map e).support, f (e.indexEquiv.symm j) • P₂.root j := by
    rw [support_map_eq, Finset.sum_image e.indexEquiv.injective.injOn,
      ← Hom.root_weightMap_apply, hf, map_sum]
    simp [Hom.root_weightMap_apply]
  rw [height_eq_sum h, support_map_eq, Finset.sum_image e.indexEquiv.injective.injOn,
    height_eq_sum hf]
  simp

/-- **Positivity is transported along equivalences of root pairings.** -/
@[simp]
theorem isPos_map_iff [CharZero R] (b : P.Base) (e : P.Equiv P₂) (i : ι) :
    (b.map e).IsPos (e.indexEquiv i) ↔ b.IsPos i := by
  rw [isPos_iff, isPos_iff, height_map]

/-- **An automorphism permuting the simple roots preserves heights.** If an automorphism `u` of a
root pairing carries every simple root of the base `b` to a simple root, then `u` fixes `b`, so
`u α` has the same height as `α` for every root `α`. -/
theorem height_indexEquiv [CharZero R] (b : P.Base) (u : P.Aut)
    (hu : ∀ j ∈ b.support, u.indexEquiv j ∈ b.support) (i : ι) :
    b.height (u.indexEquiv i) = b.height i := by
  rw [← b.height_map u i, map_eq_of_forall_mem_support hu]

/-- An automorphism permuting the simple roots of the base `b` preserves positivity of roots
relative to `b`. -/
theorem isPos_indexEquiv_iff [CharZero R] (b : P.Base) {u : P.Aut}
    (hu : ∀ j ∈ b.support, u.indexEquiv j ∈ b.support) (i : ι) :
    b.IsPos (u.indexEquiv i) ↔ b.IsPos i := by
  rw [isPos_iff, isPos_iff, height_indexEquiv b u hu]

end Map

/-- **The roots of height one are exactly the simple roots.** -/
theorem height_eq_one_iff [CharZero R] (b : P.Base) {i : ι} :
    b.height i = 1 ↔ i ∈ b.support := by
  classical
  refine ⟨fun h ↦ ?_, height_one_of_mem_support⟩
  -- Write `αᵢ = ± ∑ fⱼ αⱼ` with `fⱼ ∈ ℕ`: height one forces the sign `+` and a single `fⱼ = 1`.
  obtain ⟨f, -, hf | hf⟩ := b.exists_root_eq_sum_nat_or_neg i
  · have hsum : ∑ j ∈ b.support, f j = 1 := by
      rw [height_eq_sum (f := fun j ↦ (f j : ℤ)) (by simp [hf, natCast_zsmul])] at h
      exact_mod_cast h
    obtain ⟨j, hj, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
    have hfj : f j = 1 := by
      have := Finset.single_le_sum (f := f) (fun _ _ ↦ Nat.zero_le _) hj
      omega
    have hrest : ∀ k ∈ b.support, k ≠ j → f k = 0 := by
      rw [← Finset.add_sum_erase _ _ hj, hfj, add_eq_left, Finset.sum_eq_zero_iff] at hsum
      exact fun k hk hkj ↦ hsum k (Finset.mem_erase.mpr ⟨hkj, hk⟩)
    have hroot : P.root i = P.root j := by
      rw [hf, Finset.sum_eq_single_of_mem j hj fun k hk hkj ↦ by rw [hrest k hk hkj, zero_smul],
        hfj, one_smul]
    exact P.root.injective hroot ▸ hj
  · rw [height_eq_sum (f := fun j ↦ -(f j : ℤ)) (by simp [hf, natCast_zsmul])] at h
    have : ∑ j ∈ b.support, -(f j : ℤ) ≤ 0 := Finset.sum_nonpos fun _ _ ↦ by omega
    omega

section Reflection

variable [CharZero R] [P.IsCrystallographic] (b : P.Base)

/-- Reflection in the root indexed by `i` changes the height of `j` by the Cartan integer
`P.pairingIn ℤ j i` times the height of `i`. -/
lemma height_reflectionPerm (i j : ι) :
    b.height (P.reflectionPerm i j) = b.height j - P.pairingIn ℤ j i * b.height i := by
  rw [b.height_add_zsmul (i := j) (j := i) (z := -P.pairingIn ℤ j i)
    (by rw [root_reflectionPerm, reflection_apply_root' ℤ]; module)]
  simp [sub_eq_add_neg]

/-- Reflection in a simple root subtracts the corresponding Cartan integer from the height. -/
@[simp]
lemma height_reflectionPerm_of_mem_support {i j : ι} (hi : i ∈ b.support) :
    b.height (P.reflectionPerm i j) = b.height j - P.pairingIn ℤ j i := by
  rw [height_reflectionPerm, height_one_of_mem_support hi, mul_one]

/-- Reflection in a simple root strictly decreases height exactly when the corresponding Cartan
integer is positive. -/
lemma height_reflectionPerm_lt_iff {i j : ι} (hi : i ∈ b.support) :
    b.height (P.reflectionPerm i j) < b.height j ↔ 0 < P.pairingIn ℤ j i := by
  simp [hi]

end Reflection

end RootPairing.Base

/-- Over a field, there is a linear form taking value one on every simple root, even when
those roots do not span the weight space. -/
theorem RootPairing.Base.exists_dual_eq_one_on_root {ι 𝕜 V N : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup N] [Module 𝕜 N]
    {P : RootPairing ι 𝕜 V N} (b : P.Base) :
    ∃ g : Module.Dual 𝕜 V, ∀ i : b.support, g (P.root i) = 1 := by
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_eq_one b.linearIndepOn_root
  exact ⟨g, fun i ↦ hg i i.property⟩

namespace RootPairing

/-- **The Cartan integers of an integral combination of roots** are the matching combination of
Cartan integers: if `αᵢ = ∑ₖ fₖ αₖ` then `⟨αᵢ, αₗ^∨⟩ = ∑ₖ fₖ ⟨αₖ, αₗ^∨⟩`. -/
theorem pairingIn_eq_sum_of_root_eq_sum {ι R M N : Type*} [CommRing R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    [P.IsCrystallographic] {s : Finset ι} {i : ι} {f : ι → ℤ}
    (h : P.root i = ∑ k ∈ s, f k • P.root k) (l : ι) :
    P.pairingIn ℤ i l = ∑ k ∈ s, f k * P.pairingIn ℤ k l :=
  FaithfulSMul.algebraMap_injective ℤ R <| by
    simp_rw [algebraMap_pairingIn, map_sum, map_mul, algebraMap_pairingIn,
      ← root_coroot'_eq_pairing, h, map_sum, map_zsmul, zsmul_eq_mul, eq_intCast]

end RootPairing

namespace TauCeti

universe u v w x y

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- **A map constant on the simple roots is the height acting on that constant.** Expanding a
root in the simple roots and applying the map termwise turns the value `c` on every simple root
into the value `ht(α) • c` on every root. Only additivity is used, so the target is an arbitrary
additive group. -/
theorem apply_root_eq_height_zsmul [CharZero R] {A : Type y} [AddCommGroup A] (b : P.Base)
    (g : M →+ A) {c : A} (hg : ∀ j ∈ b.support, g (P.root j) = c) (i : ι) :
    g (P.root i) = b.height i • c := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  rw [hf, map_sum, b.height_eq_sum hf, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [map_zsmul, hg j hj]

section HeightLinearMap

variable [P.IsRootSystem]

/-- **The height functional on the weight space of a root system.** A base of a root system is a
basis of its weight space; summing the coordinates in that basis extends the integer-valued height
of roots to an `R`-linear map on the whole weight space. -/
noncomputable def heightLinearMap (b : P.Base) : M →ₗ[R] R :=
  b.toWeightBasis.sumCoords

/-- The height functional is the coordinate sum in the simple-root basis. -/
theorem heightLinearMap_apply (b : P.Base) (m : M) :
    heightLinearMap P b m = (b.toWeightBasis.repr m).sum fun _ ↦ id := by
  rw [heightLinearMap, Module.Basis.coe_sumCoords]

/-- The height functional sends every simple root to one. -/
@[simp]
theorem heightLinearMap_simpleRoot (b : P.Base) (i : b.support) :
    heightLinearMap P b (P.root i) = 1 := by
  simpa only [heightLinearMap, b.toWeightBasis_apply] using
    b.toWeightBasis.sumCoords_self_apply i

/-- On a root, the height functional agrees with the integer-valued height of the root. -/
@[simp]
theorem heightLinearMap_root [CharZero R] (b : P.Base) (i : ι) :
    heightLinearMap P b (P.root i) = (b.height i : R) := by
  have hval := apply_root_eq_height_zsmul P b (heightLinearMap P b).toAddMonoidHom (c := 1)
    (fun j hj ↦ heightLinearMap_simpleRoot P b ⟨j, hj⟩) i
  rwa [LinearMap.toAddMonoidHom_coe, Int.smul_one_eq_cast] at hval

end HeightLinearMap

variable [CharZero R]

/-- If an integral combination of roots vanishes, the same combination of their heights
vanishes. -/
theorem sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero (b : P.Base) {s : Finset ι} {e : ι → ℤ}
    (he : ∑ i ∈ s, e i • P.root i = 0) :
    ∑ i ∈ s, e i * b.height i = 0 := by
  classical
  -- Expand the roots in the simple roots and use their linear independence.
  choose g _hgsupp _hgsign hg using fun i : ι ↦ b.exists_root_eq_sum_int i
  have hcomb : ∑ j ∈ b.support, (∑ i ∈ s, e i * g i j) • P.root j = 0 := by
    rw [← he]
    simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.smul_sum, ← hg i]
  have hczero : ∀ j ∈ b.support, (∑ i ∈ s, e i * g i j) = 0 :=
    linearIndepOn_iff'.mp (b.linearIndepOn_root.restrict_scalars' ℤ) b.support
      (fun j ↦ ∑ i ∈ s, e i * g i j) (fun _ h ↦ h) hcomb
  calc ∑ i ∈ s, e i * b.height i
      = ∑ i ∈ s, ∑ j ∈ b.support, e i * g i j :=
        Finset.sum_congr rfl fun i _ ↦ by rw [b.height_eq_sum (hg i), Finset.mul_sum]
    _ = ∑ j ∈ b.support, ∑ i ∈ s, e i * g i j := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero hczero

/-- Two integral combinations of roots with the same value have the same combination of
heights. -/
theorem sum_mul_height_eq_of_sum_zsmul_root_eq (b : P.Base) {s t : Finset ι} {e f : ι → ℤ}
    (h : ∑ i ∈ s, e i • P.root i = ∑ i ∈ t, f i • P.root i) :
    ∑ i ∈ s, e i * b.height i = ∑ i ∈ t, f i * b.height i := by
  classical
  -- Extend both coefficient functions by zero to `s ∪ t`, where the two combinations can be
  -- subtracted from one another.
  have key := sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero P b (s := s ∪ t)
    (e := fun i ↦ (if i ∈ s then e i else 0) - (if i ∈ t then f i else 0)) ?_
  · simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, sub_eq_zero] at key
    exact key
  · simp_rw [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, h, sub_self]

end TauCeti
