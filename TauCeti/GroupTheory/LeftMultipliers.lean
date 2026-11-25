/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Left multipliers and the conjugation stabilizer of a function on a group

Let `f : G → C` be a function from a group to a possibly noncommutative group. This file records
two subgroups of `G` that measure how far `f` is from being a homomorphism.

* When `f 1 = 1`, the *left multipliers* of `f` are the `h : G` with `f (h * x) = f h * f x` for
  every `x`. They form a subgroup on which `f` restricts to a homomorphism, and this subgroup is
  all of `G` exactly when `f` is multiplicative.
* The *conjugation stabilizer* of `f` consists of the `g : G` with `f (g * x * g⁻¹) = f x` for
  every `x`, that is, the stabilizer of `f` under conjugation. It normalizes the left
  multipliers. Preserving every value of `f` is stronger than preserving its fibre over `1`: for
  `f` a homomorphism, the conjugation stabilizer is the preimage of the centralizer of the image.

These are the group-theoretic devices of Bass–Milnor–Serre's extension argument for Mennicke
symbols: a value function defined through standard forms is first shown to be multiplicative on
the left by corner matrices, and the multiplier subgroup is then enlarged to the whole congruence
subgroup by exhibiting enough elements of the conjugation stabilizer, with transposition used to
exchange the two corners.

## Main definitions

* `OneHom.leftMultipliers`: the subgroup of left multipliers of a map preserving `1`.
* `OneHom.leftMultipliersHom`: the restriction of the map to its left multipliers, as a
  homomorphism.
* `Function.conjStabilizer`: the subgroup of elements whose conjugation preserves every value.

## Main results

* `OneHom.leftMultipliers_eq_top_iff`: the left multipliers are everything exactly when the map is
  multiplicative.
* `OneHom.conjStabilizer_le_normalizer_leftMultipliers`: the conjugation stabilizer normalizes the
  left multipliers.
* `MonoidHom.conjStabilizer_eq_comap_centralizer`: for a homomorphism, the conjugation stabilizer
  is the preimage of the centralizer of its range.

## References

* H. Bass, J. Milnor, J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §9.
-/

public section

variable {G C : Type*} [Group G] [Group C]

namespace OneHom

variable (f : OneHom G C)

variable {f} in
/-- A map preserving `1` inverts the value at any element that splits it on the left. -/
theorem map_inv_of_forall_map_mul {h : G} (hh : ∀ x, f (h * x) = f h * f x) :
    f h⁻¹ = (f h)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← hh]; simp)

/-- The left multipliers of a map `f` with `f 1 = 1`: the elements `h` such that
`f (h * x) = f h * f x` for every `x`. They form a subgroup, on which `f` is a homomorphism. -/
def leftMultipliers : Subgroup G where
  carrier := {h | ∀ x, f (h * x) = f h * f x}
  one_mem' x := by simp
  mul_mem' {h k} hh hk x := by
    have hhk : f (h * k) = f h * f k := by simpa using hh k
    rw [mul_assoc, hh, hk, hhk, mul_assoc]
  inv_mem' {h} hh x := by
    rw [map_inv_of_forall_map_mul hh, eq_inv_mul_iff_mul_eq, ← hh, mul_inv_cancel_left]

variable {f}

theorem mem_leftMultipliers_iff {h : G} :
    h ∈ f.leftMultipliers ↔ ∀ x, f (h * x) = f h * f x :=
  Iff.rfl

/-- A left multiplier of `f` splits `f` on the left. -/
theorem map_mul_of_mem_leftMultipliers {h : G} (hh : h ∈ f.leftMultipliers) (x : G) :
    f (h * x) = f h * f x :=
  hh x

/-- A map preserving `1` inverts the values of its left multipliers. -/
theorem map_inv_of_mem_leftMultipliers {h : G} (hh : h ∈ f.leftMultipliers) :
    f h⁻¹ = (f h)⁻¹ :=
  map_inv_of_forall_map_mul hh

variable (f) in
/-- The restriction of a map preserving `1` to its left multipliers, as a homomorphism. -/
def leftMultipliersHom : f.leftMultipliers →* C where
  toFun h := f h
  map_one' := by simp
  map_mul' h k := h.property k

@[simp]
theorem leftMultipliersHom_apply (h : f.leftMultipliers) : f.leftMultipliersHom h = f h :=
  (rfl)

/-- The left multipliers of `f` are all of `G` exactly when `f` is multiplicative. -/
theorem leftMultipliers_eq_top_iff :
    f.leftMultipliers = ⊤ ↔ ∀ x y, f (x * y) = f x * f y := by
  simp [Subgroup.eq_top_iff', mem_leftMultipliers_iff]

end OneHom

namespace MonoidHom

/-- Every element is a left multiplier of a homomorphism. -/
@[simp]
theorem leftMultipliers_toOneHom (φ : G →* C) : φ.toOneHom.leftMultipliers = ⊤ :=
  OneHom.leftMultipliers_eq_top_iff.2 φ.map_mul

end MonoidHom

namespace Function

variable {D : Type*}

/-- The conjugation stabilizer of a function `f` on a group: the elements `g` such that
`f (g * x * g⁻¹) = f x` for every `x`. These preserve every value of `f` under conjugation, not only
its fibre over `1`. -/
def conjStabilizer (f : G → D) : Subgroup G where
  carrier := {g | ∀ x, f (g * x * g⁻¹) = f x}
  one_mem' x := by simp
  mul_mem' {g k} hg hk x :=
    calc f (g * k * x * (g * k)⁻¹) = f (g * (k * x * k⁻¹) * g⁻¹) := by group
      _ = f x := by rw [hg, hk]
  inv_mem' {g} hg x :=
    calc f (g⁻¹ * x * g⁻¹⁻¹) = f (g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹) := (hg _).symm
      _ = f x := by group

variable {f : G → D}

theorem mem_conjStabilizer_iff {g : G} :
    g ∈ conjStabilizer f ↔ ∀ x, f (g * x * g⁻¹) = f x :=
  Iff.rfl

/-- An element lies in the conjugation stabilizer of `f` exactly when `f` is invariant under its
inner automorphism. -/
theorem mem_conjStabilizer_iff_comp_conj {g : G} :
    g ∈ conjStabilizer f ↔ f ∘ MulAut.conj g = f := by
  simp [mem_conjStabilizer_iff, funext_iff]

/-- Conjugation by an element of the conjugation stabilizer preserves the values of `f`. -/
theorem map_conj_of_mem_conjStabilizer {g : G} (hg : g ∈ conjStabilizer f) (x : G) :
    f (g * x * g⁻¹) = f x :=
  hg x

/-- The conjugation stabilizer is all of `G` exactly when `f` is a class function. -/
theorem conjStabilizer_eq_top_iff :
    conjStabilizer f = ⊤ ↔ ∀ g x, f (g * x * g⁻¹) = f x := by
  simp [Subgroup.eq_top_iff', mem_conjStabilizer_iff]

/-- A constant function is stabilized by every conjugation. -/
@[simp]
theorem conjStabilizer_const (c : D) : conjStabilizer (fun _ : G ↦ c) = ⊤ :=
  conjStabilizer_eq_top_iff.2 fun _ _ ↦ rfl

end Function

namespace OneHom

open Function

/-- The conjugation stabilizer of a map preserving `1` normalizes its left multipliers. -/
theorem conjStabilizer_le_normalizer_leftMultipliers (f : OneHom G C) :
    conjStabilizer f ≤ Subgroup.normalizer (f.leftMultipliers : Set G) := by
  -- If `g` stabilizes `f` under conjugation and `h` is a left multiplier, then
  -- `f (g * h * g⁻¹ * x) = f (h * (g⁻¹ * x * g)) = f h * f x = f (g * h * g⁻¹) * f x`;
  -- the converse direction is the same argument for `g⁻¹`.
  have key {g h : G} (hg : g ∈ conjStabilizer f) (hh : h ∈ f.leftMultipliers) :
      g * h * g⁻¹ ∈ f.leftMultipliers := fun x ↦ by
    have hginv := (conjStabilizer f).inv_mem hg
    calc f (g * h * g⁻¹ * x) = f (g * (h * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹) := by congr 1; group
      _ = f h * f x := by rw [hg, hh, hginv]
      _ = f (g * h * g⁻¹) * f x := by rw [hg]
  intro g hg h
  simp only [SetLike.mem_coe]
  refine ⟨key hg, fun hh ↦ ?_⟩
  have hconj : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  simpa only [hconj] using key ((conjStabilizer f).inv_mem hg) hh

end OneHom

namespace MonoidHom

/-- For a homomorphism `φ`, conjugation by `g` preserves every value of `φ` exactly when `φ g`
commutes with the range of `φ`. -/
theorem conjStabilizer_eq_comap_centralizer (φ : G →* C) :
    Function.conjStabilizer φ = (Subgroup.centralizer (φ.range : Set C)).comap φ := by
  ext g
  simp only [Function.mem_conjStabilizer_iff, Subgroup.mem_comap, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe, mem_range, forall_exists_index, forall_apply_eq_imp_iff, map_mul, map_inv]
  refine forall_congr' fun x ↦ ?_
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

end MonoidHom
