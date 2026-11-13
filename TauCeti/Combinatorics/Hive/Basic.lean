/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Tactic.Abel

/-!
# Hive labellings and normalization

A hive labelling satisfies the short-diagonal inequality on every unit rhombus.
Normalized hives have value zero at the corner `A`. They form an additive monoid,
not a group: negation generally reverses the inequalities. Subtracting a constant
normalizes an arbitrary labelling without changing its rhombus inequalities.

The short-diagonal convention follows Knutson–Tao, *The honeycomb model of GLₙ(ℂ)
tensor products I*, Appendix 2.
-/

public section

namespace TauCeti.Hive

variable {n : ℕ} {R : Type*}

/-- A labelling whose obtuse-corner sum is at least its acute-corner sum on each
unit rhombus. No normalization is imposed. -/
def IsHive [Add R] [LE R] (h : Vertex n → R) : Prop :=
  ∀ ⦃a b c d⦄, IsRhombus a b c d → h b + h d ≤ h a + h c

/-- A labelling is a hive exactly when all its short-diagonal inequalities hold. -/
theorem isHive_iff [Add R] [LE R] (h : Vertex n → R) :
    IsHive h ↔ ∀ ⦃a b c d⦄, IsRhombus a b c d → h b + h d ≤ h a + h c := Iff.rfl

/-- Evaluate the short-diagonal inequality of a hive labelling on a unit rhombus. -/
theorem IsHive.le [Add R] [LE R] {h : Vertex n → R} (hh : IsHive h)
    {a b c d : Vertex n} (hr : IsRhombus a b c d) : h b + h d ≤ h a + h c := hh hr

section Symmetry

variable [Add R] [LE R]

/-- Precomposition by clockwise rotation preserves the hive inequalities. -/
theorem IsHive.rotate {h : Vertex n → R} (hh : IsHive h) :
    IsHive (fun p => h p.rotate) := fun _ _ _ _ hr => hh hr.rotate

/-- Precomposition by reflection preserves the hive inequalities. -/
theorem IsHive.reflect {h : Vertex n → R} (hh : IsHive h) :
    IsHive (fun p => h p.reflect) := fun _ _ _ _ hr => hh hr.reflect

/-- Clockwise rotation does not affect whether a labelling is a hive. -/
@[simp] theorem isHive_rotate_iff (h : Vertex n → R) :
    IsHive (fun p => h p.rotate) ↔ IsHive h := by
  constructor
  · intro hh
    simpa only [Vertex.rotate_rotate_rotate] using hh.rotate.rotate
  · exact IsHive.rotate

/-- Reflection does not affect whether a labelling is a hive. -/
@[simp] theorem isHive_reflect_iff (h : Vertex n → R) :
    IsHive (fun p => h p.reflect) ↔ IsHive h := by
  constructor
  · intro hh
    simpa only [Vertex.reflect_reflect] using hh.reflect
  · exact IsHive.reflect

/-- Restriction to a translated lattice subtriangle preserves hive inequalities. -/
theorem IsHive.restrict {m : ℕ} {h : Vertex (m + n) → R} (hh : IsHive h)
    (p : Vertex m) : IsHive (fun q => h (p.add q)) :=
  fun _ _ _ _ hr => hh (hr.add p)

end Symmetry

/-- Every constant labelling satisfies the hive inequalities. -/
@[simp] theorem isHive_const [Add R] [Preorder R] (c : R) :
    IsHive (fun _ : Vertex n => c) := fun _ _ _ _ _ => le_rfl

section AddMonoid

variable [AddCommMonoid R] [Preorder R]

/-- The zero labelling satisfies every rhombus inequality. -/
@[simp] theorem isHive_zero : IsHive (0 : Vertex n → R) := by
  intro a b c d _
  simp

/-- Pointwise addition preserves the hive inequalities. -/
theorem IsHive.add [IsOrderedAddMonoid R] {h k : Vertex n → R} (hh : IsHive h) (hk : IsHive k) :
    IsHive (h + k) := by
  intro a b c d hr
  simpa only [Pi.add_apply, add_add_add_comm] using add_le_add (hh hr) (hk hr)

/-- The additive submonoid of normalized hive labellings. -/
def hiveSubmonoid (n : ℕ) (R : Type*) [AddCommMonoid R] [Preorder R]
    [IsOrderedAddMonoid R] : AddSubmonoid (Vertex n → R) where
  carrier := {h | IsHive h ∧ h (Vertex.cornerA n) = 0}
  zero_mem' := ⟨isHive_zero, rfl⟩
  add_mem' hh hk := ⟨hh.1.add hk.1, by simp [hh.2, hk.2]⟩

@[simp] theorem mem_hiveSubmonoid [IsOrderedAddMonoid R] (h : Vertex n → R) :
    h ∈ hiveSubmonoid n R ↔ IsHive h ∧ h (Vertex.cornerA n) = 0 := Iff.rfl

/-- Adding a constant does not affect whether a labelling is a hive. -/
@[simp] theorem isHive_add_const_iff [IsOrderedCancelAddMonoid R]
    (h : Vertex n → R) (c : R) :
    IsHive (fun p => h p + c) ↔ IsHive h := by
  constructor <;> intro hh a b c' d hr
  · have hi : (h b + h d) + (c + c) ≤ (h a + h c') + (c + c) := by
      convert hh hr using 1 <;> dsimp only <;> abel
    exact (add_le_add_iff_right _).mp hi
  · convert add_le_add_right (hh hr) (c + c) using 1 <;> dsimp only <;> abel

/-- Adding a constant on the left does not affect whether a labelling is a hive. -/
@[simp] theorem isHive_const_add_iff [IsOrderedCancelAddMonoid R]
    (c : R) (h : Vertex n → R) :
    IsHive (fun p => c + h p) ↔ IsHive h := by
  simpa only [add_comm] using isHive_add_const_iff h c

end AddMonoid

section Group

variable [AddCommGroup R] [Preorder R] [IsOrderedAddMonoid R]

/-- Subtracting a constant does not affect whether a labelling is a hive. -/
@[simp] theorem isHive_sub_const_iff (h : Vertex n → R) (c : R) :
    IsHive (fun p => h p - c) ↔ IsHive h := by
  simpa only [sub_eq_add_neg] using isHive_add_const_iff h (-c)

end Group

end TauCeti.Hive

namespace TauCeti

/-- A normalized hive: a rhombus-concave labelling with value zero at `A`.
Its additive monoid structure is pointwise. -/
abbrev Hive (n : ℕ) (R : Type*) [AddCommMonoid R] [Preorder R]
    [IsOrderedAddMonoid R] := ↥(Hive.hiveSubmonoid n R)

/-- Integer-valued normalized hives. -/
abbrev IntegerHive (n : ℕ) := Hive n ℤ

/-- Real-valued normalized hives. -/
abbrev RealHive (n : ℕ) := Hive n ℝ

namespace Hive

variable {n : ℕ} {R : Type*}

section AddMonoid

variable [AddCommMonoid R] [Preorder R] [IsOrderedAddMonoid R]

instance : CoeFun (Hive n R) (fun _ => Vertex n → R) := ⟨fun h => h.val⟩

/-- Construct a normalized hive from a labelling and its two defining properties. -/
def ofLabel (h : Vertex n → R) (hh : IsHive h) (hA : h (Vertex.cornerA n) = 0) :
    Hive n R := ⟨h, hh, hA⟩

@[simp] theorem coe_ofLabel (h : Vertex n → R) (hh : IsHive h)
    (hA : h (Vertex.cornerA n) = 0) : (ofLabel h hh hA : Vertex n → R) = h := (rfl)

@[simp] theorem ofLabel_coe (h : Hive n R) (hh : IsHive (h : Vertex n → R))
    (hA : h (Vertex.cornerA n) = 0) : ofLabel (h : Vertex n → R) hh hA = h := (rfl)

@[simp] theorem ofLabel_apply (h : Vertex n → R) (hh : IsHive h)
    (hA : h (Vertex.cornerA n) = 0) (p : Vertex n) : ofLabel h hh hA p = h p := (rfl)

/-- The underlying labelling of a normalized hive satisfies the rhombus inequalities. -/
@[simp] theorem isHive (h : Hive n R) : IsHive (h : Vertex n → R) := h.property.1

/-- A normalized hive satisfies the short-diagonal inequality on every unit rhombus. -/
theorem rhombus_le (h : Hive n R) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    h b + h d ≤ h a + h c := h.isHive.le hr

@[simp] theorem apply_cornerA (h : Hive n R) : h (Vertex.cornerA n) = 0 := h.property.2

@[simp] theorem zero_apply (p : Vertex n) : (0 : Hive n R) p = 0 := (rfl)

@[simp] theorem add_apply (h k : Hive n R) (p : Vertex n) : (h + k) p = h p + k p := (rfl)

/-- Normalized hives are equal when their entries agree. -/
@[ext] theorem ext {h k : Hive n R} (he : ∀ p, h p = k p) : h = k :=
  Subtype.ext (funext he)

/-- A normalized affine labelling, with slopes `u,v` in the `y,z` coordinates.
All its rhombus inequalities are equalities. -/
def affine (u v : R) : Hive n R :=
  ofLabel (fun p => p.y • u + p.z • v) (by
    intro a b c d hr
    have hy := congrArg (fun k : ℕ => k • u) hr.midpoint_y
    have hz := congrArg (fun k : ℕ => k • v) hr.midpoint_z
    simp only [add_nsmul] at hy hz
    exact le_of_eq (calc
      (b.y • u + b.z • v) + (d.y • u + d.z • v) =
          (b.y • u + d.y • u) + (b.z • v + d.z • v) := by abel
      _ = (a.y • u + c.y • u) + (a.z • v + c.z • v) := by rw [hy, hz]
      _ = (a.y • u + a.z • v) + (c.y • u + c.z • v) := by abel)) (by simp)

/-- The labelling underlying an affine hive. -/
theorem coe_affine (u v : R) :
    (affine u v : Vertex n → R) = fun p => p.y • u + p.z • v := (rfl)

@[simp] theorem affine_apply (u v : R) (p : Vertex n) :
    affine u v p = p.y • u + p.z • v := (rfl)

/-- Zero slopes give the zero hive. -/
@[simp] theorem affine_zero : affine (0 : R) 0 = (0 : Hive n R) := by
  ext p
  simp

/-- Addition of affine hives adds their slopes. -/
@[simp] theorem affine_add (u v u' v' : R) :
    affine (u + u') (v + v') = (affine u v + affine u' v' : Hive n R) := by
  ext p
  simp only [affine_apply, add_apply, nsmul_add]
  abel

end AddMonoid

section Group

variable [AddCommGroup R] [Preorder R] [IsOrderedAddMonoid R]

/-- Normalize a hive labelling by subtracting its value at `A`. -/
def normalize (h : Vertex n → R) (hh : IsHive h) : Hive n R :=
  ofLabel (fun p => h p - h (Vertex.cornerA n))
    ((isHive_sub_const_iff _ _).mpr hh) (sub_self _)

/-- The labelling underlying normalization. -/
theorem coe_normalize (h : Vertex n → R) (hh : IsHive h) :
    (normalize h hh : Vertex n → R) = fun p => h p - h (Vertex.cornerA n) := (rfl)

@[simp] theorem normalize_apply (h : Vertex n → R) (hh : IsHive h) (p : Vertex n) :
    normalize h hh p = h p - h (Vertex.cornerA n) := (rfl)

/-- Normalization sends the zero labelling to the zero hive. -/
@[simp] theorem normalize_zero : normalize (0 : Vertex n → R) isHive_zero = 0 := by
  ext p
  simp

/-- Normalization sends every constant labelling to the zero hive. -/
@[simp] theorem normalize_const (c : R) :
    normalize (fun _ : Vertex n => c) (isHive_const c) = 0 := by
  ext p
  simp

/-- Normalization commutes with pointwise addition. -/
@[simp] theorem normalize_add (h k : Vertex n → R) (hh : IsHive h) (hk : IsHive k) :
    normalize (h + k) (hh.add hk) = normalize h hh + normalize k hk := by
  ext p
  simp only [normalize_apply, add_apply, Pi.add_apply]
  abel

/-- Normalizing an already normalized hive leaves it unchanged. -/
@[simp] theorem normalize_coe (h : Hive n R) : normalize (h : Vertex n → R) h.isHive = h := by
  ext p
  simp

/-- Normalization identifies precisely those labellings differing by a constant. -/
theorem normalize_eq_iff {h k : Vertex n → R} (hh : IsHive h) (hk : IsHive k) :
    normalize h hh = normalize k hk ↔ ∃ c, ∀ p, h p = k p + c := by
  constructor
  · intro he
    refine ⟨h (Vertex.cornerA n) - k (Vertex.cornerA n), fun p => ?_⟩
    have hp := congrArg (fun f : Hive n R => f p) he
    simp only [normalize_apply] at hp
    calc
      h p = (k p - k (Vertex.cornerA n)) + h (Vertex.cornerA n) :=
        (sub_eq_iff_eq_add).mp hp
      _ = k p + (h (Vertex.cornerA n) - k (Vertex.cornerA n)) := by abel
  · rintro ⟨c, hc⟩
    ext p
    simp only [normalize_apply, hc]
    abel

/-- Restrict to a translated subtriangle, then normalize at its first corner. -/
def restrict {m : ℕ} (h : Hive (m + n) R) (p : Vertex m) : Hive n R :=
  normalize (fun q => h (p.add q)) (h.isHive.restrict p)

/-- The labelling underlying normalized restriction. -/
theorem coe_restrict {m : ℕ} (h : Hive (m + n) R) (p : Vertex m) :
    (h.restrict p : Vertex n → R) = fun q => h (p.add q) - h (p.add (Vertex.cornerA n)) :=
  (rfl)

@[simp] theorem restrict_apply {m : ℕ} (h : Hive (m + n) R) (p : Vertex m)
    (q : Vertex n) : h.restrict p q = h (p.add q) - h (p.add (Vertex.cornerA n)) := (rfl)

/-- Restriction sends the zero hive to the zero hive. -/
@[simp] theorem restrict_zero {m : ℕ} (p : Vertex m) : (0 : Hive (m + n) R).restrict p = 0 := by
  ext q
  simp

/-- Restriction commutes with addition of hives. -/
@[simp] theorem restrict_add {m : ℕ} (h k : Hive (m + n) R) (p : Vertex m) :
    (h + k).restrict p = h.restrict p + k.restrict p := by
  ext q
  simp only [restrict_apply, add_apply]
  abel

/-- Restriction preserves the slopes of an affine hive. -/
@[simp] theorem restrict_affine {m : ℕ} (u v : R) (p : Vertex m) :
    (affine u v : Hive (m + n) R).restrict p = affine u v := by
  ext q
  simp only [restrict_apply, affine_apply, Vertex.add_y, Vertex.add_z, add_nsmul,
    Vertex.cornerA_y, Vertex.cornerA_z, add_zero]
  abel

end Group

end Hive
end TauCeti
