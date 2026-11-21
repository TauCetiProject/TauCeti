/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Algebra.Star.Basic
public import TauCeti.RingTheory.TwoSidedIdeal.Essential
public import TauCeti.RingTheory.TwoSidedIdeal.Kernel

/-!
# Annihilators of two-sided ideals

Left and right annihilators `TwoSidedIdeal.annihilator` and `TwoSidedIdeal.rightAnnihilator` of a
two-sided ideal, their antitone Galois connection, unital identifications with `Module.annihilator`,
and pseudocomplement / essentiality equivalences for self-adjoint ideals in proper star rings.

## Main declarations

* `TwoSidedIdeal.annihilator`, `TwoSidedIdeal.rightAnnihilator`,
  `TwoSidedIdeal.gc_annihilator_rightAnnihilator`.
* `TwoSidedIdeal.annihilator_eq_toTwoSided_annihilator`,
  `TwoSidedIdeal.annihilator_eq_rightAnnihilator_of_star_mem`,
  `TwoSidedIdeal.le_annihilator_iff_disjoint`, `TwoSidedIdeal.annihilator_eq_bot_iff_isEssential`.
-/

public section

open scoped Pointwise

namespace TwoSidedIdeal

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R] {I J : TwoSidedIdeal R} {a : R}

/-- The left annihilator `{a | ∀ x ∈ I, a * x = 0}` of a two-sided ideal `I`, which is a
two-sided ideal. -/
def annihilator (I : TwoSidedIdeal R) : TwoSidedIdeal R :=
  .mk' {a | ∀ x ∈ I, a * x = 0} (fun _ _ ↦ zero_mul _)
    (fun ha hb x hx ↦ by rw [add_mul, ha x hx, hb x hx, add_zero])
    (fun ha x hx ↦ by rw [neg_mul, ha x hx, neg_zero])
    (fun {b _} ha x hx ↦ by rw [mul_assoc, ha x hx, mul_zero])
    (fun {_ b} ha x hx ↦ by rw [mul_assoc, ha _ (I.mul_mem_left b x hx)])

/-- The *right annihilator* `{a : R | ∀ x ∈ I, x * a = 0}` of a two-sided ideal `I`, bundled as a
two-sided ideal of `R`. -/
def rightAnnihilator (I : TwoSidedIdeal R) : TwoSidedIdeal R :=
  .mk' {a : R | ∀ x ∈ I, x * a = 0}
    (fun _ _ => mul_zero _)
    (fun ha hb x hx => by rw [mul_add, ha x hx, hb x hx, add_zero])
    (fun ha x hx => by rw [mul_neg, ha x hx, neg_zero])
    -- Left absorption uses that `I` is a right ideal.
    (fun {r _} ha x hx => by rw [← mul_assoc]; exact ha (x * r) (I.mul_mem_right x r hx))
    (fun {_ _} ha x hx => by rw [← mul_assoc, ha x hx, zero_mul])

@[simp]
theorem mem_annihilator : a ∈ I.annihilator ↔ ∀ x ∈ I, a * x = 0 := by
  simp [annihilator]

theorem coe_annihilator (I : TwoSidedIdeal R) :
    (I.annihilator : Set R) = {a : R | ∀ x ∈ I, a * x = 0} :=
  Set.ext fun _ => mem_annihilator

@[simp]
theorem mem_rightAnnihilator : a ∈ I.rightAnnihilator ↔ ∀ x ∈ I, x * a = 0 := by
  simp [rightAnnihilator]

theorem coe_rightAnnihilator (I : TwoSidedIdeal R) :
    (I.rightAnnihilator : Set R) = {a : R | ∀ x ∈ I, x * a = 0} :=
  Set.ext fun _ => mem_rightAnnihilator

theorem mul_eq_zero_of_mem_annihilator {x : R} (ha : a ∈ I.annihilator) (hx : x ∈ I) :
    a * x = 0 :=
  mem_annihilator.1 ha x hx

theorem mul_eq_zero_of_mem_rightAnnihilator {x : R} (hx : x ∈ I) (ha : a ∈ I.rightAnnihilator) :
    x * a = 0 :=
  mem_rightAnnihilator.mp ha x hx

/-- A two-sided ideal lies in the annihilator of `I` exactly when its elements annihilate `I`
from the left. -/
theorem le_annihilator_iff : J ≤ I.annihilator ↔ ∀ a ∈ J, ∀ x ∈ I, a * x = 0 :=
  forall_congr' fun _ ↦ imp_congr_right fun _ ↦ mem_annihilator

/-- `I.rightAnnihilator` is the largest two-sided ideal `J` killing `I` on the right. -/
theorem le_rightAnnihilator_iff : J ≤ I.rightAnnihilator ↔ ∀ a ∈ J, ∀ x ∈ I, x * a = 0 :=
  forall_congr' fun _ => imp_congr_right fun _ => mem_rightAnnihilator

/-- Pointwise set-product form of the universal property of `I.annihilator`. -/
theorem le_annihilator_iff_coe_mul_eq_singleton_zero :
    J ≤ I.annihilator ↔ (J : Set R) * (I : Set R) = {0} := by
  rw [le_annihilator_iff]
  refine ⟨fun h => Set.Subset.antisymm ?_ ?_, fun h a ha x hx => ?_⟩
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr (h a ha x hx)
  · rw [Set.singleton_subset_iff]
    exact ⟨0, J.zero_mem, 0, I.zero_mem, mul_zero 0⟩
  · have hmem : a * x ∈ (J : Set R) * (I : Set R) := ⟨a, ha, x, hx, rfl⟩
    rwa [h, Set.mem_singleton_iff] at hmem

/-- Pointwise set-product form of the universal property of `I.rightAnnihilator`. -/
theorem le_rightAnnihilator_iff_coe_mul_eq_singleton_zero :
    J ≤ I.rightAnnihilator ↔ (I : Set R) * (J : Set R) = {0} := by
  rw [le_rightAnnihilator_iff]
  refine ⟨fun h => Set.Subset.antisymm ?_ ?_, fun h a ha x hx => ?_⟩
  · rintro _ ⟨x, hx, a, ha, rfl⟩
    exact Set.mem_singleton_iff.mpr (h a ha x hx)
  · rw [Set.singleton_subset_iff]
    exact ⟨0, I.zero_mem, 0, J.zero_mem, mul_zero 0⟩
  · have hmem : x * a ∈ (I : Set R) * (J : Set R) := ⟨x, hx, a, ha, rfl⟩
    rwa [h, Set.mem_singleton_iff] at hmem

theorem le_annihilator_iff_le_rightAnnihilator :
    J ≤ I.annihilator ↔ I ≤ J.rightAnnihilator := by
  rw [le_annihilator_iff, le_rightAnnihilator_iff]
  exact ⟨fun h x hx a ha => h a ha x hx, fun h a ha x hx => h x hx a ha⟩

/-- Antitone Galois connection between `annihilator` and `rightAnnihilator`. -/
theorem gc_annihilator_rightAnnihilator :
    GaloisConnection (OrderDual.toDual ∘ annihilator (R := R))
      (rightAnnihilator (R := R) ∘ OrderDual.ofDual) :=
  fun _ _ => le_annihilator_iff_le_rightAnnihilator

/-- Taking annihilators reverses inclusion. -/
theorem annihilator_antitone : Antitone (annihilator : TwoSidedIdeal R → TwoSidedIdeal R) :=
  fun _ _ hIJ _ ha ↦ mem_annihilator.2 fun _ hx ↦ mul_eq_zero_of_mem_annihilator ha (hIJ hx)

theorem annihilator_le_annihilator (h : I ≤ J) : J.annihilator ≤ I.annihilator :=
  annihilator_antitone h

theorem rightAnnihilator_anti : Antitone (rightAnnihilator (R := R)) :=
  fun _ _ h => gc_annihilator_rightAnnihilator.monotone_u h

theorem le_rightAnnihilator_annihilator (I : TwoSidedIdeal R) :
    I ≤ I.annihilator.rightAnnihilator :=
  le_annihilator_iff_le_rightAnnihilator.mp le_rfl

theorem le_annihilator_rightAnnihilator (I : TwoSidedIdeal R) :
    I ≤ I.rightAnnihilator.annihilator :=
  le_annihilator_iff_le_rightAnnihilator.mpr le_rfl

@[simp]
theorem annihilator_rightAnnihilator_annihilator (I : TwoSidedIdeal R) :
    I.annihilator.rightAnnihilator.annihilator = I.annihilator :=
  gc_annihilator_rightAnnihilator.l_u_l_eq_l I

@[simp]
theorem rightAnnihilator_annihilator_rightAnnihilator (I : TwoSidedIdeal R) :
    I.rightAnnihilator.annihilator.rightAnnihilator = I.rightAnnihilator :=
  gc_annihilator_rightAnnihilator.u_l_u_eq_u I

@[simp]
theorem annihilator_bot : (⊥ : TwoSidedIdeal R).annihilator = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_annihilator.2 fun x hx ↦ by
    rw [(mem_bot R).1 hx, mul_zero]

@[simp]
theorem rightAnnihilator_bot : (⊥ : TwoSidedIdeal R).rightAnnihilator = ⊤ :=
  gc_annihilator_rightAnnihilator.u_top

theorem annihilator_top_of_faithfulSMul [FaithfulSMul R R] :
    (⊤ : TwoSidedIdeal R).annihilator = ⊥ :=
  le_bot_iff.mp fun _ ha => (mem_bot _).mpr <| eq_of_smul_eq_smul fun x : R => by
    simpa [smul_eq_mul] using mul_eq_zero_of_mem_annihilator ha (mem_top R (x := x))

@[simp]
theorem rightAnnihilator_top [FaithfulSMul Rᵐᵒᵖ R] :
    (⊤ : TwoSidedIdeal R).rightAnnihilator = ⊥ :=
  le_bot_iff.mp fun _ ha => (mem_bot _).mpr <| MulOpposite.op_injective <|
    eq_of_smul_eq_smul fun x : R => by
      simpa [MulOpposite.smul_eq_mul_unop] using
        mul_eq_zero_of_mem_rightAnnihilator (mem_top R (x := x)) ha

@[simp]
theorem annihilator_eq_top_iff [FaithfulSMul Rᵐᵒᵖ R] {I : TwoSidedIdeal R} :
    I.annihilator = ⊤ ↔ I = ⊥ :=
  ⟨fun h => le_bot_iff.mp <| rightAnnihilator_top (R := R) ▸
      le_annihilator_iff_le_rightAnnihilator.mp h.ge,
   fun h => h ▸ annihilator_bot⟩

@[simp]
theorem rightAnnihilator_eq_top_iff [FaithfulSMul R R] {I : TwoSidedIdeal R} :
    I.rightAnnihilator = ⊤ ↔ I = ⊥ :=
  ⟨fun h => le_bot_iff.mp <| annihilator_top_of_faithfulSMul (R := R) ▸
      le_annihilator_iff_le_rightAnnihilator.mpr h.ge,
   fun h => h ▸ rightAnnihilator_bot⟩

@[simp]
theorem annihilator_sup : (I ⊔ J).annihilator = I.annihilator ⊓ J.annihilator :=
  le_antisymm (le_inf (annihilator_le_annihilator le_sup_left)
      (annihilator_le_annihilator le_sup_right))
    fun a ha ↦ by
      rw [mem_inf R, mem_annihilator, mem_annihilator] at ha
      refine mem_annihilator.2 fun x hx ↦ ?_
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hx
      rw [mul_add, ha.left y hy, ha.right z hz, add_zero]

theorem rightAnnihilator_sup (I J : TwoSidedIdeal R) :
    (I ⊔ J).rightAnnihilator = I.rightAnnihilator ⊓ J.rightAnnihilator :=
  gc_annihilator_rightAnnihilator.u_inf

theorem annihilator_iSup {ι : Sort*} (I : ι → TwoSidedIdeal R) :
    (⨆ i, I i).annihilator = ⨅ i, (I i).annihilator :=
  gc_annihilator_rightAnnihilator.l_iSup

theorem rightAnnihilator_iSup {ι : Sort*} (I : ι → TwoSidedIdeal R) :
    (⨆ i, I i).rightAnnihilator = ⨅ i, (I i).rightAnnihilator :=
  gc_annihilator_rightAnnihilator.u_iInf

/-- Pulling back along a ring equivalence commutes with `annihilator`. -/
@[simp]
theorem annihilator_comap {B E : Type*} [NonUnitalRing B]
    [EquivLike E R B] [NonUnitalRingHomClass E R B] (e : E) (I : TwoSidedIdeal B) :
    (I.comap e).annihilator = I.annihilator.comap e := by
  ext a
  rw [mem_annihilator, mem_comap, mem_annihilator]
  refine ⟨fun h y hy => ?_, fun h x hx => ?_⟩
  · have hmul := h (EquivLike.inv e y) ((mem_comap e).mpr (by simpa using hy))
    simpa [map_mul, map_zero] using congrArg e hmul
  · exact EquivLike.injective e (by simpa [map_mul, map_zero] using h (e x) ((mem_comap e).mp hx))

/-- Pulling back along a ring equivalence commutes with `rightAnnihilator`. -/
@[simp]
theorem rightAnnihilator_comap {B E : Type*} [NonUnitalRing B]
    [EquivLike E R B] [NonUnitalRingHomClass E R B] (e : E) (I : TwoSidedIdeal B) :
    (I.comap e).rightAnnihilator = I.rightAnnihilator.comap e := by
  ext a
  rw [mem_rightAnnihilator, mem_comap, mem_rightAnnihilator]
  refine ⟨fun h y hy => ?_, fun h x hx => ?_⟩
  · have hmul := h (EquivLike.inv e y) ((mem_comap e).mpr (by simpa using hy))
    simpa [map_mul, map_zero] using congrArg e hmul
  · exact EquivLike.injective e (by simpa [map_mul, map_zero] using h (e x) ((mem_comap e).mp hx))

/-- Every two-sided ideal disjoint from `I` annihilates `I`. -/
theorem le_annihilator_of_disjoint (h : Disjoint J I) : J ≤ I.annihilator :=
  le_annihilator_iff.2 fun a ha x hx ↦ (mem_bot R).1 <|
    h.le_bot ((mem_inf R).2 ⟨J.mul_mem_right a x ha, I.mul_mem_left a x hx⟩)

/-- Any two-sided ideal with `I ⊓ J = ⊥` lies in `I.annihilator`. -/
theorem le_annihilator_of_inf_eq_bot (h : I ⊓ J = ⊥) : J ≤ I.annihilator :=
  le_annihilator_of_disjoint (disjoint_iff.mpr h).symm

/-- Any two-sided ideal with `I ⊓ J = ⊥` lies in `I.rightAnnihilator`. -/
theorem le_rightAnnihilator_of_inf_eq_bot (h : I ⊓ J = ⊥) : J ≤ I.rightAnnihilator :=
  le_rightAnnihilator_iff.mpr fun a ha x hx =>
    (mem_bot _).mp <| h ▸ (⟨I.mul_mem_right x a hx, J.mul_mem_left x a ha⟩ : x * a ∈ I ⊓ J)

/-- An ideal with zero annihilator is essential. -/
theorem isEssential_of_annihilator_eq_bot (h : I.annihilator = ⊥) : I.IsEssential :=
  isEssential_iff.mpr fun _ hJ ↦ eq_bot_iff.2 <| h ▸ le_annihilator_of_disjoint hJ.symm

/-- A two-sided ideal with trivial right annihilator is essential. -/
theorem isEssential_of_rightAnnihilator_eq_bot (h : I.rightAnnihilator = ⊥) : I.IsEssential :=
  isEssential_iff_inf_eq_bot.mpr fun _ hIJ =>
    le_bot_iff.mp ((le_rightAnnihilator_of_inf_eq_bot hIJ).trans h.le)

theorem smul_mem_annihilator {M : Type*} [SMulZeroClass M R] [IsScalarTower M R R]
    (I : TwoSidedIdeal R) (c : M) {a : R} (ha : a ∈ I.annihilator) :
    c • a ∈ I.annihilator :=
  mem_annihilator.mpr fun x hx => by
    rw [smul_mul_assoc, mul_eq_zero_of_mem_annihilator ha hx, smul_zero]

theorem smul_mem_rightAnnihilator {M : Type*} [SMulZeroClass M R] [SMulCommClass M R R]
    (I : TwoSidedIdeal R) (c : M) {a : R} (ha : a ∈ I.rightAnnihilator) :
    c • a ∈ I.rightAnnihilator :=
  mem_rightAnnihilator.mpr fun x hx => by
    rw [mul_smul_comm, mul_eq_zero_of_mem_rightAnnihilator hx ha, smul_zero]

end NonUnitalRing

section Ring

variable {R : Type*} [Ring R] (I : TwoSidedIdeal R)

/-- In a unital ring, the annihilator of a two-sided ideal `I` is the module annihilator of `I`
as a left `R`-module, made two-sided. -/
theorem annihilator_eq_toTwoSided_annihilator :
    I.annihilator = (Module.annihilator R I.asIdeal).toTwoSided := by
  ext a
  simp [Module.mem_annihilator]

/-- In a unital ring `R`, `I.annihilator` coincides with `(Module.annihilator R I).toTwoSided`
for the left-multiplication `R`-module structure on `I`. -/
theorem annihilator_eq_moduleAnnihilator_toTwoSided :
    I.annihilator = (Module.annihilator R I).toTwoSided := by
  ext a
  rw [mem_annihilator, Ideal.mem_toTwoSided, Module.mem_annihilator]
  exact ⟨fun h x => Subtype.ext (h x x.property), fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩)⟩

/-- Membership in `(Module.annihilator R I).toTwoSided` for a two-sided ideal `I` of a unital
ring `R`. -/
theorem mem_moduleAnnihilator_toTwoSided_iff {a : R} :
    a ∈ (Module.annihilator R I).toTwoSided ↔ ∀ x ∈ I, a * x = 0 := by
  rw [← annihilator_eq_moduleAnnihilator_toTwoSided, mem_annihilator]

/-- For a two-sided ideal `I` of a unital ring `R`, `(Module.annihilator R I).toTwoSided` is
closed under compatible scalar multiplication. -/
theorem smul_mem_moduleAnnihilator_toTwoSided {M : Type*} [SMul M R] [IsScalarTower M R R]
    (c : M) {a : R} (ha : a ∈ (Module.annihilator R I).toTwoSided) :
    c • a ∈ (Module.annihilator R I).toTwoSided := by
  simpa only [smul_mul_assoc, one_mul] using
    (Module.annihilator R I).toTwoSided.mul_mem_left (c • (1 : R)) a ha

theorem asIdeal_annihilator : I.annihilator.asIdeal = Module.annihilator R I := by
  rw [annihilator_eq_moduleAnnihilator_toTwoSided, Ideal.asIdeal_toTwoSided]

/-- In a unital ring `R`, `I.rightAnnihilator.asIdealOpposite` coincides with
`Module.annihilator Rᵐᵒᵖ I` for the right-multiplication `Rᵐᵒᵖ`-module structure on `I`. -/
theorem asIdealOpposite_rightAnnihilator :
    I.rightAnnihilator.asIdealOpposite = Module.annihilator Rᵐᵒᵖ I := by
  ext r
  rw [mem_asIdealOpposite, mem_rightAnnihilator, Module.mem_annihilator]
  exact ⟨fun h x => Subtype.ext (h x x.property), fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩)⟩

theorem le_annihilator_iff_asIdeal_mul_eq_bot {I J : TwoSidedIdeal R} :
    J ≤ I.annihilator ↔ J.asIdeal * I.asIdeal = ⊥ := by
  rw [← le_bot_iff, Ideal.mul_le, le_annihilator_iff]
  simp only [mem_asIdeal, Submodule.mem_bot]

theorem le_rightAnnihilator_iff_asIdeal_mul_eq_bot {I J : TwoSidedIdeal R} :
    J ≤ I.rightAnnihilator ↔ I.asIdeal * J.asIdeal = ⊥ := by
  rw [← le_bot_iff, Ideal.mul_le, le_rightAnnihilator_iff]
  simp only [mem_asIdeal, Submodule.mem_bot]
  exact ⟨fun h x hx a ha => h a ha x hx, fun h a ha x hx => h x hx a ha⟩

@[simp]
theorem annihilator_top : (⊤ : TwoSidedIdeal R).annihilator = ⊥ :=
  eq_bot_iff.2 fun a ha ↦ (mem_bot R).2 <| by
    simpa using mul_eq_zero_of_mem_annihilator ha (mem_top R (x := (1 : R)))

end Ring

section IsProperStar

variable {R : Type*} [NonUnitalRing R] [StarRing R] [IsProperStar R] {I J : TwoSidedIdeal R}
  {a : R}

/-- In a proper star ring, an element annihilating a self-adjoint ideal from the left also
annihilates it from the right. -/
theorem mul_eq_zero_of_star_mem_of_mem_annihilator (hI : ∀ x ∈ I, star x ∈ I)
    (ha : a ∈ I.annihilator) {x : R} (hx : x ∈ I) : x * a = 0 := by
  -- `(x * a) * star (x * a) = x * (a * (star a * star x))`, and `star a * star x ∈ I`.
  rw [← mul_star_self_eq_zero, star_mul, mul_assoc,
    mul_eq_zero_of_mem_annihilator ha (I.mul_mem_left _ _ (hI x hx)), mul_zero]

/-- The annihilator of a self-adjoint ideal is self-adjoint. -/
theorem star_mem_annihilator (hI : ∀ x ∈ I, star x ∈ I) (ha : a ∈ I.annihilator) :
    star a ∈ I.annihilator :=
  mem_annihilator.2 fun x hx ↦ by
    rw [← star_star x, ← star_mul,
      mul_eq_zero_of_star_mem_of_mem_annihilator hI ha (hI x hx), star_zero]

theorem star_mem_annihilator_iff (hI : ∀ x ∈ I, star x ∈ I) :
    star a ∈ I.annihilator ↔ a ∈ I.annihilator :=
  ⟨fun h ↦ star_star a ▸ star_mem_annihilator hI h, star_mem_annihilator hI⟩

/-- In a proper star ring, the annihilator of a self-adjoint ideal is also its right
annihilator. -/
theorem mem_annihilator_iff_mul_left (hI : ∀ x ∈ I, star x ∈ I) :
    a ∈ I.annihilator ↔ ∀ x ∈ I, x * a = 0 := by
  refine ⟨fun ha x hx ↦ mul_eq_zero_of_star_mem_of_mem_annihilator hI ha hx, fun ha ↦ ?_⟩
  rw [← star_mem_annihilator_iff hI]
  exact mem_annihilator.2 fun x hx ↦ by
    rw [← star_star x, ← star_mul, ha _ (hI x hx), star_zero]

/-- For a self-adjoint two-sided ideal `I` in a ring with proper involution, the left and right
annihilators of `I` coincide. -/
theorem annihilator_eq_rightAnnihilator_of_star_mem (hI : ∀ x ∈ I, star x ∈ I) :
    I.annihilator = I.rightAnnihilator :=
  ext fun _ => (mem_annihilator_iff_mul_left hI).trans mem_rightAnnihilator.symm

theorem star_mem_rightAnnihilator_of_star_mem (hI : ∀ x ∈ I, star x ∈ I)
    (ha : a ∈ I.rightAnnihilator) : star a ∈ I.rightAnnihilator := by
  rw [← annihilator_eq_rightAnnihilator_of_star_mem hI] at ha ⊢
  exact star_mem_annihilator hI ha

/-- A self-adjoint ideal meets its annihilator only in `0`. -/
theorem disjoint_annihilator (hI : ∀ x ∈ I, star x ∈ I) : Disjoint I I.annihilator := by
  refine disjoint_iff.2 <| eq_bot_iff.2 fun a ha ↦ (mem_bot R).2 ?_
  rw [mem_inf R] at ha
  exact mul_star_self_eq_zero.1 (mul_eq_zero_of_mem_annihilator ha.right (hI a ha.left))

@[simp]
theorem inf_annihilator (hI : ∀ x ∈ I, star x ∈ I) : I ⊓ I.annihilator = ⊥ :=
  disjoint_iff.1 (disjoint_annihilator hI)

theorem annihilator_inf_of_star_mem (hI : ∀ x ∈ I, star x ∈ I) : I.annihilator ⊓ I = ⊥ := by
  rw [inf_comm]
  exact inf_annihilator hI

/-- The annihilator of a self-adjoint ideal `I` is the largest two-sided ideal disjoint from
`I`. -/
theorem le_annihilator_iff_disjoint (hI : ∀ x ∈ I, star x ∈ I) :
    J ≤ I.annihilator ↔ Disjoint J I :=
  ⟨fun h ↦ (disjoint_annihilator hI).symm.mono_left h, le_annihilator_of_disjoint⟩

theorem le_annihilator_iff_inf_eq_bot_of_star_mem (hI : ∀ x ∈ I, star x ∈ I) :
    J ≤ I.annihilator ↔ I ⊓ J = ⊥ := by
  rw [le_annihilator_iff_disjoint hI, disjoint_comm, disjoint_iff]

theorem le_annihilator_annihilator (hI : ∀ x ∈ I, star x ∈ I) :
    I ≤ I.annihilator.annihilator :=
  le_annihilator_iff_disjoint (fun _ ↦ star_mem_annihilator hI) |>.2 (disjoint_annihilator hI)

@[simp]
theorem annihilator_annihilator_annihilator (hI : ∀ x ∈ I, star x ∈ I) :
    I.annihilator.annihilator.annihilator = I.annihilator :=
  le_antisymm (annihilator_le_annihilator (le_annihilator_annihilator hI))
    (le_annihilator_annihilator fun _ ↦ star_mem_annihilator hI)

/-- In a proper star ring, nothing annihilates the whole ring. -/
@[simp]
theorem annihilator_top_of_isProperStar : (⊤ : TwoSidedIdeal R).annihilator = ⊥ :=
  top_inf_eq (⊤ : TwoSidedIdeal R).annihilator ▸
    inf_annihilator (I := (⊤ : TwoSidedIdeal R)) fun _ _ ↦ mem_top R

/-- A self-adjoint ideal is essential exactly when its annihilator vanishes. -/
theorem annihilator_eq_bot_iff_isEssential (hI : ∀ x ∈ I, star x ∈ I) :
    I.annihilator = ⊥ ↔ I.IsEssential :=
  ⟨isEssential_of_annihilator_eq_bot, fun h ↦ h.eq_bot_of_disjoint (disjoint_annihilator hI)⟩

theorem isEssential_iff_rightAnnihilator_eq_bot_of_star_mem (hI : ∀ x ∈ I, star x ∈ I) :
    I.IsEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [← annihilator_eq_bot_iff_isEssential hI, annihilator_eq_rightAnnihilator_of_star_mem hI]

end IsProperStar

section Prod

/-- In a product `A × B` of nonunital rings, the left annihilator of `ker snd = A × {0}` is the
preimage of `(⊤ : TwoSidedIdeal A).annihilator` along `fst`. -/
theorem annihilator_ker_snd_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).annihilator =
      (⊤ : TwoSidedIdeal A).annihilator.comap (NonUnitalRingHom.fst A B) := by
  ext p
  rw [mem_annihilator, mem_comap, mem_annihilator]
  refine ⟨fun h a _ => congrArg Prod.fst (h (a, 0) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  rw [mem_ker, NonUnitalRingHom.coe_snd] at hx
  ext
  · exact h x.fst (mem_top A)
  · simp [hx]

theorem rightAnnihilator_ker_snd_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).rightAnnihilator =
      (⊤ : TwoSidedIdeal A).rightAnnihilator.comap (NonUnitalRingHom.fst A B) := by
  ext p
  rw [mem_rightAnnihilator, mem_comap, mem_rightAnnihilator]
  refine ⟨fun h a _ => congrArg Prod.fst (h (a, 0) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  rw [mem_ker, NonUnitalRingHom.coe_snd] at hx
  ext
  · exact h x.fst (mem_top A)
  · simp [hx]

/-- In a product `A × B` of nonunital rings, the left annihilator of `ker fst = {0} × B` is the
preimage of `(⊤ : TwoSidedIdeal B).annihilator` along `snd`. -/
theorem annihilator_ker_fst_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).annihilator =
      (⊤ : TwoSidedIdeal B).annihilator.comap (NonUnitalRingHom.snd A B) := by
  ext p
  rw [mem_annihilator, mem_comap, mem_annihilator]
  refine ⟨fun h b _ => congrArg Prod.snd (h (0, b) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  rw [mem_ker, NonUnitalRingHom.coe_fst] at hx
  ext
  · simp [hx]
  · exact h x.snd (mem_top B)

theorem rightAnnihilator_ker_fst_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).rightAnnihilator =
      (⊤ : TwoSidedIdeal B).rightAnnihilator.comap (NonUnitalRingHom.snd A B) := by
  ext p
  rw [mem_rightAnnihilator, mem_comap, mem_rightAnnihilator]
  refine ⟨fun h b _ => congrArg Prod.snd (h (0, b) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  rw [mem_ker, NonUnitalRingHom.coe_fst] at hx
  ext
  · simp [hx]
  · exact h x.snd (mem_top B)

/-- In a product `A × B` with `[FaithfulSMul A A]`, the left annihilator of the first-factor ideal
`A × {0} = ker snd` is the second-factor ideal `{0} × B = ker fst`. -/
@[simp]
theorem annihilator_ker_snd {A B : Type*} [NonUnitalRing A] [FaithfulSMul A A]
    [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).annihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) := by
  ext p
  simp [annihilator_ker_snd_eq_comap, mem_comap, mem_ker, annihilator_top_of_faithfulSMul]

/-- In a product `A × B` with `[FaithfulSMul Aᵐᵒᵖ A]`, the right annihilator of the first-factor
ideal `A × {0} = ker snd` is the second-factor ideal `{0} × B = ker fst`. -/
@[simp]
theorem rightAnnihilator_ker_snd {A B : Type*} [NonUnitalRing A] [FaithfulSMul Aᵐᵒᵖ A]
    [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).rightAnnihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) := by
  ext p
  simp [rightAnnihilator_ker_snd_eq_comap, mem_comap, mem_ker]

/-- In a product `A × B` with `[FaithfulSMul B B]`, the left annihilator of the second-factor ideal
`{0} × B = ker fst` is the first-factor ideal `A × {0} = ker snd`. -/
@[simp]
theorem annihilator_ker_fst {A B : Type*} [NonUnitalRing A]
    [NonUnitalRing B] [FaithfulSMul B B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).annihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) := by
  ext p
  simp [annihilator_ker_fst_eq_comap, mem_comap, mem_ker, annihilator_top_of_faithfulSMul]

/-- In a product `A × B` with `[FaithfulSMul Bᵐᵒᵖ B]`, the right annihilator of the second-factor
ideal `{0} × B = ker fst` is the first-factor ideal `A × {0} = ker snd`. -/
@[simp]
theorem rightAnnihilator_ker_fst {A B : Type*} [NonUnitalRing A]
    [NonUnitalRing B] [FaithfulSMul Bᵐᵒᵖ B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).rightAnnihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) := by
  ext p
  simp [rightAnnihilator_ker_fst_eq_comap, mem_comap, mem_ker]

@[simp]
theorem annihilator_ker_snd_nonUnitalStarAlgHom {R A B : Type*} [Monoid R]
    [NonUnitalRing A] [DistribMulAction R A] [Star A] [FaithfulSMul A A]
    [NonUnitalRing B] [DistribMulAction R B] [Star B] :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd R A B)).annihilator =
      TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst R A B) := by
  rw [ker_nonUnitalStarAlgHom_snd, ker_nonUnitalStarAlgHom_fst, annihilator_ker_snd]

@[simp]
theorem rightAnnihilator_ker_snd_nonUnitalStarAlgHom {R A B : Type*} [Monoid R]
    [NonUnitalRing A] [DistribMulAction R A] [Star A] [FaithfulSMul Aᵐᵒᵖ A]
    [NonUnitalRing B] [DistribMulAction R B] [Star B] :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd R A B)).rightAnnihilator =
      TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst R A B) := by
  rw [ker_nonUnitalStarAlgHom_snd, ker_nonUnitalStarAlgHom_fst, rightAnnihilator_ker_snd]

@[simp]
theorem annihilator_ker_fst_nonUnitalStarAlgHom {R A B : Type*} [Monoid R]
    [NonUnitalRing A] [DistribMulAction R A] [Star A]
    [NonUnitalRing B] [DistribMulAction R B] [Star B] [FaithfulSMul B B] :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst R A B)).annihilator =
      TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd R A B) := by
  rw [ker_nonUnitalStarAlgHom_fst, ker_nonUnitalStarAlgHom_snd, annihilator_ker_fst]

@[simp]
theorem rightAnnihilator_ker_fst_nonUnitalStarAlgHom {R A B : Type*} [Monoid R]
    [NonUnitalRing A] [DistribMulAction R A] [Star A]
    [NonUnitalRing B] [DistribMulAction R B] [Star B] [FaithfulSMul Bᵐᵒᵖ B] :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst R A B)).rightAnnihilator =
      TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd R A B) := by
  rw [ker_nonUnitalStarAlgHom_fst, ker_nonUnitalStarAlgHom_snd, rightAnnihilator_ker_fst]

end Prod

end TwoSidedIdeal
