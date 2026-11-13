/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.WithZero

/-!
# Addition-closed subgroups of units

An addition-closed subgroup of the units of a commutative semiring inherits a
coefficient semifield structure. Its auxiliary addition is the given ambient addition.
Adjoining zero realizes it as a subsemiring; over a nontrivial ambient semiring this
subsemiring is a semifield, even when the ambient semiring has zero divisors.

Semiring maps carrying one such subgroup into another induce coefficient-semifield
maps and maps of the realized subsemirings. These constructions let subtraction-free
evaluation take values in an ambient algebra without requiring all its units to be
closed under addition.

Inversion uses Mathlib's `commGroupWithZeroOfIsUnitOrEqZero`; the comparison
with zero adjunction uses `WithZero.lift'` and `MulEquiv.ofBijective`.

The coefficient-semifield convention is that of Fomin–Zelevinsky,
*Cluster algebras IV: Coefficients*, Definition 2.1.
-/

public section

namespace Subgroup

open TauCeti

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/-- A subgroup of ambient units is addition-closed if every sum of its values is
again the value of a member. This includes the requirement that these sums are units. -/
class IsAddClosed (G : Subgroup Rˣ) : Prop where
  /-- Closure under the addition of the ambient semiring. -/
  exists_add (a b : G) : ∃ c : G, ((c : Rˣ) : R) = (a : Rˣ) + (b : Rˣ)

variable (G : Subgroup Rˣ) [G.IsAddClosed]

/-- The auxiliary addition is the unique lift of ambient addition. -/
noncomputable instance instAddOfIsAddClosed : Add G where
  add a b := (IsAddClosed.exists_add a b).choose

/-- The inclusion of an addition-closed unit subgroup preserves auxiliary addition. -/
@[simp, norm_cast]
theorem val_add (a b : G) : ((a + b : G) : Rˣ).val = (a : Rˣ) + (b : Rˣ) :=
  (IsAddClosed.exists_add a b).choose_spec

/-- An addition-closed subgroup of units is a coefficient semifield. -/
noncomputable instance : CoefficientSemifield G where
  add_assoc a b c := Subtype.ext <| Units.ext <| by simp only [val_add, add_assoc]
  add_comm a b := Subtype.ext <| Units.ext <| by simp only [val_add, add_comm]
  left_distrib a b c := Subtype.ext <| Units.ext <| by simp [mul_add]
  right_distrib a b c := Subtype.ext <| Units.ext <| by simp [add_mul]

/-- The subsemiring consisting of zero and the values of the subgroup. -/
def withZeroSubsemiring : Subsemiring R where
  carrier := {r | r = 0 ∨ ∃ a : G, ((a : Rˣ) : R) = r}
  zero_mem' := Or.inl rfl
  one_mem' := Or.inr ⟨1, rfl⟩
  add_mem' := by
    rintro x y (rfl | ⟨a, rfl⟩) (rfl | ⟨b, rfl⟩)
    · exact Or.inl (zero_add 0)
    · exact Or.inr ⟨b, zero_add _ |>.symm⟩
    · exact Or.inr ⟨a, add_zero _ |>.symm⟩
    · exact Or.inr ⟨a + b, G.val_add a b⟩
  mul_mem' := by
    rintro x y (rfl | ⟨a, rfl⟩) (rfl | ⟨b, rfl⟩)
    · exact Or.inl (zero_mul 0)
    · exact Or.inl (zero_mul _)
    · exact Or.inl (mul_zero _)
    · exact Or.inr ⟨a * b, rfl⟩

@[simp]
theorem mem_withZeroSubsemiring (r : R) :
    r ∈ G.withZeroSubsemiring ↔ r = 0 ∨ ∃ a : G, ((a : Rˣ) : R) = r :=
  Iff.rfl

/-- The inclusion of the subgroup into the units of its realized subsemiring. -/
def toWithZeroSubsemiringUnits : G →* G.withZeroSubsemiringˣ :=
  (((Units.coeHom R).comp G.subtype).codRestrict G.withZeroSubsemiring
    fun a ↦ Or.inr ⟨a, rfl⟩).toHomUnits

@[simp]
theorem val_toWithZeroSubsemiringUnits (a : G) :
    ((G.toWithZeroSubsemiringUnits a : G.withZeroSubsemiring) : R) = (a : Rˣ) :=
  (rfl)

/-- The inclusion of subgroup members into the realized unit group is injective. -/
theorem toWithZeroSubsemiringUnits_injective :
    Function.Injective G.toWithZeroSubsemiringUnits := fun _ _ h ↦
  Subtype.ext (Units.ext (by simpa using congrArg Subtype.val (congrArg Units.val h)))

/-- The underlying values of two included subgroup members are equal precisely when the
members are equal. -/
@[simp]
theorem toWithZeroSubsemiringUnits_inj (a b : G) :
    G.toWithZeroSubsemiringUnits a = G.toWithZeroSubsemiringUnits b ↔ a = b :=
  (toWithZeroSubsemiringUnits_injective G).eq_iff

/-- The included subgroup members coerce to equal realized elements precisely when the
members are equal. -/
@[simp]
theorem coe_toWithZeroSubsemiringUnits_inj (a b : G) :
    (G.toWithZeroSubsemiringUnits a : G.withZeroSubsemiring) =
      G.toWithZeroSubsemiringUnits b ↔ a = b := by
  exact ⟨fun h ↦ toWithZeroSubsemiringUnits_injective G (Units.ext h),
    congrArg (fun a : G ↦ (G.toWithZeroSubsemiringUnits a : G.withZeroSubsemiring))⟩

/-- An included subgroup member is the identity precisely when the member is the identity. -/
@[simp]
theorem toWithZeroSubsemiringUnits_eq_one (a : G) :
    G.toWithZeroSubsemiringUnits a = 1 ↔ a = 1 := by
  simpa only [← map_one G.toWithZeroSubsemiringUnits] using G.toWithZeroSubsemiringUnits_inj a 1

/-- The value of every nonzero element of the realized subsemiring comes from the subgroup. -/
theorem exists_val_of_ne_zero {a : G.withZeroSubsemiring} (ha : a ≠ 0) :
    ∃ b : G, ((b : Rˣ) : R) = (a : R) := by
  exact a.property.resolve_left (fun h ↦ ha (Subtype.ext h))

/-- The realized subsemiring is a semifield. Ambient multiplication and addition are
retained; only inversion of zero and of subgroup values is added. -/
noncomputable instance [Nontrivial R] : Semifield G.withZeroSubsemiring where
  toCommSemiring := inferInstance
  __ := commGroupWithZeroOfIsUnitOrEqZero fun a ↦
    or_iff_not_imp_right.mpr (fun ha ↦ by
      obtain ⟨b, hb⟩ := G.exists_val_of_ne_zero ha
      exact ⟨G.toWithZeroSubsemiringUnits b,
        Subtype.ext ((G.val_toWithZeroSubsemiringUnits b).trans hb)⟩)
  nnqsmul := _
  nnqsmul_def _ _ := rfl

/-- The ambient value of a realized inverse unit is an ambient inverse unit. -/
@[simp]
theorem val_inv_toWithZeroSubsemiringUnits (a : G) :
    ((((G.toWithZeroSubsemiringUnits a)⁻¹ : G.withZeroSubsemiringˣ) :
      G.withZeroSubsemiring) : R) = (((a : Rˣ)⁻¹ : Rˣ) : R) :=
  G.val_toWithZeroSubsemiringUnits a⁻¹

/-- The ambient value of a division of realized units is a division of ambient units. -/
@[simp]
theorem val_div_toWithZeroSubsemiringUnits (a b : G) :
    (((G.toWithZeroSubsemiringUnits a / G.toWithZeroSubsemiringUnits b :
      G.withZeroSubsemiringˣ) : G.withZeroSubsemiring) : R) =
      (((a : Rˣ) / (b : Rˣ) : Rˣ) : R) := by
  rw [← map_div]
  exact G.val_toWithZeroSubsemiringUnits (a / b)

/-- The ambient value of an integer power of a realized unit is an ambient integer power. -/
@[simp]
theorem val_zpow_toWithZeroSubsemiringUnits (a : G) (n : ℤ) :
    (((G.toWithZeroSubsemiringUnits a ^ n : G.withZeroSubsemiringˣ) :
      G.withZeroSubsemiring) : R) = (((a : Rˣ) ^ n : Rˣ) : R) := by
  rw [← map_zpow]
  exact G.val_toWithZeroSubsemiringUnits (a ^ n)

/-- Realized inversion agrees with the inverse of the corresponding unit. -/
private theorem inv_val_toWithZeroSubsemiringUnits [Nontrivial R] (a : G) :
    (G.toWithZeroSubsemiringUnits a : G.withZeroSubsemiring)⁻¹ =
      ((G.toWithZeroSubsemiringUnits a)⁻¹ : G.withZeroSubsemiringˣ) :=
  inv_eq_of_mul_eq_one_left (G.toWithZeroSubsemiringUnits a).inv_mul

/-- Ambient inclusion preserves inversion of subgroup members, viewed as ambient units. -/
@[simp]
theorem coe_inv_toWithZeroSubsemiringUnits [Nontrivial R] (a : G) :
    (((G.toWithZeroSubsemiringUnits a : G.withZeroSubsemiring)⁻¹ : G.withZeroSubsemiring) : R) =
      (((a : Rˣ)⁻¹ : Rˣ) : R) := by
  rw [inv_val_toWithZeroSubsemiringUnits, val_inv_toWithZeroSubsemiringUnits]

/-- Ambient inclusion preserves division of subgroup members, viewed as ambient units. -/
@[simp]
theorem coe_div_toWithZeroSubsemiringUnits [Nontrivial R] (a b : G) :
    (((G.toWithZeroSubsemiringUnits a : G.withZeroSubsemiring) /
      (G.toWithZeroSubsemiringUnits b : G.withZeroSubsemiring) : G.withZeroSubsemiring) : R) =
      (((a : Rˣ) / (b : Rˣ) : Rˣ) : R) := by
  rw [div_eq_mul_inv, inv_val_toWithZeroSubsemiringUnits, ← Units.val_mul]
  have h : G.toWithZeroSubsemiringUnits a * (G.toWithZeroSubsemiringUnits b)⁻¹ =
      G.toWithZeroSubsemiringUnits a / G.toWithZeroSubsemiringUnits b :=
    div_eq_mul_inv _ _
  rw [h, val_div_toWithZeroSubsemiringUnits]

/-- Ambient inclusion preserves integer powers of subgroup members, viewed as ambient units. -/
@[simp]
theorem coe_zpow_toWithZeroSubsemiringUnits [Nontrivial R] (a : G) (n : ℤ) :
    (((G.toWithZeroSubsemiringUnits a : G.withZeroSubsemiring) ^ n : G.withZeroSubsemiring) : R) =
      (((a : Rˣ) ^ n : Rˣ) : R) := by
  rw [← Units.val_zpow_eq_zpow_val (G.toWithZeroSubsemiringUnits a) n]
  exact val_zpow_toWithZeroSubsemiringUnits G a n

section AmbientSemifield

variable {F : Type*} [Semifield F] (P : Subgroup Fˣ) [P.IsAddClosed]

/-- Coercion from a realized semifield preserves inversion. -/
@[simp, norm_cast]
theorem coe_inv_withZeroSubsemiring (a : P.withZeroSubsemiring) :
    ((a⁻¹ : P.withZeroSubsemiring) : F) = (a : F)⁻¹ :=
  map_inv₀ P.withZeroSubsemiring.subtype a

/-- Coercion from a realized semifield preserves division. -/
@[simp, norm_cast]
theorem coe_div_withZeroSubsemiring (a b : P.withZeroSubsemiring) :
    ((a / b : P.withZeroSubsemiring) : F) = (a : F) / (b : F) :=
  map_div₀ P.withZeroSubsemiring.subtype a b

/-- Coercion from a realized semifield preserves integer powers. -/
@[simp, norm_cast]
theorem coe_zpow_withZeroSubsemiring (a : P.withZeroSubsemiring) (n : ℤ) :
    ((a ^ n : P.withZeroSubsemiring) : F) = (a : F) ^ n :=
  map_zpow₀ P.withZeroSubsemiring.subtype a n

end AmbientSemifield

/-- The inclusion after adjoining zero, as a multiplicative map. -/
private def withZeroSubsemiringHom : WithZero G →*₀ G.withZeroSubsemiring :=
  WithZero.lift' ((Units.coeHom _).comp G.toWithZeroSubsemiringUnits)

/-- The inclusion after adjoining zero sends a subgroup member to its unit copy. -/
@[simp]
private theorem withZeroSubsemiringHom_coe (a : G) :
    G.withZeroSubsemiringHom a = G.toWithZeroSubsemiringUnits a := rfl

private theorem withZeroSubsemiringHom_coe_ne_zero [Nontrivial R] (a : G) :
    G.withZeroSubsemiringHom a ≠ 0 :=
  Units.ne_zero (G.toWithZeroSubsemiringUnits a)

private noncomputable def withZeroSubsemiringMulEquiv [Nontrivial R] :
    WithZero G ≃* G.withZeroSubsemiring :=
  MulEquiv.ofBijective G.withZeroSubsemiringHom
    ⟨by
      intro a b h
      induction a using WithZero.recZeroCoe <;>
        induction b using WithZero.recZeroCoe
      · rfl
      · rename_i b
        exact absurd h.symm (G.withZeroSubsemiringHom_coe_ne_zero b)
      · rename_i a
        exact absurd h (G.withZeroSubsemiringHom_coe_ne_zero a)
      · rename_i a b
        exact congrArg WithZero.coe <|
          Subtype.ext <| Units.ext <| by simpa using congrArg Subtype.val h,
      by
        intro a
        obtain h | ⟨b, hb⟩ := a.property
        · exact ⟨0, Subtype.ext (by simp [h])⟩
        · exact ⟨b, Subtype.ext (by simp [hb])⟩⟩

@[simp]
private theorem withZeroSubsemiringMulEquiv_apply [Nontrivial R] (a : WithZero G) :
    G.withZeroSubsemiringMulEquiv a = G.withZeroSubsemiringHom a := rfl

/-- Adjoining one zero identifies a subgroup with its realized subsemiring, preserving
both multiplication and auxiliary addition. -/
noncomputable def withZeroSubsemiringEquiv [Nontrivial R] :
    WithZero G ≃+* G.withZeroSubsemiring :=
  { G.withZeroSubsemiringMulEquiv with
    map_add' := by
      intro a b
      induction a using WithZero.recZeroCoe <;>
        induction b using WithZero.recZeroCoe
      · exact zero_add _ |>.symm
      · exact zero_add _ |>.symm
      · exact add_zero _ |>.symm
      · rename_i a b
        exact Subtype.ext <| by simp [← WithZero.coe_add] }

@[simp]
theorem withZeroSubsemiringEquiv_coe [Nontrivial R] (a : G) :
    G.withZeroSubsemiringEquiv (a : WithZero G) = G.toWithZeroSubsemiringUnits a :=
  (rfl)

/-- The inverse comparison sends an included subgroup member to its nonzero copy. -/
@[simp]
theorem withZeroSubsemiringEquiv_symm_toWithZeroSubsemiringUnits [Nontrivial R] (a : G) :
    G.withZeroSubsemiringEquiv.symm (G.toWithZeroSubsemiringUnits a) = (a : WithZero G) :=
  G.withZeroSubsemiringEquiv.symm_apply_eq.mpr (G.withZeroSubsemiringEquiv_coe a).symm

/-- Nonzero sums in the realized subsemiring cannot cancel to zero. -/
instance : Subsingleton (AddUnits G.withZeroSubsemiring) := by
  refine subsingleton_of_forall_eq 0 fun u ↦ AddUnits.ext ?_
  by_contra hu
  have : Nontrivial R := ⟨u.val.val, 0, fun h ↦ hu (Subtype.ext h)⟩
  obtain ⟨a, ha⟩ := G.exists_val_of_ne_zero hu
  have hb : (↑(-u) : G.withZeroSubsemiring) ≠ 0 := by
    intro h
    have := u.val_neg
    simp_all
  obtain ⟨b, hb⟩ := G.exists_val_of_ne_zero hb
  have hsum : ((a + b : G) : Rˣ).val = 0 := by
    rw [G.val_add, ha, hb]
    exact congrArg Subtype.val u.val_neg
  exact (a + b : G).val.ne_zero hsum

/-- The inclusion into the realized unit group preserves auxiliary addition. -/
@[simp]
theorem toWithZeroSubsemiringUnits_add [Nontrivial R] (a b : G) :
    G.toWithZeroSubsemiringUnits (a + b) =
      G.toWithZeroSubsemiringUnits a + G.toWithZeroSubsemiringUnits b := by
  ext
  simp

/-- The image of an addition-closed unit subgroup under a semiring map is addition-closed. -/
instance isAddClosed_map (f : R →+* S) :
    (G.map (Units.map (f : R →* S))).IsAddClosed where
  exists_add a b := by
    obtain ⟨a, ha, ea⟩ := a.property
    obtain ⟨b, hb, eb⟩ := b.property
    refine ⟨⟨Units.map (f : R →* S) (⟨a, ha⟩ + ⟨b, hb⟩ : G),
      mem_map.mpr ⟨_, (⟨a, ha⟩ + ⟨b, hb⟩ : G).property, rfl⟩⟩, ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_ofClass, G.val_add, ← ea, ← eb]
    exact map_add f _ _

/-- Realization commutes with taking the image under an ambient semiring map. -/
@[simp]
theorem withZeroSubsemiring_map (f : R →+* S) :
    (G.map (Units.map (f : R →* S))).withZeroSubsemiring = G.withZeroSubsemiring.map f := by
  ext r
  constructor
  · rintro (rfl | ⟨a, ha⟩)
    · exact ⟨0, G.withZeroSubsemiring.zero_mem, map_zero f⟩
    · obtain ⟨b, hb, eb⟩ := a.property
      exact ⟨b, Or.inr ⟨⟨b, hb⟩, rfl⟩, (congrArg Units.val eb).trans ha⟩
  · rintro ⟨a, (rfl | ⟨b, rfl⟩), rfl⟩
    · exact Or.inl (map_zero f)
    · exact Or.inr ⟨⟨Units.map (f : R →* S) b,
        mem_map.mpr ⟨b, b.property, rfl⟩⟩, rfl⟩

variable (H : Subgroup Sˣ) [H.IsAddClosed]

/-- Products of addition-closed unit subgroups are addition-closed under the canonical
identification of units of a product with pairs of units. -/
instance isAddClosed_prod :
    ((G.prod H).comap MulEquiv.prodUnits.toMonoidHom).IsAddClosed where
  exists_add a b := by
    let aG : G := ⟨(MulEquiv.prodUnits (a : (R × S)ˣ)).1, a.property.1⟩
    let bG : G := ⟨(MulEquiv.prodUnits (b : (R × S)ˣ)).1, b.property.1⟩
    let aH : H := ⟨(MulEquiv.prodUnits (a : (R × S)ˣ)).2, a.property.2⟩
    let bH : H := ⟨(MulEquiv.prodUnits (b : (R × S)ˣ)).2, b.property.2⟩
    refine ⟨⟨MulEquiv.prodUnits.symm ((aG + bG : G), (aH + bH : H)), ?_⟩, ?_⟩
    · simp [mem_prod]
    · exact Prod.ext (G.val_add aG bG) (H.val_add aH bH)

/-- A semiring map carrying subgroup members into the target subgroup restricts to a
coefficient-semifield homomorphism. No injectivity or ambient semifield is required. -/
def coefficientSemifieldMap (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H) : CoefficientSemifieldHom G H where
  __ := (Units.map f.toMonoidHom |>.comp G.subtype).codRestrict H fun a ↦ by
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, RingHom.toMonoidHom_eq_coe]
      using hf a a.property
  map_add' a b := Subtype.ext <| Units.ext <| by simp [val_add, map_add]

/-- The unit-level inclusion of a coefficient-semifield restriction. -/
@[simp]
theorem coe_coefficientSemifieldMap (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H) (a : G) :
    ((G.coefficientSemifieldMap H f hf a : H) : Sˣ) = Units.map (f : R →* S) (a : Rˣ) :=
  (rfl)

/-- The value-level inclusion of a coefficient-semifield restriction. -/
theorem val_coefficientSemifieldMap (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H) (a : G) :
    (((G.coefficientSemifieldMap H f hf a : H) : Sˣ) : S) = f (a : Rˣ) :=
  (rfl)

/-- A compatible ambient map carries the realized source subsemiring into the target. -/
theorem map_mem_withZeroSubsemiring (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H)
    {a : R} (ha : a ∈ G.withZeroSubsemiring) : f a ∈ H.withZeroSubsemiring := by
  obtain rfl | ⟨a, rfl⟩ := ha
  · exact Or.inl (map_zero f)
  · exact Or.inr ⟨G.coefficientSemifieldMap H f hf a,
      G.val_coefficientSemifieldMap H f hf a⟩

/-- The induced semiring map between the zero-adjoined realizations. -/
def withZeroSubsemiringMap (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H) :
    G.withZeroSubsemiring →+* H.withZeroSubsemiring :=
  f.restrict _ _ fun _ ha ↦ G.map_mem_withZeroSubsemiring H f hf ha

@[simp]
theorem coe_withZeroSubsemiringMap (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H) (a : G.withZeroSubsemiring) :
    (G.withZeroSubsemiringMap H f hf a : S) = f (a : R) :=
  (rfl)

/-- The two induced maps agree on subgroup members. -/
@[simp]
theorem withZeroSubsemiringMap_toWithZeroSubsemiringUnits (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H) (a : G) :
    G.withZeroSubsemiringMap H f hf (G.toWithZeroSubsemiringUnits a) =
      H.toWithZeroSubsemiringUnits (G.coefficientSemifieldMap H f hf a) := by
  ext
  simp

/-- The comparison with zero adjunction is natural for compatible ambient maps. -/
theorem withZeroSubsemiringMap_withZeroSubsemiringEquiv [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H) (a : WithZero G) :
    G.withZeroSubsemiringMap H f hf (G.withZeroSubsemiringEquiv a) =
      H.withZeroSubsemiringEquiv
        (WithZero.map' (G.coefficientSemifieldMap H f hf).toMonoidHom a) := by
  induction a using WithZero.recZeroCoe <;> simp

/-- Restricting an identity ambient map gives the identity on coefficients. -/
@[simp]
theorem coefficientSemifieldMap_id :
    G.coefficientSemifieldMap G (RingHom.id R) (by simp) =
      CoefficientSemifieldHom.id G := by
  ext a
  simp

/-- Restricting an identity ambient map gives the identity on the realization. -/
@[simp]
theorem withZeroSubsemiringMap_id :
    G.withZeroSubsemiringMap G (RingHom.id R) (by simp) =
      RingHom.id _ := by
  ext a
  simp

variable (K : Subgroup Tˣ) [K.IsAddClosed]

/-- Coefficient restrictions respect composition. -/
theorem coefficientSemifieldMap_comp (f : R →+* S) (g : S →+* T)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H)
    (hg : ∀ b ∈ H, Units.map (g : S →* T) b ∈ K)
    (hgf : ∀ a ∈ G, Units.map ((g.comp f : R →+* T) : R →* T) a ∈ K :=
      fun a ha ↦ hg _ (hf a ha)) :
    G.coefficientSemifieldMap K (g.comp f) hgf =
      (H.coefficientSemifieldMap K g hg).comp (G.coefficientSemifieldMap H f hf) := by
  ext a
  simp

/-- Restrictions to the realized subsemirings respect composition. -/
theorem withZeroSubsemiringMap_comp (f : R →+* S) (g : S →+* T)
    (hf : ∀ a ∈ G, Units.map (f : R →* S) a ∈ H)
    (hg : ∀ b ∈ H, Units.map (g : S →* T) b ∈ K)
    (hgf : ∀ a ∈ G, Units.map ((g.comp f : R →+* T) : R →* T) a ∈ K :=
      fun a ha ↦ hg _ (hf a ha)) :
    G.withZeroSubsemiringMap K (g.comp f) hgf =
      (H.withZeroSubsemiringMap K g hg).comp (G.withZeroSubsemiringMap H f hf) := by
  ext a
  simp

end Subgroup
