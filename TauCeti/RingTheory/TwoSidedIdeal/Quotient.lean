/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Quotients of possibly nonunital rings by two-sided ideals

For a two-sided ideal `I : TwoSidedIdeal A` of a possibly nonunital ring `A`, we equip `A ⧸ I` with
its quotient nonunital ring structure, built on the additive subgroup quotient
`A ⧸ AddSubgroup.ofClass I` so that additive and metric quotient instances transfer
definitionally. When `A` is unital, `A ⧸ I` agrees definitionally with `A ⧸ I.asIdeal` and
inherits its ring instance without diamonds at instance transparency. The algebra instance is not
diamond free there: its module structure is not defeq at instance transparency to the `ℕ`- and
`ℤ`-module structures of the additive group quotient, nor to other module structures put on the
quotient.

## Main definitions and results

* `TwoSidedIdeal.coe_map_of_surjective` and `TwoSidedIdeal.mem_map_iff_of_surjective`: pushforward
  along a surjective nonunital ring homomorphism has carrier equal to the set-theoretic image.
* `TwoSidedIdeal.instHasQuotient` and `TwoSidedIdeal.Quotient.nonUnitalRing`: the quotient `A ⧸ I`
  of a possibly nonunital ring by a two-sided ideal.
* `TwoSidedIdeal.Quotient.mk`: the canonical surjective nonunital ring homomorphism `A →ₙ+* A ⧸ I`,
  with kernel `I` (`TwoSidedIdeal.Quotient.ker_mk`).
* `TwoSidedIdeal.Quotient.lift` and `TwoSidedIdeal.Quotient.factor`: universal descent of nonunital
  ring homomorphisms through `A ⧸ I` and canonical maps between quotients.
* `TwoSidedIdeal.quotEquivOfEq`: ring equivalence between quotients by equal two-sided ideals.
* `TwoSidedIdeal.Quotient.comap_map_mk` and `TwoSidedIdeal.Quotient.comapMkRelIso`: order
  isomorphism between two-sided ideals of `A ⧸ I` and two-sided ideals of `A` containing `I`.
-/

public section

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R S F : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- The pushforward of a two-sided ideal along a surjective nonunital ring homomorphism has
carrier equal to its set-theoretic image. -/
theorem coe_map_of_surjective (f : F) (hf : Function.Surjective f) (I : TwoSidedIdeal R) :
    (I.map f : Set S) = f '' I := by
  let M : TwoSidedIdeal S := TwoSidedIdeal.mk' (f '' I)
    ⟨0, I.zero_mem, map_zero f⟩
    (by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, I.add_mem hx hy, map_add f x y⟩)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, I.neg_mem hx, map_neg f x⟩)
    (by
      rintro x _ ⟨y, hy, rfl⟩
      obtain ⟨r, rfl⟩ := hf x
      exact ⟨r * y, I.mul_mem_left r y hy, map_mul f r y⟩)
    (by
      rintro _ y ⟨x, hx, rfl⟩
      obtain ⟨r, rfl⟩ := hf y
      exact ⟨x * r, I.mul_mem_right x r hx, map_mul f x r⟩)
  have hle : I.map f ≤ M :=
    span_le.mpr fun _ hx => (mem_mk' _ _ _ _ _ _ _).mpr hx
  have hge : M ≤ I.map f := fun _ hy =>
    subset_span ((mem_mk' _ _ _ _ _ _ _).mp hy)
  exact (congrArg SetLike.coe (le_antisymm hle hge)).trans (coe_mk' _ _ _ _ _ _)

/-- Membership in the pushforward of a two-sided ideal along a surjective nonunital ring
homomorphism. -/
theorem mem_map_iff_of_surjective (f : F) (hf : Function.Surjective f) {I : TwoSidedIdeal R}
    {y : S} : y ∈ I.map f ↔ ∃ x ∈ I, f x = y := by
  rw [← SetLike.mem_coe, coe_map_of_surjective f hf I]
  rfl

end NonUnitalNonAssocRing

section NonUnitalRing

variable {A B C : Type*} [NonUnitalRing A]

/-- The equivalence relation `x ≈ y ↔ -x + y ∈ I` associated to a two-sided ideal `I`, chosen to be
definitionally equal to the `AddSubgroup` relation so that additive and normed quotient structures
transfer directly. -/
@[expose] def quotientRel (I : TwoSidedIdeal A) : Setoid A :=
  QuotientAddGroup.leftRel (AddSubgroup.ofClass I)

theorem quotientRel_def {I : TwoSidedIdeal A} {x y : A} :
    I.quotientRel x y ↔ x - y ∈ I := by
  rw [quotientRel, QuotientAddGroup.leftRel_apply, ← SetLike.mem_coe, AddSubgroup.coe_ofClass,
    SetLike.mem_coe, ← neg_mem_iff, neg_add_rev, neg_neg, add_comm, ← sub_eq_add_neg]

/-- The quotient `A ⧸ I` of a possibly nonunital ring `A` by a two-sided ideal `I`. -/
instance instHasQuotient : HasQuotient A (TwoSidedIdeal A) :=
  ⟨fun I => Quotient I.quotientRel⟩

namespace Quotient

/-- On a `TwoSidedIdeal`, `quotientRel` is a ring congruence relation. -/
@[expose] protected def ringCon (I : TwoSidedIdeal A) : RingCon A where
  __ := QuotientAddGroup.con (AddSubgroup.ofClass I)
  mul' {a₁ b₁ a₂ b₂} (h₁ : I.quotientRel a₁ b₁) (h₂ : I.quotientRel a₂ b₂) :
      I.quotientRel (a₁ * a₂) (b₁ * b₂) := by
    rw [quotientRel_def] at h₁ h₂ ⊢
    have hsplit : a₁ * a₂ - b₁ * b₂ = a₁ * (a₂ - b₂) + (a₁ - b₁) * b₂ := by
      rw [mul_sub, sub_mul, sub_add_sub_cancel]
    rw [hsplit]
    exact I.add_mem (I.mul_mem_left a₁ _ h₂) (I.mul_mem_right _ b₂ h₁)

instance addCommGroup (I : TwoSidedIdeal A) : AddCommGroup (A ⧸ I) :=
  inferInstanceAs <| AddCommGroup (A ⧸ AddSubgroup.ofClass I)

instance nonUnitalRing (I : TwoSidedIdeal A) : NonUnitalRing (A ⧸ I) :=
  inferInstanceAs <| NonUnitalRing (TwoSidedIdeal.Quotient.ringCon I).Quotient

instance nonUnitalCommRing {A : Type*} [NonUnitalCommRing A] (I : TwoSidedIdeal A) :
    NonUnitalCommRing (A ⧸ I) where
  mul_comm := Quotient.ind₂' fun a b => congrArg Quotient.mk'' (mul_comm a b)

-- Verify that the ring additive group agrees definitionally with the subgroup quotient.
example (I : TwoSidedIdeal A) : (nonUnitalRing I).toAddCommGroup = addCommGroup I := by
  with_reducible_and_instances rfl

/-- The canonical nonunital ring homomorphism from `A` to `A ⧸ I`. -/
def mk (I : TwoSidedIdeal A) : A →ₙ+* A ⧸ I where
  toFun := QuotientAddGroup.mk
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem quotientAddGroupMk_eq_mk (I : TwoSidedIdeal A) (x : A) :
    (QuotientAddGroup.mk x : A ⧸ I) = mk I x :=
  (rfl)

theorem mk_surjective (I : TwoSidedIdeal A) : Function.Surjective (mk I) :=
  QuotientAddGroup.mk_surjective

/-- Induction principle on elements of `A ⧸ I` along `TwoSidedIdeal.Quotient.mk`. -/
@[elab_as_elim]
protected theorem induction_on {I : TwoSidedIdeal A} {p : A ⧸ I → Prop} (x : A ⧸ I)
    (h : ∀ a : A, p (mk I a)) : p x :=
  Quotient.inductionOn' x h

protected theorem «forall» {I : TwoSidedIdeal A} {p : A ⧸ I → Prop} :
    (∀ x : A ⧸ I, p x) ↔ ∀ a : A, p (mk I a) :=
  ⟨fun h a => h (mk I a), fun h x => Quotient.induction_on x h⟩

@[simp]
theorem eq_zero_iff_mem {I : TwoSidedIdeal A} {a : A} :
    mk I a = 0 ↔ a ∈ I :=
  QuotientAddGroup.eq_zero_iff (N := AddSubgroup.ofClass I) a

protected theorem eq {I : TwoSidedIdeal A} {x y : A} :
    mk I x = mk I y ↔ x - y ∈ I := by
  rw [← sub_eq_zero, ← map_sub, eq_zero_iff_mem]

/-- The quotient `A ⧸ I` is a subsingleton if and only if `I = ⊤`. -/
protected theorem subsingleton_iff {I : TwoSidedIdeal A} :
    Subsingleton (A ⧸ I) ↔ I = ⊤ := by
  rw [subsingleton_iff_forall_eq (0 : A ⧸ I), Quotient.forall]
  simp [eq_zero_iff_mem, eq_top_iff, IsConcreteLE.le_iff]

/-- The quotient `A ⧸ I` is nontrivial if and only if `I ≠ ⊤`. -/
protected theorem nontrivial_iff {I : TwoSidedIdeal A} :
    Nontrivial (A ⧸ I) ↔ I ≠ ⊤ := by
  rw [← not_subsingleton_iff_nontrivial, Quotient.subsingleton_iff]

@[simp]
theorem ker_mk (I : TwoSidedIdeal A) : TwoSidedIdeal.ker (mk I) = I := by
  ext x
  rw [TwoSidedIdeal.mem_ker, eq_zero_iff_mem]

/-- Two nonunital ring homomorphisms out of `A ⧸ I` agree when their compositions with `mk I`
agree. -/
@[ext 1100]
theorem nonUnitalRingHom_ext [NonUnitalNonAssocSemiring B] {I : TwoSidedIdeal A}
    ⦃f g : A ⧸ I →ₙ+* B⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g :=
  NonUnitalRingHom.ext <| Quotient.forall.mpr (DFunLike.congr_fun h)

/-- Descend a nonunital ring homomorphism `f : A →ₙ+* B` vanishing on `I` to `A ⧸ I →ₙ+* B`. -/
def lift (I : TwoSidedIdeal A) [NonUnitalNonAssocSemiring B] (f : A →ₙ+* B)
    (hf : ∀ a ∈ I, f a = 0) : A ⧸ I →ₙ+* B :=
  { QuotientAddGroup.lift (AddSubgroup.ofClass I) f.toAddMonoidHom hf with
    map_mul' := fun x y => Quotient.inductionOn₂' x y (map_mul f) }

@[simp]
theorem lift_mk (I : TwoSidedIdeal A) [NonUnitalNonAssocSemiring B] (f : A →ₙ+* B)
    (hf : ∀ a ∈ I, f a = 0) (a : A) :
    lift I f hf (mk I a) = f a :=
  (rfl)

@[simp]
theorem lift_comp_mk (I : TwoSidedIdeal A) [NonUnitalNonAssocSemiring B] (f : A →ₙ+* B)
    (hf : ∀ a ∈ I, f a = 0) :
    (lift I f hf).comp (mk I) = f :=
  NonUnitalRingHom.ext <| lift_mk I f hf

theorem lift_surjective_of_surjective {I : TwoSidedIdeal A} [NonUnitalNonAssocSemiring B]
    {f : A →ₙ+* B} (hf : ∀ a ∈ I, f a = 0) (hsurj : Function.Surjective f) :
    Function.Surjective (lift I f hf) := by
  intro b
  obtain ⟨a, rfl⟩ := hsurj b
  exact ⟨mk I a, lift_mk I f hf a⟩

theorem lift_injective_of_ker_le {I : TwoSidedIdeal A} [NonUnitalNonAssocSemiring B]
    {f : A →ₙ+* B} (hf : ∀ a ∈ I, f a = 0) (hker : TwoSidedIdeal.ker f ≤ I) :
    Function.Injective (lift I f hf) := by
  rw [injective_iff_map_eq_zero]
  refine Quotient.forall.mpr fun a ha => ?_
  rw [lift_mk] at ha
  exact eq_zero_iff_mem.mpr (hker ((TwoSidedIdeal.mem_ker f).mpr ha))

/-- The canonical nonunital ring homomorphism `A ⧸ I →ₙ+* A ⧸ J` for `I ≤ J`. -/
def factor {I J : TwoSidedIdeal A} (h : I ≤ J) : A ⧸ I →ₙ+* A ⧸ J :=
  lift I (mk J) fun _ hx => eq_zero_iff_mem.mpr (h hx)

@[simp]
theorem factor_mk {I J : TwoSidedIdeal A} (h : I ≤ J) (a : A) :
    factor h (mk I a) = mk J a :=
  (rfl)

@[simp]
theorem factor_comp_mk {I J : TwoSidedIdeal A} (h : I ≤ J) :
    (factor h).comp (mk I) = mk J :=
  lift_comp_mk _ _ _

@[simp]
theorem factor_refl (I : TwoSidedIdeal A) :
    factor (le_refl I) = NonUnitalRingHom.id (A ⧸ I) := by
  ext
  simp

@[simp]
theorem factor_comp {I J K : TwoSidedIdeal A} (h₁ : I ≤ J) (h₂ : J ≤ K) :
    (factor h₂).comp (factor h₁) = factor (h₁.trans h₂) := by
  ext
  simp

theorem factor_surjective {I J : TwoSidedIdeal A} (h : I ≤ J) :
    Function.Surjective (factor h) :=
  lift_surjective_of_surjective _ (mk_surjective J)

/-- For any two-sided ideal `K` containing `I`, pulling back `K.map (mk I)` along `mk I` recovers
`K`. -/
theorem comap_map_mk {I K : TwoSidedIdeal A} (h : I ≤ K) :
    (K.map (mk I)).comap (mk I) = K := by
  ext a
  rw [TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_map_iff_of_surjective (mk I) (mk_surjective I)]
  refine ⟨?_, fun ha => ⟨a, ha, rfl⟩⟩
  rintro ⟨b, hbK, hba⟩
  have hsub : a - b ∈ I := Quotient.eq.mp hba.symm
  simpa using K.add_mem (h hsub) hbK

/-- Correspondence theorem for two-sided ideals: two-sided ideals of `A ⧸ I` correspond
order-isomorphically to two-sided ideals of `A` containing `I`, via `comap (mk I)` and
`map (mk I)`. -/
def comapMkRelIso (I : TwoSidedIdeal A) :
    TwoSidedIdeal (A ⧸ I) ≃o Set.Ici I where
  toFun J := ⟨J.comap (mk I), fun _ ha =>
    (TwoSidedIdeal.mem_comap (mk I)).mpr ((eq_zero_iff_mem.mpr ha).symm ▸ J.zero_mem)⟩
  invFun K := K.val.map (mk I)
  left_inv J := by
    ext x
    rw [TwoSidedIdeal.mem_map_iff_of_surjective (mk I) (mk_surjective I)]
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨a, ha, rfl⟩
      exact (TwoSidedIdeal.mem_comap (mk I)).mp ha
    · obtain ⟨a, rfl⟩ := mk_surjective I x
      exact ⟨a, (TwoSidedIdeal.mem_comap (mk I)).mpr hx, rfl⟩
  right_inv K := Subtype.ext (comap_map_mk K.property)
  map_rel_iff' {J₁ J₂} :=
    ⟨fun h x hx => by
      change J₁.comap (mk I) ≤ J₂.comap (mk I) at h
      obtain ⟨a, rfl⟩ := mk_surjective I x
      exact (TwoSidedIdeal.mem_comap (mk I)).mp
        (IsConcreteLE.le_iff.mp h ((TwoSidedIdeal.mem_comap (mk I)).mpr hx)),
     fun h => TwoSidedIdeal.comap_le_comap (mk I) h⟩

@[simp]
theorem comapMkRelIso_apply (I : TwoSidedIdeal A) (J : TwoSidedIdeal (A ⧸ I)) :
    (comapMkRelIso I J).val = J.comap (mk I) :=
  (rfl)

@[simp]
theorem comapMkRelIso_symm_apply (I : TwoSidedIdeal A) (K : Set.Ici I) :
    (comapMkRelIso I).symm K = K.val.map (mk I) :=
  (rfl)

/-- Under `comapMkRelIso`, the preimage ideal of `J : TwoSidedIdeal (A ⧸ I)` has carrier
`(mk I) ⁻¹' J`. -/
theorem coe_comapMkRelIso (I : TwoSidedIdeal A) (J : TwoSidedIdeal (A ⧸ I)) :
    ((comapMkRelIso I J).val : Set A) = mk I ⁻¹' (J : Set (A ⧸ I)) := by
  rw [comapMkRelIso_apply]
  ext a
  exact TwoSidedIdeal.mem_comap (mk I)

end Quotient

/-- Ring equivalence between quotients by equal two-sided ideals. -/
def quotEquivOfEq {I J : TwoSidedIdeal A} (h : I = J) : A ⧸ I ≃+* A ⧸ J where
  toFun := Quotient.factor h.le
  invFun := Quotient.factor h.ge
  left_inv := Quotient.forall.mpr fun a => by simp
  right_inv := Quotient.forall.mpr fun a => by simp
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
theorem quotEquivOfEq_mk {I J : TwoSidedIdeal A} (h : I = J) (a : A) :
    quotEquivOfEq h (Quotient.mk I a) = Quotient.mk J a :=
  (rfl)

@[simp]
theorem quotEquivOfEq_symm {I J : TwoSidedIdeal A} (h : I = J) :
    (quotEquivOfEq h).symm = quotEquivOfEq h.symm :=
  RingEquiv.ext <| Quotient.forall.mpr fun _ => rfl

end NonUnitalRing

section Ring

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

namespace Quotient

instance ring (I : TwoSidedIdeal A) : Ring (A ⧸ I) :=
  inferInstanceAs <| Ring (A ⧸ I.asIdeal)

instance commRing {A : Type*} [CommRing A] (I : TwoSidedIdeal A) : CommRing (A ⧸ I) :=
  inferInstanceAs <| CommRing (A ⧸ I.asIdeal)

instance algebra (I : TwoSidedIdeal A) : Algebra R (A ⧸ I) :=
  inferInstanceAs <| Algebra R (A ⧸ I.asIdeal)

instance isScalarTower {S : Type*} [CommSemiring S] [SMul R S] [Algebra S A]
    [IsScalarTower R S A] (I : TwoSidedIdeal A) : IsScalarTower R S (A ⧸ I) :=
  inferInstanceAs <| IsScalarTower R S (A ⧸ I.asIdeal)

-- Verify that the unital ring structure agrees definitionally with the nonunital one.
example (I : TwoSidedIdeal A) : (ring I).toNonUnitalRing = nonUnitalRing I := by
  with_reducible_and_instances rfl

/-- The canonical unital ring homomorphism `A →+* A ⧸ I` when `A` is unital. -/
def mkRingHom (I : TwoSidedIdeal A) : A →+* A ⧸ I :=
  { mk I with map_one' := rfl }

@[simp]
theorem coe_mkRingHom (I : TwoSidedIdeal A) : ⇑(mkRingHom I) = mk I :=
  (rfl)

@[simp]
theorem mk_one (I : TwoSidedIdeal A) : mk I (1 : A) = 1 :=
  (rfl)

theorem idealQuotientMk_asIdeal_eq_mk (I : TwoSidedIdeal A) (a : A) :
    (Ideal.Quotient.mk I.asIdeal a : A ⧸ I) = mk I a :=
  (rfl)

theorem algebraMap_apply (I : TwoSidedIdeal A) (r : R) :
    algebraMap R (A ⧸ I) r = mk I (algebraMap R A r) :=
  (rfl)

@[simp]
theorem mk_algebraMap (I : TwoSidedIdeal A) (r : R) :
    mk I (algebraMap R A r) = algebraMap R (A ⧸ I) r :=
  (rfl)

@[simp]
theorem mkRingHom_comp_algebraMap (I : TwoSidedIdeal A) :
    (mkRingHom I).comp (algebraMap R A) = algebraMap R (A ⧸ I) :=
  (rfl)

end Quotient

end Ring

end TwoSidedIdeal
