/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.TwoSidedIdeal.Operations

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

* `TwoSidedIdeal.instHasQuotient` and `TwoSidedIdeal.Quotient.nonUnitalRing`: the quotient `A ⧸ I`
  of a possibly nonunital ring by a two-sided ideal.
* `TwoSidedIdeal.Quotient.mk`: the canonical surjective nonunital ring homomorphism `A →ₙ+* A ⧸ I`,
  with kernel `I` (`TwoSidedIdeal.Quotient.ker_mk`).
* `TwoSidedIdeal.Quotient.lift` and `TwoSidedIdeal.Quotient.factor`: universal descent of nonunital
  ring homomorphisms through `A ⧸ I` and canonical maps between quotients.
* `TwoSidedIdeal.Quotient.opEquiv`: the canonical ring isomorphism `(A ⧸ I)ᵐᵒᵖ ≃+* Aᵐᵒᵖ ⧸ I.op`,
  together with quotient pushforward/pullback lemmas `TwoSidedIdeal.comap_map_mk` and
  `TwoSidedIdeal.map_mk_eq_top_iff`.
* `TwoSidedIdeal.quotEquivOfEq`: ring equivalence between quotients by equal two-sided ideals.
-/

public section

namespace TwoSidedIdeal

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

/-- Canonical ring isomorphism `(A ⧸ I)ᵐᵒᵖ ≃+* Aᵐᵒᵖ ⧸ I.op` identifying the opposite of a
quotient ring with the quotient of the opposite ring by `I.op`. -/
def opEquiv (I : TwoSidedIdeal A) : (A ⧸ I)ᵐᵒᵖ ≃+* Aᵐᵒᵖ ⧸ I.op :=
  let toFunAux : A ⧸ I →+ Aᵐᵒᵖ ⧸ I.op :=
    QuotientAddGroup.lift (AddSubgroup.ofClass I)
      ((mk I.op).toAddMonoidHom.comp (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddMonoidHom)
      fun _ ha => eq_zero_iff_mem.mpr (mem_op_iff.mpr ha)
  let invHom : Aᵐᵒᵖ →ₙ+* (A ⧸ I)ᵐᵒᵖ :=
    { toFun := fun u => MulOpposite.op (mk I u.unop)
      map_zero' := rfl
      map_add' := fun u v => by rw [MulOpposite.unop_add, map_add, MulOpposite.op_add]
      map_mul' := fun u v => by rw [MulOpposite.unop_mul, map_mul, ← MulOpposite.op_mul] }
  { toFun := fun x => toFunAux x.unop
    invFun := lift I.op invHom fun u hu => by
      rw [← invHom.coe_toMulHom]
      simp only [invHom, MulHom.coe_mk, eq_zero_iff_mem.mpr (mem_op_iff.mp hu),
        MulOpposite.op_zero]
    left_inv := fun x => by
      obtain ⟨x, rfl⟩ := MulOpposite.op_surjective x
      obtain ⟨a, rfl⟩ := mk_surjective I x
      rfl
    right_inv := Quotient.forall.mpr fun _ => rfl
    map_add' := fun x y => by rw [MulOpposite.unop_add, map_add]
    map_mul' := fun x y => by
      obtain ⟨x, rfl⟩ := MulOpposite.op_surjective x
      obtain ⟨a, rfl⟩ := mk_surjective I x
      obtain ⟨y, rfl⟩ := MulOpposite.op_surjective y
      obtain ⟨b, rfl⟩ := mk_surjective I y
      exact (map_mul (mk I.op) (MulOpposite.op a) (MulOpposite.op b)).symm }

@[simp]
theorem opEquiv_op_mk (I : TwoSidedIdeal A) (a : A) :
    opEquiv I (MulOpposite.op (mk I a)) = mk I.op (MulOpposite.op a) := by
  rfl

@[simp]
theorem opEquiv_symm_mk (I : TwoSidedIdeal A) (u : Aᵐᵒᵖ) :
    (opEquiv I).symm (mk I.op u) = MulOpposite.op (mk I u.unop) := by
  rfl

end Quotient

/-- Pulling back the image of `I` in `A ⧸ J` along the quotient map recovers `I ⊔ J`. -/
@[simp]
theorem comap_map_mk (I J : TwoSidedIdeal A) :
    TwoSidedIdeal.comap (Quotient.mk J) (TwoSidedIdeal.map (Quotient.mk J) I) = I ⊔ J := by
  ext a
  rw [TwoSidedIdeal.mem_comap, mem_map_iff_of_surjective (Quotient.mk_surjective J),
    TwoSidedIdeal.mem_sup]
  constructor
  · rintro ⟨x, hx, hxa⟩
    refine ⟨x, hx, a - x, ?_, add_sub_cancel x a⟩
    have hsub : x - a ∈ J := Quotient.eq.mp hxa
    simpa only [neg_sub] using J.neg_mem hsub
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨x, hx, Quotient.eq.mpr ?_⟩
    simpa only [sub_add_cancel_left] using J.neg_mem hy

/-- The image of `I` in `A ⧸ J` is the whole quotient if and only if `I ⊔ J = ⊤`. -/
@[simp]
theorem map_mk_eq_top_iff {I J : TwoSidedIdeal A} :
    TwoSidedIdeal.map (Quotient.mk J) I = ⊤ ↔ I ⊔ J = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← comap_map_mk I J, h]
    ext a
    simp [TwoSidedIdeal.mem_comap]
  · ext z
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective J z
    simp only [TwoSidedIdeal.mem_top, iff_true]
    have ha : a ∈ TwoSidedIdeal.comap (Quotient.mk J) (TwoSidedIdeal.map (Quotient.mk J) I) := by
      rw [comap_map_mk, h]
      exact TwoSidedIdeal.mem_top A
    exact (TwoSidedIdeal.mem_comap (Quotient.mk J)).mp ha

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
