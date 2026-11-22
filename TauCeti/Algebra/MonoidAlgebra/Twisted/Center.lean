/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Centers of twisted monoid algebras

Commutation with the basis elements tests centrality for every twisted monoid algebra.
For a commutative cancellative monoid, centrality says that each coefficient multiplied by either
opposite factor-set value gives the same result. The factors themselves may differ when the scalar
coefficient cannot be cancelled. With cancellation away from zero, the center is the span
of the basis elements at which the factor set is symmetric against every monoid element.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

section Monoid

variable {R G : Type*} [CommSemiring R] [Monoid G]
  {α : G → G → Rˣ} [IsFactorSet α]

/-- A twisted monoid-algebra element is central exactly when it commutes with every
basis element. -/
theorem mem_center_iff_commute_of (f : twistedMonoidAlgebra R G α) :
    f ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔ ∀ b, Commute f (of b) := by
  -- The algebra is associative, so the basis test's additional associativity conditions vanish.
  rw [Subalgebra.mem_center_iff, ← Semigroup.mem_center_iff]
  simpa only [mul_assoc, eq_self, implies_true, forall_const, and_true,
    Commute.symm_iff, basis_apply] using
    ((basis R G α).mem_center_iff (z := f))

end Monoid

section CommMonoid

variable {R G : Type*} [CommSemiring R] [CommMonoid G]
  {α : G → G → Rˣ} [IsFactorSet α]

/-- A basis element is central exactly when the factor set is symmetric against every
index, without requiring index cancellation or scalar cancellation. -/
@[simp]
theorem of_mem_center_iff (a : G) :
    of a ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔ ∀ b, α a b = α b a := by
  rw [mem_center_iff_commute_of]
  constructor
  · intro h b
    have he := (h b).eq
    rw [of_mul_of, of_mul_of, mul_comm b a] at he
    apply Units.ext
    simpa only [map_smul, repr_of, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] using congrArg (fun z ↦ (basis R G α).repr z (a * b)) he
  · intro h b
    rw [commute_iff_eq, of_mul_of, of_mul_of, h b, mul_comm a b]

/-- The submonoid of indices whose normalized basis elements are central. -/
def centralIndices (α : G → G → Rˣ) [IsFactorSet α] : Submonoid G where
  carrier := {a | ∀ b, α a b = α b a}
  one_mem' := by simp [IsFactorSet.one_left, IsFactorSet.one_right]
  mul_mem' := by
    intro a b ha hb
    apply (of_mem_center_iff (α := α) (a * b)).mp
    have hc := (Subalgebra.center R (twistedMonoidAlgebra R G α)).mul_mem
      ((of_mem_center_iff a).mpr ha) ((of_mem_center_iff b).mpr hb)
    rw [of_mul_of] at hc
    simpa only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] using
      (Subalgebra.center R (twistedMonoidAlgebra R G α)).smul_mem hc (↑(α a b)⁻¹ : R)

/-- Central-index membership is symmetry of the factor set. -/
@[simp]
theorem mem_centralIndices (a : G) : a ∈ centralIndices α ↔ ∀ b, α a b = α b a := Iff.rfl

/-- The central-index twist restricts the original factor set along the inclusion. -/
instance : IsFactorSet (fun a b : centralIndices α ↦ α a b) :=
  IsFactorSet.comp (centralIndices α).subtype α

/-- The restricted twisted algebra embeds canonically in the center, preserving its twist. -/
noncomputable def centerHom (α : G → G → Rˣ) [IsFactorSet α] :
    twistedMonoidAlgebra R (centralIndices α) (fun a b ↦ α a b) →ₐ[R]
      Subalgebra.center R (twistedMonoidAlgebra R G α) :=
  lift (fun a ↦ ⟨of (a : G), (of_mem_center_iff _).mpr ((mem_centralIndices _).mp a.property)⟩)
    (by apply Subtype.ext; simp)
    (by intro a b; apply Subtype.ext; simp only [of_mul_of, Subalgebra.coe_mul,
      Subalgebra.coe_smul, Submonoid.coe_mul])

/-- The restricted center map sends normalized basis elements to bundled central elements. -/
@[simp]
theorem centerHom_of (a : centralIndices α) :
    centerHom α (of a) =
      ⟨of (a : G), (of_mem_center_iff _).mpr ((mem_centralIndices _).mp a.property)⟩ := by
  simp only [centerHom, lift_of]

/-- In ambient basis coordinates, the restricted center map extends coefficients by zero. -/
theorem repr_centerHom (f : twistedMonoidAlgebra R (centralIndices α) (fun a b ↦ α a b)) :
    (basis R G α).repr ((centerHom α f :
      Subalgebra.center R (twistedMonoidAlgebra R G α)) : twistedMonoidAlgebra R G α) =
        Finsupp.mapDomain (fun a : centralIndices α ↦ (a : G))
          ((basis R (centralIndices α) (fun a b ↦ α a b)).repr f) := by
  let b := basis R (centralIndices α) (fun a b ↦ α a b)
  have h : (basis R G α).repr.toLinearMap ∘ₗ
      ((Subalgebra.center R (twistedMonoidAlgebra R G α)).val.toLinearMap ∘ₗ
        (centerHom α).toLinearMap) =
      Finsupp.lmapDomain R R (fun a : centralIndices α ↦ (a : G)) ∘ₗ b.repr.toLinearMap := by
    apply b.ext
    intro a
    simp [b, LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun h f

/-- The restricted center map leaves every included coefficient unchanged. -/
@[simp]
theorem repr_centerHom_apply (f : twistedMonoidAlgebra R (centralIndices α) (fun a b ↦ α a b))
    (a : centralIndices α) :
    (basis R G α).repr ((centerHom α f :
      Subalgebra.center R (twistedMonoidAlgebra R G α)) : twistedMonoidAlgebra R G α) (a : G) =
      (basis R (centralIndices α) (fun a b ↦ α a b)).repr f a := by
  rw [repr_centerHom, Finsupp.mapDomain_apply_of_injective Subtype.val_injective]

/-- Coefficients of the restricted center map vanish outside the included indices. -/
theorem repr_centerHom_apply_eq_zero
    (f : twistedMonoidAlgebra R (centralIndices α) (fun a b ↦ α a b))
    (a : G) (ha : a ∉ centralIndices α) :
    (basis R G α).repr ((centerHom α f :
      Subalgebra.center R (twistedMonoidAlgebra R G α)) : twistedMonoidAlgebra R G α) a = 0 := by
  rw [repr_centerHom]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨x, rfl⟩
  exact ha x.property

/-- The restricted center map is injective even without scalar cancellation. -/
theorem centerHom_injective : Function.Injective (centerHom α) := by
  intro f g h
  apply (basis R (centralIndices α) _).repr.injective
  apply Finsupp.mapDomain_injective Subtype.val_injective
  have he := congrArg (fun x : Subalgebra.center R (twistedMonoidAlgebra R G α) ↦
    (basis R G α).repr (x : twistedMonoidAlgebra R G α)) h
  simpa only [repr_centerHom] using he

end CommMonoid

section CancelCommMonoid

variable {R G : Type*} [CommSemiring R] [CancelCommMonoid G]
  {α : G → G → Rˣ} [IsFactorSet α]

/-- Centrality means that every coefficient multiplied by either opposite factor-set value
gives the same result. The two factor-set values need not themselves be equal. -/
theorem mem_center_iff_coeff (f : twistedMonoidAlgebra R G α) :
    f ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔ ∀ a b,
      (basis R G α).repr f a * (α a b : R) =
        (basis R G α).repr f a * (α b a : R) := by
  rw [mem_center_iff_commute_of]
  simp_rw [commute_of_iff]
  exact forall_comm

/-- If nonzero scalar coefficients can be cancelled, centrality is support on exponents
where the factor set is symmetric against every test element. -/
theorem mem_center_iff_support [IsLeftCancelMulZero R] (f : twistedMonoidAlgebra R G α) :
    f ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔
      ∀ a ∈ ((basis R G α).repr f).support, ∀ b, α a b = α b a := by
  rw [mem_center_iff_coeff]
  simp_rw [mul_eq_mul_left_iff, Units.val_inj, or_iff_not_imp_right,
    Finsupp.mem_support_iff]
  exact forall_congr' fun a ↦ forall_comm

/-- The center is the span of the symmetric-factor-set basis elements when nonzero
scalar coefficients can be cancelled. -/
theorem center_toSubmodule_eq_span [IsLeftCancelMulZero R] :
    (Subalgebra.center R (twistedMonoidAlgebra R G α)).toSubmodule =
      Submodule.span R (of '' {a : G | ∀ b, α a b = α b a}) := by
  have hb : (basis R G α : G → twistedMonoidAlgebra R G α) = of :=
    funext fun a ↦ basis_apply R G α a
  have hi : (basis R G α) '' {a : G | ∀ b, α a b = α b a} =
      of '' {a : G | ∀ b, α a b = α b a} := congrArg (fun v ↦ v '' _) hb
  rw [← hi]
  ext f
  rw [Subalgebra.mem_toSubmodule, mem_center_iff_support, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]

/-- Under index and nonzero-scalar cancellation, the restricted map exhausts the center. -/
theorem centerHom_surjective [IsLeftCancelMulZero R] : Function.Surjective (centerHom α) := by
  rintro ⟨f, hf⟩
  have hs := (mem_center_iff_support f).mp hf
  have hm : (basis R G α).repr f ∈ Set.range
      (Finsupp.mapDomain (fun a : centralIndices α ↦ (a : G))) := by
    apply (Finsupp.mem_range_mapDomain_iff _ Subtype.val_injective _).mpr
    intro a ha
    by_contra hn
    exact ha ⟨⟨a, (mem_centralIndices a).mpr (hs a (Finsupp.mem_support_iff.mpr hn))⟩, rfl⟩
  obtain ⟨v, hv⟩ := hm
  refine ⟨(basis R (centralIndices α) _).repr.symm v, Subtype.ext ?_⟩
  apply (basis R G α).repr.injective
  rw [repr_centerHom, LinearEquiv.apply_symm_apply, hv]

/-- The center is the twisted algebra restricted to its central-index submonoid. -/
noncomputable def centerEquiv [IsLeftCancelMulZero R] :
    twistedMonoidAlgebra R (centralIndices α) (fun a b ↦ α a b) ≃ₐ[R]
      Subalgebra.center R (twistedMonoidAlgebra R G α) :=
  AlgEquiv.ofBijective (centerHom α) ⟨centerHom_injective, centerHom_surjective⟩

/-- The restricted center equivalence preserves bundled normalized basis elements. -/
@[simp]
theorem centerEquiv_of [IsLeftCancelMulZero R] (a : centralIndices α) :
    centerEquiv (α := α) (of a) =
      ⟨of (a : G), (of_mem_center_iff _).mpr ((mem_centralIndices _).mp a.property)⟩ :=
  (AlgEquiv.ofBijective_apply _ _ _).trans (centerHom_of a)

/-- The forward map of the restricted center equivalence is the canonical inclusion. -/
@[simp]
theorem centerEquiv_toAlgHom [IsLeftCancelMulZero R] :
    (centerEquiv (α := α)).toAlgHom = centerHom α :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- Inverse center coordinates are the ambient coefficients at the included central indices. -/
@[simp]
theorem repr_centerEquiv_symm_apply [IsLeftCancelMulZero R]
    (f : Subalgebra.center R (twistedMonoidAlgebra R G α)) (a : centralIndices α) :
    (basis R (centralIndices α) (fun a b ↦ α a b)).repr (centerEquiv.symm f) a =
      (basis R G α).repr (f : twistedMonoidAlgebra R G α) (a : G) := by
  simpa only [← centerEquiv_toAlgHom, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply] using
    (repr_centerHom_apply (centerEquiv.symm f) a).symm

/-- The inverse restricted center equivalence recovers the basis element at a central index. -/
@[simp]
theorem centerEquiv_symm_of [IsLeftCancelMulZero R] (a : centralIndices α) :
    (centerEquiv (α := α)).symm
      ⟨of (a : G), (of_mem_center_iff _).mpr ((mem_centralIndices _).mp a.property)⟩ = of a :=
  (centerEquiv (α := α)).symm_apply_eq.mpr (centerEquiv_of a).symm

end CancelCommMonoid

end TauCeti.TwistedMonoidAlgebra
