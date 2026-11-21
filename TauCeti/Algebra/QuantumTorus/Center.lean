/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuantumTorus.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Center
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The center of a based quantum torus

The center is determined by coefficients weighted by the opposite twist factors; without
scalar cancellation the two factors themselves need not be equal. When nonzero scalar
coefficients cancel, the center is spanned by normalized monomials on the central exponent
subgroup. The restricted torus always embeds in the center; this embedding is an
equivalence when nonzero scalar coefficients cancel. These results specialize arbitrary-factor-set
twisted group algebras.

The central exponent subgroup is defined by equality of opposite powers of the parameter,
using equalizers of additive homomorphisms. This definition makes sense for units in any
monoid, without constructing a torus. For alternating forms its condition is
`u ^ (2 * Λ a b) = 1` for every `b`, including finite-order parameters.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), Proposition 11.2.
-/

public section

namespace Units

variable {R L : Type*} [Monoid R] [AddCommGroup L]

/-- The exponents for which the opposite powers of a scalar unit agree against every test
exponent. When a based quantum torus exists, these are exactly its central monomials. -/
def quantumTorusCentralExponents (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) : AddSubgroup L :=
  ⨅ b : L, (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ.flip b).toAddMonoidHom).eqLocus
    (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ b).toAddMonoidHom)

private theorem centralExponentEqualizer_mem (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a b : L) :
    a ∈ (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ.flip b).toAddMonoidHom).eqLocus
      (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ b).toAddMonoidHom) ↔
        u ^ (Λ a b) = u ^ (Λ b a) := by
  -- The subgroup equalizer has the same membership equation as its underlying submonoid.
  change (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ.flip b).toAddMonoidHom) a =
    (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ b).toAddMonoidHom) a ↔ _
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    MonoidHom.coe_toAdditiveRight, Function.comp_apply, zpowersHom_apply,
    toAdd_ofAdd, Additive.ofMul.injective.eq_iff]
  exact (congrArg (fun n : ℤ ↦ u ^ n = u ^ (Λ b a))
    (LinearMap.flip_apply Λ a b)).to_iff

/-- Membership in the central exponent subgroup is equality of opposite powers. -/
@[simp]
theorem mem_quantumTorusCentralExponents (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ (Λ a b) = u ^ (Λ b a) := by
  simp only [quantumTorusCentralExponents, AddSubgroup.mem_iInf, centralExponentEqualizer_mem]

/-- The skew part of any bilinear form detects central exponents, including at finite order. -/
theorem mem_quantumTorusCentralExponents_iff (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ ((Λ - Λ.flip) a b) = 1 := by
  rw [mem_quantumTorusCentralExponents]
  apply forall_congr'
  intro b
  have hf : (Λ.flip a) b = Λ b a := LinearMap.flip_apply Λ b a
  simp only [LinearMap.sub_apply]
  rw [hf, zpow_sub, _root_.mul_inv_eq_one]

/-- An infinite-order parameter makes the central exponent subgroup the kernel of the skew part. -/
theorem quantumTorusCentralExponents_eq_ker (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (hu : ¬ IsOfFinOrder u) :
    u.quantumTorusCentralExponents Λ = (LinearMap.ker (Λ - Λ.flip)).toAddSubgroup := by
  ext a
  rw [mem_quantumTorusCentralExponents_iff, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  constructor
  · intro h
    ext b
    exact (injective_zpow_iff_not_isOfFinOrder.mpr hu)
      ((h b).trans (zpow_zero u).symm)
  · intro h b
    rw [LinearMap.congr_fun h b]
    exact zpow_zero u

end Units

namespace TauCeti.QuantumTorus

section Monoid

variable {R L : Type*} [Monoid R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- For an alternating form, central exponents are detected by the commutation factors,
without an infinite-order hypothesis on the parameter. -/
theorem _root_.LinearMap.BilinForm.IsAlt.mem_quantumTorusCentralExponents_iff
    (hΛ : Λ.IsAlt) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ (2 * Λ a b) = 1 := by
  rw [Units.mem_quantumTorusCentralExponents_iff]
  apply forall_congr'
  intro b
  have he : (Λ - Λ.flip) a b = 2 * Λ a b := by
    have hf : (Λ.flip a) b = Λ b a := LinearMap.flip_apply Λ b a
    simp only [LinearMap.sub_apply]
    rw [hf]
    have := hΛ.neg_eq a b
    omega
  rw [he]

/-- For an alternating form and a parameter whose square has infinite order, the central
exponent subgroup is the radical of the form. -/
theorem _root_.LinearMap.BilinForm.IsAlt.quantumTorusCentralExponents_eq_ker
    (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2)) :
    u.quantumTorusCentralExponents Λ = (LinearMap.ker Λ).toAddSubgroup := by
  ext a
  rw [hΛ.mem_quantumTorusCentralExponents_iff, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  constructor
  · intro h
    ext b
    apply (injective_zpow_iff_not_isOfFinOrder.mpr hu)
    simpa only [← zpow_natCast, ← zpow_mul, Nat.cast_ofNat, zpow_zero,
      LinearMap.zero_apply] using h b
  · intro h b
    rw [LinearMap.congr_fun h b]
    simp

end Monoid

variable {R L : Type*} [CommSemiring R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- A torus element is central exactly when it commutes with every normalized monomial. -/
theorem mem_center_iff_commute_monomial (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      ∀ b, Commute f (monomial u Λ b) := by
  simpa only [Multiplicative.forall, monomial_def] using
    (TwistedMonoidAlgebra.mem_center_iff_commute_of (α := factorSet u Λ) f)

/-- A torus element is central if and only if every coefficient weighted by either
opposite twist factor agrees. Without scalar cancellation, the factors themselves may differ. -/
theorem mem_center_iff_coeff (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔ ∀ a b,
      (basis u Λ).repr f a * (u ^ (Λ a b) : Rˣ) =
        (basis u Λ).repr f a * (u ^ (Λ b a) : Rˣ) := by
  simpa only [Multiplicative.forall, ← basis_repr_apply, factorSet_apply,
    toAdd_ofAdd] using
    (TwistedMonoidAlgebra.mem_center_iff_coeff (α := factorSet u Λ) f)

/-- A normalized monomial is central precisely at the central exponent subgroup.
No cancellation or nontriviality assumption is needed for its scalar coefficient one. -/
@[simp]
theorem monomial_mem_center_iff (a : L) :
    monomial u Λ a ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      a ∈ u.quantumTorusCentralExponents Λ := by
  simpa only [monomial_def, Multiplicative.forall, factorSet_apply,
    Units.mem_quantumTorusCentralExponents, toAdd_ofAdd] using
    (TwistedMonoidAlgebra.of_mem_center_iff (α := factorSet u Λ) (Multiplicative.ofAdd a))

/-- If nonzero scalar coefficients cancel, centrality is support on central exponents. -/
theorem mem_center_iff_support [IsLeftCancelMulZero R] (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      ∀ a ∈ ((basis u Λ).repr f).support, a ∈ u.quantumTorusCentralExponents Λ := by
  simpa only [Multiplicative.forall, Finsupp.mem_support_iff, ← basis_repr_apply,
    factorSet_apply, Units.mem_quantumTorusCentralExponents, toAdd_ofAdd] using
    (TwistedMonoidAlgebra.mem_center_iff_support (α := factorSet u Λ) f)

/-- The center is the span of its normalized central monomials when scalar coefficients cancel. -/
theorem center_toSubmodule_eq_span [IsLeftCancelMulZero R] :
    (Subalgebra.center R (QuantumTorus R L u Λ)).toSubmodule =
      Submodule.span R (monomial u Λ '' (u.quantumTorusCentralExponents Λ : Set L)) := by
  let S := {a : Multiplicative L | ∀ b, factorSet u Λ a b = factorSet u Λ b a}
  have hs : (u.quantumTorusCentralExponents Λ : Set L) = Multiplicative.ofAdd ⁻¹' S := by
    ext a
    simp only [SetLike.mem_coe, Units.mem_quantumTorusCentralExponents, Set.mem_preimage, S,
      Set.mem_ofPred_eq, Multiplicative.forall, factorSet_apply, toAdd_ofAdd]
  have hm : monomial u Λ = TwistedMonoidAlgebra.of (α := factorSet u Λ) ∘
      Multiplicative.ofAdd := funext monomial_def
  have hi : (TwistedMonoidAlgebra.of (α := factorSet u Λ) '' S) =
      monomial u Λ '' (u.quantumTorusCentralExponents Λ : Set L) := by
    rw [hs, hm, Set.image_comp, Multiplicative.ofAdd.surjective.image_preimage]
  rw [← hi]
  exact TwistedMonoidAlgebra.center_toSubmodule_eq_span

private def centralIndexEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    Multiplicative (u.quantumTorusCentralExponents Λ) ≃*
      TwistedMonoidAlgebra.centralIndices (factorSet u Λ) where
  toFun a := ⟨Multiplicative.ofAdd (a.toAdd : L), by
    simpa only [TwistedMonoidAlgebra.mem_centralIndices, factorSet_apply,
      Multiplicative.forall, toAdd_ofAdd] using
      (Units.mem_quantumTorusCentralExponents u Λ _).mp a.toAdd.property⟩
  invFun a := Multiplicative.ofAdd ⟨a.val.toAdd, by
    simpa only [Units.mem_quantumTorusCentralExponents, factorSet_apply,
      Multiplicative.forall, toAdd_ofAdd] using
      (TwistedMonoidAlgebra.mem_centralIndices _).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem centralIndexEquiv_apply_coe (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a : Multiplicative (u.quantumTorusCentralExponents Λ)) :
    ((centralIndexEquiv u Λ) a : Multiplicative L) =
      Multiplicative.ofAdd (a.toAdd : L) := rfl

private theorem centralIndexEquiv_symm_apply_coe (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a : TwistedMonoidAlgebra.centralIndices (factorSet u Λ)) :
    (((centralIndexEquiv u Λ).symm a).toAdd : L) = a.val.toAdd := rfl

private noncomputable def centralTorusEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap) ≃ₐ[R]
      twistedMonoidAlgebra R (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
        (fun a b ↦ factorSet u Λ a b) := by
  let e := centralIndexEquiv u Λ
  exact AlgEquiv.ofAlgHom
    (TwistedMonoidAlgebra.lift (fun a ↦ TwistedMonoidAlgebra.of (e a))
      (by simp) (by
        intro a b
        simp only [TwistedMonoidAlgebra.of_mul_of, map_mul]
        congr 1
        simp only [e, factorSet_apply, centralIndexEquiv_apply_coe, toAdd_ofAdd,
          LinearMap.compl₁₂_apply, AddMonoidHom.coe_toIntLinearMap,
          AddSubgroup.subtype_apply]))
    (TwistedMonoidAlgebra.lift (fun a ↦ TwistedMonoidAlgebra.of (e.symm a))
      (by simp) (by
        intro a b
        simp only [TwistedMonoidAlgebra.of_mul_of, map_mul]
        congr 1
        simp only [e, factorSet_apply, LinearMap.compl₁₂_apply,
          AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply,
          centralIndexEquiv_symm_apply_coe]))
    (by apply TwistedMonoidAlgebra.algHom_ext; intro a; simp)
    (by apply TwistedMonoidAlgebra.algHom_ext; intro a; simp)

private theorem centralTorusEquiv_monomial (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a : u.quantumTorusCentralExponents Λ) :
    centralTorusEquiv u Λ (monomial u _ a) =
      TwistedMonoidAlgebra.of (centralIndexEquiv u Λ (Multiplicative.ofAdd a)) := by
  rw [← AlgEquiv.toAlgHom_apply]
  simp only [centralTorusEquiv, AlgEquiv.toAlgHom_ofAlgHom, monomial_def,
    TwistedMonoidAlgebra.lift_of]

/-- The canonical map from the torus on central exponents to the center, preserving its
restricted bilinear twist. It reuses the arbitrary-factor-set restricted center map. -/
noncomputable def _root_.Units.quantumTorusCenterHom (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap) →ₐ[R]
      Subalgebra.center R (QuantumTorus R L u Λ) :=
  (TwistedMonoidAlgebra.centerHom (factorSet u Λ)).comp (centralTorusEquiv u Λ).toAlgHom

/-- The restricted map preserves normalized monomials inside the bundled center. -/
@[simp]
theorem _root_.Units.quantumTorusCenterHom_monomial (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : u.quantumTorusCentralExponents Λ) :
    (u.quantumTorusCenterHom Λ) (monomial u _ a) =
      ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr a.property⟩ := by
  apply Subtype.ext
  simp only [Units.quantumTorusCenterHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    centralTorusEquiv_monomial, TwistedMonoidAlgebra.centerHom_of]
  simp only [centralIndexEquiv_apply_coe, monomial_def, toAdd_ofAdd]

/-- The restricted central torus embeds without a scalar cancellation assumption. -/
theorem _root_.Units.quantumTorusCenterHom_injective (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) : Function.Injective (u.quantumTorusCenterHom Λ) :=
  TwistedMonoidAlgebra.centerHom_injective.comp (centralTorusEquiv u Λ).injective

/-- If nonzero scalar coefficients cancel, every central element has a restricted preimage. -/
theorem _root_.Units.quantumTorusCenterHom_surjective [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) : Function.Surjective (u.quantumTorusCenterHom Λ) :=
  TwistedMonoidAlgebra.centerHom_surjective.comp (centralTorusEquiv u Λ).surjective

/-- With nonzero-scalar cancellation, the restricted central torus is the actual center. -/
noncomputable def _root_.Units.quantumTorusCenterEquiv [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap) ≃ₐ[R]
      Subalgebra.center R (QuantumTorus R L u Λ) :=
  AlgEquiv.ofBijective (u.quantumTorusCenterHom Λ)
    ⟨u.quantumTorusCenterHom_injective Λ, u.quantumTorusCenterHom_surjective Λ⟩

/-- The center equivalence preserves normalized monomials inside the bundled center. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_monomial [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : u.quantumTorusCentralExponents Λ) :
    (u.quantumTorusCenterEquiv Λ) (monomial u _ a) =
      ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr a.property⟩ :=
  (AlgEquiv.ofBijective_apply _ _ _).trans (u.quantumTorusCenterHom_monomial Λ a)

/-- The center equivalence has the canonical center homomorphism as its algebra map. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_toAlgHom [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    (u.quantumTorusCenterEquiv Λ).toAlgHom = u.quantumTorusCenterHom Λ :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- The inverse center equivalence sends a bundled central monomial to its restricted monomial. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_symm_monomial [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : u.quantumTorusCentralExponents Λ) :
    (u.quantumTorusCenterEquiv Λ).symm
      ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr a.property⟩ = monomial u _ a := by
  apply (u.quantumTorusCenterEquiv Λ).symm_apply_eq.mpr
  exact (u.quantumTorusCenterEquiv_monomial Λ a).symm

/-- At generic parameter, the center is the ordinary additive group algebra on the radical. -/
noncomputable def _root_.LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivGroupAlgebra
    [IsLeftCancelMulZero R] (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2)) :
    Subalgebra.center R (QuantumTorus R L u Λ) ≃ₐ[R]
      AddMonoidAlgebra R (LinearMap.ker Λ).toAddSubgroup := by
  let S := u.quantumTorusCentralExponents Λ
  let ΛS := Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap
  have ht : ∀ a b : S, u ^ (ΛS a b) = 1 := by
    intro a b
    have ha : (a : L) ∈ (LinearMap.ker Λ).toAddSubgroup := by
      rw [← hΛ.quantumTorusCentralExponents_eq_ker hu]
      exact a.property
    have he := LinearMap.congr_fun (LinearMap.mem_ker.mp ha) (b : L)
    simpa only [ΛS, LinearMap.compl₁₂_apply, AddMonoidHom.coe_toIntLinearMap,
      AddSubgroup.subtype_apply, he, LinearMap.zero_apply] using zpow_zero u
  exact (u.quantumTorusCenterEquiv Λ).symm.trans
    ((untwistedEquiv u ΛS ht).trans (AddMonoidAlgebra.domCongr R R
      (AddEquiv.addSubgroupCongr (hΛ.quantumTorusCentralExponents_eq_ker hu))))

/-- The ordinary radical-algebra identification sends central normalized monomials
to basis terms. -/
@[simp]
theorem _root_.LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivGroupAlgebra_monomial
    [IsLeftCancelMulZero R] (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2))
    (a : u.quantumTorusCentralExponents Λ) :
    hΛ.quantumTorusCenterEquivGroupAlgebra hu
      ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr a.property⟩ =
        AddMonoidAlgebra.single
          (AddEquiv.addSubgroupCongr (hΛ.quantumTorusCentralExponents_eq_ker hu) a) 1 := by
  simp only [LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivGroupAlgebra,
    AlgEquiv.trans_apply, Units.quantumTorusCenterEquiv_symm_monomial,
    untwistedEquiv_monomial, AddMonoidAlgebra.domCongr_single]

end TauCeti.QuantumTorus
