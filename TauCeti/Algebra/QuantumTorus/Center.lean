/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuantumTorus.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Center
public import TauCeti.LinearAlgebra.BilinearForm.Basic

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

namespace TauCeti.QuantumTorus

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
  left_inv a := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [toAdd_ofAdd]
  right_inv a := by
    apply Subtype.ext
    simp only [toAdd_ofAdd, ofAdd_toAdd]
  map_mul' a b := by
    apply Subtype.ext
    simp only [toAdd_mul, AddSubgroup.coe_add, ofAdd_add, Submonoid.coe_mul]

private theorem centralIndexEquiv_apply_coe (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a : Multiplicative (u.quantumTorusCentralExponents Λ)) :
    ((centralIndexEquiv u Λ) a : Multiplicative L) =
      Multiplicative.ofAdd (a.toAdd : L) := rfl

private theorem centralForm_apply (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a b : u.quantumTorusCentralExponents Λ) :
    (Λ.compl₁₂ (u.quantumTorusCentralExponents Λ).subtype.toIntLinearMap
      (u.quantumTorusCentralExponents Λ).subtype.toIntLinearMap) a b = Λ (a : L) (b : L) := by
  simp only [LinearMap.compl₁₂_apply, AddMonoidHom.coe_toIntLinearMap,
    AddSubgroup.subtype_apply]

private noncomputable def centralTorusHom (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap) →ₐ[R]
      twistedMonoidAlgebra R (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
        (fun a b ↦ factorSet u Λ a b) :=
  TwistedMonoidAlgebra.lift
    (fun a ↦ TwistedMonoidAlgebra.of (centralIndexEquiv u Λ a)) (by simp) (by
      intro a b
      simp only [TwistedMonoidAlgebra.of_mul_of, map_mul]
      congr 1
      simp only [factorSet_apply, centralIndexEquiv_apply_coe, toAdd_ofAdd, centralForm_apply])

private theorem centralTorusHom_toLinearMap (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    let ΛS := Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap
    (centralTorusHom u Λ).toLinearMap =
      ((TwistedMonoidAlgebra.basis R (Multiplicative S) (factorSet u ΛS)).equiv
        (TwistedMonoidAlgebra.basis R (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
          (fun a b ↦ factorSet u Λ a b)) (centralIndexEquiv u Λ).toEquiv).toLinearMap := by
  dsimp only
  apply (TwistedMonoidAlgebra.basis R _ _).ext
  intro a
  simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
  rw [Module.Basis.equiv_apply]
  simp only [TwistedMonoidAlgebra.basis_apply, centralTorusHom,
    TwistedMonoidAlgebra.lift_of, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]

private noncomputable def centralTorusEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap) ≃ₐ[R]
      twistedMonoidAlgebra R (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
        (fun a b ↦ factorSet u Λ a b) := by
  apply AlgEquiv.ofBijective (centralTorusHom u Λ)
  have h : Function.Bijective (centralTorusHom u Λ).toLinearMap := by
    rw [centralTorusHom_toLinearMap]
    exact LinearEquiv.bijective _
  rw [AlgHom.coe_toLinearMap] at h
  exact h

private theorem centralTorusEquiv_monomial (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a : u.quantumTorusCentralExponents Λ) :
    centralTorusEquiv u Λ (monomial u _ a) =
      TwistedMonoidAlgebra.of (centralIndexEquiv u Λ (Multiplicative.ofAdd a)) := by
  simp only [centralTorusEquiv, AlgEquiv.ofBijective_apply, centralTorusHom,
    monomial_def, TwistedMonoidAlgebra.lift_of]

private theorem centralTorusEquiv_repr (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (f : let S := u.quantumTorusCentralExponents Λ
      QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap))
    (a : u.quantumTorusCentralExponents Λ) :
    (TwistedMonoidAlgebra.basis R (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
      (fun a b ↦ factorSet u Λ a b)).repr (centralTorusEquiv u Λ f)
        (centralIndexEquiv u Λ (Multiplicative.ofAdd a)) =
      (basis u (Λ.compl₁₂ (u.quantumTorusCentralExponents Λ).subtype.toIntLinearMap
        (u.quantumTorusCentralExponents Λ).subtype.toIntLinearMap)).repr f a := by
  let S := u.quantumTorusCentralExponents Λ
  let ΛS := Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap
  let bs := TwistedMonoidAlgebra.basis R (Multiplicative S) (factorSet u ΛS)
  let bt := TwistedMonoidAlgebra.basis R (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
    (fun a b ↦ factorSet u Λ a b)
  let e := (centralIndexEquiv u Λ).toEquiv
  have hm : centralTorusEquiv u Λ f = bs.equiv bt e f := by
    rw [centralTorusEquiv, AlgEquiv.ofBijective_apply]
    have h := LinearMap.congr_fun (centralTorusHom_toLinearMap u Λ) f
    simpa only [bs, bt, e, S, ΛS, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] using h
  have hr : (bt.reindex e.symm).repr (centralTorusEquiv u Λ f) = bs.repr f := by
    rw [hm]
    simp only [Module.Basis.equiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hc := congrArg (fun l ↦ l (Multiplicative.ofAdd a)) hr
  simpa only [Module.Basis.repr_reindex_apply, Equiv.symm_symm,
    bs, bt, e, S, ΛS, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    ← basis_repr_apply] using hc

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

/-- Included exponent coefficients are unchanged by the restricted center map. -/
@[simp]
theorem _root_.Units.basis_repr_quantumTorusCenterHom_apply (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L)
    (f : let S := u.quantumTorusCentralExponents Λ
      QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap))
    (a : u.quantumTorusCentralExponents Λ) :
    (basis u Λ).repr ((u.quantumTorusCenterHom Λ f :
      Subalgebra.center R (QuantumTorus R L u Λ)) : QuantumTorus R L u Λ) (a : L) =
      (basis u (Λ.compl₁₂ (u.quantumTorusCentralExponents Λ).subtype.toIntLinearMap
        (u.quantumTorusCentralExponents Λ).subtype.toIntLinearMap)).repr f a := by
  have h := TwistedMonoidAlgebra.repr_centerHom_apply (centralTorusEquiv u Λ f)
    (centralIndexEquiv u Λ (Multiplicative.ofAdd a))
  simpa only [Units.quantumTorusCenterHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    centralIndexEquiv_apply_coe, toAdd_ofAdd, basis_repr_apply] using
      h.trans (centralTorusEquiv_repr u Λ f a)

/-- Ambient exponent coefficients outside the central subgroup vanish under the center map. -/
theorem _root_.Units.basis_repr_quantumTorusCenterHom_apply_eq_zero (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L)
    (f : let S := u.quantumTorusCentralExponents Λ
      QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap))
    (a : L) (ha : a ∉ u.quantumTorusCentralExponents Λ) :
    (basis u Λ).repr ((u.quantumTorusCenterHom Λ f :
      Subalgebra.center R (QuantumTorus R L u Λ)) : QuantumTorus R L u Λ) a = 0 := by
  have ha' : Multiplicative.ofAdd a ∉ TwistedMonoidAlgebra.centralIndices (factorSet u Λ) := by
    simpa only [TwistedMonoidAlgebra.mem_centralIndices, factorSet_apply,
      Multiplicative.forall, toAdd_ofAdd, Units.mem_quantumTorusCentralExponents] using ha
  simpa only [Units.quantumTorusCenterHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    basis_repr_apply] using TwistedMonoidAlgebra.repr_centerHom_apply_eq_zero
      (centralTorusEquiv u Λ f) (Multiplicative.ofAdd a) ha'

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
  (centralTorusEquiv u Λ).trans (TwistedMonoidAlgebra.centerEquiv (α := factorSet u Λ))

/-- The center equivalence preserves normalized monomials inside the bundled center. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_monomial [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : u.quantumTorusCentralExponents Λ) :
    (u.quantumTorusCenterEquiv Λ) (monomial u _ a) =
      ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr a.property⟩ :=
  by
    rw [Units.quantumTorusCenterEquiv, AlgEquiv.trans_apply,
      centralTorusEquiv_monomial, TwistedMonoidAlgebra.centerEquiv_of]
    apply Subtype.ext
    simp only [centralIndexEquiv_apply_coe, monomial_def, toAdd_ofAdd]

/-- The center equivalence has the canonical center homomorphism as its algebra map. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_toAlgHom [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    (u.quantumTorusCenterEquiv Λ).toAlgHom = u.quantumTorusCenterHom Λ :=
  by
    apply AlgHom.ext
    intro x
    simp only [Units.quantumTorusCenterEquiv, Units.quantumTorusCenterHom,
      AlgEquiv.toAlgHom_apply, AlgEquiv.trans_apply, AlgHom.comp_apply]
    exact congrArg (fun f ↦ f (centralTorusEquiv u Λ x))
      (TwistedMonoidAlgebra.centerEquiv_toAlgHom (α := factorSet u Λ))

/-- The inverse center equivalence sends a bundled central monomial to its restricted monomial. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_symm_monomial [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : u.quantumTorusCentralExponents Λ) :
    (u.quantumTorusCenterEquiv Λ).symm
      ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr a.property⟩ = monomial u _ a := by
  apply (u.quantumTorusCenterEquiv Λ).symm_apply_eq.mpr
  exact (u.quantumTorusCenterEquiv_monomial Λ a).symm

/-- For an alternating form, when the parameter square has infinite order and nonzero scalar
coefficients cancel, the center is the ordinary additive group algebra on the radical. -/
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
    simpa only [ΛS, S, centralForm_apply, he, LinearMap.zero_apply] using zpow_zero u
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

/-- The inverse radical-algebra equivalence sends each basis singleton to its scalar
multiple of the bundled central monomial, indexed directly by the radical. -/
@[simp]
theorem _root_.LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivGroupAlgebra_symm_single
    [IsLeftCancelMulZero R] (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2))
    (a : (LinearMap.ker Λ).toAddSubgroup) (r : R) :
    (hΛ.quantumTorusCenterEquivGroupAlgebra hu).symm (AddMonoidAlgebra.single a r) =
      r • ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr (by
        rw [hΛ.quantumTorusCentralExponents_eq_ker hu]
        exact a.property)⟩ := by
  have ha : (a : L) ∈ u.quantumTorusCentralExponents Λ := by
    rw [hΛ.quantumTorusCentralExponents_eq_ker hu]
    exact a.property
  let b : u.quantumTorusCentralExponents Λ := ⟨a, ha⟩
  have hb : AddEquiv.addSubgroupCongr (hΛ.quantumTorusCentralExponents_eq_ker hu) b = a := by
    apply Subtype.ext
    simp only [AddEquiv.addSubgroupCongr_apply, b]
  apply (hΛ.quantumTorusCenterEquivGroupAlgebra hu).symm_apply_eq.mpr
  rw [map_smul, hΛ.quantumTorusCenterEquivGroupAlgebra_monomial hu b, hb]
  simp

end TauCeti.QuantumTorus
