/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuantumTorus.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Center
public import TauCeti.Algebra.QuantumTorus.CentralExponents
public import TauCeti.Algebra.Group.Submonoid.Operations
public import TauCeti.Algebra.Module.Submodule.Lattice

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

private theorem centralIndices_eq (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    (u.quantumTorusCentralExponents Λ).toIntSubmodule.toAddSubgroup.toSubgroup.toSubmonoid =
      TwistedMonoidAlgebra.centralIndices (factorSet u Λ) := by
  rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
  ext a
  simp only [Subgroup.mem_toSubmonoid, Multiplicative.mem_toSubgroup,
    TwistedMonoidAlgebra.mem_centralIndices, Units.mem_quantumTorusCentralExponents,
    Multiplicative.forall, factorSet_apply, toAdd_ofAdd]

private theorem mem_centralIndices_iff (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    Multiplicative.ofAdd a ∈ TwistedMonoidAlgebra.centralIndices (factorSet u Λ) ↔
      a ∈ u.quantumTorusCentralExponents Λ := by
  rw [← centralIndices_eq]
  simp only [Subgroup.mem_toSubmonoid, Multiplicative.mem_toSubgroup, toAdd_ofAdd,
    AddSubgroup.toIntSubmodule_toAddSubgroup]

/-- A normalized monomial is central precisely at the central exponent subgroup.
No cancellation or nontriviality assumption is needed for its scalar coefficient one. -/
@[simp]
theorem monomial_mem_center_iff (a : L) :
    monomial u Λ a ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      a ∈ u.quantumTorusCentralExponents Λ := by
  rw [monomial_def, TwistedMonoidAlgebra.of_mem_center_iff,
    ← TwistedMonoidAlgebra.mem_centralIndices]
  exact mem_centralIndices_iff u Λ a

/-- If nonzero scalar coefficients cancel, centrality is support on central exponents. -/
theorem mem_center_iff_support [IsLeftCancelMulZero R] (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      ∀ a ∈ ((basis u Λ).repr f).support, a ∈ u.quantumTorusCentralExponents Λ := by
  simpa only [← TwistedMonoidAlgebra.mem_centralIndices, Multiplicative.forall,
    Finsupp.mem_support_iff, ← basis_repr_apply, mem_centralIndices_iff] using
    (TwistedMonoidAlgebra.mem_center_iff_support (α := factorSet u Λ) f)

/-- Support on central exponents suffices for centrality without scalar cancellation. -/
theorem mem_center_of_support (f : QuantumTorus R L u Λ)
    (h : ∀ a ∈ ((basis u Λ).repr f).support, a ∈ u.quantumTorusCentralExponents Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) := by
  apply TwistedMonoidAlgebra.mem_center_of_support
  intro a ha
  exact (TwistedMonoidAlgebra.mem_centralIndices a).mp
    ((mem_centralIndices_iff u Λ a.toAdd).mpr
      (h a.toAdd (by simpa only [Finsupp.mem_support_iff, basis_repr_apply, ofAdd_toAdd] using ha)))

/-- The center is the span of its normalized central monomials when scalar coefficients cancel. -/
theorem center_toSubmodule_eq_span [IsLeftCancelMulZero R] :
    (Subalgebra.center R (QuantumTorus R L u Λ)).toSubmodule =
      Submodule.span R (monomial u Λ '' (u.quantumTorusCentralExponents Λ : Set L)) := by
  let S : Set (Multiplicative L) := TwistedMonoidAlgebra.centralIndices (factorSet u Λ)
  have hs : (u.quantumTorusCentralExponents Λ : Set L) = Multiplicative.ofAdd ⁻¹' S := by
    ext a
    exact (mem_centralIndices_iff u Λ a).symm
  have hm : monomial u Λ = TwistedMonoidAlgebra.of (α := factorSet u Λ) ∘
      Multiplicative.ofAdd := funext monomial_def
  have hi : (TwistedMonoidAlgebra.of (α := factorSet u Λ) '' S) =
      monomial u Λ '' (u.quantumTorusCentralExponents Λ : Set L) := by
    rw [hs, hm, Set.image_comp, Multiplicative.ofAdd.surjective.image_preimage]
  rw [← hi]
  have hs' : S = {a | ∀ b, factorSet u Λ a b = factorSet u Λ b a} :=
    Set.ext fun a ↦ TwistedMonoidAlgebra.mem_centralIndices a
  rw [hs']
  exact TwistedMonoidAlgebra.center_toSubmodule_eq_span (R := R) (α := factorSet u Λ)

private def centralIndexEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    Multiplicative (u.quantumTorusCentralExponents Λ).toIntSubmodule ≃*
      TwistedMonoidAlgebra.centralIndices (factorSet u Λ) :=
  MulEquiv.submonoidCongr (centralIndices_eq u Λ)

private theorem centralIndexEquiv_apply_coe (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a : Multiplicative (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    ((centralIndexEquiv u Λ) a : Multiplicative L) =
      Multiplicative.ofAdd (a.toAdd : L) := by
  -- The multiplicative subtype's ambient value is definitionally the tag of its exponent.
  exact MulEquiv.submonoidCongr_apply (centralIndices_eq u Λ) a

private theorem centralFactorSet_eq (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a b : Multiplicative (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    factorSet u (Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule) a b =
      factorSet u Λ (centralIndexEquiv u Λ a) (centralIndexEquiv u Λ b) := by
  simp only [factorSet_apply, centralIndexEquiv_apply_coe, toAdd_ofAdd,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]

private noncomputable def centralTorusEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    let S := (u.quantumTorusCentralExponents Λ).toIntSubmodule
    QuantumTorus R S u (Λ.restrict S) ≃ₐ[R]
      twistedMonoidAlgebra R (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
        (fun a b ↦ factorSet u Λ a b) :=
  TwistedMonoidAlgebra.domCongr (centralIndexEquiv u Λ) (centralFactorSet_eq u Λ)

private theorem centralTorusEquiv_monomial (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    centralTorusEquiv u Λ (monomial u _ a) =
      TwistedMonoidAlgebra.of (centralIndexEquiv u Λ (Multiplicative.ofAdd a)) := by
  rw [centralTorusEquiv, monomial_def, TwistedMonoidAlgebra.domCongr_of]

private theorem repr_centralTorusEquiv_apply (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (f : let S := (u.quantumTorusCentralExponents Λ).toIntSubmodule
      QuantumTorus R S u (Λ.restrict S))
    (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    (TwistedMonoidAlgebra.basis R
      (TwistedMonoidAlgebra.centralIndices (factorSet u Λ))
      (fun a b ↦ factorSet u Λ a b)).repr (centralTorusEquiv u Λ f)
        (centralIndexEquiv u Λ (Multiplicative.ofAdd a)) =
      (basis u (Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule)).repr f a := by
  rw [centralTorusEquiv]
  simpa only [basis_repr_apply] using TwistedMonoidAlgebra.repr_domCongr_apply
    (β := fun a b : TwistedMonoidAlgebra.centralIndices (factorSet u Λ) ↦ factorSet u Λ a b)
    (centralIndexEquiv u Λ) (centralFactorSet_eq u Λ) f (Multiplicative.ofAdd a)

/-- A normalized central monomial, bundled as an element of the center. -/
noncomputable def _root_.Units.quantumTorusCenterMonomial (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : L) (ha : a ∈ u.quantumTorusCentralExponents Λ) :
    Subalgebra.center R (QuantumTorus R L u Λ) :=
  ⟨monomial u Λ a, (monomial_mem_center_iff _).mpr ha⟩

/-- The bundled central monomial has its normalized ambient value. -/
@[simp]
theorem _root_.Units.coe_quantumTorusCenterMonomial (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : L) (ha : a ∈ u.quantumTorusCentralExponents Λ) :
    (u.quantumTorusCenterMonomial Λ a ha : QuantumTorus R L u Λ) = monomial u Λ a := (rfl)

/-- The canonical map from the torus on central exponents to the center, preserving its
restricted bilinear twist. It reuses the arbitrary-factor-set restricted center map. -/
noncomputable def _root_.Units.quantumTorusCenterHom (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    let S := (u.quantumTorusCentralExponents Λ).toIntSubmodule
    QuantumTorus R S u (Λ.restrict S) →ₐ[R]
      Subalgebra.center R (QuantumTorus R L u Λ) :=
  (TwistedMonoidAlgebra.centerHom (factorSet u Λ)).comp (centralTorusEquiv u Λ).toAlgHom

/-- The restricted map preserves normalized monomials inside the bundled center. -/
@[simp]
theorem _root_.Units.quantumTorusCenterHom_monomial (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    (u.quantumTorusCenterHom Λ) (monomial u _ a) =
      u.quantumTorusCenterMonomial Λ (a : L)
        ((AddSubgroup.mem_toIntSubmodule _ _).mp a.property) := by
  rw [Units.quantumTorusCenterHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    centralTorusEquiv_monomial, TwistedMonoidAlgebra.centerHom_of]
  apply Subtype.ext
  simp only [TwistedMonoidAlgebra.coe_centerOf, Units.coe_quantumTorusCenterMonomial,
    centralIndexEquiv_apply_coe, toAdd_ofAdd, monomial_def]

/-- Included exponent coefficients are unchanged by the restricted center map. -/
@[simp]
theorem _root_.Units.basis_repr_quantumTorusCenterHom_apply (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L)
    (f : let S := (u.quantumTorusCentralExponents Λ).toIntSubmodule
      QuantumTorus R S u (Λ.restrict S))
    (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    (basis u Λ).repr ((u.quantumTorusCenterHom Λ f :
      Subalgebra.center R (QuantumTorus R L u Λ)) : QuantumTorus R L u Λ) (a : L) =
      (basis u (Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule)).repr f a := by
  have h := TwistedMonoidAlgebra.repr_centerHom_apply (centralTorusEquiv u Λ f)
    (centralIndexEquiv u Λ (Multiplicative.ofAdd a))
  have hr := repr_centralTorusEquiv_apply u Λ f a
  simpa only [Units.quantumTorusCenterHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    centralIndexEquiv_apply_coe, toAdd_ofAdd, basis_repr_apply] using h.trans hr

/-- Ambient exponent coefficients outside the central subgroup vanish under the center map. -/
theorem _root_.Units.basis_repr_quantumTorusCenterHom_apply_eq_zero (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L)
    (f : let S := (u.quantumTorusCentralExponents Λ).toIntSubmodule
      QuantumTorus R S u (Λ.restrict S))
    (a : L) (ha : a ∉ u.quantumTorusCentralExponents Λ) :
    (basis u Λ).repr ((u.quantumTorusCenterHom Λ f :
      Subalgebra.center R (QuantumTorus R L u Λ)) : QuantumTorus R L u Λ) a = 0 := by
  have ha' : Multiplicative.ofAdd a ∉ TwistedMonoidAlgebra.centralIndices (factorSet u Λ) :=
    fun h ↦ ha ((mem_centralIndices_iff u Λ a).mp h)
  simpa only [Units.quantumTorusCenterHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    basis_repr_apply] using TwistedMonoidAlgebra.repr_centerHom_apply_eq_zero
      (centralTorusEquiv u Λ f) (Multiplicative.ofAdd a) ha'

/-- A bundled center element is in the restricted torus map's image exactly when its
coefficients are supported on central exponents, without scalar cancellation. -/
theorem _root_.Units.mem_range_quantumTorusCenterHom_iff (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (f : Subalgebra.center R (QuantumTorus R L u Λ)) :
    f ∈ Set.range (u.quantumTorusCenterHom Λ) ↔
      ∀ a ∈ ((basis u Λ).repr f.val).support, a ∈ u.quantumTorusCentralExponents Λ := by
  have hr : Set.range (u.quantumTorusCenterHom Λ) =
      Set.range (TwistedMonoidAlgebra.centerHom (factorSet u Λ)) := by
    rw [Units.quantumTorusCenterHom, AlgHom.coe_comp]
    exact (centralTorusEquiv u Λ).surjective.range_comp _
  rw [hr]
  simpa only [Multiplicative.forall, Finsupp.mem_support_iff, ← basis_repr_apply,
    mem_centralIndices_iff] using TwistedMonoidAlgebra.mem_range_centerHom_iff f

/-- The restricted central torus embeds without a scalar cancellation assumption. -/
theorem _root_.Units.quantumTorusCenterHom_injective (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) : Function.Injective (u.quantumTorusCenterHom Λ) :=
  TwistedMonoidAlgebra.centerHom_injective.comp (centralTorusEquiv u Λ).injective

/-- If nonzero scalar coefficients cancel, every central element has a restricted preimage. -/
theorem _root_.Units.quantumTorusCenterHom_surjective [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) : Function.Surjective (u.quantumTorusCenterHom Λ) :=
  by
    intro f
    exact (u.mem_range_quantumTorusCenterHom_iff Λ f).mpr
      ((mem_center_iff_support f.val).mp f.property)

/-- With nonzero-scalar cancellation, the restricted central torus is the actual center. -/
noncomputable def _root_.Units.quantumTorusCenterEquiv [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    let S := (u.quantumTorusCentralExponents Λ).toIntSubmodule
    QuantumTorus R S u (Λ.restrict S) ≃ₐ[R]
      Subalgebra.center R (QuantumTorus R L u Λ) :=
  (centralTorusEquiv u Λ).trans (TwistedMonoidAlgebra.centerEquiv (α := factorSet u Λ))

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

/-- Direct applications of the center equivalence are its canonical center map. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_apply [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L)
    (f : let S := (u.quantumTorusCentralExponents Λ).toIntSubmodule
      QuantumTorus R S u (Λ.restrict S)) :
    u.quantumTorusCenterEquiv Λ f = u.quantumTorusCenterHom Λ f := by
  rw [← AlgEquiv.toAlgHom_apply, Units.quantumTorusCenterEquiv_toAlgHom]

/-- The inverse center equivalence sends a bundled central monomial to its restricted monomial. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquiv_symm_monomial [IsLeftCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    (u.quantumTorusCenterEquiv Λ).symm
      (u.quantumTorusCenterMonomial Λ (a : L)
        ((AddSubgroup.mem_toIntSubmodule _ _).mp a.property)) =
        monomial u _ a := by
  apply (u.quantumTorusCenterEquiv Λ).symm_apply_eq.mpr
  simp

/-- Inverse restricted torus coordinates are the corresponding ambient center coefficients. -/
@[simp]
theorem _root_.Units.basis_repr_quantumTorusCenterEquiv_symm_apply
    [IsLeftCancelMulZero R] (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (f : Subalgebra.center R (QuantumTorus R L u Λ))
    (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    (basis u (Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule)).repr
      ((u.quantumTorusCenterEquiv Λ).symm f) a =
        (basis u Λ).repr (f : QuantumTorus R L u Λ) (a : L) := by
  simpa only [← Units.quantumTorusCenterEquiv_toAlgHom, AlgEquiv.toAlgHom_apply,
    AlgEquiv.apply_symm_apply] using
    (u.basis_repr_quantumTorusCenterHom_apply Λ ((u.quantumTorusCenterEquiv Λ).symm f) a).symm

/-- If the twist on central exponents is trivial and nonzero scalars cancel, the center is
the ordinary additive group algebra on its central exponent submodule. -/
noncomputable def _root_.Units.quantumTorusCenterEquivAddMonoidAlgebra
    [IsLeftCancelMulZero R] (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (ht : ∀ a b : (u.quantumTorusCentralExponents Λ).toIntSubmodule,
      u ^ ((Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule) a b) = 1) :
    Subalgebra.center R (QuantumTorus R L u Λ) ≃ₐ[R]
      AddMonoidAlgebra R (u.quantumTorusCentralExponents Λ).toIntSubmodule :=
  (u.quantumTorusCenterEquiv Λ).symm.trans (untwistedEquiv u _ ht)

/-- Under a trivial restricted twist, central monomials become ordinary basis terms. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquivAddMonoidAlgebra_monomial
    [IsLeftCancelMulZero R] (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (ht : ∀ a b : (u.quantumTorusCentralExponents Λ).toIntSubmodule,
      u ^ ((Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule) a b) = 1)
    (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    u.quantumTorusCenterEquivAddMonoidAlgebra Λ ht
      (u.quantumTorusCenterMonomial Λ (a : L)
        ((AddSubgroup.mem_toIntSubmodule _ _).mp a.property)) =
        AddMonoidAlgebra.single a 1 := by
  simp only [Units.quantumTorusCenterEquivAddMonoidAlgebra, AlgEquiv.trans_apply,
    Units.quantumTorusCenterEquiv_symm_monomial, untwistedEquiv_monomial]

/-- The inverse untwisted center equivalence sends singleton coefficients to scalar monomials. -/
@[simp]
theorem _root_.Units.quantumTorusCenterEquivAddMonoidAlgebra_symm_single
    [IsLeftCancelMulZero R] (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (ht : ∀ a b : (u.quantumTorusCentralExponents Λ).toIntSubmodule,
      u ^ ((Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule) a b) = 1)
    (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) (r : R) :
    (u.quantumTorusCenterEquivAddMonoidAlgebra Λ ht).symm (AddMonoidAlgebra.single a r) =
      r • u.quantumTorusCenterMonomial Λ (a : L)
        ((AddSubgroup.mem_toIntSubmodule _ _).mp a.property) := by
  apply (u.quantumTorusCenterEquivAddMonoidAlgebra Λ ht).symm_apply_eq.mpr
  rw [map_smul, u.quantumTorusCenterEquivAddMonoidAlgebra_monomial Λ ht a]
  simp

/-- Untwisting the center preserves every coefficient at its central exponent. -/
@[simp]
theorem _root_.Units.coeff_quantumTorusCenterEquivAddMonoidAlgebra
    [IsLeftCancelMulZero R] (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (ht : ∀ a b : (u.quantumTorusCentralExponents Λ).toIntSubmodule,
      u ^ ((Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule) a b) = 1)
    (f : Subalgebra.center R (QuantumTorus R L u Λ))
    (a : (u.quantumTorusCentralExponents Λ).toIntSubmodule) :
    (u.quantumTorusCenterEquivAddMonoidAlgebra Λ ht f).coeff a =
      (basis u Λ).repr f.val (a : L) := by
  rw [Units.quantumTorusCenterEquivAddMonoidAlgebra, AlgEquiv.trans_apply,
    coeff_untwistedEquiv, Units.basis_repr_quantumTorusCenterEquiv_symm_apply]

private def centralRadicalEquiv (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2)) :
    (u.quantumTorusCentralExponents Λ).toIntSubmodule ≃+
      (LinearMap.ker Λ).toAddSubgroup :=
  AddEquiv.addSubgroupCongr ((AddSubgroup.toIntSubmodule_toAddSubgroup _).trans
    (hΛ.quantumTorusCentralExponents_eq_ker hu))

private theorem central_twist_trivial (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2)) :
    ∀ a b : (u.quantumTorusCentralExponents Λ).toIntSubmodule,
      u ^ ((Λ.restrict (u.quantumTorusCentralExponents Λ).toIntSubmodule) a b) = 1 := by
  intro a b
  have ha : (a : L) ∈ (LinearMap.ker Λ).toAddSubgroup := by
    rw [← hΛ.quantumTorusCentralExponents_eq_ker hu]
    exact (AddSubgroup.mem_toIntSubmodule _ _).mp a.property
  have he := LinearMap.congr_fun (LinearMap.mem_ker.mp ha) (b : L)
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, he,
    LinearMap.zero_apply, zpow_zero]

/-- For an alternating form, when the parameter square has infinite order and nonzero scalar
coefficients cancel, the center is the ordinary additive group algebra on the radical. -/
noncomputable def _root_.LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivAddMonoidAlgebraKer
    [IsLeftCancelMulZero R] (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2)) :
    Subalgebra.center R (QuantumTorus R L u Λ) ≃ₐ[R]
      AddMonoidAlgebra R (LinearMap.ker Λ).toAddSubgroup :=
  (u.quantumTorusCenterEquivAddMonoidAlgebra Λ (central_twist_trivial hΛ hu)).trans
    (AddMonoidAlgebra.domCongr R R (centralRadicalEquiv hΛ hu))

/-- The radical-algebra equivalence sends a monomial indexed by the radical to its basis term. -/
@[simp]
theorem _root_.LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivAddMonoidAlgebraKer_monomial
    [IsLeftCancelMulZero R] (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2))
    (a : (LinearMap.ker Λ).toAddSubgroup) :
    hΛ.quantumTorusCenterEquivAddMonoidAlgebraKer hu
      (u.quantumTorusCenterMonomial Λ (a : L)
        (hΛ.mem_quantumTorusCentralExponents_of_mem_ker a.property)) =
        AddMonoidAlgebra.single a 1 := by
  let e := centralRadicalEquiv hΛ hu
  have h := congrArg (AddMonoidAlgebra.domCongr R R e)
    (u.quantumTorusCenterEquivAddMonoidAlgebra_monomial Λ (central_twist_trivial hΛ hu)
      (e.symm a))
  have he : (e.symm a : L) = a := AddEquiv.addSubgroupCongr_symm_apply _ a
  simp only [AddMonoidAlgebra.domCongr_single, AddEquiv.apply_symm_apply] at h
  simpa only [he, LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivAddMonoidAlgebraKer,
    AlgEquiv.trans_apply] using h

/-- The inverse radical-algebra equivalence sends singleton coefficients to central monomials. -/
@[simp]
theorem _root_.LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivAddMonoidAlgebraKer_symm_single
    [IsLeftCancelMulZero R] (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2))
    (a : (LinearMap.ker Λ).toAddSubgroup) (r : R) :
    (hΛ.quantumTorusCenterEquivAddMonoidAlgebraKer hu).symm (AddMonoidAlgebra.single a r) =
      r • u.quantumTorusCenterMonomial Λ (a : L)
        (hΛ.mem_quantumTorusCentralExponents_of_mem_ker a.property) := by
  apply (hΛ.quantumTorusCenterEquivAddMonoidAlgebraKer hu).symm_apply_eq.mpr
  rw [map_smul, hΛ.quantumTorusCenterEquivAddMonoidAlgebraKer_monomial hu a]
  simp

/-- The radical-algebra coefficient at a radical exponent is the ambient torus coefficient. -/
@[simp]
theorem _root_.LinearMap.BilinForm.IsAlt.coeff_quantumTorusCenterEquivAddMonoidAlgebraKer
    [IsLeftCancelMulZero R] (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2))
    (f : Subalgebra.center R (QuantumTorus R L u Λ))
    (a : (LinearMap.ker Λ).toAddSubgroup) :
    (hΛ.quantumTorusCenterEquivAddMonoidAlgebraKer hu f).coeff a =
      (basis u Λ).repr f.val (a : L) := by
  rw [LinearMap.BilinForm.IsAlt.quantumTorusCenterEquivAddMonoidAlgebraKer,
    AlgEquiv.trans_apply, AddMonoidAlgebra.coeff_domCongr,
    Units.coeff_quantumTorusCenterEquivAddMonoidAlgebra]
  exact congrArg ((basis u Λ).repr f.val) (AddEquiv.addSubgroupCongr_symm_apply _ a)

end TauCeti.QuantumTorus
