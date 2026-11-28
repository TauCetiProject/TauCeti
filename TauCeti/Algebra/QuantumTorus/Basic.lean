/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Algebra.Units.Basic

/-!
# Based quantum tori

The based quantum torus of an integral bilinear form `Λ` and a scalar unit `u` has
basis `Xᵃ` and multiplication `Xᵃ Xᵇ = u ^ Λ(a,b) • Xᵃ⁺ᵇ`. It is constructed from
`TauCeti.twistedMonoidAlgebra`, using the factor set obtained by exponentiating `Λ`.
For an alternating form, the inverse of `Xᵃ` is exactly `X⁻ᵃ`.

The construction works over commutative semirings and on any additive commutative
group of exponents. In particular, it applies to the finite free exponent lattices
of quantum cluster charts, including the zero lattice. No order or infinite-order
hypothesis on the scalar parameter is used.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4, especially (4.1).
-/

public section

namespace TauCeti

namespace QuantumTorus

variable {R L : Type*} [CommSemiring R] [AddCommGroup L]

/-- Exponentiating an integral bilinear form gives a normalized factor set. -/
def factorSet (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a b : Multiplicative L) : Rˣ :=
  u ^ (Λ a.toAdd b.toAdd)

@[simp]
theorem factorSet_apply (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a b : Multiplicative L) : factorSet u Λ a b = u ^ (Λ a.toAdd b.toAdd) :=
  (rfl)

instance (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) : IsFactorSet (factorSet u Λ) where
  cocycle a b c := by
    simp [factorSet, map_add, zpow_add, mul_comm, mul_assoc]
  one_left a := by simp [factorSet]

end QuantumTorus

/-- The based quantum torus with scalar unit `u` and integral form `Λ`, realized as
its twisted group algebra. Alternation is needed for the normalized inverse and
commutation formulas, but not for the algebra construction. -/
noncomputable abbrev QuantumTorus (R : Type*) [CommSemiring R] (L : Type*) [AddCommGroup L]
    (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :=
  twistedMonoidAlgebra R (Multiplicative L) (QuantumTorus.factorSet u Λ)

namespace QuantumTorus

variable {R L : Type*} [CommSemiring R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- The normalized monomial with exponent `a`. -/
noncomputable def monomial (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    QuantumTorus R L u Λ :=
  TwistedMonoidAlgebra.of (Multiplicative.ofAdd a)

/-- The normalized monomial is the standard generator of the twisted algebra. -/
theorem monomial_def (a : L) :
    monomial u Λ a = TwistedMonoidAlgebra.of (Multiplicative.ofAdd a) :=
  (rfl)

@[simp]
theorem monomial_zero : monomial u Λ 0 = 1 :=
  TwistedMonoidAlgebra.of_one

/-- The normalized monomial multiplication rule. -/
@[simp]
theorem monomial_mul_monomial (a b : L) :
    monomial u Λ a * monomial u Λ b =
      ((u ^ (Λ a b) : Rˣ) : R) • monomial u Λ (a + b) :=
  TwistedMonoidAlgebra.of_mul_of _ _

/-- The normalized monomials form a basis, with additive exponent indices. -/
noncomputable def basis (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    Module.Basis L R (QuantumTorus R L u Λ) :=
  (TwistedMonoidAlgebra.basis R (Multiplicative L) (factorSet u Λ)).reindex
    Multiplicative.toAdd

@[simp]
theorem basis_apply (a : L) : basis u Λ a = monomial u Λ a := by
  simp [basis, monomial]

@[simp]
theorem basis_repr_monomial (a : L) :
    (basis u Λ).repr (monomial u Λ a) = Finsupp.single a 1 := by
  rw [← basis_apply, Module.Basis.repr_self]

/-- The representation of the identity is supported on the zero exponent. -/
@[simp]
theorem basis_repr_one :
    (basis u Λ).repr 1 = Finsupp.single 0 1 := by
  rw [← monomial_zero, basis_repr_monomial]

/-- Scalar multiples of one are supported on the zero exponent. -/
@[simp]
theorem basis_repr_algebraMap (r : R) :
    (basis u Λ).repr (algebraMap R (QuantumTorus R L u Λ) r) = Finsupp.single 0 r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, basis_repr_one, Finsupp.smul_single,
    smul_eq_mul, mul_one]

/-- The additive-index torus coefficients are the corresponding twisted-algebra coefficients. -/
theorem basis_repr_apply (f : QuantumTorus R L u Λ) (a : L) :
    (basis u Λ).repr f a =
      (TwistedMonoidAlgebra.basis R (Multiplicative L) (factorSet u Λ)).repr f
        (Multiplicative.ofAdd a) := by
  simp only [basis, Module.Basis.repr_reindex_apply, Multiplicative.toAdd_symm_eq]

/-- The coefficient at a free index after right multiplication by a monomial. -/
@[simp]
theorem basis_repr_mul_monomial_apply_sub (f : QuantumTorus R L u Λ) (b c : L) :
    (basis u Λ).repr (f * monomial u Λ b) c =
      (basis u Λ).repr f (c - b) * (u ^ (Λ (c - b) b) : Rˣ) := by
  simpa only [basis_repr_apply, monomial_def, factorSet_apply, ← ofAdd_neg,
    ← ofAdd_add, ← sub_eq_add_neg, toAdd_ofAdd] using
    TwistedMonoidAlgebra.repr_mul_of_apply_mul_inv (β := factorSet u Λ) f
      (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)

/-- The coefficient at a free index after left multiplication by a monomial. -/
@[simp]
theorem basis_repr_monomial_mul_apply_sub (f : QuantumTorus R L u Λ) (b c : L) :
    (basis u Λ).repr (monomial u Λ b * f) c =
      (basis u Λ).repr f (c - b) * (u ^ (Λ b (c - b)) : Rˣ) := by
  simpa only [basis_repr_apply, monomial_def, factorSet_apply, ← ofAdd_neg,
    ← ofAdd_add, add_comm (-b) c, ← sub_eq_add_neg, toAdd_ofAdd] using
    TwistedMonoidAlgebra.repr_of_mul_apply_inv_mul (β := factorSet u Λ) f
      (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)

/-- A map out of a based quantum torus is determined by its normalized monomials. -/
@[ext]
theorem algHom_ext {B : Type*} [Semiring B] [Algebra R B]
    {f g : QuantumTorus R L u Λ →ₐ[R] B}
    (h : ∀ a, f (monomial u Λ a) = g (monomial u Λ a)) : f = g :=
  TwistedMonoidAlgebra.algHom_ext fun a ↦ h a.toAdd

/-- Extend a family satisfying the normalized multiplication rule to an algebra map.
Uniqueness is `QuantumTorus.algHom_ext`. -/
noncomputable def lift (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    {B : Type*} [Semiring B] [Algebra R B]
    (M : L → B) (hzero : M 0 = 1)
    (hmul : ∀ a b, M a * M b = ((u ^ (Λ a b) : Rˣ) : R) • M (a + b)) :
    QuantumTorus R L u Λ →ₐ[R] B :=
  TwistedMonoidAlgebra.lift (fun a ↦ M a.toAdd) hzero fun a b ↦ hmul a.toAdd b.toAdd

@[simp]
theorem lift_monomial {B : Type*} [Semiring B] [Algebra R B]
    (M : L → B) (hzero : M 0 = 1)
    (hmul : ∀ a b, M a * M b = ((u ^ (Λ a b) : Rˣ) : R) • M (a + b)) (a : L) :
    lift u Λ M hzero hmul (monomial u Λ a) = M a :=
  TwistedMonoidAlgebra.lift_of ..

/-- Normalized monomials as units. Negating the exponent gives their inverse
when the form is alternating. -/
noncomputable def monomialUnit (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    (QuantumTorus R L u Λ)ˣ where
  val := monomial u Λ a
  inv := ((u ^ (Λ a a) : Rˣ) : R) • monomial u Λ (-a)
  val_inv := by simp [map_neg, smul_smul]
  inv_val := by simp [map_neg, smul_smul]

@[simp]
theorem val_monomialUnit (a : L) :
    (monomialUnit u Λ a : QuantumTorus R L u Λ) = monomial u Λ a :=
  (rfl)

@[simp]
theorem monomialUnit_zero : monomialUnit u Λ 0 = 1 :=
  Units.ext monomial_zero

/-- The underlying inverse of a normalized monomial, including the diagonal correction. -/
theorem val_inv_monomialUnit (a : L) :
    (((monomialUnit u Λ a)⁻¹ : (QuantumTorus R L u Λ)ˣ) : QuantumTorus R L u Λ) =
      ((u ^ (Λ a a) : Rˣ) : R) • monomial u Λ (-a) :=
  (rfl)

/-- The inverse of a normalized monomial, including the diagonal correction. -/
theorem monomialUnit_inv_eq_map_mul (a : L) :
    (monomialUnit u Λ a)⁻¹ =
      Units.map (algebraMap R (QuantumTorus R L u Λ)) (u ^ (Λ a a)) *
        monomialUnit u Λ (-a) :=
  Units.ext <| by simp [val_inv_monomialUnit, Algebra.smul_def, -map_zpow]

/-- For alternating forms, the inverse of a monomial unit has negated exponent. -/
@[simp]
theorem monomialUnit_inv (hΛ : Λ.IsAlt) (a : L) :
    (monomialUnit u Λ a)⁻¹ = monomialUnit u Λ (-a) :=
  Units.ext <| by simp [val_inv_monomialUnit, hΛ.self_eq_zero]

/-- The normalized monomial multiplication rule, in the group of units. -/
@[simp]
theorem monomialUnit_mul (a b : L) :
    monomialUnit u Λ a * monomialUnit u Λ b =
      Units.map (algebraMap R (QuantumTorus R L u Λ)) (u ^ (Λ a b)) *
        monomialUnit u Λ (a + b) :=
  Units.ext <| by simp [Algebra.smul_def, -map_zpow]

/-- Pushing normalized monomial units along an `R`-algebra homomorphism preserves the `(u, Λ)`
multiplication law. -/
theorem map_monomialUnit_mul {B : Type*} [Semiring B] [Algebra R B]
    (χ : QuantumTorus R L u Λ →ₐ[R] B) (a b : L) :
    Units.map χ.toMonoidHom (monomialUnit u Λ a) * Units.map χ.toMonoidHom (monomialUnit u Λ b) =
      Units.map (algebraMap R B) (u ^ (Λ a b)) *
        Units.map χ.toMonoidHom (monomialUnit u Λ (a + b)) := by
  rw [← map_mul, monomialUnit_mul, map_mul]
  exact congrArg (· * _) (Units.ext <| χ.commutes _)

/-- Normalized monomials are units in their based quantum torus. -/
@[simp]
theorem isUnit_monomial (a : L) : IsUnit (monomial u Λ a) :=
  (monomialUnit u Λ a).isUnit

/-- A map out of a based quantum torus is determined by its values on the monomials
of a spanning set of exponents. -/
theorem algHom_ext_of_span_eq_top {B : Type*} [Semiring B] [Algebra R B]
    {f g : QuantumTorus R L u Λ →ₐ[R] B} (s : Set L) (hs : Submodule.span ℤ s = ⊤)
    (h : ∀ a ∈ s, f (monomial u Λ a) = g (monomial u Λ a)) : f = g := by
  refine TwistedMonoidAlgebra.algHom_ext_of_closure_eq_top (s := Multiplicative.toAdd ⁻¹' s)
    ?_ fun a ha ↦ h a.toAdd ha
  rw [← AddSubgroup.toSubgroup_closure, ← Submodule.span_int_eq_addSubgroupClosure, hs]
  simp

/-- A map out of a based quantum torus is determined by its values on the monomials
of a lattice basis. -/
theorem algHom_ext_of_basis {B : Type*} [Semiring B] [Algebra R B]
    {f g : QuantumTorus R L u Λ →ₐ[R] B} {I : Type*} (b : Module.Basis I ℤ L)
    (h : ∀ i, f (monomial u Λ (b i)) = g (monomial u Λ (b i))) : f = g :=
  algHom_ext_of_span_eq_top (Set.range b) b.span_eq <| by
    rintro _ ⟨i, rfl⟩
    exact h i

/-- Integer powers of a normalized monomial unit, including the quadratic diagonal correction. -/
theorem monomialUnit_zpow_eq_map_mul (a : L) (n : ℤ) :
    monomialUnit u Λ a ^ n =
      Units.map (algebraMap R (QuantumTorus R L u Λ)) (u ^ (n * (n - 1) / 2 * Λ a a)) *
        monomialUnit u Λ (n • a) := by
  have hq (m : ℤ) : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
    rw [(by ring : (m + 1) * m = m * (m - 1) + m * 2),
      Int.add_mul_ediv_right _ _ (by decide : (2 : ℤ) ≠ 0)]
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, ih, mul_assoc, monomialUnit_mul, Units.map_algebraMap_mul_map_algebraMap,
      ← zpow_add, add_zsmul, one_zsmul, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
      add_sub_cancel_right, hq (k : ℤ), add_mul]
  | pred k ih =>
    have hq' : (-(k : ℤ) - 1) * (-(k : ℤ) - 1 - 1) / 2 =
        -(k : ℤ) * (-(k : ℤ) - 1) / 2 + 1 + (k : ℤ) := by
      have h0 := hq (-(k : ℤ) - 1)
      rw [sub_add_cancel] at h0
      omega
    rw [zpow_sub_one, ih, monomialUnit_inv_eq_map_mul,
      Units.map_algebraMap_mul_mul_map_algebraMap_mul, monomialUnit_mul,
      Units.map_algebraMap_mul_map_algebraMap, ← zpow_add, ← zpow_add, sub_zsmul, one_zsmul,
      map_zsmul, map_neg, LinearMap.smul_apply, smul_eq_mul, hq', ← sub_eq_add_neg]
    congr 3
    ring

/-- Pushing integer powers of normalized monomial units along an `R`-algebra homomorphism preserves
the quadratic diagonal correction. -/
theorem map_monomialUnit_zpow {B : Type*} [Semiring B] [Algebra R B]
    (χ : QuantumTorus R L u Λ →ₐ[R] B) (a : L) (n : ℤ) :
    Units.map χ.toMonoidHom (monomialUnit u Λ a) ^ n =
      Units.map (algebraMap R B) (u ^ (n * (n - 1) / 2 * Λ a a)) *
        Units.map χ.toMonoidHom (monomialUnit u Λ (n • a)) := by
  rw [← map_zpow, monomialUnit_zpow_eq_map_mul, map_mul]
  exact congrArg (· * _) (Units.ext <| χ.commutes _)

/-- When `Λ a a = 0`, integer multiples of `a` correspond to integer powers of `monomialUnit u Λ a`
without requiring `Λ` to be globally alternating. -/
theorem monomialUnit_zsmul_of_self_eq_zero {a : L} (ha : Λ a a = 0) (n : ℤ) :
    monomialUnit u Λ (n • a) = monomialUnit u Λ a ^ n := by
  rw [monomialUnit_zpow_eq_map_mul, ha, mul_zero, zpow_zero, map_one, one_mul]

/-- Two quantum-torus algebra maps `χ'` and `χ` agreeing on all generators `monomial (single i 1)`
away from `k` (for forms agreeing off `k`) agree on every monomial `monomial a` with `a k = 0`. -/
theorem algHom_monomial_eq_of_apply_eq_zero {I B : Type*} [Semiring B] [Algebra R B]
    {Λ Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)} {k : I}
    {χ : QuantumTorus R (I →₀ ℤ) u Λ →ₐ[R] B}
    {χ' : QuantumTorus R (I →₀ ℤ) u Λ' →ₐ[R] B}
    (h_off : ∀ i ≠ k, χ' (monomial u Λ' (Finsupp.single i 1)) =
      χ (monomial u Λ (Finsupp.single i 1)))
    (hoff : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    {a : I →₀ ℤ} (ha : a k = 0) :
    χ' (monomial u Λ' a) = χ (monomial u Λ a) := by
  classical
  suffices Units.map χ'.toMonoidHom (monomialUnit u Λ' a) =
      Units.map χ.toMonoidHom (monomialUnit u Λ a) by
    simpa using congrArg (Units.val : Bˣ → B) this
  induction a using Finsupp.induction with
  | zero => ext; simp
  | single_add i n f hif hn ih =>
    have hik : i ≠ k := by rintro rfl; simp [Finsupp.notMem_support_iff.mp hif, hn] at ha
    have hfk : f k = 0 := by simpa [Finsupp.add_apply, Finsupp.single_eq_of_ne hik.symm] using ha
    have hsingle : Units.map χ'.toMonoidHom (monomialUnit u Λ' (Finsupp.single i n)) =
        Units.map χ.toMonoidHom (monomialUnit u Λ (Finsupp.single i n)) := by
      have hpow : Units.map χ'.toMonoidHom (monomialUnit u Λ' (Finsupp.single i 1)) ^ n =
          Units.map χ.toMonoidHom (monomialUnit u Λ (Finsupp.single i 1)) ^ n :=
        congrArg (· ^ n) (Units.ext <| by simpa using h_off i hik)
      rw [map_monomialUnit_zpow, map_monomialUnit_zpow, Finsupp.smul_single_one,
        hoff _ _ (Finsupp.single_eq_of_ne hik.symm) (Finsupp.single_eq_of_ne hik.symm)] at hpow
      exact mul_left_cancel hpow
    have hmul₁ := map_monomialUnit_mul χ' (Finsupp.single i n) f
    rw [hoff _ _ (Finsupp.single_eq_of_ne hik.symm) hfk] at hmul₁
    exact mul_left_cancel
      (hmul₁.symm.trans (by rw [hsingle, ih hfk, map_monomialUnit_mul χ (Finsupp.single i n) f]))

/-- For alternating forms, integer powers of a monomial unit simplify to monomial units. -/
@[simp]
theorem monomialUnit_zpow (hΛ : Λ.IsAlt) (a : L) (n : ℤ) :
    monomialUnit u Λ a ^ n = monomialUnit u Λ (n • a) :=
  (monomialUnit_zsmul_of_self_eq_zero (hΛ.self_eq_zero a) n).symm

/-- For alternating forms, powers of a monomial unit simplify to monomial units. -/
@[simp]
theorem monomialUnit_pow (hΛ : Λ.IsAlt) (a : L) (n : ℕ) :
    monomialUnit u Λ a ^ n = monomialUnit u Λ (n • a) := by
  simpa using monomialUnit_zpow hΛ a n

/-- For alternating forms, powers of a monomial simplify to monomials. -/
@[simp]
theorem monomial_pow (hΛ : Λ.IsAlt) (a : L) (n : ℕ) :
    monomial u Λ a ^ n = monomial u Λ (n • a) := by
  simpa only [Units.val_pow_eq_pow_val, val_monomialUnit] using
    congrArg Units.val (monomialUnit_pow hΛ a n)

/-- Alternation gives the usual quasi-commutation factor `u ^ (2 * Λ(a,b))`. -/
theorem monomial_mul_monomial_eq_smul_mul (hΛ : Λ.IsAlt) (a b : L) :
    monomial u Λ a * monomial u Λ b =
      ((u ^ (2 * Λ a b) : Rˣ) : R) • (monomial u Λ b * monomial u Λ a) := by
  have hexp : 2 * Λ a b + Λ b a = Λ a b := by
    have := hΛ.neg_eq a b
    omega
  rw [monomial_mul_monomial, monomial_mul_monomial, smul_smul, ← Units.val_mul,
    ← zpow_add, hexp, add_comm b a]

/-- When all twist factors are one, the based torus is the ordinary group algebra,
with its normalized monomial basis preserved. In particular this applies at `u = 1`
and for the zero form. -/
noncomputable def untwistedEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (h : ∀ a b, u ^ (Λ a b) = 1) :
    QuantumTorus R L u Λ ≃ₐ[R] AddMonoidAlgebra R L :=
  ((TwistedMonoidAlgebra.equivOfCoboundary
    (1 : Multiplicative L → Multiplicative L → Rˣ) (factorSet u Λ) (fun _ ↦ 1)
    (fun a b ↦ by simp [factorSet, h])).trans
      (TwistedMonoidAlgebra.monoidAlgebraEquiv R (Multiplicative L))).trans
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R L).symm

@[simp]
theorem untwistedEquiv_monomial (h : ∀ a b, u ^ (Λ a b) = 1) (a : L) :
    untwistedEquiv u Λ h (monomial u Λ a) = AddMonoidAlgebra.single a 1 := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R L).injective
  simp [untwistedEquiv, monomial, AddMonoidAlgebra.toMultiplicativeAlgEquiv_single]

@[simp]
theorem untwistedEquiv_symm_single (h : ∀ a b, u ^ (Λ a b) = 1) (a : L) (r : R) :
    (untwistedEquiv u Λ h).symm (AddMonoidAlgebra.single a r) = r • monomial u Λ a := by
  conv_lhs => rw [← mul_one r, ← AddMonoidAlgebra.smul_single']
  rw [map_smul]
  congr 1
  exact (untwistedEquiv u Λ h).symm_apply_eq.mpr (untwistedEquiv_monomial h a).symm

/-- Untwisting preserves the coefficient at each exponent of the normalized monomial basis. -/
@[simp]
theorem coeff_untwistedEquiv (h : ∀ a b, u ^ (Λ a b) = 1)
    (f : QuantumTorus R L u Λ) (a : L) :
    (untwistedEquiv u Λ h f).coeff a = (basis u Λ).repr f a := by
  have he : (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
      (untwistedEquiv u Λ h).toLinearMap = (basis u Λ).repr.toLinearMap := by
    apply (basis u Λ).ext
    intro b
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
      basis_apply, untwistedEquiv_monomial, AddMonoidAlgebra.coeffLinearEquiv_apply,
      AddMonoidAlgebra.coeff_single, basis_repr_monomial]
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
    AddMonoidAlgebra.coeffLinearEquiv_apply] using
      congrArg (fun c : L →₀ R ↦ c a) (LinearMap.congr_fun he f)

end QuantumTorus

end TauCeti
