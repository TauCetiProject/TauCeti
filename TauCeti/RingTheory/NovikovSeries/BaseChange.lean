/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Map
public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Vector-valued Novikov series as a module over the Novikov ring

Let `H` be an additive monoid with a period homomorphism `N : H →+ ℝ`, and let `V` be a module over
a semiring `R`. A Novikov series with coefficients in `V` is a function `A ↦ v_A` from `H` to `V`
with only finitely many nonzero values below every period cutoff. For the second homology
`H = H₂(X; ℤ)` of a closed symplectic manifold with its area homomorphism, and `V = H^*(X; ℚ)`,
these series form the completed state module `V ⊗̂ Λ_ω` of Gromov–Witten theory, and the Novikov
ring `Λ_ω = NovikovSeries ℚ H₂(X; ℤ) ω` is its ring of coefficients.

This file makes the Novikov ring act on vector-valued series by convolution along scalar
multiplication,

`(a • v)_h = ∑_(u + u' = h) a_u • v_(u')`,

a finite sum (`TauCeti.NovikovSeries.module`). The module laws are the associativity and
biadditivity of convolution (`TauCeti.NovikovSeries.convolution_assoc`). For `V = R` this is
the multiplication of the Novikov ring, so the structure is a definition, to be installed with
`letI := NovikovSeries.module R V N`, rather than a second instance of `Module` for the Novikov
ring over itself. It is compatible with the coefficientwise action of `R`: a constant series
`single 0 r` acts as `r` (`TauCeti.NovikovSeries.single_zero_smul`).

* **Finite bases.** A basis `b` of `V` indexed by a finite type identifies series with
  coefficients in `V` with families of scalar series (`TauCeti.NovikovSeries.basisCoords`), and this
  identification is linear over the Novikov ring (`TauCeti.NovikovSeries.basisCoords_smul`). So the
  monomials `single 0 (b i)` form a basis of the series with coefficients in `V` over the Novikov
  ring (`TauCeti.NovikovSeries.basis`, `TauCeti.NovikovSeries.basis_apply`); in particular, for `V`
  finite and free over `R`, these series form a finite free module over the Novikov ring
  (`TauCeti.NovikovSeries.module_free`, `TauCeti.NovikovSeries.module_finite`).
* **Comparison with the tensor product.** For a commutative semiring `R`, the canonical map
  `Λ ⊗[R] V → NovikovSeries V H N`, `a ⊗ x ↦ (A ↦ a_A • x)`, with `Λ = NovikovSeries R H N`
  (`TauCeti.NovikovSeries.ofTensorProduct`), is `Λ`-linear and sends the basis
  `1 ⊗ b i` of `Λ ⊗[R] V` induced by `b` (Mathlib's `Algebra.TensorProduct.basis`) to the basis
  `single 0 (b i)` (`TauCeti.NovikovSeries.ofTensorProduct_basis`). Hence it is an isomorphism
  when `V` is finite and free over `R` (`TauCeti.NovikovSeries.ofTensorProductEquiv`). This is a
  statement about finite free modules, not a completed base change theorem. The construction and
  the reduction of surjectivity to `R^n` follow Mathlib's comparison map
  `AdicCompletion.ofTensorProduct` for adic completions; `TauCeti.HahnModule.tensorProductEquiv`
  is the analogue for module-valued Hahn series.

For a basis `b` of the rational cohomology of a closed symplectic manifold, the basis coordinates
`κ_b` of `TauCeti.RingTheory.NovikovModule.BasisCoordinates` are linear for this action and the
transported Novikov module structure (`TauCeti.NovikovSeries.basisCoordinates_smul`), so the
Novikov module structure transported along `κ_b` is the one constructed here, for every `b`.

## Main definitions

* `TauCeti.NovikovSeries.module R V N`: Novikov series act on Novikov series with coefficients in
  `V` by convolution.
* `TauCeti.NovikovSeries.basisCoordsLinearEquiv b`, `TauCeti.NovikovSeries.basis b`: the basis
  coordinates as a linear equivalence over the Novikov ring, and the basis of monomials
  `single 0 (b i)`.
* `TauCeti.NovikovSeries.ofTensorProduct`: the canonical map `Λ ⊗[R] V → NovikovSeries V H N`.
* `TauCeti.NovikovSeries.ofTensorProductEquiv`: the canonical map as a linear equivalence over the
  Novikov ring, for `V` finite and free over `R`.

## Main results

* `TauCeti.NovikovSeries.single_smul_single`, `TauCeti.NovikovSeries.single_zero_smul`: monomials
  act by adding exponents, and constant series act through the coefficients.
* `TauCeti.NovikovSeries.isScalarTower_module`, `TauCeti.NovikovSeries.smulCommClass_module`: the
  action is compatible with the coefficientwise action of `R`.
* `TauCeti.NovikovSeries.ofTensorProduct_bijective_of_basis`,
  `TauCeti.NovikovSeries.ofTensorProduct_bijective`: the canonical map from the tensor product is
  bijective for a module with a finite basis, and so for a finite free module.
* `TauCeti.NovikovSeries.ofTensorProduct_surjective`: the canonical map from the tensor product is
  onto for a finite module, so the series with coefficients in a finite module form a finite
  module over the Novikov ring (`TauCeti.NovikovSeries.module_finite`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 11.1 (quantum cohomology with Novikov
  coefficients).
-/

public section

noncomputable section

open Finset Function TensorProduct

namespace TauCeti

namespace NovikovSeries

section Module

variable {R H V : Type*} [AddMonoid H] [Semiring R] [AddCommMonoid V] [Module R V]

variable (R V) in
/-- **Novikov series act on vector-valued Novikov series** by convolution along scalar
multiplication: the coefficient of `a • v` at `h` is the finite sum of `a_u • v_(u')` over the pairs
of support exponents with `u + u' = h`. For `V = R` this is the multiplication of the Novikov ring,
so this module structure is a definition rather than an instance; install it with
`letI := NovikovSeries.module R V N`. -/
@[instance_reducible]
def module (N : H →+ ℝ) : Module (NovikovSeries R H N) (NovikovSeries V H N) where
  smul := convolution (smulAddHom R V)
  one_smul v := by
    ext h
    exact (coeff_convolution_single_zero_left _ 1 v h).trans (one_smul R _)
  mul_smul := convolution_assoc _ _ _ _ fun x y z => mul_smul x y z
  smul_zero := convolution_zero _
  smul_add := convolution_add_right _
  add_smul := convolution_add_left _
  zero_smul := zero_convolution _

variable {N : H →+ ℝ}

/-- The action of the Novikov ring is convolution along scalar multiplication. -/
theorem smul_eq_convolution (a : NovikovSeries R H N) (v : NovikovSeries V H N) :
    letI := module R V N
    a • v = convolution (smulAddHom R V) a v :=
  (rfl)

/-- A coefficient of `a • v` is the sum of `a_u • v_(u')` over any finite set of pairs `(u, u')`
with `u + u' = h` containing every such pair of support exponents. -/
theorem coeff_smul_eq_sum {a : NovikovSeries R H N} {v : NovikovSeries V H N} {h : H}
    {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hav : ∀ u u', u + u' = h → a.coeff u ≠ 0 → v.coeff u' ≠ 0 → (u, u') ∈ s) :
    letI := module R V N
    (a • v).coeff h = ∑ p ∈ s, a.coeff p.1 • v.coeff p.2 :=
  coeff_convolution_eq_sum hs hav

/-- Monomials act by adding exponents: `(r e^g) • (x e^g') = (r • x) e^(g + g')`. -/
@[simp]
theorem single_smul_single (g g' : H) (r : R) (x : V) :
    letI := module R V N
    (single g r : NovikovSeries R H N) • (single g' x : NovikovSeries V H N) =
      single (g + g') (r • x) :=
  convolution_single_single _ g g' r x

/-- A constant series `single 0 r` acts as the scalar `r` on each coefficient. -/
@[simp]
theorem single_zero_smul (r : R) (v : NovikovSeries V H N) :
    letI := module R V N
    (single 0 r : NovikovSeries R H N) • v = r • v := by
  ext h
  exact coeff_convolution_single_zero_left _ r v h

/-- A series acting on a constant series `single 0 x` multiplies `x` by each coefficient. -/
@[simp]
theorem coeff_smul_single_zero (a : NovikovSeries R H N) (x : V) (h : H) :
    letI := module R V N
    (a • (single 0 x : NovikovSeries V H N)).coeff h = a.coeff h • x :=
  coeff_convolution_single_zero_right _ a x h

/-- The action of the Novikov ring extends the coefficientwise action of `R`:
`(r • a) • v = r • (a • v)`. -/
theorem isScalarTower_module :
    letI := module R V N
    IsScalarTower R (NovikovSeries R H N) (NovikovSeries V H N) := by
  let := module R V N
  refine ⟨fun r a v => ?_⟩
  rw [← single_zero_mul_eq_smul, mul_smul, single_zero_smul]

end Module

section Basis

variable {R H V ι : Type*} [AddMonoid H] {N : H →+ ℝ} [Semiring R] [AddCommMonoid V] [Module R V]
  [Finite ι] (b : Module.Basis ι R V)

/-- **The basis coordinates are linear over the Novikov ring**: the coordinate series of `a • v`
are the products of `a` with the coordinate series of `v`. -/
theorem basisCoords_smul (a : NovikovSeries R H N) (v : NovikovSeries V H N) :
    letI := module R V N
    basisCoords b (a • v) = a • basisCoords b v := by
  ext i h
  set s := (finite_setOf_add_eq a v h).toFinset
  have hs (p : H × H) : p ∈ s ↔ p.1 + p.2 = h ∧ a.coeff p.1 ≠ 0 ∧ v.coeff p.2 ≠ 0 :=
    Set.Finite.mem_toFinset _
  rw [coeff_basisCoords, coeff_smul_eq_sum (s := s) (fun p hp => ((hs p).1 hp).1)
    fun u w huw hu hw => (hs _).2 ⟨huw, hu, hw⟩, Pi.smul_apply, smul_eq_mul,
    coeff_mul_eq_sum (s := s) (fun p hp => ((hs p).1 hp).1) fun u w huw hu hw => (hs _).2
      ⟨huw, hu, fun hv => hw (by rw [coeff_basisCoords, hv, map_zero, Finsupp.zero_apply])⟩,
    map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_basisCoords]

/-- The basis coordinates of a vector-valued Novikov series, as a linear equivalence over the
Novikov ring with families of scalar Novikov series. -/
def basisCoordsLinearEquiv :
    letI := module R V N
    NovikovSeries V H N ≃ₗ[NovikovSeries R H N] (ι → NovikovSeries R H N) :=
  letI := module R V N
  { basisCoords b with map_smul' := basisCoords_smul b }

/-- The linear equivalence over the Novikov ring is the family of coordinate series. -/
@[simp]
theorem basisCoordsLinearEquiv_apply (v : NovikovSeries V H N) :
    basisCoordsLinearEquiv b v = basisCoords b v :=
  (rfl)

/-- The inverse linear equivalence over the Novikov ring is the inverse of the coordinates. -/
@[simp]
theorem basisCoordsLinearEquiv_symm_apply (v : ι → NovikovSeries R H N) :
    (basisCoordsLinearEquiv (N := N) b).symm v = (basisCoords b).symm v :=
  (rfl)

/-- The basis of the Novikov series with coefficients in `V` over the Novikov ring induced by a
finite basis `b` of `V`: its vectors are the constant series `single 0 (b i)`
(`TauCeti.NovikovSeries.basis_apply`). -/
def basis :
    letI := module R V N
    Module.Basis ι (NovikovSeries R H N) (NovikovSeries V H N) :=
  letI := module R V N
  Module.Basis.ofEquivFun (basisCoordsLinearEquiv b)

/-- The coordinates in the basis of constant series are the coordinate series of `b`. -/
@[simp]
theorem basis_repr_apply (v : NovikovSeries V H N) (i : ι) :
    letI := module R V N
    (basis (N := N) b).repr v i = basisCoords b v i := by
  simp [basis]

/-- The basis vectors are the constant series `single 0 (b i)`. -/
@[simp]
theorem basis_apply (i : ι) :
    letI := module R V N
    basis (N := N) b i = single 0 (b i) := by
  classical
  let := module R V N
  have := Fintype.ofFinite ι
  simp only [basis, Module.Basis.coe_ofEquivFun, basisCoordsLinearEquiv_symm_apply]
  ext h
  rw [coeff_basisCoords_symm, Finset.sum_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, coeff_zero, zero_smul]) (by simp), Pi.single_eq_same]
  obtain rfl | hh := eq_or_ne h 0
  · rw [one_def, coeff_single_same, coeff_single_same, one_smul]
  · rw [one_def, coeff_single_of_ne hh, coeff_single_of_ne hh, zero_smul]

/-- **Novikov series with coefficients in a finite free module form a free module over the Novikov
ring**, with the basis `TauCeti.NovikovSeries.basis` of constant series. -/
theorem module_free [Module.Free R V] [Module.Finite R V] :
    letI := module R V N
    Module.Free (NovikovSeries R H N) (NovikovSeries V H N) :=
  letI := module R V N
  Module.Free.of_basis (basis (Module.Free.chooseBasis R V))

end Basis

section TensorProduct

variable {R H V : Type*} [AddMonoid H] {N : H →+ ℝ} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- Over a commutative semiring, the coefficientwise action of `R` commutes with the action of the
Novikov ring. -/
theorem smulCommClass_module :
    letI := module R V N
    SMulCommClass R (NovikovSeries R H N) (NovikovSeries V H N) := by
  let := module R V N
  refine ⟨fun r a v => ?_⟩
  rw [← single_zero_smul, ← single_zero_smul, ← mul_smul, ← mul_smul, ← algebraMap_self_apply,
    Algebra.commutes]

variable (N) in
/-- **The canonical map from the tensor product.** The `Λ`-linear map
`Λ ⊗[R] V → NovikovSeries V H N`, for the Novikov ring `Λ = NovikovSeries R H N`, sending
`a ⊗ x` to the series `A ↦ a_A • x`. It is an isomorphism when `V` is finite and free over `R`
(`TauCeti.NovikovSeries.ofTensorProductEquiv`). -/
def ofTensorProduct :
    letI := module R V N
    NovikovSeries R H N ⊗[R] V →ₗ[NovikovSeries R H N] NovikovSeries V H N :=
  letI := module R V N
  haveI := isScalarTower_module (R := R) (V := V) (N := N)
  haveI := smulCommClass_module (R := R) (V := V) (N := N)
  AlgebraTensorModule.lift
    { toFun a :=
        { toFun x := a • single 0 x
          map_add' x y := by rw [single_add, smul_add]
          map_smul' r x := by rw [RingHom.id_apply, ← smul_single, smul_comm] }
      map_add' a a' := LinearMap.ext fun x => add_smul a a' _
      map_smul' a a' := LinearMap.ext fun x => mul_smul a a' _ }

/-- The canonical map sends `a ⊗ x` to `a • single 0 x`. -/
@[simp]
theorem ofTensorProduct_tmul (a : NovikovSeries R H N) (x : V) :
    letI := module R V N
    ofTensorProduct N (a ⊗ₜ x) = a • (single 0 x : NovikovSeries V H N) :=
  (rfl)

/-- The canonical map sends `a ⊗ x` to the series with coefficients `a_A • x`. -/
theorem coeff_ofTensorProduct_tmul (a : NovikovSeries R H N) (x : V) (h : H) :
    (ofTensorProduct N (a ⊗ₜ x)).coeff h = a.coeff h • x := by
  rw [ofTensorProduct_tmul, coeff_smul_single_zero]

variable {ι : Type*} [Finite ι]

/-- The canonical map sends the basis `1 ⊗ b i` of `Λ ⊗[R] V` induced by `b` to the basis
`single 0 (b i)` of the Novikov series with coefficients in `V`. -/
theorem ofTensorProduct_basis (b : Module.Basis ι R V) (i : ι) :
    ofTensorProduct N (Algebra.TensorProduct.basis (NovikovSeries R H N) b i) = basis b i := by
  let := module R V N
  rw [Algebra.TensorProduct.basis_apply, ofTensorProduct_tmul, one_smul, basis_apply]

/-- The canonical map is the isomorphism matching the basis of `Λ ⊗[R] V` induced by `b` with the
basis of constant series `single 0 (b i)`. -/
theorem ofTensorProduct_eq_basis_equiv (b : Module.Basis ι R V) :
    letI := module R V N
    ofTensorProduct N =
      ((Algebra.TensorProduct.basis (NovikovSeries R H N) b).equiv (basis b)
        (Equiv.refl ι)).toLinearMap := by
  let := module R V N
  refine (Algebra.TensorProduct.basis (NovikovSeries R H N) b).ext fun i => ?_
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, ofTensorProduct_basis]

/-- **The canonical map from the tensor product is bijective for a module with a finite basis.** -/
theorem ofTensorProduct_bijective_of_basis (b : Module.Basis ι R V) :
    Bijective (ofTensorProduct (R := R) (V := V) N) := by
  let := module R V N
  rw [ofTensorProduct_eq_basis_equiv b]
  exact LinearEquiv.bijective _

/-- Applying a linear map `f` coefficientwise commutes with the canonical maps from the tensor
products: it corresponds to `1 ⊗ f`. -/
theorem map_ofTensorProduct {W : Type*} [AddCommMonoid W] [Module R W] (f : V →ₗ[R] W)
    (t : NovikovSeries R H N ⊗[R] V) :
    map f.toAddMonoidHom (AddMonoidHom.id H) exists_period_rescale_id (ofTensorProduct N t) =
      ofTensorProduct N (f.lTensor (NovikovSeries R H N) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    ext h
    rw [coeff_map_id_right, LinearMap.lTensor_tmul, coeff_ofTensorProduct_tmul,
      coeff_ofTensorProduct_tmul, LinearMap.toAddMonoidHom_coe, map_smul]
  | add t t' ht ht' => rw [map_add, map_add, map_add, map_add, ht, ht']

/-- **The canonical map from the tensor product is onto for a finite module.** A finite module is a
quotient of some `R^n`, and Novikov series with coefficients in a quotient lift coefficientwise. -/
theorem ofTensorProduct_surjective [Module.Finite R V] :
    Surjective (ofTensorProduct (R := R) (V := V) N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R V
  intro x
  obtain ⟨y, rfl⟩ := map_surjective f.toAddMonoidHom (AddMonoidHom.id H) exists_period_rescale_id
    hf (fun h => ⟨h, rfl⟩) x
  obtain ⟨t, rfl⟩ := (ofTensorProduct_bijective_of_basis (N := N) (Pi.basisFun R (Fin n))).2 y
  exact ⟨_, (map_ofTensorProduct f t).symm⟩

/-- **Novikov series with coefficients in a finite module form a finite module over the Novikov
ring.** -/
theorem module_finite [Module.Finite R V] :
    letI := module R V N
    Module.Finite (NovikovSeries R H N) (NovikovSeries V H N) :=
  letI := module R V N
  Module.Finite.of_surjective (ofTensorProduct N) ofTensorProduct_surjective

/-- **The canonical map from the tensor product is bijective for a finite free module.** -/
theorem ofTensorProduct_bijective [Module.Free R V] [Module.Finite R V] :
    Bijective (ofTensorProduct (R := R) (V := V) N) :=
  ofTensorProduct_bijective_of_basis (Module.Free.chooseBasis R V)

variable (R V N) in
/-- **The completed state module of a finite free module is its base change to the Novikov ring.**
For `V` finite and free over `R`, the canonical map `Λ ⊗[R] V → NovikovSeries V H N`,
`a ⊗ x ↦ (A ↦ a_A • x)`, as a linear equivalence over the Novikov ring `Λ`. -/
def ofTensorProductEquiv [Module.Free R V] [Module.Finite R V] :
    letI := module R V N
    NovikovSeries R H N ⊗[R] V ≃ₗ[NovikovSeries R H N] NovikovSeries V H N :=
  letI := module R V N
  LinearEquiv.ofBijective (ofTensorProduct N) ofTensorProduct_bijective

/-- The linear equivalence is the canonical map. -/
@[simp]
theorem ofTensorProductEquiv_apply [Module.Free R V] [Module.Finite R V]
    (x : NovikovSeries R H N ⊗[R] V) :
    ofTensorProductEquiv R V N x = ofTensorProduct N x :=
  (rfl)

/-- The inverse of the linear equivalence sends a constant series `single 0 x` to `1 ⊗ x`. -/
@[simp]
theorem ofTensorProductEquiv_symm_single_zero [Module.Free R V] [Module.Finite R V] (x : V) :
    (ofTensorProductEquiv R V N).symm (single 0 x) = 1 ⊗ₜ x := by
  let := module R V N
  rw [LinearEquiv.symm_apply_eq, ofTensorProductEquiv_apply, ofTensorProduct_tmul, one_smul]

end TensorProduct

end NovikovSeries

end TauCeti
