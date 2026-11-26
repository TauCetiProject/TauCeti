/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.RingTheory.MvPolynomial.Cartier
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.Algebra.Bilinear
import TauCeti.Algebra.MvPolynomial.Division

/-!
# Projection traces for normal-crossing hypersurfaces

On the quotient of a polynomial ring over the prime field by the product of the variables,
the root stage is the regular module with scalars restricted along an iterated Frobenius.
The projection trace retains just the monomials whose root exponents are integral. It
retracts the inclusion of the base stage and is compatible with the finite-stage inclusions.
Multiplication followed by this trace identifies each root stage with its linear dual.

The quotient duality proof lifts the functional's values on residue monomials to polynomials
before applying the complementary-residue formula. It uses the same Cartier calculation as
the polynomial constructions `TauCeti.MvPolynomial.frobeniusTraceDual` and
`MvPolynomial.frobeniusTrace_frobeniusTraceDual_mul`.

## Reference

* B. Zavyalov, *Mod-p Poincaré Duality in p-adic Analytic Geometry*,
  [Definition 4.3.1 and Theorem 4.3.2, Step 2](https://arxiv.org/abs/2111.01830v3).
-/

public section

namespace TauCeti

open _root_.MvPolynomial

/-- The normal-crossing coordinate ring obtained by setting the product of the variables to zero. -/
abbrev MonomialRootAlgebra (R σ : Type*) [CommRing R] [Fintype σ] :=
  MvPolynomial σ R ⧸ Ideal.span {∏ i : σ, (X i : MvPolynomial σ R)}

namespace MonomialRootAlgebra

section Quotient

variable {R σ : Type*} [CommRing R] [Fintype σ]

local notation "P" => MvPolynomial σ R
local notation "A" => MonomialRootAlgebra R σ
local notation "J" => Ideal.span {∏ i : σ, (X i : P)}
local notation "π" => Ideal.Quotient.mk J

/-- The image of a coordinate monomial in the normal-crossing quotient. -/
noncomputable def monomialClass (d : σ →₀ ℕ) (c : R) : A :=
  π (monomial d c)

/-- The monomial class is the image of the polynomial monomial under the quotient map. -/
theorem monomialClass_eq_mk (d : σ →₀ ℕ) (c : R) :
    monomialClass d c = π (monomial d c) :=
  (rfl)

/-- The zero exponent gives the image of the coefficient. -/
@[simp]
theorem monomialClass_zero (c : R) :
    monomialClass (0 : σ →₀ ℕ) c = algebraMap R A c := by
  rw [monomialClass_eq_mk, monomial_zero', IsScalarTower.algebraMap_apply R P A,
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]

/-- Multiplication of coordinate monomial classes adds exponents and multiplies coefficients. -/
@[simp]
theorem monomialClass_mul (d e : σ →₀ ℕ) (c b : R) :
    monomialClass d c * monomialClass e b = monomialClass (d + e) (c * b) := by
  simp only [monomialClass_eq_mk, ← map_mul, monomial_mul_monomial]

/-- A polynomial vanishes in the quotient exactly when every monomial in its support
is divisible by the product of the variables. -/
theorem mk_eq_zero_iff (f : P) : π f = 0 ↔ ∀ d ∈ f.support, ∀ i, 0 < d i := by
  have hprod : (∏ i : σ, X i : P) = monomial (Finsupp.equivFunOnFinite.symm (fun _ ↦ 1)) 1 := by
    simpa using (TauCeti.prod_X_pow_eq_monomial_equivFunOnFinite_symm
      (σ := σ) (R := R) 1)
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hprod, monomial_one_dvd_iff]
  simp [Finsupp.le_def, Nat.succ_le_iff]

/-- The defining relation kills exactly those monomials with zero coefficient or with
positive exponent in every coordinate. -/
@[simp]
theorem monomialClass_eq_zero_iff (d : σ →₀ ℕ) (c : R) :
    monomialClass d c = 0 ↔ c = 0 ∨ ∀ i, 0 < d i := by
  classical
  by_cases hc : c = 0
  · simp [monomialClass_eq_mk, hc]
  · simp [monomialClass_eq_mk, mk_eq_zero_iff, support_monomial, hc]

/-- The product of the coordinate functions vanishes in the hypersurface. -/
@[simp]
theorem prod_mk_X_eq_zero : ∏ i : σ, π (X i) = 0 := by
  rw [← map_prod]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The normal-crossing relation does not kill any nonzero constants. -/
instance {p : ℕ} [CharP R p] [Nonempty σ] : CharP A p := by
  apply CharP.quotient' p
  intro a ha
  have hJ : J ≤ RingHom.ker (constantCoeff : P →+* R) := by
    apply Ideal.span_le.mpr
    rintro f rfl
    apply RingHom.mem_ker.mpr
    rw [map_prod]
    simp
  have h := hJ ha
  rw [RingHom.mem_ker, map_natCast] at h
  simpa using congrArg (C : R → P) h

private noncomputable def projection (q : ℕ) [NeZero q] : A →ₗ[R] A :=
  ((J : Ideal P).restrictScalars R).liftQ
    ((Ideal.Quotient.mkₐ R J).toLinearMap ∘ₗ cartier R q 0)
    (fun _ hf ↦ Ideal.Quotient.eq_zero_iff_mem.2 (cartier_zero_mem_span_prod_X hf))

private theorem projection_mk (q : ℕ) [NeZero q] (f : P) :
    projection q (π f) = π (cartier R q 0 f) := by
  calc
    _ = ((Ideal.Quotient.mkₐ R J).toLinearMap ∘ₗ cartier R q 0) f :=
      Submodule.liftQ_apply _ _ f
    _ = _ := by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]

end Quotient

variable {p : ℕ} {σ : Type*} [Fintype σ]

local notation "P" => MvPolynomial σ (ZMod p)
local notation "A" => MonomialRootAlgebra (ZMod p) σ
local notation "J" => Ideal.span {∏ i : σ, (X i : P)}
local notation "π" => Ideal.Quotient.mk J

section Prime

variable [Nonempty σ] [Fact p.Prime]

/-- The `m`-th root stage, with scalars restricted along the `m`-fold Frobenius. -/
noncomputable def rootModule (m : ℕ) : ModuleCat A :=
  (ModuleCat.restrictScalars (iterateFrobenius A p m)).obj (ModuleCat.of A A)

/-- Regard a class in the hypersurface as an element of the `m`-th root stage. -/
noncomputable def toRoot (m : ℕ) : A ≃+ rootModule (p := p) (σ := σ) m :=
  AddEquiv.refl _

/-- Scalars act by the `p ^ m`-th power on the root stage. -/
@[simp]
theorem smul_toRoot (m : ℕ) (a b : A) :
    a • toRoot m b = toRoot m (a ^ p ^ m * b) := by
  calc
    _ = iterateFrobenius A p m a • b :=
      ModuleCat.restrictScalars.smul_def' _ (M := ModuleCat.of A A) a b
    _ = _ := by rw [iterateFrobenius_def]; rfl

/-- The transition from stage `m` to stage `m + k` applies the `k`-fold Frobenius to the
underlying classes. -/
noncomputable def rootTransition (m k : ℕ) :
    rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) (m + k) where
  toFun x := toRoot (m + k) (iterateFrobenius A p k ((toRoot m).symm x))
  map_add' x y := by simp
  map_smul' a x := by
    obtain ⟨b, rfl⟩ := (toRoot m).surjective x
    simp only [RingHom.id_apply, smul_toRoot, AddEquiv.symm_apply_apply, map_mul,
      iterateFrobenius_def, ← pow_mul, ← pow_add]

/-- On quotient classes the stage transition raises to the `p ^ k`-th power. -/
@[simp]
theorem rootTransition_toRoot (m k : ℕ) (a : A) :
    rootTransition m k (toRoot m a) = toRoot (m + k) (a ^ p ^ k) := by
  simp [rootTransition, iterateFrobenius_def]

/-- The transition with zero increment is the identity. -/
@[simp]
theorem rootTransition_zero (m : ℕ) :
    rootTransition (p := p) (σ := σ) m 0 = LinearMap.id := by
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  exact (rootTransition_toRoot m 0 a).trans (by simp)

private theorem cast_rootModule_apply {m i j : ℕ} (h : i = j)
    (L : rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) i)
    (x : rootModule (p := p) (σ := σ) m) :
    (h ▸ L : _ →ₗ[A] rootModule (p := p) (σ := σ) j) x =
      toRoot j ((toRoot i).symm (L x)) := by
  subst j
  exact (AddEquiv.apply_symm_apply _ _).symm

/-- Successive transitions agree with the transition for the sum of their increments. -/
theorem rootTransition_comp (m k l : ℕ) :
    (rootTransition (p := p) (σ := σ) (m + k) l).comp (rootTransition m k) =
      (Nat.add_assoc m k l).symm ▸ rootTransition m (k + l) := by
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  rw [LinearMap.comp_apply, rootTransition_toRoot, rootTransition_toRoot, cast_rootModule_apply,
    rootTransition_toRoot, AddEquiv.symm_apply_apply, ← pow_mul, ← pow_add]

/-- A linear map out of a root stage is determined by its values on the monomial classes. -/
theorem rootModule_hom_ext {m : ℕ} {M : Type*} [AddCommMonoid M] [Module A M]
    {L K : rootModule (p := p) (σ := σ) m →ₗ[A] M}
    (h : ∀ (d : σ →₀ ℕ) (c : ZMod p), L (toRoot m (monomialClass d c)) =
      K (toRoot m (monomialClass d c))) : L = K := by
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction f using MvPolynomial.induction_on' with
  | monomial d c => simpa only [monomialClass_eq_mk] using h d c
  | add f g hf hg => simp only [map_add, hf, hg]

/-- The root-stage projection onto integral exponents, as a linear map over the base ring. -/
noncomputable def projectionTrace (m : ℕ) : rootModule (p := p) (σ := σ) m →ₗ[A] A :=
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  { toFun := fun x ↦ projection (p ^ m) ((toRoot m).symm x)
    map_add' := fun x y ↦ by rw [map_add, map_add]
    map_smul' := by
      intro a x
      obtain ⟨b, rfl⟩ := (toRoot m).surjective x
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [smul_toRoot, AddEquiv.symm_apply_apply, ← map_pow π, ← expand_prime_pow, ← map_mul]
      simp only [AddEquiv.symm_apply_apply, projection_mk,
        RingHom.id_apply, smul_eq_mul]
      rw [cartier_expand_mul (r := 0) (by simp [Nat.pos_of_neZero]), map_mul] }

/-- On a polynomial representative the projection trace is the zero-offset Cartier operator. -/
theorem projectionTrace_toRoot_mk (m : ℕ) (f : P) :
    have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    projectionTrace m (toRoot m (π f)) = π (cartier (ZMod p) (p ^ m) 0 f) := by
  simp only [projectionTrace, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply,
    projection_mk]

/-- On a monomial, the projection divides all exponents by `p ^ m` if they are divisible,
and otherwise gives zero. The coefficient remains unchanged. -/
@[simp]
theorem projectionTrace_toRoot_monomialClass (m : ℕ) (d : σ →₀ ℕ) (c : ZMod p) :
    projectionTrace m (toRoot m (monomialClass d c)) =
      if ∀ i, p ^ m ∣ d i then monomialClass (d.mapRange (· / p ^ m) (Nat.zero_div _)) c
      else 0 := by
  classical
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [monomialClass_eq_mk, projectionTrace_toRoot_mk]
  let q := p ^ m
  let r := d.mapRange (· % q) (Nat.zero_mod _)
  have hr : ∀ i, r i < q := fun i ↦ by simp [r, Nat.mod_lt, Nat.pos_of_neZero q]
  have hzero : r = 0 ↔ ∀ i, q ∣ d i := by
    simp [r, Finsupp.ext_iff, Nat.dvd_iff_mod_eq_zero]
  conv_lhs => rw [← Finsupp.nsmul_mapRange_div_add_mapRange_mod q d]
  rw [TauCeti.MvPolynomial.cartier_monomial_nsmul_add (r := 0) (s := r)
    (fun _ ↦ Nat.pos_of_neZero q) hr]
  simp only [hzero, q, apply_ite π, map_zero, monomialClass_eq_mk]

/-- The projection trace sends the unit to the unit. -/
@[simp]
theorem projectionTrace_toRoot_one (m : ℕ) :
    projectionTrace m (toRoot m (1 : A)) = 1 := by
  simpa using projectionTrace_toRoot_monomialClass m (0 : σ →₀ ℕ) (1 : ZMod p)

/-- The trace retracts the map from the base ring to the root stage. -/
@[simp]
theorem projectionTrace_toRoot_pow (m : ℕ) (a : A) :
    projectionTrace m (toRoot m (a ^ p ^ m)) = a := by
  rw [← mul_one (a ^ p ^ m), ← smul_toRoot, LinearMap.map_smul, projectionTrace_toRoot_one]
  simp

/-- The projection at the base stage is the identity. -/
@[simp]
theorem projectionTrace_zero_toRoot (a : A) : projectionTrace 0 (toRoot 0 a) = a := by
  simpa only [pow_zero, pow_one] using projectionTrace_toRoot_pow 0 a

/-- Restricting the projection at stage `m + k` along the `k`-fold Frobenius
recovers the stage `m` projection. -/
@[simp]
theorem projectionTrace_add_toRoot_pow (m k : ℕ) (a : A) :
    projectionTrace (m + k) (toRoot (m + k) (a ^ p ^ k)) = projectionTrace m (toRoot m a) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ (m + k)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← map_pow π, ← expand_prime_pow, projectionTrace_toRoot_mk, projectionTrace_toRoot_mk]
  congr 1
  ext d
  simp [pow_add, mul_comm (p ^ m), mul_smul,
    coeff_expand_smul _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

/-- The higher-stage trace composed with the stage transition is the lower-stage trace. -/
@[simp]
theorem projectionTrace_comp_rootTransition (m k : ℕ) :
    (projectionTrace (p := p) (σ := σ) (m + k)).comp (rootTransition m k) = projectionTrace m := by
  apply rootModule_hom_ext
  intro d c
  simp only [LinearMap.comp_apply, rootTransition_toRoot, projectionTrace_add_toRoot_pow]

end Prime

section Pairing

local notation "t" => (∏ i : σ, (X i : P))

variable (q : ℕ) [NeZero q]

local notation "topExp[" q "]" => (Finsupp.equivFunOnFinite.symm (fun _ : σ ↦ q - 1))
local notation "resExp[" q "]" => (fun β : σ →₀ Fin q ↦ β.mapRange Fin.val (Fin.val_zero q))

private theorem pow_prod_X_dvd_of_cartier_top_mul (f : P)
    (hf : ∀ g : P, π (cartier (ZMod p) q topExp[q] (f * g)) = 0) : t ^ q ∣ f := by
  have ht : expand q t = t ^ q := by simp [map_prod, Finset.prod_pow]
  have h := mem_map_expand_of_forall_cartier_mul_mem (n := q) f J
    (fun g ↦ Ideal.Quotient.eq_zero_iff_mem.mp (hf g))
  rwa [Ideal.map_span, Set.image_singleton, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ht,
    Ideal.mem_span_singleton] at h

omit [NeZero q] in
private theorem pow_prod_X_dvd_pow_mul_iff {k : ℕ} (hk : k ≤ q) (f : P) [Fact p.Prime] :
    t ^ q ∣ t ^ k * f ↔ t ^ (q - k) ∣ f := by
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_ne_zero i
  conv_lhs => rw [← Nat.add_sub_of_le hk, pow_add]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ ht)

variable [Nonempty σ] [Fact p.Prime]

/-- Multiplication followed by the root-stage projection trace, as a bilinear pairing. -/
noncomputable def projectionPairing (m : ℕ) :
    rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) m →ₗ[A] A := by
  have mul : rootModule (p := p) (σ := σ) m →ₗ[A]
      rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) m := by
    let alg := (iterateFrobenius A p m).toAlgebra
    exact @LinearMap.mul A A _ _ alg.toModule
      (@Algebra.to_smulCommClass A A _ _ alg) (@IsScalarTower.right A A _ _ alg)
  exact mul.compr₂ₛₗ (projectionTrace m)

/-- The value of the pairing on the underlying quotient classes. -/
@[simp]
theorem projectionPairing_toRoot (m : ℕ) (a b : A) :
    projectionPairing m (toRoot m a) (toRoot m b) = projectionTrace m (toRoot m (a * b)) := by
  rfl

private theorem exists_cartier_top_representer (m : ℕ)
    (φ : rootModule (p := p) (σ := σ) m →ₗ[A] A) :
    have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    ∃ f : P, ∀ g : P,
      π (cartier (ZMod p) (p ^ m) (Finsupp.equivFunOnFinite.symm (fun _ : σ ↦ p ^ m - 1))
        (f * g)) = φ (toRoot m (π g)) := by
  classical
  let q := p ^ m
  have hq : NeZero q := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  choose a ha using fun β : σ →₀ Fin q ↦
    Ideal.Quotient.mk_surjective (φ (toRoot m (π (monomial (resExp[q] β) 1))))
  refine ⟨TauCeti.MvPolynomial.cartierDual q a, fun g ↦ ?_⟩
  rw [cartier_cartierDual_mul]
  conv_rhs => rw [← sum_monomial_mul_expand_cartier (n := q) g]
  simp only [map_sum, map_mul, ha]
  apply Finset.sum_congr rfl
  intro β _
  conv_rhs => rw [expand_prime_pow, map_pow, mul_comm, ← smul_toRoot,
    LinearMap.map_smul, smul_eq_mul]

private theorem projectionPairing_toRoot_mk (m : ℕ) (f g : P) :
    have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    projectionPairing m (toRoot m (π f)) (toRoot m (π g)) =
      π (cartier (ZMod p) (p ^ m) topExp[p ^ m] (t ^ (p ^ m - 1) * (f * g))) := by
  let := (⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩ : NeZero (p ^ m))
  calc
    _ = π (cartier (ZMod p) (p ^ m) 0 (f * g)) := by
      rw [projectionPairing_toRoot, ← map_mul, projectionTrace_toRoot_mk]
    _ = _ := congrArg π (cartier_prod_X_pow_mul (n := p ^ m) (f * g)).symm

private theorem projectionPairing_injective (m : ℕ) :
    Function.Injective (projectionPairing (p := p) (σ := σ) m) := by
  apply (injective_iff_map_eq_zero (projectionPairing (p := p) (σ := σ) m)).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  let q := p ^ m
  have : NeZero q := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h : t ^ q ∣ t ^ (q - 1) * f := by
    apply pow_prod_X_dvd_of_cartier_top_mul q
    intro g
    have hg := DFunLike.congr_fun hx (toRoot m (π g))
    simpa only [projectionPairing_toRoot_mk, LinearMap.zero_apply, mul_assoc] using hg
  rw [pow_prod_X_dvd_pow_mul_iff q (Nat.sub_le q 1),
    Nat.sub_sub_self (Nat.pos_of_neZero q), pow_one] at h
  exact (toRoot m).map_eq_zero_iff.mpr
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h))

private theorem projectionPairing_surjective (m : ℕ) :
    Function.Surjective (projectionPairing (p := p) (σ := σ) m) := by
  intro φ
  let q := p ^ m
  have : NeZero q := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := exists_cartier_top_representer m φ
  -- The functional kills the hypersurface relation, so its representative lies in (t ^ (q - 1)).
  have hz : t ^ q ∣ t * f := by
    apply pow_prod_X_dvd_of_cartier_top_mul q
    intro g
    rw [mul_right_comm t f g, mul_comm (t * g), hf, map_mul]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))]
  have hz := (pow_prod_X_dvd_pow_mul_iff q (Nat.pos_of_neZero q) f).mp (by simpa using hz)
  obtain ⟨f', rfl⟩ := hz
  refine ⟨toRoot m (π f'), ?_⟩
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [projectionPairing_toRoot_mk, ← hf, mul_assoc]

/-- The pairing obtained by multiplying the underlying quotient classes and applying the
projection trace is perfect on every finite root stage. -/
instance (m : ℕ) : (projectionPairing (p := p) (σ := σ) m).IsPerfPair where
  bijective_left := ⟨projectionPairing_injective m, projectionPairing_surjective m⟩
  bijective_right := by
    have h : (projectionPairing (p := p) (σ := σ) m).flip = projectionPairing m := by
      ext x y
      obtain ⟨a, rfl⟩ := (toRoot m).surjective x
      obtain ⟨b, rfl⟩ := (toRoot m).surjective y
      simp [mul_comm]
    rw [h]
    exact ⟨projectionPairing_injective m, projectionPairing_surjective m⟩

end Pairing
end MonomialRootAlgebra
end TauCeti
