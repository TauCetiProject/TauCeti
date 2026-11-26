/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.RingTheory.MvPolynomial.Cartier
import Mathlib.Algebra.CharP.Quotient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Expand
import TauCeti.Algebra.MvPolynomial.Division

/-!
# Projection traces for normal-crossing hypersurfaces

On the quotient of a polynomial ring over the prime field by the product of the variables,
the root stage is the regular module with scalars restricted along an iterated Frobenius.
The projection trace retains just the monomials whose root exponents are integral. It
retracts the inclusion of the base stage and is compatible with the finite-stage inclusions.
Multiplication followed by this trace identifies each root stage with its linear dual.

The duality calculation uses complementary residues in the existing polynomial Cartier
decomposition, with the hypersurface relation imposed on the Cartier coefficients.

## Reference

* B. Zavyalov, *Mod-p Poincaré Duality in p-adic Analytic Geometry*,
  [Definition 4.3.1 and Theorem 4.3.2, Step 2](https://arxiv.org/abs/2111.01830v3).
-/

public section

namespace TauCeti

open _root_.MvPolynomial

/-- The normal-crossing coordinate ring obtained by setting the product of the variables to zero. -/
abbrev MonomialRootAlgebra (p : ℕ) (σ : Type*) [Fintype σ] :=
  MvPolynomial σ (ZMod p) ⧸ Ideal.span {∏ i : σ, (X i : MvPolynomial σ (ZMod p))}

namespace MonomialRootAlgebra

variable {p : ℕ} {σ : Type*} [Fintype σ]

local notation "P" => MvPolynomial σ (ZMod p)
local notation "A" => MonomialRootAlgebra p σ
local notation "J" => Ideal.span {∏ i : σ, (X i : P)}
local notation "π" => Ideal.Quotient.mk J

/-- The image of a coordinate monomial in the normal-crossing quotient. -/
noncomputable def monomialClass (d : σ →₀ ℕ) (c : ZMod p) : A :=
  π (monomial d c)

/-- The monomial class is the image of the polynomial monomial under the quotient map. -/
theorem monomialClass_eq_mk (d : σ →₀ ℕ) (c : ZMod p) :
    monomialClass d c = π (monomial d c) :=
  (rfl)

/-- The zero exponent gives the image of the coefficient. -/
@[simp]
theorem monomialClass_zero (c : ZMod p) :
    monomialClass (0 : σ →₀ ℕ) c = algebraMap (ZMod p) A c := by
  rw [monomialClass_eq_mk, monomial_zero', IsScalarTower.algebraMap_apply (ZMod p) P A,
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]

/-- Multiplication of coordinate monomial classes adds exponents and multiplies coefficients. -/
@[simp]
theorem monomialClass_mul (d e : σ →₀ ℕ) (c b : ZMod p) :
    monomialClass d c * monomialClass e b = monomialClass (d + e) (c * b) := by
  simp only [monomialClass_eq_mk, ← map_mul, monomial_mul_monomial]

/-- A polynomial vanishes in the quotient exactly when every monomial in its support
is divisible by the product of the variables. -/
theorem mk_eq_zero_iff (f : P) : π f = 0 ↔ ∀ d ∈ f.support, ∀ i, 0 < d i := by
  have hprod : (∏ i : σ, X i : P) = monomial (Finsupp.equivFunOnFinite.symm (fun _ ↦ 1)) 1 := by
    simpa using (TauCeti.prod_X_pow_eq_monomial_equivFunOnFinite_symm
      (σ := σ) (R := ZMod p) 1)
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hprod, monomial_one_dvd_iff]
  simp [Finsupp.le_def, Nat.succ_le_iff]

/-- The defining relation kills exactly those monomials with zero coefficient or with
positive exponent in every coordinate. -/
@[simp]
theorem monomialClass_eq_zero_iff (d : σ →₀ ℕ) (c : ZMod p) :
    monomialClass d c = 0 ↔ c = 0 ∨ ∀ i, 0 < d i := by
  classical
  by_cases hc : c = 0
  · simp [monomialClass_eq_mk, hc]
  · simp [monomialClass_eq_mk, mk_eq_zero_iff, support_monomial, hc]

/-- The product of the coordinate functions vanishes in the hypersurface. -/
@[simp]
theorem prod_mk_X : ∏ i : σ, π (X i) = 0 := by
  rw [← map_prod]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The normal-crossing relation does not kill any nonzero constants. -/
instance [Nonempty σ] : CharP A p := by
  apply CharP.quotient' p
  intro a ha
  have hJ : J ≤ RingHom.ker (constantCoeff : P →+* ZMod p) := by
    apply Ideal.span_le.mpr
    rintro f rfl
    apply RingHom.mem_ker.mpr
    rw [map_prod]
    simp
  have h := hJ ha
  rw [RingHom.mem_ker, map_natCast] at h
  simpa using congrArg (C : ZMod p → P) h

private theorem cartier_mem (q : ℕ) [NeZero q] {f : P} (hf : f ∈ J) :
    cartier (ZMod p) q 0 f ∈ J := by
  simp only [← Ideal.Quotient.eq_zero_iff_mem, mk_eq_zero_iff] at hf ⊢
  intro d hd i
  have hqd : q • d ∈ f.support := by
    simpa [MvPolynomial.mem_support_iff] using hd
  have hi := hf (q • d) hqd i
  exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hi

private noncomputable def projection (q : ℕ) [NeZero q] : A →ₗ[ZMod p] A :=
  ((J : Ideal P).restrictScalars (ZMod p)).liftQ
    ((Ideal.Quotient.mkₐ (ZMod p) J).toLinearMap ∘ₗ cartier (ZMod p) q 0)
    (fun _ hf ↦ Ideal.Quotient.eq_zero_iff_mem.2 (cartier_mem q hf))

private theorem projection_mk (q : ℕ) [NeZero q] (f : P) :
    projection q (π f) = π (cartier (ZMod p) q 0 f) :=
  (rfl)

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
    a • toRoot m b = toRoot m (a ^ p ^ m * b) :=
  (rfl)

omit [Nonempty σ] in
/-- Substituting the `p ^ m`-th powers of the coordinates induces the `m`-fold Frobenius. -/
theorem mk_expand_prime_pow (m : ℕ) (f : P) :
    π (expand (p ^ m) f) = (π f) ^ p ^ m := by
  have h : iterateFrobenius (ZMod p) p m = RingHom.id _ :=
    RingHom.ext fun c ↦ ZMod.pow_card_pow c
  have hf := congrArg π (map_iterateFrobenius_expand p f m)
  simpa only [h, map_id, RingHom.id_apply, map_pow] using hf

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
      rw [smul_toRoot, AddEquiv.symm_apply_apply, ← mk_expand_prime_pow, ← map_mul]
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
  split_ifs with h
  · let e := d.mapRange (· / p ^ m) (Nat.zero_div _)
    have he : p ^ m • e + 0 = d := by
      ext i
      simpa [e] using Nat.mul_div_cancel' (h i)
    simpa only [monomialClass, he] using
      congrArg π (TauCeti.MvPolynomial.cartier_monomial_nsmul_add_self
        (n := p ^ m) (r := 0) e c)
  · suffices cartier (ZMod p) (p ^ m) 0 (monomial d c) = 0 by rw [this, map_zero]
    ext e
    have hne : d ≠ p ^ m • e := by
      rintro rfl
      exact h fun i ↦ by simp
    simp [coeff_monomial, hne]

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
theorem projectionTrace_toRoot_pow_add (m k : ℕ) (a : A) :
    projectionTrace (m + k) (toRoot (m + k) (a ^ p ^ k)) = projectionTrace m (toRoot m a) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : NeZero (p ^ (m + k)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← mk_expand_prime_pow, projectionTrace_toRoot_mk, projectionTrace_toRoot_mk]
  congr 1
  ext d
  simp [pow_add, mul_comm (p ^ m), mul_smul,
    coeff_expand_smul _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

end Prime

section Pairing

local notation "t" => (∏ i : σ, (X i : P))

variable (q : ℕ) [NeZero q]

local notation "topExp[" q "]" => (Finsupp.equivFunOnFinite.symm (fun _ : σ ↦ q - 1))
local notation "resExp[" q "]" => (fun β : σ →₀ Fin q ↦ β.mapRange Fin.val (Fin.val_zero q))

private theorem mk_cartier_top_mul_complement (β : σ →₀ Fin q) (f : P) :
    π (cartier (ZMod p) q topExp[q] (monomial (topExp[q] - resExp[q] β) 1 * f)) =
      π (cartier (ZMod p) q (resExp[q] β) f) := by
  congr 1
  ext d
  have hβ : resExp[q] β ≤ topExp[q] := fun i ↦ by
    simpa using Nat.le_sub_one_of_lt (β i).isLt
  have hd : q • d + topExp[q] = (topExp[q] - resExp[q] β) + (q • d + resExp[q] β) := by
    calc
      _ = q • d + ((topExp[q] - resExp[q] β) + resExp[q] β) :=
        congrArg (q • d + ·) (tsub_add_cancel_of_le hβ).symm
      _ = _ := by ac_rfl
  rw [coeff_cartier, coeff_cartier, hd, coeff_monomial_mul, one_mul]

private theorem mk_cartier_top_mul_pow (f : P) :
    π (cartier (ZMod p) q topExp[q] (t ^ (q - 1) * f)) = π (cartier (ZMod p) q 0 f) := by
  simpa only [Finsupp.mapRange_zero, tsub_zero,
    ← TauCeti.prod_X_pow_eq_monomial_equivFunOnFinite_symm] using
    mk_cartier_top_mul_complement q (0 : σ →₀ Fin q) f

private theorem pow_prod_X_dvd_of_cartier_top_mul (f : P)
    (hf : ∀ g : P, π (cartier (ZMod p) q topExp[q] (f * g)) = 0) : t ^ q ∣ f := by
  classical
  have ht : expand q t = t ^ q := by simp [map_prod, Finset.prod_pow]
  rw [← ht, ← sum_monomial_mul_expand_cartier (n := q) f, ← Ideal.mem_span_singleton]
  apply Ideal.sum_mem
  intro β _
  apply Ideal.mul_mem_left
  rw [Ideal.mem_span_singleton]
  have hβ := hf (monomial (topExp[q] - resExp[q] β) 1)
  rw [mul_comm, mk_cartier_top_mul_complement] at hβ
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hβ
  obtain ⟨g, hg⟩ := hβ
  exact ⟨expand q g, by rw [hg, map_mul]⟩

variable [Nonempty σ] [Fact p.Prime]

/-- Multiplication followed by the root-stage projection trace, as a bilinear pairing. -/
noncomputable def projectionPairing (m : ℕ) :
    rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) m →ₗ[A] A :=
  LinearMap.mk₂ A
    (fun (x y : rootModule (p := p) (σ := σ) m) ↦
      projectionTrace m (toRoot m ((toRoot m).symm x * (toRoot m).symm y)))
    (by
      intro x y z
      simp [add_mul])
    (by
      intro a x y
      obtain ⟨x, rfl⟩ := (toRoot m).surjective x
      simp only [smul_toRoot, AddEquiv.symm_apply_apply, mul_assoc]
      rw [← smul_toRoot, LinearMap.map_smul])
    (by
      intro x y z
      simp [mul_add])
    (by
      intro a x y
      obtain ⟨y, rfl⟩ := (toRoot m).surjective y
      simp only [smul_toRoot, AddEquiv.symm_apply_apply, mul_left_comm _ (a ^ p ^ m)]
      rw [← smul_toRoot, LinearMap.map_smul])

/-- The value of the pairing on the underlying quotient classes. -/
@[simp]
theorem projectionPairing_toRoot (m : ℕ) (a b : A) :
    projectionPairing m (toRoot m a) (toRoot m b) = projectionTrace m (toRoot m (a * b)) := by
  simp [projectionPairing]

private theorem exists_cartier_top_representer (m : ℕ)
    (φ : rootModule (p := p) (σ := σ) m →ₗ[A] A) :
    have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    ∃ f : P, ∀ g : P,
      π (cartier (ZMod p) (p ^ m) (Finsupp.equivFunOnFinite.symm (fun _ : σ ↦ p ^ m - 1))
        (f * g)) = φ (toRoot m (π g)) := by
  classical
  let q := p ^ m
  have hq : NeZero q := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hr : ∀ i : σ, topExp[q] i < q := by
    intro i
    simpa using Nat.sub_one_lt (NeZero.ne q)
  -- Lift the functional on each residue monomial to a polynomial coefficient.
  choose a ha using fun β : σ →₀ Fin q ↦
    Ideal.Quotient.mk_surjective (φ (toRoot m (π (monomial (resExp[q] β) 1))))
  let f : P := ∑ β, expand q (a β) * monomial (topExp[q] - resExp[q] β) 1
  have hf (β : σ →₀ Fin q) :
      π (cartier (ZMod p) q topExp[q] (f * monomial (resExp[q] β) 1)) =
        φ (toRoot m (π (monomial (resExp[q] β) 1))) := by
    simp only [f, Finset.sum_mul, map_sum, mul_assoc,
      cartier_expand_mul hr, map_mul,
      mk_cartier_top_mul_complement]
    have hβ (δ : σ →₀ Fin q) : resExp[q] δ = resExp[q] β ↔ δ = β :=
      ⟨fun h ↦ Finsupp.ext fun i ↦ Fin.ext (DFunLike.congr_fun h i), congrArg _⟩
    have hcart (δ : σ →₀ Fin q) :
        cartier (ZMod p) q (resExp[q] δ) (monomial (resExp[q] β) 1) =
          if δ = β then 1 else 0 := by
      have h := TauCeti.MvPolynomial.cartier_monomial_nsmul_add (R := ZMod p) (n := q)
        (r := resExp[q] δ) (s := resExp[q] β) (fun i ↦ (δ i).isLt) (fun i ↦ (β i).isLt) 0 1
      have hd : resExp[q] β = resExp[q] δ ↔ δ = β := eq_comm.trans (hβ δ)
      simpa only [smul_zero, zero_add, monomial_zero', C_1, hd] using h
    simp [hcart, apply_ite π, ha]
  refine ⟨f, fun g ↦ ?_⟩
  rw [← sum_monomial_mul_expand_cartier (n := q) g]
  simp only [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro β _
  let b := monomial (resExp[q] β) (1 : ZMod p)
  let c := cartier (ZMod p) q (resExp[q] β) g
  have hφ : φ (toRoot m (π (b * expand q c))) = π c * φ (toRoot m (π b)) := by
    rw [mul_comm, map_mul, mk_expand_prime_pow, ← smul_toRoot, LinearMap.map_smul, smul_eq_mul]
  rw [hφ, mul_comm b, mul_left_comm f, cartier_expand_mul hr, map_mul, hf]

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
    simpa only [projectionPairing_toRoot, ← map_mul, projectionTrace_toRoot_mk,
      LinearMap.zero_apply, mul_assoc, mk_cartier_top_mul_pow] using hg
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_ne_zero i
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have htq : t ^ q = t ^ (q - 1) * t := by rw [← pow_succ, hq]
  rw [htq, mul_dvd_mul_iff_left (pow_ne_zero _ ht)] at h
  exact (toRoot m).map_eq_zero_iff.mpr
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h))

private theorem projectionPairing_surjective (m : ℕ) :
    Function.Surjective (projectionPairing (p := p) (σ := σ) m) := by
  intro φ
  let q := p ^ m
  have : NeZero q := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := exists_cartier_top_representer m φ
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_ne_zero i
  -- The functional kills the hypersurface relation, so its representative lies in (t ^ (q - 1)).
  have hz : t ^ q ∣ t * f := by
    apply pow_prod_X_dvd_of_cartier_top_mul q
    intro g
    rw [mul_right_comm t f g, mul_comm (t * g), hf, map_mul]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))]
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have htq : t ^ q = t * t ^ (q - 1) := by rw [← pow_succ', hq]
  rw [htq, mul_dvd_mul_iff_left ht] at hz
  obtain ⟨f', rfl⟩ := hz
  refine ⟨toRoot m (π f'), ?_⟩
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [projectionPairing_toRoot, ← map_mul, projectionTrace_toRoot_mk, ← hf, mul_assoc,
    mk_cartier_top_mul_pow]

/-- The projection trace identifies every finite root stage with its linear dual. -/
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
