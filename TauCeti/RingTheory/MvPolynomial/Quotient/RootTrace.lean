/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.RingTheory.MvPolynomial.Cartier
public import TauCeti.RingTheory.MvPolynomial.Quotient.NormalCrossing

/-!
# Projection traces for normal-crossing hypersurfaces

For a finite nonempty coordinate type, consider the quotient of a polynomial ring over the
prime field by the product of the variables. The root stage is the regular module with scalars
restricted along an iterated Frobenius.
The projection trace retains the monomials whose exponents are divisible by `p ^ m` and divides
their exponents by `p ^ m` (`MonomialRootAlgebra.projectionTrace_toRoot_monomialClass`).
It retracts the base inclusion (`MonomialRootAlgebra.projectionTrace_comp_rootTransition_zero`)
and commutes with the finite-stage inclusions
(`MonomialRootAlgebra.projectionTrace_comp_rootTransition`).
The `LinearMap.IsPerfPair` instance for `MonomialRootAlgebra.projectionPairing` identifies each
root stage with its linear dual.

The equivalence `(projectionPairing m).toPerfPair` sends a root-stage element `x` to the
functional `y ↦ projectionPairing m x y`. The underlying Cartier duality is supplied by
`TauCeti.MvPolynomial.cartierDual` and `MvPolynomial.cartier_cartierDual_mul`.

## Reference

* B. Zavyalov, *Mod-p Poincaré Duality in p-adic Analytic Geometry*,
  [Definition 4.3.1 and Theorem 4.3.2, Step 2](https://arxiv.org/abs/2111.01830v3).
-/

public section

namespace TauCeti

open _root_.MvPolynomial

namespace MonomialRootAlgebra

section Quotient

variable {R σ : Type*} [CommRing R] [Fintype σ]

local notation "P" => MvPolynomial σ R
local notation "A" => MonomialRootAlgebra R σ
local notation "J" => Ideal.span {∏ i : σ, (X i : P)}
local notation "π" => Ideal.Quotient.mk J

private noncomputable def projection (q : ℕ) [NeZero q] : A →ₗ[R] A :=
  ((J : Ideal P).restrictScalars R).liftQ
    ((Ideal.Quotient.mkₐ R J).toLinearMap ∘ₗ cartier R q 0)
    (fun f hf ↦ Ideal.Quotient.eq_zero_iff_mem.2 (f.cartier_zero_mem_span_prod_X hf))

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

private theorem smul_toRoot_iterate (m : ℕ) (a b : A) :
    a • toRoot m b = toRoot m (iterateFrobenius A p m a * b) := by
  -- Restriction of scalars leaves the underlying additive group and the identification unchanged.
  calc
    _ = toRoot m (iterateFrobenius A p m a • b) :=
      ModuleCat.restrictScalars.smul_def' _ (M := ModuleCat.of A A) a b
    _ = _ := by rw [smul_eq_mul]

/-- Scalars act by the `p ^ m`-th power on the root stage. -/
@[simp]
theorem smul_toRoot (m : ℕ) (a b : A) :
    a • toRoot m b = toRoot m (a ^ p ^ m * b) := by
  rw [smul_toRoot_iterate, iterateFrobenius_def]

/-- At stage zero the underlying additive identification is linear over the base ring. -/
noncomputable def toRootZero : A ≃ₗ[A] rootModule (p := p) (σ := σ) 0 :=
  (ModuleCat.restrictScalarsId'App (iterateFrobenius A p 0)
    (iterateFrobenius_zero A p) (ModuleCat.of A A)).symm.toLinearEquiv

/-- The stage-zero linear identification sends an element to its underlying quotient class. -/
@[simp]
theorem toRootZero_apply (a : A) : toRootZero a = toRoot 0 a :=
  (rfl)

/-- The transition from stage `m` to stage `m + k` applies the `k`-fold Frobenius to the
underlying classes. -/
noncomputable def rootTransition (m k : ℕ) :
    rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) (m + k) :=
  ((ModuleCat.restrictScalarsComp'App (iterateFrobenius A p m)
    (iterateFrobenius A p k) (iterateFrobenius A p (m + k))
    (by rw [Nat.add_comm m k, iterateFrobenius_add]) (ModuleCat.of A A)).inv.hom).comp
    (((ModuleCat.restrictScalars (iterateFrobenius A p m)).map
      (ModuleCat.semilinearMapAddEquiv (iterateFrobenius A p k) (ModuleCat.of A A)
        (ModuleCat.of A A) (LinearMap.iterateFrobenius A A p k))).hom)

/-- On quotient classes the stage transition raises to the `p ^ k`-th power. -/
@[simp]
theorem rootTransition_toRoot (m k : ℕ) (a : A) :
    rootTransition m k (toRoot m a) = toRoot (m + k) (a ^ p ^ k) := by
  -- Restriction and its comparison isomorphism retain the underlying additive carrier.
  unfold rootTransition rootModule toRoot
  rfl

/-- The transition with zero increment is the identity. -/
@[simp]
theorem rootTransition_zero (m : ℕ) :
    rootTransition (p := p) (σ := σ) m 0 = LinearMap.id := by
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  exact (rootTransition_toRoot m 0 a).trans (by simp)

/-- Successive transitions apply the Frobenius for the sum of their increments. -/
theorem rootTransition_comp_apply (m k l : ℕ) (x : rootModule (p := p) (σ := σ) m) :
    rootTransition (m + k) l (rootTransition m k x) =
      toRoot (m + k + l) ((toRoot m).symm x ^ p ^ (k + l)) := by
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  rw [rootTransition_toRoot, rootTransition_toRoot, AddEquiv.symm_apply_apply,
    pow_add, pow_mul]

/-- Composing stage transitions gives the transition for the sum of their increments,
after transporting the target along associativity of addition. -/
theorem rootTransition_comp (m k l : ℕ) :
    (rootTransition (p := p) (σ := σ) (m + k) l).comp (rootTransition m k) =
      (LinearEquiv.cast (M := fun n ↦ rootModule (p := p) (σ := σ) n)
        (Nat.add_assoc m k l).symm).toLinearMap.comp (rootTransition m (k + l)) := by
  ext x
  rw [LinearMap.comp_apply, rootTransition_comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  rw [rootTransition_toRoot, AddEquiv.symm_apply_apply]
  have hcast (i j : ℕ) (h : i = j) (b : A) :
      LinearEquiv.cast (R := A) (M := fun n ↦ rootModule (p := p) (σ := σ) n) h (toRoot i b) =
        toRoot j b := by
    subst j
    rfl
  exact (hcast _ _ _ _).symm

/-- A linear map out of a root stage is determined by its values on the monomial classes. -/
theorem rootModule_linearMap_ext {m : ℕ} {M : Type*} [AddCommMonoid M] [Module A M]
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
  { toFun := fun x ↦ projection (p ^ m) ((toRoot m).symm x)
    map_add' := fun x y ↦ by rw [map_add, map_add]
    map_smul' := by
      intro a x
      obtain ⟨b, rfl⟩ := (toRoot m).surjective x
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hexpand (h : P) : expand (p ^ m) h = h ^ p ^ m := by
        simpa only [ZMod.card] using FiniteField.MvPolynomial.expand_card_pow m h
      rw [smul_toRoot, AddEquiv.symm_apply_apply, ← map_pow π, ← hexpand, ← map_mul]
      simp only [AddEquiv.symm_apply_apply, projection_mk, RingHom.id_apply, smul_eq_mul]
      rw [cartier_expand_mul (r := 0) (by simp [Nat.pos_of_neZero]), map_mul] }

/-- On a polynomial representative the projection trace is the zero-offset Cartier operator. -/
theorem projectionTrace_toRoot_mk (m : ℕ) (f : P) :
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
  have hexpand : expand (p ^ k) f = f ^ p ^ k := by
    simpa only [ZMod.card] using FiniteField.MvPolynomial.expand_card_pow k f
  rw [← map_pow π, ← hexpand, projectionTrace_toRoot_mk, projectionTrace_toRoot_mk]
  congr 1
  ext d
  simp [pow_add, mul_comm (p ^ m), mul_smul,
    coeff_expand_smul _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

/-- The higher-stage trace composed with the stage transition is the lower-stage trace. -/
@[simp]
theorem projectionTrace_comp_rootTransition (m k : ℕ) :
    (projectionTrace (p := p) (σ := σ) (m + k)).comp (rootTransition m k) = projectionTrace m := by
  apply rootModule_linearMap_ext
  intro d c
  simp only [LinearMap.comp_apply, rootTransition_toRoot, projectionTrace_add_toRoot_pow]

/-- The projection trace splits the linear inclusion from the base ring. -/
@[simp]
theorem projectionTrace_comp_rootTransition_zero (m : ℕ) :
    (projectionTrace (p := p) (σ := σ) (0 + m)).comp
      ((rootTransition 0 m).comp toRootZero.toLinearMap) = LinearMap.id := by
  rw [← LinearMap.comp_assoc, projectionTrace_comp_rootTransition]
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    toRootZero_apply, projectionTrace_zero_toRoot]

/-- The transitions between finite root stages are injective. -/
theorem rootTransition_injective (m k : ℕ) :
    Function.Injective (rootTransition (p := p) (σ := σ) m k) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  obtain ⟨b, rfl⟩ := (toRoot m).surjective y
  simp only [rootTransition_toRoot, EmbeddingLike.apply_eq_iff_eq] at h
  apply congrArg (toRoot m)
  simpa only [projectionTrace_toRoot_pow] using
    congrArg (fun c ↦ projectionTrace k (toRoot k c)) h

end Prime

section Pairing

local notation "t" => (∏ i : σ, (X i : P))

private noncomputable def topExp (q : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ : σ ↦ q - 1)

variable [Nonempty σ] [Fact p.Prime]

omit [Nonempty σ] in
private theorem prod_X_ne_zero : (t : P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_ne_zero i

private noncomputable def rootMul (m : ℕ) :
    rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) m →ₗ[A]
      rootModule (p := p) (σ := σ) m :=
  let alg := (iterateFrobenius A p m).toAlgebra
  @LinearMap.mul A A _ _ alg.toModule
    (@Algebra.to_smulCommClass A A _ _ alg) (@IsScalarTower.right A A _ _ alg)

/-- Under the additive identification, root-stage multiplication multiplies quotient classes. -/
private theorem rootMul_toRoot (m : ℕ) (a b : A) :
    rootMul m (toRoot m a) (toRoot m b) = toRoot m (a * b) := by
  -- The restricted module and `toRoot` use the underlying quotient type.
  unfold rootMul
  let alg := (iterateFrobenius A p m).toAlgebra
  exact @LinearMap.mul_apply' A A _ _ alg.toModule
    (@Algebra.to_smulCommClass A A _ _ alg) (@IsScalarTower.right A A _ _ alg) a b

/-- Multiplication followed by the root-stage projection trace, as a bilinear pairing. -/
noncomputable def projectionPairing (m : ℕ) :
    rootModule (p := p) (σ := σ) m →ₗ[A] rootModule (p := p) (σ := σ) m →ₗ[A] A :=
  (rootMul m).compr₂ₛₗ (projectionTrace m)

/-- The value of the pairing on the underlying quotient classes. -/
@[simp]
theorem projectionPairing_toRoot (m : ℕ) (a b : A) :
    projectionPairing m (toRoot m a) (toRoot m b) = projectionTrace m (toRoot m (a * b)) := by
  rw [projectionPairing, LinearMap.compr₂ₛₗ_apply, rootMul_toRoot]

/-- The projection pairing is symmetric. -/
@[simp]
theorem projectionPairing_flip (m : ℕ) :
    (projectionPairing (p := p) (σ := σ) m).flip = projectionPairing m := by
  ext x y
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  obtain ⟨b, rfl⟩ := (toRoot m).surjective y
  simp [mul_comm]

private theorem exists_cartier_top_representer (m : ℕ)
    (φ : rootModule (p := p) (σ := σ) m →ₗ[A] A) :
    ∃ f : P, ∀ g : P,
      π (cartier (ZMod p) (p ^ m) (Finsupp.equivFunOnFinite.symm (fun _ : σ ↦ p ^ m - 1))
        (f * g)) = φ (toRoot m (π g)) := by
  classical
  let q := p ^ m
  choose a ha using fun β : σ →₀ Fin q ↦
    let d := β.mapRange Fin.val (Fin.val_zero q)
    Ideal.Quotient.mk_surjective (φ (toRoot m (π (monomial d 1))))
  refine ⟨TauCeti.MvPolynomial.cartierDual q a, fun g ↦ ?_⟩
  rw [cartier_cartierDual_mul, finsum_eq_sum_of_fintype]
  conv_rhs => rw [← sum_monomial_mul_expand_cartier (n := q) g]
  simp only [map_sum, map_mul, ha]
  apply Finset.sum_congr rfl
  intro β _
  have hexpand (h : P) : expand q h = h ^ p ^ m := by
    simpa only [ZMod.card] using FiniteField.MvPolynomial.expand_card_pow m h
  conv_rhs => rw [hexpand, map_pow, mul_comm, ← smul_toRoot,
    LinearMap.map_smul, smul_eq_mul]

private theorem projectionPairing_toRoot_mk (m : ℕ) (f g : P) :
      projectionPairing m (toRoot m (π f)) (toRoot m (π g)) =
      π (cartier (ZMod p) (p ^ m) (topExp (p ^ m)) (t ^ (p ^ m - 1) * (f * g))) := by
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
  have h : t ^ q ∣ t ^ (q - 1) * f := by
    apply MvPolynomial.pow_prod_X_dvd_of_cartier_top_mul
    intro g
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hg := DFunLike.congr_fun hx (toRoot m (π g))
    simpa only [projectionPairing_toRoot_mk, LinearMap.zero_apply, mul_assoc, topExp] using hg
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.pos_of_neZero q)
  conv at h =>
    lhs
    rw [← hq, pow_succ]
  rw [mul_dvd_mul_iff_left (pow_ne_zero _ prod_X_ne_zero)] at h
  exact (toRoot m).map_eq_zero_iff.mpr
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h))

private theorem projectionPairing_surjective (m : ℕ) :
    Function.Surjective (projectionPairing (p := p) (σ := σ) m) := by
  intro φ
  let q := p ^ m
  obtain ⟨f, hf⟩ := exists_cartier_top_representer m φ
  -- The functional kills the hypersurface relation, so its representative lies in (t ^ (q - 1)).
  have hz : t ^ q ∣ t * f := by
    apply MvPolynomial.pow_prod_X_dvd_of_cartier_top_mul
    intro g
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [mul_right_comm t f g, mul_comm (t * g), hf, map_mul]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))]
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.pos_of_neZero q)
  conv at hz =>
    lhs
    rw [← hq, pow_succ']
  rw [mul_dvd_mul_iff_left prod_X_ne_zero] at hz
  obtain ⟨f', rfl⟩ := hz
  refine ⟨toRoot m (π f'), ?_⟩
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [projectionPairing_toRoot_mk, topExp, ← hf, mul_assoc]

/-- The pairing obtained by multiplying the underlying quotient classes and applying the
projection trace is perfect on every finite root stage for a finite nonempty coordinate type. -/
instance (m : ℕ) : (projectionPairing (p := p) (σ := σ) m).IsPerfPair where
  bijective_left := ⟨projectionPairing_injective m, projectionPairing_surjective m⟩
  bijective_right := by
    rw [projectionPairing_flip]
    exact ⟨projectionPairing_injective m, projectionPairing_surjective m⟩

end Pairing
end MonomialRootAlgebra
end TauCeti
