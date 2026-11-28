/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.RingTheory.MvPolynomial.Cartier
public import TauCeti.RingTheory.MvPolynomial.Quotient.NormalCrossing

/-!
# Projection traces for normal-crossing hypersurfaces

The additive root stage `MonomialRootAlgebra.rootStage` is a copy of the quotient of
the polynomial ring over `ZMod p` by the product of the variables. For prime `p` and
a finite nonempty coordinate type, restricting scalars along iterated Frobenius equips
the stage with the module structure bundled by `MonomialRootAlgebra.rootModule`.
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
  ((J : Ideal P).restrictScalars R).mapQ ((J : Ideal P).restrictScalars R)
    (cartier R q 0) (fun f hf ↦ f.cartier_zero_mem_span_prod_X hf)

private theorem projection_mk (q : ℕ) [NeZero q] (f : P) :
    projection q (π f) = π (cartier R q 0 f) := by
  exact Submodule.mapQ_apply _ _ _ f

end Quotient

variable {p : ℕ} {σ : Type*} [Fintype σ]

local notation "P" => MvPolynomial σ (ZMod p)
local notation "A" => MonomialRootAlgebra (ZMod p) σ
local notation "J" => Ideal.span {∏ i : σ, (X i : P)}
local notation "π" => Ideal.Quotient.mk J

/-- The additive carrier of the `m`-th root stage for any natural number `p`. -/
def rootStage (_m : ℕ) : Type _ := A

noncomputable instance (m : ℕ) : AddCommGroup (rootStage (p := p) (σ := σ) m) :=
  inferInstanceAs (AddCommGroup A)

/-- Regard a class in the hypersurface as an element of the `m`-th root stage. -/
noncomputable def toRoot (m : ℕ) : A ≃+ rootStage (p := p) (σ := σ) m :=
  AddEquiv.refl _

local notation "Stage" => rootStage (p := p) (σ := σ)

section Prime

variable [Nonempty σ] [Fact p.Prime]

/-- The root-stage action is the regular action restricted along the `m`-fold Frobenius. -/
noncomputable instance (m : ℕ) : Module A (rootStage (p := p) (σ := σ) m) :=
  letI := Module.compHom A (iterateFrobenius A p m)
  (toRoot m).symm.module A

/-- The `m`-th root stage as a bundled module over the hypersurface. -/
noncomputable abbrev rootModule (m : ℕ) : ModuleCat A :=
  ModuleCat.of A (rootStage (p := p) (σ := σ) m)

/-- Scalars act by the `p ^ m`-th power on the root stage. -/
@[simp]
theorem smul_toRoot (m : ℕ) (a b : A) :
    a • toRoot m b = toRoot m (a ^ p ^ m * b) := by
  -- Expose the transferred action on the quotient to apply the Frobenius power formula.
  change toRoot m (iterateFrobenius A p m a • (toRoot m).symm (toRoot m b)) = _
  rw [AddEquiv.symm_apply_apply, iterateFrobenius_def, smul_eq_mul]

/-- At stage zero the underlying additive identification is linear over the base ring. -/
noncomputable def toRootZero : A ≃ₗ[A] Stage 0 :=
  (toRoot 0).toLinearEquiv (fun a b ↦ by
    rw [smul_toRoot]
    simp only [pow_zero, pow_one, smul_eq_mul])

/-- The stage-zero linear identification sends an element to its underlying quotient class. -/
@[simp]
theorem toRootZero_apply (a : A) : toRootZero a = toRoot 0 a :=
  congrFun (AddEquiv.coe_toLinearEquiv _ _) a

/-- The transition from stage `m` to stage `r` applies the `(r - m)`-fold Frobenius to the
underlying classes. -/
noncomputable def rootTransition (m r : ℕ) (h : m ≤ r) :
    Stage m →ₗ[A] Stage r :=
  { toFun := fun x ↦ toRoot r (iterateFrobenius A p (r - m) ((toRoot m).symm x))
    map_add' := fun x y ↦ by rw [map_add, map_add, map_add]
    map_smul' := by
      intro a x
      obtain ⟨b, rfl⟩ := (toRoot m).surjective x
      rw [smul_toRoot, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
        smul_toRoot, iterateFrobenius_def, mul_pow, ← pow_mul, ← pow_add,
        Nat.add_sub_of_le h]
      rw [RingHom.id_apply, iterateFrobenius_def] }

/-- On quotient classes the stage transition raises to the `p ^ (r - m)`-th power. -/
@[simp]
theorem rootTransition_toRoot (m r : ℕ) (h : m ≤ r) (a : A) :
    rootTransition m r h (toRoot m a) = toRoot r (a ^ p ^ (r - m)) := by
  simp only [rootTransition, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply,
    iterateFrobenius_def]

/-- The transition from a stage to itself is the identity. -/
@[simp]
theorem rootTransition_self (m : ℕ) :
    rootTransition (p := p) (σ := σ) m m le_rfl = LinearMap.id := by
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  rw [rootTransition_toRoot, Nat.sub_self, pow_zero, pow_one, LinearMap.id_apply]

/-- Composing stage transitions gives the transition between their endpoints. -/
@[simp]
theorem rootTransition_comp (m r s : ℕ) (hmr : m ≤ r) (hrs : r ≤ s) :
    (rootTransition (p := p) (σ := σ) r s hrs).comp (rootTransition m r hmr) =
      rootTransition m s (hmr.trans hrs) := by
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  simp only [LinearMap.comp_apply, rootTransition_toRoot, ← iterateFrobenius_def (R := A) p,
    ← iterateFrobenius_add_apply, Nat.sub_add_sub_cancel hrs hmr]

omit [Nonempty σ] in
private theorem mk_expand (m : ℕ) (f : P) : π (expand (p ^ m) f) = (π f) ^ p ^ m := by
  rw [← map_pow]
  congr 1
  simpa only [ZMod.card] using FiniteField.MvPolynomial.expand_card_pow m f

/-- The root-stage projection onto integral exponents, as a linear map over the base ring. -/
noncomputable def projectionTrace (m : ℕ) : Stage m →ₗ[A] A :=
  { toFun := fun x ↦ projection (p ^ m) ((toRoot m).symm x)
    map_add' := fun x y ↦ by rw [map_add, map_add]
    map_smul' := by
      intro a x
      obtain ⟨b, rfl⟩ := (toRoot m).surjective x
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [smul_toRoot, AddEquiv.symm_apply_apply, ← mk_expand, ← map_mul]
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
  rw [← mk_expand, projectionTrace_toRoot_mk, projectionTrace_toRoot_mk]
  congr 1
  ext d
  simp [pow_add, mul_comm (p ^ m), mul_smul,
    coeff_expand_smul _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

/-- The higher-stage trace composed with the stage transition is the lower-stage trace. -/
@[simp]
theorem projectionTrace_comp_rootTransition (m r : ℕ) (h : m ≤ r) :
    (projectionTrace (p := p) (σ := σ) r).comp (rootTransition m r h) = projectionTrace m := by
  ext x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  rw [LinearMap.comp_apply, rootTransition_toRoot]
  have htrace := projectionTrace_add_toRoot_pow m (r - m) a
  rw [Nat.add_sub_of_le h] at htrace
  exact htrace

/-- The projection trace splits the linear inclusion from the base ring. -/
@[simp]
theorem projectionTrace_comp_rootTransition_zero (m : ℕ) :
    (projectionTrace (p := p) (σ := σ) m).comp
      ((rootTransition 0 m (Nat.zero_le m)).comp toRootZero.toLinearMap) = LinearMap.id := by
  rw [← LinearMap.comp_assoc, projectionTrace_comp_rootTransition]
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    toRootZero_apply, projectionTrace_zero_toRoot]

/-- The transitions between finite root stages are injective. -/
theorem rootTransition_injective (m r : ℕ) (h : m ≤ r) :
    Function.Injective (rootTransition (p := p) (σ := σ) m r h) := by
  apply Function.LeftInverse.injective (g := fun x ↦
    toRoot m (projectionTrace (r - m) (toRoot (r - m) ((toRoot r).symm x))))
  intro x
  obtain ⟨a, rfl⟩ := (toRoot m).surjective x
  rw [rootTransition_toRoot]
  dsimp only
  rw [AddEquiv.symm_apply_apply, projectionTrace_toRoot_pow]

end Prime

section Pairing

local notation "t" => (∏ i : σ, (X i : P))

private noncomputable def topExp (q : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ : σ ↦ q - 1)

variable [Nonempty σ] [Fact p.Prime]

private noncomputable def rootMul (m : ℕ) :
    Stage m →ₗ[A] Stage m →ₗ[A] Stage m :=
  let alg := (iterateFrobenius A p m).toAlgebra
  letI : Module A A := alg.toModule
  let e := (toRoot m).symm.linearEquiv A
  ((@LinearMap.mul A A _ _ alg.toModule
    (@Algebra.to_smulCommClass A A _ _ alg) (@IsScalarTower.right A A _ _ alg)).compl₁₂
      e.toLinearMap e.toLinearMap).compr₂ₛₗ e.symm.toLinearMap

/-- Under the additive identification, root-stage multiplication multiplies quotient classes. -/
private theorem rootMul_toRoot (m : ℕ) (a b : A) :
    rootMul m (toRoot m a) (toRoot m b) = toRoot m (a * b) := by
  simp only [rootMul, LinearMap.compr₂ₛₗ_apply, LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe, AddEquiv.linearEquiv_apply, AddEquiv.linearEquiv_symm_apply,
    AddEquiv.symm_apply_apply, LinearMap.mul_apply', AddEquiv.symm_symm]

/-- Multiplication followed by the root-stage projection trace, as a bilinear pairing. -/
noncomputable def projectionPairing (m : ℕ) :
    Stage m →ₗ[A] Stage m →ₗ[A] A :=
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
  rw [LinearMap.flip_apply, projectionPairing_toRoot, projectionPairing_toRoot, mul_comm a b]

private theorem exists_cartier_top_representer (m : ℕ)
    (φ : Stage m →ₗ[A] A) :
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
  conv_rhs => rw [mk_expand, mul_comm, ← smul_toRoot,
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
    rw [projectionPairing_toRoot_mk, LinearMap.zero_apply] at hg
    simpa only [mul_assoc, topExp] using hg
  rw [← pow_sub_one_mul (NeZero.ne q) t] at h
  have ht := isRegular_prod_X (R := ZMod p) (Finset.univ : Finset σ)
  rw [mul_dvd_mul_iff_left (ht.pow _).ne_zero] at h
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
    simp [Ideal.Quotient.mk_singleton_self t]
  rw [← mul_pow_sub_one (NeZero.ne q) t] at hz
  have ht := isRegular_prod_X (R := ZMod p) (Finset.univ : Finset σ)
  rw [mul_dvd_mul_iff_left ht.ne_zero] at hz
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
