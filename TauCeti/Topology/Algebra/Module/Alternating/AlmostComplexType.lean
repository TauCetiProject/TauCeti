/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.Aeval
public import TauCeti.Topology.Algebra.Module.Alternating.Curry
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The `(p,q)` type of complex-valued alternating forms

Let `J` be a continuous real-linear endomorphism of a real topological vector space `V` with
`J² = -1`, and let `F` be a complex topological vector space. A continuous real alternating map
`ω : V [⋀^Fin k]→L[ℝ] F` is a complex-valued `k`-form on `V`, and it decomposes uniquely into
components of type `(p,q)`, `p + q = k`. This file develops that decomposition directly on the
real alternating carrier, without passing to the complexification of `V`.

Every endomorphism `J` of `V` acts on forms as a derivation,
`J.alternatingDerivation ω v = ∑ i, ω (update v i (J (v i)))`. On a form of type `(p,q)` it acts by
`(p - q) * I`, and since `p + q = k` this eigenvalue determines `(p,q)`; this is the definition of
`ContinuousAlternatingMap.IsOfType`. A one-form `α` has type `(1,0)` exactly when
`α (J v) = I • α v`, and type `(0,1)` exactly when `α (J v) = -I • α v`.

When `J² = -1`, every polynomial vanishing at the numbers `(p - q) * I` with `p + q = k`
annihilates the derivation on `k`-forms. Since these numbers are distinct, the corresponding
Lagrange basis polynomials, evaluated at the derivation, are the type projections
`ContinuousLinearMap.typeProjection J p q`. They are complementary idempotents whose ranges are the
forms of each type. Types and type projections are compatible with pullback along maps
intertwining the complex structures and with complex-linear coefficient maps, and conjugate-linear
coefficient maps such as complex conjugation exchange the types `(p,q)` and `(q,p)`.

These fibrewise statements are the linear algebra behind the type decomposition of complex-valued
differential forms on an almost complex manifold.

## Main declarations

* `ContinuousLinearMap.alternatingDerivation`: an endomorphism of `V` acting as a derivation on
  alternating maps.
* `ContinuousAlternatingMap.IsOfType`: a `k`-form has type `(p,q)`.
* `ContinuousLinearMap.aeval_alternatingDerivation_eq_zero`: the polynomial identity satisfied by
  the derivation of an endomorphism with `J² = -1`.
* `ContinuousLinearMap.typeProjection`: for `J² = -1`, the projection onto the forms of type
  `(p,q)`.
* `ContinuousLinearMap.sum_typeProjection`: a form is the sum of its components of each type.
* `ContinuousLinearMap.isOfType_typeProjection`,
  `ContinuousAlternatingMap.IsOfType.typeProjection_self`: the projections land in, and fix, the
  forms of their type.
* `ContinuousLinearMap.typeProjection_eq_of_sum_eq`: uniqueness of the type decomposition.
* `ContinuousAlternatingMap.isOfType_one_zero_iff`,
  `ContinuousAlternatingMap.isOfType_zero_one_iff`, `ContinuousLinearMap.typeProjection_one_zero`
  and `ContinuousLinearMap.typeProjection_zero_one`: one-forms.

## Implementation notes

The polynomial identity is proved by induction on the degree. Inserting a vector `v` as the first
argument, the combinations `ι_v ∓ I • ι_{J v}` of interior products intertwine the derivation on
`(k+1)`-forms with the derivation on `k`-forms shifted by `±I`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.2.
-/

public section

noncomputable section

open Complex Polynomial Function
open scoped ComplexConjugate

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  {F G : Type*} [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul ℂ F]
  [AddCommGroup G] [Module ℂ G] [Module ℝ G] [IsScalarTower ℝ ℂ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul ℂ G]

namespace ContinuousLinearMap

section Derivation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The form obtained by applying `J` to the `i`-th argument. -/
private def compSlot (J : V →L[ℝ] V) (ω : V [⋀^ι]→L[ℝ] F) (i : ι) :
    ContinuousMultilinearMap ℝ (fun _ : ι ↦ V) F :=
  ω.toContinuousMultilinearMap.compContinuousLinearMap (update (fun _ ↦ .id ℝ V) i J)

omit [Module ℂ F] [IsScalarTower ℝ ℂ F] [IsTopologicalAddGroup F] [ContinuousConstSMul ℂ F]
  [Fintype ι] in
private lemma compSlot_apply (J : V →L[ℝ] V) (ω : V [⋀^ι]→L[ℝ] F) (i : ι) (v : ι → V) :
    compSlot J ω i v = ω (update v i (J (v i))) := by
  simp only [compSlot, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine congrArg ω (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [update_of_ne hj]

omit [Module ℂ F] [IsScalarTower ℝ ℂ F] [ContinuousConstSMul ℂ F] in
/-- The sum of the forms obtained by applying `J` to one argument at a time is alternating. -/
private lemma sum_compSlot_eq_zero (J : V →L[ℝ] V) (ω : V [⋀^ι]→L[ℝ] F) (v : ι → V)
    {a b : ι} (hv : v a = v b) (hab : a ≠ b) :
    (∑ i, compSlot J ω i) v = 0 := by
  rw [sum_apply, Fintype.sum_eq_add a b hab]
  · rw [compSlot_apply, compSlot_apply]
    have hswap : update v b (J (v b)) = update v a (J (v a)) ∘ Equiv.swap a b := by
      rw [update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_left, ← hv]
      congr 1
      ext j
      rcases eq_or_ne j a with rfl | hja
      · simp [hv]
      rcases eq_or_ne j b with rfl | hjb
      · simp [hv]
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb]
    rw [hswap, add_comm]
    simpa using ω.toAlternatingMap.map_swap_add (update v a (J (v a))) hab
  · rintro i ⟨hia, hib⟩
    rw [compSlot_apply]
    exact ω.map_eq_zero_of_eq _ (by simp [update_of_ne hia.symm, update_of_ne hib.symm, hv]) hab

/-- An endomorphism `J` of `V` acts on alternating maps on `V` as a derivation: the result is the
sum, over all arguments, of the alternating map with `J` applied to that argument. -/
def alternatingDerivation (J : V →L[ℝ] V) :
    (V [⋀^ι]→L[ℝ] F) →ₗ[ℂ] V [⋀^ι]→L[ℝ] F where
  toFun ω := ⟨∑ i, compSlot J ω i, fun v _ _ hv hab ↦ sum_compSlot_eq_zero J ω v hv hab⟩
  map_add' ω ω' := by
    ext v
    simp [sum_apply, compSlot_apply, Finset.sum_add_distrib]
  map_smul' c ω := by
    ext v
    simp [sum_apply, compSlot_apply, Finset.smul_sum]

theorem alternatingDerivation_apply (J : V →L[ℝ] V) (ω : V [⋀^ι]→L[ℝ] F) (v : ι → V) :
    J.alternatingDerivation ω v = ∑ i, ω (update v i (J (v i))) := by
  simp [alternatingDerivation, sum_apply, compSlot_apply]

/-- On a one-form, the derivation is precomposition with `J`. -/
theorem alternatingDerivation_apply_vecCons_fin_one (J : V →L[ℝ] V) (α : V [⋀^Fin 1]→L[ℝ] F)
    (v : V) : J.alternatingDerivation α ![v] = α ![J v] := by
  rw [alternatingDerivation_apply, Fin.sum_univ_one]
  exact congrArg α (by ext i; fin_cases i; rfl)

/-- The derivation is natural for pullback along a map intertwining the endomorphisms. -/
theorem alternatingDerivation_compContinuousLinearMap {J : V →L[ℝ] V} {K : W →L[ℝ] W}
    {f : W →L[ℝ] V} (hf : ∀ w, J (f w) = f (K w)) (ω : V [⋀^ι]→L[ℝ] F) :
    K.alternatingDerivation (ω.compContinuousLinearMap f) =
      (J.alternatingDerivation ω).compContinuousLinearMap f := by
  ext v
  simp only [alternatingDerivation_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg ω ?_
  rw [comp_update]
  simp [hf]

/-- The derivation commutes with real-linear coefficient maps. -/
theorem alternatingDerivation_compContinuousAlternatingMap (J : V →L[ℝ] V) (L : F →L[ℝ] G)
    (ω : V [⋀^ι]→L[ℝ] F) :
    J.alternatingDerivation (L.compContinuousAlternatingMap ω) =
      L.compContinuousAlternatingMap (J.alternatingDerivation ω) := by
  ext v
  simp [alternatingDerivation_apply]

end Derivation

end ContinuousLinearMap

namespace ContinuousAlternatingMap

section IsOfType

variable {k : ℕ} {J : V →L[ℝ] V} {ω ω' : V [⋀^Fin k]→L[ℝ] F} {p q : ℕ}

/-- A complex-valued `k`-form `ω` has type `(p,q)` for `J` when `p + q = k` and the derivation
induced by `J` acts on `ω` as multiplication by `(p - q) * I`. For an almost complex structure
`J`, these are the forms whose complex-multilinear extension to the complexification vanishes
unless exactly `p` of its arguments are of type `(1,0)` and the other `q` of type `(0,1)`. -/
def IsOfType (ω : V [⋀^Fin k]→L[ℝ] F) (J : V →L[ℝ] V) (p q : ℕ) : Prop :=
  p + q = k ∧ J.alternatingDerivation ω = (((p : ℂ) - q) * I) • ω

theorem isOfType_iff : ω.IsOfType J p q ↔
    p + q = k ∧ J.alternatingDerivation ω = (((p : ℂ) - q) * I) • ω :=
  Iff.rfl

theorem IsOfType.add_eq (h : ω.IsOfType J p q) : p + q = k :=
  h.1

theorem IsOfType.alternatingDerivation_eq (h : ω.IsOfType J p q) :
    J.alternatingDerivation ω = (((p : ℂ) - q) * I) • ω :=
  h.2

@[simp]
theorem isOfType_zero_iff : (0 : V [⋀^Fin k]→L[ℝ] F).IsOfType J p q ↔ p + q = k := by
  simp [isOfType_iff]

theorem IsOfType.add (h : ω.IsOfType J p q) (h' : ω'.IsOfType J p q) :
    (ω + ω').IsOfType J p q :=
  ⟨h.1, by rw [map_add, h.2, h'.2, smul_add]⟩

theorem IsOfType.smul (h : ω.IsOfType J p q) (c : ℂ) : (c • ω).IsOfType J p q :=
  ⟨h.1, by rw [map_smul, h.2, smul_comm]⟩

theorem IsOfType.neg (h : ω.IsOfType J p q) : (-ω).IsOfType J p q :=
  ⟨h.1, by rw [map_neg, h.2, smul_neg]⟩

theorem IsOfType.sub (h : ω.IsOfType J p q) (h' : ω'.IsOfType J p q) :
    (ω - ω').IsOfType J p q :=
  ⟨h.1, by rw [map_sub, h.2, h'.2, smul_sub]⟩

/-- Every complex-valued function, as a `0`-form, has type `(0,0)`. -/
theorem isOfType_zero_zero (ω : V [⋀^Fin 0]→L[ℝ] F) (J : V →L[ℝ] V) : ω.IsOfType J 0 0 :=
  ⟨rfl, by ext v; simp [ContinuousLinearMap.alternatingDerivation_apply]⟩

/-- A one-form has type `(1,0)` exactly when it is complex-linear for `J`. -/
theorem isOfType_one_zero_iff (α : V [⋀^Fin 1]→L[ℝ] F) :
    α.IsOfType J 1 0 ↔ ∀ v, α ![J v] = I • α ![v] := by
  simp only [isOfType_iff, true_and, Nat.cast_one, Nat.cast_zero, sub_zero, one_mul]
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · rw [← J.alternatingDerivation_apply_vecCons_fin_one, h, smul_apply]
  · ext w
    obtain ⟨v, rfl⟩ : ∃ v, w = ![v] := ⟨w 0, by ext i; fin_cases i; rfl⟩
    rw [J.alternatingDerivation_apply_vecCons_fin_one, h, smul_apply]

/-- A one-form has type `(0,1)` exactly when it is conjugate-linear for `J`. -/
theorem isOfType_zero_one_iff (α : V [⋀^Fin 1]→L[ℝ] F) :
    α.IsOfType J 0 1 ↔ ∀ v, α ![J v] = -I • α ![v] := by
  simp only [isOfType_iff, zero_add, true_and, Nat.cast_one, Nat.cast_zero, zero_sub, neg_mul,
    one_mul]
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · rw [← J.alternatingDerivation_apply_vecCons_fin_one, h, smul_apply]
  · ext w
    obtain ⟨v, rfl⟩ : ∃ v, w = ![v] := ⟨w 0, by ext i; fin_cases i; rfl⟩
    rw [J.alternatingDerivation_apply_vecCons_fin_one, h, smul_apply]

/-- Pullback along a map intertwining the endomorphisms preserves type. -/
theorem IsOfType.compContinuousLinearMap {K : W →L[ℝ] W} {f : W →L[ℝ] V}
    (hf : ∀ w, J (f w) = f (K w)) (h : ω.IsOfType J p q) :
    (ω.compContinuousLinearMap f).IsOfType K p q :=
  ⟨h.1, by
    ext v
    rw [ContinuousLinearMap.alternatingDerivation_compContinuousLinearMap hf, h.2]
    simp⟩

/-- A complex-linear coefficient map preserves type. -/
theorem IsOfType.compContinuousAlternatingMap {L : F →L[ℝ] G}
    (hL : ∀ (c : ℂ) x, L (c • x) = c • L x) (h : ω.IsOfType J p q) :
    (L.compContinuousAlternatingMap ω).IsOfType J p q :=
  ⟨h.1, by
    ext v
    rw [ContinuousLinearMap.alternatingDerivation_compContinuousAlternatingMap, h.2]
    simp [hL]⟩

/-- A conjugate-linear coefficient map, such as complex conjugation, exchanges the types
`(p,q)` and `(q,p)`. -/
theorem IsOfType.compContinuousAlternatingMap_of_map_smul_conj {L : F →L[ℝ] G}
    (hL : ∀ (c : ℂ) x, L (c • x) = conj c • L x) (h : ω.IsOfType J p q) :
    (L.compContinuousAlternatingMap ω).IsOfType J q p :=
  ⟨by rw [add_comm, h.1], by
    ext v
    rw [ContinuousLinearMap.alternatingDerivation_compContinuousAlternatingMap, h.2]
    simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe, comp_apply, smul_apply, hL]
    congr 1
    simp only [map_mul, map_sub, map_natCast, conj_I]
    ring⟩

end IsOfType

end ContinuousAlternatingMap

namespace ContinuousLinearMap

section Polynomial

/-- The eigenvalue of the derivation on forms of type `(p,q)`. -/
private def typeEigenvalue (pq : ℕ × ℕ) : ℂ :=
  ((pq.1 : ℂ) - pq.2) * I

private lemma typeEigenvalue_mk (p q : ℕ) : typeEigenvalue (p, q) = ((p : ℂ) - q) * I :=
  (rfl)

private lemma typeEigenvalue_injOn (k : ℕ) :
    Set.InjOn typeEigenvalue (Finset.antidiagonal k : Set (ℕ × ℕ)) := by
  rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' h
  simp only [Finset.mem_coe, Finset.mem_antidiagonal] at hpq hpq'
  have h' : (p : ℤ) - q = p' - q' := by
    exact_mod_cast mul_right_cancel₀ I_ne_zero (h : ((p : ℂ) - q) * I = ((p' : ℂ) - q') * I)
  ext <;> simp only <;> omega

/-- A polynomial vanishing at every type eigenvalue of degree `k` is a multiple of the nodal
polynomial of these eigenvalues. -/
private lemma nodal_dvd {k : ℕ} {g : ℂ[X]}
    (hg : ∀ pq ∈ Finset.antidiagonal k, g.eval (typeEigenvalue pq) = 0) :
    Lagrange.nodal (Finset.antidiagonal k) typeEigenvalue ∣ g := by
  rw [Lagrange.nodal_eq]
  refine Finset.prod_dvd_of_coprime (fun i hi j hj hij ↦ ?_) fun i hi ↦ dvd_iff_isRoot.2 (hg i hi)
  exact isCoprime_X_sub_C_of_isUnit_sub
    (sub_ne_zero.2 ((typeEigenvalue_injOn k).ne hi hj hij)).isUnit

end Polynomial

variable {J : V →L[ℝ] V} {k : ℕ}

section TypeProjection

variable (J) in
/-- The Lagrange basis polynomial at `(p - q) * I` of the nodes `(p' - q') * I`, `p' + q' = k`,
evaluated at the derivation induced by `J` on complex-valued `k`-forms. For `J² = -1` this is the
projection onto the forms of type `(p,q)` for `J`, and it vanishes unless `p + q = k`. -/
def typeProjection (p q : ℕ) : Module.End ℂ (V [⋀^Fin k]→L[ℝ] F) :=
  aeval J.alternatingDerivation (Lagrange.basis (Finset.antidiagonal k) typeEigenvalue (p, q))

variable {ω : V [⋀^Fin k]→L[ℝ] F} {p q p' q' : ℕ}

private lemma aeval_apply_of_isOfType (h : ω.IsOfType J p q) (g : ℂ[X]) :
    aeval (J.alternatingDerivation : Module.End ℂ (V [⋀^Fin k]→L[ℝ] F)) g ω =
      g.eval (typeEigenvalue (p, q)) • ω :=
  Module.End.aeval_apply_of_mem_apply_eq_smul h.2

/-- The operators `J.typeProjection p q` with `p + q = k` sum to the identity on `k`-forms. For
`J² = -1`, this says that every complex-valued form is the sum of its components of each type. -/
theorem sum_typeProjection (J : V →L[ℝ] V) (ω : V [⋀^Fin k]→L[ℝ] F) :
    ∑ pq ∈ Finset.antidiagonal k, J.typeProjection pq.1 pq.2 ω = ω := by
  simp only [typeProjection, Prod.mk.eta]
  rw [← LinearMap.sum_apply, ← map_sum,
    Lagrange.sum_basis (typeEigenvalue_injOn k) ⟨(k, 0), by simp⟩, map_one, Module.End.one_apply]

/-- The projection onto type `(p,q)` fixes the forms of type `(p,q)`. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.IsOfType.typeProjection_self (h : ω.IsOfType J p q) :
    J.typeProjection p q ω = ω := by
  rw [typeProjection, aeval_apply_of_isOfType h,
    Lagrange.eval_basis_self (typeEigenvalue_injOn k) (by simpa using h.1), one_smul]

/-- The projection onto any other type annihilates the forms of type `(p,q)`. -/
theorem _root_.ContinuousAlternatingMap.IsOfType.typeProjection_of_ne (h : ω.IsOfType J p q)
    (hne : (p', q') ≠ (p, q)) : J.typeProjection p' q' ω = 0 := by
  rw [typeProjection, aeval_apply_of_isOfType h,
    Lagrange.eval_basis_of_ne hne (by simpa using h.1), zero_smul]

/-- A form of two different types vanishes. -/
theorem _root_.ContinuousAlternatingMap.IsOfType.eq_zero_of_ne (h : ω.IsOfType J p q)
    (h' : ω.IsOfType J p' q') (hne : (p, q) ≠ (p', q')) : ω = 0 := by
  rw [← h.typeProjection_self, h'.typeProjection_of_ne hne]

/-- The components of a sum of forms of each type are its type components. -/
theorem typeProjection_eq_of_sum_eq {η : ℕ × ℕ → V [⋀^Fin k]→L[ℝ] F}
    (hη : ∀ pq ∈ Finset.antidiagonal k, (η pq).IsOfType J pq.1 pq.2)
    (hω : ∑ pq ∈ Finset.antidiagonal k, η pq = ω) (hpq : p + q = k) :
    J.typeProjection p q ω = η (p, q) := by
  rw [← hω, map_sum, Finset.sum_eq_single (p, q)]
  · exact (hη (p, q) (by simpa using hpq)).typeProjection_self
  · intro pq hpq' hne
    exact (hη pq hpq').typeProjection_of_ne (Ne.symm hne)
  · intro h
    exact absurd (by simpa using hpq) h

/-- On one-forms, `J.typeProjection 1 0` sends `α` to `(α - I • α ∘ J) / 2`. For `J² = -1`, this is
the type-`(1,0)` component of `α`. -/
theorem typeProjection_one_zero (J : V →L[ℝ] V) :
    (J.typeProjection 1 0 : Module.End ℂ (V [⋀^Fin 1]→L[ℝ] F)) =
      (2 : ℂ)⁻¹ • (1 - I • J.alternatingDerivation) := by
  have h : Finset.antidiagonal 1 = {(1, 0), (0, 1)} := by decide
  rw [typeProjection, h, Lagrange.basis_pair_left (by decide)]
  ext ω v
  simp only [Lagrange.basisDivisor, typeEigenvalue, Nat.cast_one, CharP.cast_eq_zero, sub_zero,
    one_mul, zero_sub, neg_mul, sub_neg_eq_add, map_neg, map_mul, aeval_C, map_add, aeval_X,
    Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.coe_smul, Pi.smul_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    ContinuousAlternatingMap.coe_sub, Pi.sub_apply]
  rw [← two_mul, mul_inv, inv_I]
  match_scalars <;> ring_nf
  norm_num

/-- On one-forms, `J.typeProjection 0 1` sends `α` to `(α + I • α ∘ J) / 2`. For `J² = -1`, this is
the type-`(0,1)` component of `α`. -/
theorem typeProjection_zero_one (J : V →L[ℝ] V) :
    (J.typeProjection 0 1 : Module.End ℂ (V [⋀^Fin 1]→L[ℝ] F)) =
      (2 : ℂ)⁻¹ • (1 + I • J.alternatingDerivation) := by
  have h : Finset.antidiagonal 1 = {(1, 0), (0, 1)} := by decide
  rw [typeProjection, h, Lagrange.basis_pair_right (by decide)]
  ext ω v
  simp only [Lagrange.basisDivisor, typeEigenvalue, CharP.cast_eq_zero, Nat.cast_one, zero_sub,
    neg_mul, one_mul, sub_zero, map_mul, aeval_C, aeval_sub, aeval_X, Module.End.mul_apply,
    LinearMap.sub_apply, Module.algebraMap_end_apply, ContinuousAlternatingMap.coe_smul,
    ContinuousAlternatingMap.coe_sub, Pi.smul_apply, Pi.sub_apply, smul_add, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, ContinuousAlternatingMap.add_apply]
  rw [← neg_add', ← two_mul, inv_neg, mul_inv, inv_I]
  match_scalars <;> ring_nf
  norm_num

/-- Pullback along a continuous linear map, as a complex-linear map of forms. -/
private def pullback (f : W →L[ℝ] V) : (V [⋀^Fin k]→L[ℝ] F) →ₗ[ℂ] W [⋀^Fin k]→L[ℝ] F where
  toFun ω := ω.compContinuousLinearMap f
  map_add' ω ω' := by ext; simp
  map_smul' c ω := by ext; simp

/-- Composition with a `σ`-semilinear coefficient map, as a `σ`-semilinear map of forms. -/
private def coeffMap {σ : ℂ →+* ℂ} (L : F →L[ℝ] G) (hL : ∀ (c : ℂ) x, L (c • x) = σ c • L x) :
    (V [⋀^Fin k]→L[ℝ] F) →ₛₗ[σ] V [⋀^Fin k]→L[ℝ] G where
  toFun ω := L.compContinuousAlternatingMap ω
  map_add' ω ω' := by ext; simp
  map_smul' c ω := by ext; simp [hL]

/-- A `σ`-semilinear coefficient map intertwines the polynomial defining a type projection with
its image under `σ`. -/
private lemma aeval_map_basis_compContinuousAlternatingMap {σ : ℂ →+* ℂ} {L : F →L[ℝ] G}
    (hL : ∀ (c : ℂ) x, L (c • x) = σ c • L x) (p q : ℕ) (ω : V [⋀^Fin k]→L[ℝ] F) :
    aeval J.alternatingDerivation
        ((Lagrange.basis (Finset.antidiagonal k) typeEigenvalue (p, q)).map σ)
        (L.compContinuousAlternatingMap ω) =
      L.compContinuousAlternatingMap (J.typeProjection p q ω) :=
  LinearMap.congr_fun (Module.End.aeval_map_comp_of_comp_eq (f := coeffMap (V := V) L hL)
    (LinearMap.ext (alternatingDerivation_compContinuousAlternatingMap J L)) _) ω

/-- Complex conjugation exchanges the type eigenvalues of `(p,q)` and `(q,p)`. -/
private lemma conj_typeEigenvalue (pq : ℕ × ℕ) :
    conj (typeEigenvalue pq) = typeEigenvalue pq.swap := by
  simp only [typeEigenvalue, map_mul, map_sub, map_natCast, conj_I, Prod.fst_swap, Prod.snd_swap]
  ring

/-- Complex conjugation exchanges the polynomials defining the type projections onto `(p,q)` and
`(q,p)`. -/
private lemma map_conj_basis (p q : ℕ) :
    (Lagrange.basis (Finset.antidiagonal k) typeEigenvalue (p, q)).map (starRingEnd ℂ) =
      Lagrange.basis (Finset.antidiagonal k) typeEigenvalue (q, p) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X, map_inv₀, map_sub,
    conj_typeEigenvalue, Prod.swap_prod_mk]
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ (by simp) (by simp) (by simp) <;>
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_erase, Finset.mem_antidiagonal, ne_eq, Prod.mk.injEq,
      Prod.swap_prod_mk] at h ⊢
    omega

/-- Pullback along a map intertwining the endomorphisms commutes with the type projections. -/
theorem typeProjection_compContinuousLinearMap {K : W →L[ℝ] W} {f : W →L[ℝ] V}
    (hf : ∀ w, J (f w) = f (K w)) (ω : V [⋀^Fin k]→L[ℝ] F) :
    K.typeProjection p q (ω.compContinuousLinearMap f) =
      (J.typeProjection p q ω).compContinuousLinearMap f :=
  LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq (f := pullback (F := F) f)
    (LinearMap.ext (alternatingDerivation_compContinuousLinearMap hf)) _) ω

/-- A complex-linear coefficient map commutes with the type projections. -/
theorem typeProjection_compContinuousAlternatingMap {L : F →L[ℝ] G}
    (hL : ∀ (c : ℂ) x, L (c • x) = c • L x) (ω : V [⋀^Fin k]→L[ℝ] F) :
    J.typeProjection p q (L.compContinuousAlternatingMap ω) =
      L.compContinuousAlternatingMap (J.typeProjection p q ω) := by
  have h := aeval_map_basis_compContinuousAlternatingMap (σ := RingHom.id ℂ) (J := J) hL p q ω
  rwa [Polynomial.map_id] at h

/-- A conjugate-linear coefficient map, such as complex conjugation, sends the type-`(p,q)`
projection to the type-`(q,p)` projection. -/
theorem typeProjection_compContinuousAlternatingMap_of_map_smul_conj {L : F →L[ℝ] G}
    (hL : ∀ (c : ℂ) x, L (c • x) = conj c • L x) (ω : V [⋀^Fin k]→L[ℝ] F) :
    J.typeProjection q p (L.compContinuousAlternatingMap ω) =
      L.compContinuousAlternatingMap (J.typeProjection p q ω) := by
  rw [← aeval_map_basis_compContinuousAlternatingMap hL, map_conj_basis]
  rfl

end TypeProjection

section Decomposition

variable [ContinuousConstSMul ℝ F]

section Interior

variable {n : ℕ}

/-- Inserting a vector as the first argument, as a complex-linear map of forms. -/
private def interior (v : V) : (V [⋀^Fin (n + 1)]→L[ℝ] F) →ₗ[ℂ] V [⋀^Fin n]→L[ℝ] F where
  toFun ω := ω.curryLeftTopological v
  map_add' ω ω' := by
    ext w
    simp [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
  map_smul' c ω := by
    ext w
    simp [ContinuousAlternatingMap.curryLeftTopological_apply_apply]

private lemma interior_apply (v : V) (ω : V [⋀^Fin (n + 1)]→L[ℝ] F) (w : Fin n → V) :
    interior v ω w = ω (Matrix.vecCons v w) :=
  ω.curryLeftTopological_apply_apply v w

private lemma interior_neg (v : V) (ω : V [⋀^Fin (n + 1)]→L[ℝ] F) :
    interior (-v) ω = -interior v ω :=
  map_neg (ω.curryLeftTopological) v

/-- Inserting `v` into the derivation of a form. -/
private lemma interior_alternatingDerivation (J : V →L[ℝ] V) (v : V)
    (ω : V [⋀^Fin (n + 1)]→L[ℝ] F) :
    interior v (J.alternatingDerivation ω) =
      J.alternatingDerivation (interior v ω) + interior (J v) ω := by
  ext w
  simp only [interior_apply, alternatingDerivation_apply, ContinuousAlternatingMap.add_apply,
    Fin.sum_univ_succ, Matrix.vecCons, Fin.update_cons_zero, Fin.cons_zero, Fin.cons_succ,
    ← Fin.cons_update]
  exact add_comm _ _

/-- The combination `ι_v - I • ι_{J v}` intertwines the derivation with the derivation
shifted by `I`. -/
private lemma interior_sub_comp_alternatingDerivation {J : V →L[ℝ] V} (hJ : ∀ v, J (J v) = -v)
    (v : V) :
    (interior v - I • interior (J v)) ∘ₗ
        (J.alternatingDerivation : Module.End ℂ (V [⋀^Fin (n + 1)]→L[ℝ] F)) =
      (J.alternatingDerivation + algebraMap ℂ _ I) ∘ₗ (interior v - I • interior (J v)) := by
  ext ω : 1
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    interior_alternatingDerivation, hJ, interior_neg, LinearMap.add_apply,
    Module.algebraMap_end_apply, map_sub, map_smul]
  match_scalars <;> ring_nf
  simp

/-- The combination `ι_v + I • ι_{J v}` intertwines the derivation with the derivation
shifted by `-I`. -/
private lemma interior_add_comp_alternatingDerivation {J : V →L[ℝ] V} (hJ : ∀ v, J (J v) = -v)
    (v : V) :
    (interior v + I • interior (J v)) ∘ₗ
        (J.alternatingDerivation : Module.End ℂ (V [⋀^Fin (n + 1)]→L[ℝ] F)) =
      (J.alternatingDerivation - algebraMap ℂ _ I) ∘ₗ (interior v + I • interior (J v)) := by
  ext ω : 1
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    interior_alternatingDerivation, hJ, interior_neg, LinearMap.sub_apply,
    Module.algebraMap_end_apply, map_add, map_smul]
  match_scalars <;> ring_nf
  simp

end Interior

section Nodal

/-- The derivation of an almost complex structure on `k`-forms is annihilated by the nodal
polynomial of the type eigenvalues. -/
private lemma aeval_alternatingDerivation_nodal (hJ : ∀ v, J (J v) = -v) (k : ℕ) :
    aeval (J.alternatingDerivation : Module.End ℂ (V [⋀^Fin k]→L[ℝ] F))
      (Lagrange.nodal (Finset.antidiagonal k) typeEigenvalue) = 0 := by
  induction k with
  | zero =>
    ext ω v
    simp [Lagrange.nodal_eq, typeEigenvalue, alternatingDerivation_apply]
  | succ n ih =>
    -- A polynomial of degree-`n` type vanishes on degree-`n` forms.
    have hvan : ∀ g : ℂ[X], (∀ pq ∈ Finset.antidiagonal n, g.eval (typeEigenvalue pq) = 0) →
        aeval (J.alternatingDerivation : Module.End ℂ (V [⋀^Fin n]→L[ℝ] F)) g = 0 := by
      intro g hg
      obtain ⟨h, rfl⟩ := nodal_dvd hg
      rw [map_mul, ih, zero_mul]
    set P := Lagrange.nodal (Finset.antidiagonal (n + 1)) typeEigenvalue
    have hP : ∀ pq ∈ Finset.antidiagonal (n + 1), P.eval (typeEigenvalue pq) = 0 :=
      fun pq hpq ↦ Lagrange.eval_nodal_at_node hpq
    -- Shifting the nodes by `±I` sends the degree-`n` eigenvalues to degree-`n + 1` ones, so `P`
    -- annihilates the shifted derivations on degree-`n` forms. By `aeval_comp`, evaluating `P` at
    -- the shifted derivation is evaluating the shifted polynomial at the derivation.
    have hplus : aeval (J.alternatingDerivation + algebraMap ℂ _ I :
        Module.End ℂ (V [⋀^Fin n]→L[ℝ] F)) P = 0 := by
      have h := hvan (P.comp (X + C I)) fun ⟨p, q⟩ hpq ↦ by
        rw [eval_comp]
        convert hP (p + 1, q) (by simpa [Finset.mem_antidiagonal, add_right_comm] using hpq)
          using 2
        simp [typeEigenvalue]
        ring
      simpa [aeval_comp] using h
    have hminus : aeval (J.alternatingDerivation - algebraMap ℂ _ I :
        Module.End ℂ (V [⋀^Fin n]→L[ℝ] F)) P = 0 := by
      have h := hvan (P.comp (X - C I)) fun ⟨p, q⟩ hpq ↦ by
        rw [eval_comp]
        convert hP (p, q + 1) (by simpa [Finset.mem_antidiagonal, ← add_assoc] using hpq) using 2
        simp [typeEigenvalue]
        ring
      simpa [aeval_comp] using h
    ext ω w
    set Ω := aeval (J.alternatingDerivation : Module.End ℂ (V [⋀^Fin (n + 1)]→L[ℝ] F)) P ω
    have hint : ∀ v, interior v Ω = 0 := by
      intro v
      have h₁ := congrArg (fun T ↦ T ω) (Module.End.aeval_comp_of_comp_eq
        (interior_sub_comp_alternatingDerivation (F := F) hJ v).symm P)
      have h₂ := congrArg (fun T ↦ T ω) (Module.End.aeval_comp_of_comp_eq
        (interior_add_comp_alternatingDerivation (F := F) hJ v).symm P)
      simp only [LinearMap.comp_apply] at h₁ h₂
      rw [hplus] at h₁
      rw [hminus] at h₂
      simp only [LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply] at h₁ h₂
      have h₃ : (2 : ℂ) • interior v Ω = 0 := by
        rw [two_smul]
        calc interior v Ω + interior v Ω
            = (interior v Ω - I • interior (J v) Ω) + (interior v Ω + I • interior (J v) Ω) := by
              abel
          _ = 0 := by rw [← h₁, ← h₂, add_zero]
      exact (smul_eq_zero.1 h₃).resolve_left two_ne_zero
    rw [LinearMap.zero_apply, ← Fin.cons_self_tail w]
    simpa [interior_apply, Matrix.vecCons] using congrArg (fun T ↦ T (Fin.tail w)) (hint (w 0))

end Nodal

/-- For `J² = -1`, a polynomial vanishing at every eigenvalue `(p - q) * I` with `p + q = k`
annihilates the derivation induced by `J` on complex-valued `k`-forms. -/
theorem aeval_alternatingDerivation_eq_zero (hJ : ∀ v, J (J v) = -v) {g : ℂ[X]}
    (hg : ∀ p q, p + q = k → g.eval (((p : ℂ) - q) * I) = 0) :
    aeval (J.alternatingDerivation : Module.End ℂ (V [⋀^Fin k]→L[ℝ] F)) g = 0 := by
  obtain ⟨h, rfl⟩ := nodal_dvd fun pq hpq ↦ hg pq.1 pq.2 (Finset.mem_antidiagonal.1 hpq)
  rw [map_mul, aeval_alternatingDerivation_nodal hJ, zero_mul]

variable {ω : V [⋀^Fin k]→L[ℝ] F} {p q p' q' : ℕ}

/-- The derivation acts on the type-`(p,q)` component by `(p - q) * I`. -/
theorem alternatingDerivation_typeProjection (hJ : ∀ v, J (J v) = -v)
    (ω : V [⋀^Fin k]→L[ℝ] F) :
    J.alternatingDerivation (J.typeProjection p q ω) =
      (((p : ℂ) - q) * I) • J.typeProjection p q ω := by
  have h := congrArg (fun T : Module.End ℂ (V [⋀^Fin k]→L[ℝ] F) ↦ T ω)
    (aeval_alternatingDerivation_eq_zero (F := F) hJ
      (g := (X - C (((p : ℂ) - q) * I)) *
        Lagrange.basis (Finset.antidiagonal k) typeEigenvalue (p, q)) fun p' q' hpq' ↦ by
      rcases eq_or_ne (p', q') (p, q) with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simp
      · rw [eval_mul, ← typeEigenvalue_mk,
          Lagrange.eval_basis_of_ne (Ne.symm h) (by simpa using hpq'), mul_zero])
  rw [map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
    Module.algebraMap_end_apply, LinearMap.zero_apply, sub_eq_zero] at h
  exact h

/-- The type-`(p,q)` component of a form has type `(p,q)`. -/
theorem isOfType_typeProjection (hJ : ∀ v, J (J v) = -v) (hpq : p + q = k)
    (ω : V [⋀^Fin k]→L[ℝ] F) : (J.typeProjection p q ω).IsOfType J p q :=
  ⟨hpq, alternatingDerivation_typeProjection hJ ω⟩

/-- The type-`(p,q)` projection of `k`-forms vanishes unless `p + q = k`. -/
@[simp]
theorem typeProjection_eq_zero (hJ : ∀ v, J (J v) = -v) (hpq : p + q ≠ k) :
    (J.typeProjection p q : Module.End ℂ (V [⋀^Fin k]→L[ℝ] F)) = 0 :=
  aeval_alternatingDerivation_eq_zero hJ fun p' q' hpq' ↦
    Lagrange.eval_basis_of_ne (s := Finset.antidiagonal k) (v := typeEigenvalue) (i := (p, q))
      (j := (p', q')) (fun h ↦ hpq (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hpq'))
      (Finset.mem_antidiagonal.2 hpq')

/-- A form has type `(p,q)` exactly when `p + q = k` and its type-`(p,q)` component is the whole
form. -/
theorem isOfType_iff_typeProjection_eq (hJ : ∀ v, J (J v) = -v) :
    ω.IsOfType J p q ↔ p + q = k ∧ J.typeProjection p q ω = ω :=
  ⟨fun h ↦ ⟨h.1, h.typeProjection_self⟩, fun ⟨hpq, h⟩ ↦ h ▸ isOfType_typeProjection hJ hpq ω⟩

/-- The type projections are complementary idempotents. -/
@[simp]
theorem typeProjection_typeProjection (hJ : ∀ v, J (J v) = -v) (ω : V [⋀^Fin k]→L[ℝ] F) :
    J.typeProjection p' q' (J.typeProjection p q ω) =
      if (p', q') = (p, q) then J.typeProjection p q ω else 0 := by
  by_cases hpq : p + q = k
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact (isOfType_typeProjection hJ hpq ω).typeProjection_self
    · exact (isOfType_typeProjection hJ hpq ω).typeProjection_of_ne h
  · simp [typeProjection_eq_zero hJ hpq]

end Decomposition

end ContinuousLinearMap
