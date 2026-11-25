/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation.Coaction
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.MvPolynomial
public import TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra.Basic
public import TauCeti.Algebra.Polynomial.EvenComp
public import TauCeti.Data.ZMod.MonoidHomEquiv
public import TauCeti.Data.ZMod.Two

/-!
# Examples of invariant quotients

This file checks the invariant quotients `X // G = Spec O(X)^G` on three small examples.

* **`𝔾ₘ` on `𝔸²` with weights `1` and `-1`.** The invariants are the polynomials in `x y`, so the
  quotient `𝔸² // 𝔾ₘ` is the line with coordinate `x y`
  (`TauCeti.QuotientExamples.coinvariants_mvPolynomialWeight_one_neg_one_eq_adjoin`).
* **`C₂` on `𝔸¹` by `x ↦ -x`.** Over a ring without additive torsion, such as the `2`-adic
  integers `ℤ_[2]`, the invariants of `R[x]` are `R[x²]`
  (`TauCeti.QuotientExamples.fixedPoints_negX_eq_adjoin`). Over a ring of characteristic two,
  such as `𝔽₂`, the action is trivial, so `x` is invariant
  (`TauCeti.QuotientExamples.fixedPoints_negX_eq_top`), while `x` does not lie in `R[x²]`
  (`Polynomial.X_notMem_adjoin_X_sq`): the natural map `𝔽₂[x²] → 𝔽₂[x]` is not surjective.
  Hence reduction from `ℤ_[2]` to `𝔽₂` does not carry the invariants onto the invariants: the
  image misses `x` (`TauCeti.QuotientExamples.X_notMem_map_fixedPoints_padicInt`). Forming
  invariants does not commute with this non-flat base change. The group `C₂` is not linearly
  reductive over `ℤ_[2]`, and this example does not treat it as reductive.
* **`𝔾ₐ` acting on itself by conjugation.** `𝔾ₐ` is commutative, so conjugation is trivial and
  every function on `𝔾ₐ` is invariant
  (`TauCeti.QuotientExamples.conjugationInvariants_symmetricAlgebra_eq_top`): the conjugation
  quotient `𝔾ₐ // 𝔾ₐ` is `𝔸¹` itself. Every conjugacy class `{x}` is a closed orbit, although
  `𝔾ₐ` is not reductive.
-/

public section

namespace TauCeti.QuotientExamples

/-! ### `𝔾ₘ` acting on `𝔸²` with weights `1` and `-1` -/

section Gm

open _root_.MvPolynomial ComoduleAlgebra

variable (R : Type*) [CommSemiring R]

/-- **`𝔾ₘ` acting on `𝔸²` with weights `1` and `-1`** has invariants the polynomials in `x y`:
the affine quotient `𝔸² // 𝔾ₘ` is the line with coordinate `x y`. -/
theorem coinvariants_mvPolynomialWeight_one_neg_one_eq_adjoin :
    letI := mvPolynomialWeight (R := R)
      (![Multiplicative.ofAdd 1, Multiplicative.ofAdd (-1)] : Fin 2 → Multiplicative ℤ)
    coinvariants R (MonoidAlgebra R (Multiplicative ℤ)) (MvPolynomial (Fin 2) R) =
      Algebra.adjoin R {X 0 * X 1} := by
  let := mvPolynomialWeight (R := R)
    (![Multiplicative.ofAdd 1, Multiplicative.ofAdd (-1)] : Fin 2 → Multiplicative ℤ)
  have hw (s : Fin 2 →₀ ℕ) :
      Finsupp.weight (Additive.ofMul ∘ (![Multiplicative.ofAdd 1, Multiplicative.ofAdd (-1)] :
        Fin 2 → Multiplicative ℤ)) s = Additive.ofMul (Multiplicative.ofAdd ((s 0 : ℤ) - s 1)) := by
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_two]
    apply Additive.toMul.injective
    apply Multiplicative.toAdd.injective
    simp [sub_eq_add_neg]
  refine le_antisymm (fun p hp ↦ ?_) ?_
  · rw [mem_coinvariants_mvPolynomialWeight_iff] at hp
    rw [p.as_sum]
    refine Subalgebra.sum_mem _ fun s hs ↦ ?_
    have hs' : s 0 = s 1 := by
      have := hp (mem_support_iff.1 hs)
      rw [hw, ofMul_eq_zero, ofAdd_eq_one, sub_eq_zero] at this
      exact_mod_cast this
    have hmon : monomial s (p.coeff s) = MvPolynomial.C (p.coeff s) * (X 0 * X 1) ^ s 0 := by
      rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, ← hs', mul_pow]
    rw [hmon]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin rfl) _)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_coinvariants_mvPolynomialWeight_iff]
    intro s hs
    have hX : (X 0 * X 1 : MvPolynomial (Fin 2) R) =
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
      rw [X, X, monomial_mul_monomial, one_mul]
    rw [hX] at hs
    rw [Finset.mem_singleton.1 (support_monomial_subset (mem_support_iff.2 hs)), hw]
    simp

end Gm

/-! ### `C₂` acting on `𝔸¹` by `x ↦ -x` -/

section C2

open Polynomial

variable (R : Type*) [CommRing R]

/-- The group `C₂ = Multiplicative (ZMod 2)` acting on `R[X]` by `X ↦ -X`, as a homomorphism to
the automorphisms of `R[X]`: the generator acts by `p(X) ↦ p(-X)`. -/
noncomputable def negXHom : Multiplicative (ZMod 2) →* (R[X] ≃ₐ[R] R[X]) :=
  (zmodMonoidHomEquiv 2 _).symm ⟨algEquivAevalNegX, algEquivAevalNegX_sq⟩

/-- The action of `C₂ = Multiplicative (ZMod 2)` on `R[X]` by `X ↦ -X`.

This is not an instance: `R[X]` carries other actions of groups of order two. -/
@[implicit_reducible]
noncomputable def negXAction : MulSemiringAction (Multiplicative (ZMod 2)) R[X] :=
  MulSemiringAction.compHom R[X] (negXHom R)

/-- The generator of `C₂` maps to the automorphism `p(X) ↦ p(-X)`. -/
@[simp]
theorem negXHom_ofAdd_one : negXHom R (Multiplicative.ofAdd 1) = algEquivAevalNegX :=
  zmodMonoidHomEquiv_symm_apply_ofAdd_one _

variable {R}

/-- An element of `C₂` acts on `R[X]` through `negXHom`. -/
theorem negXAction_smul_def (g : Multiplicative (ZMod 2)) (p : R[X]) :
    letI := negXAction R
    g • p = negXHom R g p :=
  (MulAction.compHom_smul_def (negXHom R) g p).trans (AlgEquiv.smul_def _ p)

/-- The generator of `C₂` acts on `R[X]` by `p(X) ↦ p(-X)`. -/
theorem negXAction_smul_ofAdd_one (p : R[X]) :
    letI := negXAction R
    Multiplicative.ofAdd (1 : ZMod 2) • p = p.comp (-X) := by
  rw [negXAction_smul_def, negXHom_ofAdd_one, algEquivAevalNegX_apply, comp_eq_aeval]

/-- A polynomial is invariant under `C₂` exactly when it is even: `p(-X) = p(X)`. -/
theorem mem_fixedPoints_negX_iff {p : R[X]} :
    letI := negXAction R
    p ∈ FixedPoints.subring R[X] (Multiplicative (ZMod 2)) ↔ p.comp (-X) = p := by
  let := negXAction R
  refine ⟨fun hp ↦ (negXAction_smul_ofAdd_one p).symm.trans (hp _), fun hp g ↦ ?_⟩
  rcases g.eq_one_or_eq_ofAdd_one with rfl | rfl
  · exact one_smul _ p
  · exact (negXAction_smul_ofAdd_one p).trans hp

/-- **Over a ring without additive torsion, the `C₂`-invariants of `R[X]` are `R[X²]`.** This
applies to the `2`-adic integers `ℤ_[2]`. -/
theorem fixedPoints_negX_eq_adjoin [IsAddTorsionFree R] :
    letI := negXAction R
    FixedPoints.subring R[X] (Multiplicative (ZMod 2)) =
      (Algebra.adjoin R {(X ^ 2 : R[X])}).toSubring := by
  let := negXAction R
  ext p
  rw [mem_fixedPoints_negX_iff, Subalgebra.mem_toSubring, mem_adjoin_X_sq_iff]
  refine ⟨fun hp ↦ ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := exists_eq_comp_X_sq_of_comp_neg_X_eq hp
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    simp [comp_assoc]

/-- **In characteristic two, `C₂` acts trivially on `R[X]`**, since `-X = X`: every polynomial,
in particular `X`, is invariant. -/
theorem fixedPoints_negX_eq_top [CharP R 2] :
    letI := negXAction R
    FixedPoints.subring R[X] (Multiplicative (ZMod 2)) = ⊤ := by
  let := negXAction R
  refine eq_top_iff.2 fun p _ ↦ mem_fixedPoints_negX_iff.2 ?_
  rw [CharTwo.neg_eq, comp_X]

/-- **Invariants do not commute with reduction modulo `2`.** The reduction modulo `2` of the
`C₂`-invariants of `ℤ_[2][X]` lies in `𝔽₂[X²]` and so misses `X`, which is invariant in `𝔽₂[X]`
by `fixedPoints_negX_eq_top`. -/
theorem X_notMem_map_fixedPoints_padicInt :
    letI := negXAction ℤ_[2]
    (X : (ZMod 2)[X]) ∉ (FixedPoints.subring ℤ_[2][X] (Multiplicative (ZMod 2))).map
      (mapRingHom (PadicInt.toZMod (p := 2))) := by
  let := negXAction ℤ_[2]
  rw [fixedPoints_negX_eq_adjoin]
  rintro ⟨q, hq, hqX⟩
  obtain ⟨r, rfl⟩ := mem_adjoin_X_sq_iff.1 (Subalgebra.mem_toSubring.1 hq)
  refine X_notMem_adjoin_X_sq (R := ZMod 2) (mem_adjoin_X_sq_iff.2 ⟨r.map PadicInt.toZMod, ?_⟩)
  simpa [map_comp] using hqX

end C2

/-! ### `𝔾ₐ` acting on itself by conjugation -/

section Ga

variable (R : Type*) [CommRing R]

/-- **Conjugation on `𝔾ₐ` is trivial**: every function on `𝔾ₐ = Spec R[X]` is conjugation
invariant, so the conjugation quotient `𝔾ₐ // 𝔾ₐ` is `𝔸¹`, although `𝔾ₐ` is not reductive. -/
theorem conjugationInvariants_symmetricAlgebra_eq_top :
    HopfAlgebra.conjugationInvariants R (SymmetricAlgebra R R) = ⊤ :=
  (HopfAlgebra.conjugationInvariants_eq_classFunctions R _).trans HopfAlgebra.classFunctions_eq_top

end Ga

end TauCeti.QuotientExamples
