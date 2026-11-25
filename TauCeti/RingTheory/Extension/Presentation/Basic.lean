/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import TauCeti.Algebra.Algebra.Hom

/-!
# Algebra homomorphisms out of a presented algebra

Let `P` be a presentation of an `R`-algebra `S`. Every family in an `R`-algebra `T` satisfying
the relations of `P` is the family of values on the generators of an `R`-algebra homomorphism
`S →ₐ[R] T`. This homomorphism is unique: an `R`-algebra homomorphism out of `S` is determined
by its values on the generators (`Algebra.Generators.algHom_ext`, in
`TauCeti.RingTheory.Extension.Generators`).

## Main definitions

* `Algebra.Generators.kerPresentation P`: the presentation using the chosen generators of `P`
  and every element of its kernel as a relation.
* `Algebra.Presentation.lift P x hx`: the `R`-algebra homomorphism out of `S` sending the
  generators of `P` to a family `x` satisfying the relations of `P`.

## Main results

* `Algebra.Presentation.lift_val`: `P.lift x hx` sends the `i`-th generator to `x i`.
* `Algebra.Presentation.range_points_coordinates`: over a base `k`, the coefficient restrictions
  and generator values of the `k`-algebra homomorphisms out of `S` are exactly the solutions of
  the relations of `P`, with the coefficient homomorphism out of `R` varying.
* `Algebra.Presentation.eval_relation_eq_zero`: the generator values of an `R`-point of `S` are a
  zero of every relation.
* `MvPolynomial.map_ker_aeval_eq_ker_aeval_tmul`: base change of the kernel of a surjection
  `R[ι] → S` is the kernel of the corresponding map `B[ι] → B ⊗[R] S`.
* `Algebra.Presentation.ker_baseChange_eq_map`: the kernel of the base change of a presentation is
  the extension of its kernel.
-/

public section

open MvPolynomial TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Generators

/-- The presentation attached to a family of algebra generators, taking every element of the
kernel as a defining relation. No finiteness assumption on the generators or relations is needed. -/
def kerPresentation {ι : Type*} (P : Generators R S ι) :
    Presentation R S ι P.ker where
  toGenerators := P
  relation := Subtype.val
  span_range_relation_eq_ker := by rw [Subtype.range_coe, Ideal.span_eq]

/-- Taking all kernel relations preserves the chosen generators. -/
@[simp]
theorem kerPresentation_toGenerators {ι : Type*} (P : Generators R S ι) :
    P.kerPresentation.toGenerators = P := (rfl)

/-- The relations in the presentation of a generating family are the kernel elements themselves. -/
@[simp]
theorem kerPresentation_relation {ι : Type*} (P : Generators R S ι) (r : P.ker) :
    P.kerPresentation.relation r = r := (rfl)

end Generators

namespace Presentation

variable {ι σ : Type*} (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T]

/-- The `R`-algebra homomorphism out of `S` sending the generators of the presentation `P` to a
family `x` that satisfies the relations of `P`. -/
noncomputable def lift (x : ι → T) (hx : ∀ r, aeval x (P.relation r) = 0) : S →ₐ[R] T :=
  (aeval P.val).liftOfSurjective P.aeval_val_surjective (aeval x) <| by
    -- the kernel of `aeval P.val` is spanned by the relations, which `aeval x` kills
    simp only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom]
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
    exact Set.range_subset_iff.2 hx

/-- `P.lift x hx` sends the `i`-th generator of `P` to `x i`. -/
@[simp]
theorem lift_val (x : ι → T) (hx : ∀ r, aeval x (P.relation r) = 0) (i : ι) :
    P.lift x hx (P.val i) = x i := by
  rw [lift, ← aeval_X (R := R) P.val i, AlgHom.liftOfSurjective_apply, aeval_X]

section Points

variable {k : Type*} [CommSemiring k] [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- Evaluating a polynomial at the coefficient restriction and generator values of a point
agrees with applying the point to its evaluation in the presented algebra. -/
theorem aevalTower_comp_toAlgHom_val {E : Type*} [CommSemiring E] [Algebra k E]
    (x : S →ₐ[k] E) (p : MvPolynomial ι R) :
    aevalTower (x.comp (IsScalarTower.toAlgHom k R S)) (fun i ↦ x (P.val i)) p =
      x (aeval P.val p) := by
  -- The underlying ring hom of `aevalTower` is `eval₂Hom`; its coefficient map here is
  -- `x.toRingHom.comp (algebraMap R S)`, by the definitions of `AlgHom.comp` and `toAlgHom`.
  exact (MvPolynomial.map_aeval P.val x.toRingHom p).symm

variable {E : Type*} [CommRing E] [Algebra k E]

/-- The coordinate image of a presented algebra is the solution set of its defining relations,
with the coefficient point varying over points of the base algebra. -/
theorem range_points_coordinates :
    Set.range (fun x : S →ₐ[k] E ↦
      (x.comp (IsScalarTower.toAlgHom k R S), fun i ↦ x (P.val i))) =
      {z : (R →ₐ[k] E) × (ι → E) | ∀ j, aevalTower z.1 z.2 (P.relation j) = 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ j
    rw [P.aevalTower_comp_toAlgHom_val]
    simp
  · intro hz
    let f := (aeval (R := R) P.val).restrictScalars k
    have hker : RingHom.ker f ≤ RingHom.ker (aevalTower z.1 z.2) := by
      have hfker : RingHom.ker f = P.ker := by
        rw [P.ker_eq_ker_aeval_val]
        exact congrArg RingHom.ker (AlgHom.coe_restrictScalars k (aeval P.val))
      rw [hfker, ← P.span_range_relation_eq_ker]
      exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hz j)
    have hmem : aevalTower z.1 z.2 ∈
        Set.range (fun x : S →ₐ[k] E ↦ x.comp f) := by
      rw [AlgHom.range_comp_right_of_surjective f P.aeval_val_surjective]
      exact hker
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, Prod.ext ?_ (funext fun i ↦ ?_)⟩
    · ext r
      simpa [f] using congrArg (fun g : MvPolynomial ι R →ₐ[k] E ↦ g (C r)) hx
    · simpa [f] using congrArg (fun g : MvPolynomial ι R →ₐ[k] E ↦ g (X i)) hx

end Points

section BaseRing

/-- Over the base ring itself, the coefficient restriction of a point is the identity, so the
tower evaluation at a point is plain evaluation of polynomials. -/
theorem aevalTower_comp_eq_eval (x : S →ₐ[R] R) (p : MvPolynomial ι R) :
    aevalTower (x.comp (IsScalarTower.toAlgHom R R S)) (fun i ↦ x (P.val i)) p =
      eval (fun i ↦ x (P.val i)) p := by
  rw [Subsingleton.elim (x.comp (IsScalarTower.toAlgHom R R S)) (Algebra.ofId R R),
    MvPolynomial.aevalTower_ofId, MvPolynomial.aeval_eq_eval]

/-- The values of a point `x : S →ₐ[R] R` at the generators are a zero of every relation. -/
theorem eval_relation_eq_zero (x : S →ₐ[R] R) (j : σ) :
    eval (fun i ↦ x (P.val i)) (P.relation j) = 0 := by
  rw [← P.aevalTower_comp_eq_eval, P.aevalTower_comp_toAlgHom_val, P.aeval_val_relation,
    map_zero]

end BaseRing

section BaseChange

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The kernel of the base change of a presentation to `K` is the extension of its kernel. -/
theorem ker_baseChange_eq_map (K : Type*) [CommRing K] [Algebra R K] :
    (P.baseChange K).ker = P.ker.map (algebraMap P.Ring (P.baseChange K).Ring) := by
  rw [← P.span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
  exact (P.baseChange K).ker_eq_ker_aeval_val.trans
    (P.span_range_relation_eq_ker_baseChange K).symm

end BaseChange

end Presentation

/-- Base change of the kernel of a surjection from a polynomial ring onto `S`: if `ϕ : R[ι] → S`
sends the variables to `val`, then for every commutative `R`-algebra `B` the kernel of the map
`B[ι] → B ⊗[R] S` sending the variables to `1 ⊗ val i` is the extension of `ker ϕ` to `B[ι]`. -/
theorem _root_.MvPolynomial.map_ker_aeval_eq_ker_aeval_tmul {ι : Type*} {val : ι → S}
    (B : Type*) [CommRing B] [Algebra R B] (hϕ : Function.Surjective (aeval (R := R) val)) :
    (RingHom.ker (aeval (R := R) val)).map (map (algebraMap R B)) =
      RingHom.ker (aeval (R := B) fun v ↦ (1 : B) ⊗ₜ[R] val v :
        MvPolynomial ι B →ₐ[B] B ⊗[R] S) := by
  let PA := (Generators.ofSurjective val hϕ).kerPresentation
  have hval : PA.val = val := by
    rw [Generators.kerPresentation_toGenerators]
    funext i
    exact Generators.ofSurjective_val _ _ i
  have hvalB : (PA.baseChange B).val = fun v ↦ 1 ⊗ₜ[R] val v := by
    rw [Presentation.baseChange_toGenerators]
    ext v
    rw [Generators.baseChange_val, hval]
  simpa only [Generators.ker_eq_ker_aeval_val, hval, hvalB, MvPolynomial.algebraMap_def] using
    (PA.ker_baseChange_eq_map B).symm

end Algebra
