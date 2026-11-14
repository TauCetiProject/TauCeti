/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic

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
