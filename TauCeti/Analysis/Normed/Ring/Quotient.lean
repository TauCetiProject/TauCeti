/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.Topology.Algebra.Algebra
public import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Quotients of normed rings by two-sided ideals

Let `I` be a two-sided ideal of a possibly noncommutative seminormed ring `R`. The quotient ring
`R ⧸ I` carries the quotient norm `‖x‖ = inf {‖a‖ : a ↦ x}`, and this norm is submultiplicative,
so `R ⧸ I` is a seminormed ring; it is a normed ring when `I` is closed, and it is complete when
`R` is (`Submodule.Quotient.completeSpace`). For a normed `𝕜`-algebra the quotient is a normed
`𝕜`-algebra. Mathlib provides these structures for commutative rings; the statements here are
their noncommutative counterparts, as needed for Banach algebras such as operator algebras. A
`TwoSidedIdeal` `J` is covered through its underlying ideal `J.asIdeal`, which is two-sided.

No normalization `‖1‖ = 1` is assumed. The identity of the quotient satisfies
`‖1‖ ≤ ‖(1 : R)‖`, and when geometric series are summable in `R` (for instance when `R` is
complete) and `I` is proper, also `1 ≤ ‖1‖`, because a proper ideal contains no element within
distance `1` of the identity. In particular a quotient of a Banach algebra with `‖1‖ = 1` by a
proper closed ideal again has `‖1‖ = 1`.

The quotient map `Ideal.Quotient.mkA` does not increase norms (`Ideal.Quotient.norm_mkA_le`),
and a continuous algebra homomorphism vanishing on `I` descends to a continuous algebra
homomorphism `Ideal.Quotient.liftA` on `R ⧸ I` with the same bound on representatives. The
continuous first isomorphism theorem says that a continuous surjective homomorphism `f : A → B`
of Banach algebras induces an isomorphism `A ⧸ ker f ≃ B` of topological algebras. Its inverse is
bounded by the open mapping theorem, but it is in general not an isometry: the quotient norm of
`a` is the distance from `a` to `ker f`, which need not be `‖f a‖`.

## Main definitions

* `Ideal.Quotient.seminormedRing`, `Ideal.Quotient.normedRing`,
  `Ideal.Quotient.normedAlgebraOfIsTwoSided`: the quotient norm structures.
* `ContinuousAlgHom.quotientKerEquivOfSurjective`: the continuous first isomorphism theorem for
  Banach algebras.

## Main results

* `Ideal.Quotient.norm_mk_le_norm` and `Ideal.Quotient.exists_norm_mk_lt`: the quotient norm is
  at most the norm of any representative, and is approached by representatives.
* `Ideal.Quotient.norm_one_le` and `Ideal.Quotient.one_le_norm_one`: bounds for the norm of the
  identity of a quotient.
* `Ideal.Quotient.norm_liftA_apply_le`: a norm bound for an induced homomorphism.

Kernels of continuous algebra homomorphisms into normed algebras are closed
(`ContinuousAlgHom.isClosed_ker`), so the quotient by such a kernel is a normed algebra.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §1.3 and §2.1.
* F. F. Bonsall and J. Duncan, *Complete Normed Algebras*, §7.
-/

public section

open Topology

namespace Ideal.Quotient

section SeminormedRing

variable {R : Type*} [SeminormedRing R] (I : Ideal R) [I.IsTwoSided]

/-- The quotient map by a two-sided ideal does not increase norms. -/
theorem norm_mk_le_norm (a : R) : ‖Ideal.Quotient.mk I a‖ ≤ ‖a‖ :=
  Submodule.Quotient.norm_mk_le I a

/-- Every element of the quotient by a two-sided ideal has a representative of norm less than
its quotient norm plus `ε`. -/
theorem exists_norm_mk_lt {I : Ideal R} [I.IsTwoSided] (x : R ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : R, Ideal.Quotient.mk I a = x ∧ ‖a‖ < ‖x‖ + ε :=
  Submodule.Quotient.norm_mk_lt x hε

/-- The quotient of a seminormed ring by a two-sided ideal, with the quotient norm, is a
seminormed ring. -/
noncomputable instance seminormedRing : SeminormedRing (R ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    -- Lifting `x` and `y` to representatives of norm at most `‖x‖ + ε` and `‖y‖ + ε` bounds
    -- `‖x * y‖` by `(‖x‖ + ε) * (‖y‖ + ε)`; let `ε` tend to `0`.
    have h : ∀ ε > 0, ‖x * y‖ ≤ (‖x‖ + ε) * (‖y‖ + ε) := by
      intro ε hε
      obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt x hε
      obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt y hε
      rw [← map_mul]
      calc ‖Ideal.Quotient.mk I (a * b)‖ ≤ ‖a * b‖ := norm_mk_le_norm I _
        _ ≤ ‖a‖ * ‖b‖ := norm_mul_le a b
        _ ≤ _ := mul_le_mul ha.le hb.le (norm_nonneg b) (by positivity)
    have hT : Filter.Tendsto (fun ε : ℝ ↦ (‖x‖ + ε) * (‖y‖ + ε)) (𝓝[>] 0)
        (𝓝 (‖x‖ * ‖y‖)) := by
      have hc : Continuous fun ε : ℝ ↦ (‖x‖ + ε) * (‖y‖ + ε) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall h)

/-- The quotient of a seminormed ring by a closed two-sided ideal is a normed ring. -/
noncomputable instance normedRing [IsClosed (I : Set R)] : NormedRing (R ⧸ I) :=
  { seminormedRing I, Submodule.Quotient.normedAddCommGroup I with }

/-- The identity of a quotient has norm at most the norm of the identity. -/
theorem norm_one_le : ‖(1 : R ⧸ I)‖ ≤ ‖(1 : R)‖ :=
  norm_mk_le_norm I 1

variable (𝕜 : Type*) [NormedField 𝕜] [NormedAlgebra 𝕜 R]

/-- The quotient of a seminormed `𝕜`-algebra by a two-sided ideal is a normed `𝕜`-algebra. -/
noncomputable instance normedAlgebraOfIsTwoSided : NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

end SeminormedRing

section Unit

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] {I : Ideal R} [I.IsTwoSided]

/-- In a normed ring with summable geometric series (for instance a Banach algebra), the identity
of the quotient by a proper two-sided ideal has norm at least `1`. -/
theorem one_le_norm_one (hI : I ≠ ⊤) : 1 ≤ ‖(1 : R ⧸ I)‖ := by
  by_contra! h
  obtain ⟨m, hm, hm1⟩ := exists_norm_mk_lt (1 : R ⧸ I) (sub_pos.2 h)
  -- The representative `m` of `1` lies within distance `1` of `0`, so `1 - m ∈ I` is within
  -- distance `1` of the identity.
  refine hI (I.eq_top_of_norm_lt_one (x := 1 - m) ?_ (by simpa using hm1))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, hm, sub_self]

/-- A quotient of a normed ring with `‖1‖ = 1` and summable geometric series (for instance a
Banach algebra) by a proper two-sided ideal again has `‖1‖ = 1`. -/
instance normOneClass [NormOneClass R] [Nontrivial (R ⧸ I)] : NormOneClass (R ⧸ I) where
  norm_one := le_antisymm ((norm_one_le I).trans_eq norm_one)
    (one_le_norm_one (Ideal.Quotient.nontrivial_iff.mp ‹_›))

end Unit

section ContinuousAlgHom

variable {R A B : Type*} [CommSemiring R] [SeminormedRing A] [Algebra R A] (I : Ideal A)
  [I.IsTwoSided]

/-- The quotient map by a two-sided ideal, as a continuous algebra homomorphism, does not increase
norms. -/
theorem norm_mkA_le (a : A) : ‖mkA R I a‖ ≤ ‖a‖ :=
  (mkA_apply R I a).symm ▸ norm_mk_le_norm I a

/-- A homomorphism bounded by `C` on `A` is bounded by `C` on the quotient. -/
theorem norm_liftA_apply_le [SeminormedRing B] [Algebra R B] (f : A →A[R] B)
    (hI : ∀ a ∈ I, f a = 0) {C : ℝ} (hC : ∀ a, ‖f a‖ ≤ C * ‖a‖) (x : A ⧸ I) :
    ‖liftA I f hI x‖ ≤ C * ‖x‖ := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [liftA_mk]
  rcases le_or_gt C 0 with hC0 | hC0
  · -- For `C ≤ 0` any representative `a` works, since `‖x‖ ≤ ‖a‖`.
    exact (hC a).trans (mul_le_mul_of_nonpos_left (norm_mk_le_norm I a) hC0)
  · -- For `C > 0`, this is the bound for lifts of bounded additive group homomorphisms.
    exact (QuotientAddGroup.norm_lift_apply_le (S := I.toAddSubgroup)
      ((f : A →+ B).mkNormedAddGroupHom C hC) hI (Ideal.Quotient.mk I a)).trans
      (mul_le_mul_of_nonneg_right (AddMonoidHom.mkNormedAddGroupHom_norm_le _ hC0.le hC)
        (norm_nonneg _))

end ContinuousAlgHom

end Ideal.Quotient

namespace ContinuousAlgHom

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A] [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

/-- **The continuous first isomorphism theorem** for Banach algebras: a continuous surjective
algebra homomorphism `f : A → B` induces an isomorphism of topological algebras
`A ⧸ ker f ≃ B`. Its inverse is continuous by the open mapping theorem; it need not be an
isometry. -/
noncomputable def quotientKerEquivOfSurjective (f : A →A[𝕜] B) (hf : Function.Surjective f) :
    (A ⧸ RingHom.ker f) ≃A[𝕜] B where
  toAlgEquiv := Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[𝕜] B)) hf
  continuous_toFun := continuous_quotientKerAlgEquivOfSurjective f hf
  continuous_invFun := by
    let e : (A ⧸ RingHom.ker f) ≃ₗ[𝕜] B :=
      (Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[𝕜] B)) hf).toLinearEquiv
    have he : Continuous e := by
      have h := continuous_quotientKerAlgEquivOfSurjective f hf
      rw [← AlgEquiv.coe_toLinearEquiv] at h
      exact h
    -- The inverse is continuous by the open mapping theorem.
    exact e.continuous_symm he

/-- The underlying algebra isomorphism is the algebraic first isomorphism theorem. -/
@[simp]
theorem toAlgEquiv_quotientKerEquivOfSurjective (f : A →A[𝕜] B) (hf : Function.Surjective f) :
    (quotientKerEquivOfSurjective f hf).toAlgEquiv =
      Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[𝕜] B)) hf :=
  (rfl)

@[simp]
theorem quotientKerEquivOfSurjective_mk (f : A →A[𝕜] B) (hf : Function.Surjective f) (a : A) :
    quotientKerEquivOfSurjective f hf (Ideal.Quotient.mk _ a) = f a :=
  Ideal.quotientKerAlgEquivOfSurjective_mk hf a

@[simp]
theorem quotientKerEquivOfSurjective_symm_apply (f : A →A[𝕜] B) (hf : Function.Surjective f)
    (a : A) : (quotientKerEquivOfSurjective f hf).symm (f a) = Ideal.Quotient.mk _ a :=
  (quotientKerEquivOfSurjective f hf).symm_apply_eq.mpr
    (quotientKerEquivOfSurjective_mk f hf a).symm

end ContinuousAlgHom
