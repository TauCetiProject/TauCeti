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

For normed `𝕜`-algebras, the quotient map is a continuous algebra homomorphism of norm at most `1`
with kernel `I`, and a continuous algebra homomorphism vanishing on `I` descends to a continuous
algebra homomorphism on `R ⧸ I`, with the same bound on representatives. The continuous first
isomorphism theorem says that a continuous surjective homomorphism `f : A → B` of Banach algebras
induces an isomorphism `A ⧸ ker f ≃ B` of topological algebras. Its inverse is bounded by the
open mapping theorem, but it is in general not an isometry: the quotient norm of `a` is the
distance from `a` to `ker f`, which need not be `‖f a‖`.

## Main definitions

* `Ideal.Quotient.seminormedRing`, `Ideal.Quotient.normedRing`,
  `Ideal.Quotient.normedAlgebraOfIsTwoSided`: the quotient norm structures.
* `Ideal.Quotient.mkA`: the quotient map as a continuous algebra homomorphism.
* `Ideal.Quotient.liftA`: the universal property of the quotient for continuous algebra
  homomorphisms.
* `ContinuousAlgHom.quotientKerEquivOfSurjective`: the continuous first isomorphism theorem for
  Banach algebras.

## Main results

* `Ideal.Quotient.norm_one_le` and `Ideal.Quotient.one_le_norm_one`: bounds for the norm of the
  identity of a quotient.
* `Ideal.Quotient.norm_liftA_apply_le`: a norm bound for an induced homomorphism.
* `Ideal.Quotient.continuousAlgHom_ext`: continuous algebra homomorphisms out of `A ⧸ I` are
  determined by their composites with the quotient map.

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

/-- The quotient of a seminormed ring by a two-sided ideal, with the quotient norm, is a
seminormed ring. -/
noncomputable instance seminormedRing : SeminormedRing (R ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    -- Lifting `x` and `y` to representatives of norm at most `‖x‖ + ε` and `‖y‖ + ε` bounds
    -- `‖x * y‖` by `(‖x‖ + ε) * (‖y‖ + ε)`; let `ε` tend to `0`.
    have h : ∀ ε > 0, ‖x * y‖ ≤ (‖x‖ + ε) * (‖y‖ + ε) := by
      intro ε hε
      obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt (S := I) x hε
      obtain ⟨b, rfl, hb⟩ := Submodule.Quotient.norm_mk_lt (S := I) y hε
      rw [Ideal.Quotient.mk_eq_mk, Ideal.Quotient.mk_eq_mk, ← map_mul]
      calc ‖Ideal.Quotient.mk I (a * b)‖ ≤ ‖a * b‖ := Submodule.Quotient.norm_mk_le _ _
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
  Submodule.Quotient.norm_mk_le I 1

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
  obtain ⟨m, hm, hm1⟩ := Submodule.Quotient.norm_mk_lt (S := I) (1 : R ⧸ I) (sub_pos.2 h)
  -- The representative `m` of `1` lies within distance `1` of `0`, so `1 - m ∈ I` is within
  -- distance `1` of the identity.
  refine hI (I.eq_top_of_norm_lt_one (x := 1 - m) ?_ (by simpa using hm1))
  rw [Ideal.Quotient.mk_eq_mk] at hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, hm, sub_self]

/-- A quotient of a normed ring with `‖1‖ = 1` and summable geometric series (for instance a
Banach algebra) by a proper two-sided ideal again has `‖1‖ = 1`. -/
instance normOneClass [NormOneClass R] [Nontrivial (R ⧸ I)] : NormOneClass (R ⧸ I) where
  norm_one := le_antisymm ((norm_one_le I).trans_eq norm_one)
    (one_le_norm_one (Ideal.Quotient.nontrivial_iff.mp ‹_›))

end Unit

section ContinuousAlgHom

variable (R : Type*) {A B : Type*} [CommSemiring R] [SeminormedRing A] [Algebra R A]
  (I : Ideal A) [I.IsTwoSided]

/-- The quotient map onto the quotient by a two-sided ideal, as a continuous algebra
homomorphism. It does not increase norms (`Submodule.Quotient.norm_mk_le`). -/
noncomputable def mkA : A →A[R] A ⧸ I where
  toAlgHom := Ideal.Quotient.mkₐ R I
  cont := I.isQuotientMap_mkQ.continuous

@[simp]
theorem mkA_apply (a : A) : mkA R I a = Ideal.Quotient.mk I a :=
  (rfl)

theorem coe_mkA : ⇑(mkA R I) = Ideal.Quotient.mk I :=
  (rfl)

@[simp]
theorem toAlgHom_mkA : (mkA R I : A →ₐ[R] A ⧸ I) = Ideal.Quotient.mkₐ R I :=
  (rfl)

theorem mkA_surjective : Function.Surjective (mkA R I) :=
  Ideal.Quotient.mk_surjective

@[simp]
theorem ker_mkA : RingHom.ker (mkA R I) = I :=
  Ideal.Quotient.mkₐ_ker R I

variable {R}

section Lift

variable [Semiring B] [TopologicalSpace B] [Algebra R B]

/-- Two continuous algebra homomorphisms out of `A ⧸ I` agree when they agree after composition
with the quotient map. -/
@[ext 1100]
theorem continuousAlgHom_ext {f g : A ⧸ I →A[R] B} (h : f.comp (mkA R I) = g.comp (mkA R I)) :
    f = g :=
  ContinuousAlgHom.coe_inj.mp (Ideal.Quotient.algHom_ext R (congr_arg ContinuousAlgHom.toAlgHom h))

/-- A continuous algebra homomorphism vanishing on a two-sided ideal `I` descends to a continuous
algebra homomorphism on `A ⧸ I`. -/
noncomputable def liftA (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) : A ⧸ I →A[R] B where
  toAlgHom := Ideal.Quotient.liftₐ I f hI
  cont := Ideal.Quotient.continuous_lift I f.continuous hI

@[simp]
theorem toAlgHom_liftA (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) :
    (liftA I f hI : A ⧸ I →ₐ[R] B) = Ideal.Quotient.liftₐ I f hI :=
  (rfl)

@[simp]
theorem liftA_mk (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) (a : A) :
    liftA I f hI (Ideal.Quotient.mk I a) = f a :=
  Ideal.Quotient.lift_mk I (f : A →+* B) hI

@[simp]
theorem liftA_comp_mkA (f : A →A[R] B) (hI : ∀ a ∈ I, f a = 0) :
    (liftA I f hI).comp (mkA R I) = f :=
  ContinuousAlgHom.ext fun a ↦ liftA_mk I f hI a

end Lift

/-- A homomorphism bounded by `C` on `A` is bounded by `C` on the quotient. -/
theorem norm_liftA_apply_le [SeminormedRing B] [Algebra R B] (f : A →A[R] B)
    (hI : ∀ a ∈ I, f a = 0) {C : ℝ} (hC : ∀ a, ‖f a‖ ≤ C * ‖a‖) (x : A ⧸ I) :
    ‖liftA I f hI x‖ ≤ C * ‖x‖ := by
  rcases le_or_gt C 0 with hC0 | hC0
  · -- For `C ≤ 0` any representative `a` works, since `‖x‖ ≤ ‖a‖`.
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [liftA_mk]
    exact (hC a).trans (mul_le_mul_of_nonpos_left (Submodule.Quotient.norm_mk_le I a) hC0)
  · -- For `C > 0`, this is the bound for lifts of bounded additive group homomorphisms.
    exact (QuotientAddGroup.norm_lift_apply_le (S := I.toAddSubgroup)
      ((f : A →+ B).mkNormedAddGroupHom C hC) hI x).trans
      (mul_le_mul_of_nonneg_right (AddMonoidHom.mkNormedAddGroupHom_norm_le _ hC0.le hC)
        (norm_nonneg x))

end ContinuousAlgHom

end Ideal.Quotient

namespace ContinuousAlgHom

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A] [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

omit [CompleteSpace A] [CompleteSpace B] in
/-- The algebraic first isomorphism `A ⧸ ker f ≃ B` is the map `Ideal.Quotient.liftA` induced
by `f`. -/
private theorem coe_quotientKerAlgEquivOfSurjective (f : A →A[𝕜] B)
    (hf : Function.Surjective f) :
    ⇑(Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[𝕜] B)) hf) =
      ⇑(Ideal.Quotient.liftA (RingHom.ker f) f fun _ ↦ id) := by
  funext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientKerAlgEquivOfSurjective_mk]
  exact (Ideal.Quotient.liftA_mk _ f _ a).symm

/-- **The continuous first isomorphism theorem** for Banach algebras: a continuous surjective
algebra homomorphism `f : A → B` induces an isomorphism of topological algebras
`A ⧸ ker f ≃ B`. Its inverse is continuous by the open mapping theorem; it need not be an
isometry. -/
noncomputable def quotientKerEquivOfSurjective (f : A →A[𝕜] B) (hf : Function.Surjective f) :
    (A ⧸ RingHom.ker f) ≃A[𝕜] B where
  toAlgEquiv := Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[𝕜] B)) hf
  continuous_toFun := by
    have h := (Ideal.Quotient.liftA (RingHom.ker f) f fun _ ↦ id).continuous
    rw [← coe_quotientKerAlgEquivOfSurjective f hf] at h
    exact h
  continuous_invFun := by
    let e : (A ⧸ RingHom.ker f) ≃ₗ[𝕜] B :=
      (Ideal.quotientKerAlgEquivOfSurjective (f := (f : A →ₐ[𝕜] B)) hf).toLinearEquiv
    have he : Continuous e := by
      have h := (Ideal.Quotient.liftA (RingHom.ker f) f fun _ ↦ id).continuous
      rw [← coe_quotientKerAlgEquivOfSurjective f hf] at h
      exact h
    -- The inverse is continuous by the open mapping theorem.
    exact e.continuous_symm he

@[simp]
theorem quotientKerEquivOfSurjective_mk (f : A →A[𝕜] B) (hf : Function.Surjective f) (a : A) :
    quotientKerEquivOfSurjective f hf (Ideal.Quotient.mk _ a) = f a :=
  (rfl)

@[simp]
theorem quotientKerEquivOfSurjective_symm_apply (f : A →A[𝕜] B) (hf : Function.Surjective f)
    (a : A) : (quotientKerEquivOfSurjective f hf).symm (f a) = Ideal.Quotient.mk _ a :=
  (quotientKerEquivOfSurjective f hf).symm_apply_eq.mpr
    (quotientKerEquivOfSurjective_mk f hf a).symm

end ContinuousAlgHom
