/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Recovering covariant intertwiners from integrated forms

A bounded operator intertwining both members of two covariant pairs also intertwines their
vector-integrated forms. Conversely, for a measure positive on nonempty open sets, the integrated
intertwining identities determine the mixed operators `π(a) U(g)`. They therefore recover the
coefficient intertwiner, and recover the group intertwiner when the source coefficient
representation is nondegenerate. In particular, a nondegenerate covariant pair is uniquely
determined by its integrated form on compactly supported continuous coefficient functions.

The converse uses scalar compact-support tests of matrix coefficients, rather than inversion of
Haar measure or a norm-continuous operator integral. The measure need only be finite on compact
sets and positive on nonempty open sets; neither left invariance, separability nor σ-finiteness
is needed. The coefficient algebras may be nonunital and the Hilbert spaces may be zero.

The conventions and correspondence follow Dana Williams, *Crossed Products of C*-Algebras*,
Chapter 2. We use `CovariantRepresentation.integratedOperator` for vector integration and
`NonUnitalStarAlgHom.IsNondegenerate` for density of coefficient-generated vectors.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H K : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {α : CStarAction G A} (P : CovariantRepresentation α H) (Q : CovariantRepresentation α K)
  [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] (T : H →L[ℂ] K)

/-- An intertwiner of both members of covariant pairs intertwines their integrated forms. -/
theorem comp_integratedOperator
    (hπ : ∀ a, T.comp (P.coefficient a) = (Q.coefficient a).comp T)
    (hU : ∀ g, T.comp (P.group g) = (Q.group g).comp T) (f : C_c(G, A)) :
    T.comp (P.integratedOperator μ f) = (Q.integratedOperator μ f).comp T := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, integratedOperator_apply]
  rw [← T.integral_comp_comm (P.integrable_integrand μ f v)]
  congr 1 with g
  calc T (P.coefficient (f g) (P.group g v))
      = Q.coefficient (f g) (T (P.group g v)) :=
        congrArg (fun S : H →L[ℂ] K => S (P.group g v)) (hπ (f g))
    _ = Q.coefficient (f g) (Q.group g (T v)) :=
      congrArg (Q.coefficient (f g)) (congrArg (fun S : H →L[ℂ] K => S v) (hU g))

section Recovery

variable [R1Space G] [LocallyCompactSpace G] [μ.IsOpenPosMeasure]

/-- Intertwining all integrated operators recovers intertwining of the mixed operators
`π(a) U(g)`, even when the coefficient representation is degenerate. -/
theorem comp_coefficient_mul_group_of_comp_integratedOperator
    (hT : ∀ f : C_c(G, A),
      T.comp (P.integratedOperator μ f) = (Q.integratedOperator μ f).comp T)
    (a : A) (g : G) :
    T.comp (P.coefficient a * P.group g) = (Q.coefficient a * Q.group g).comp T := by
  ext v
  apply ext_inner_left ℂ
  intro w
  let k : G → ℂ := fun s =>
    ⟪w, T (P.coefficient a (P.group s v)) - Q.coefficient a (Q.group s (T v))⟫_ℂ
  have hkc : Continuous k := by
    exact continuous_const.inner
      ((T.continuous.comp ((P.coefficient a).continuous.comp (P.continuous_orbit v))).sub
        ((Q.coefficient a).continuous.comp (Q.continuous_orbit (T v))))
  have hk0 : k = 0 := hkc.eq_zero_of_forall_integral_mul_eq_zero (μ := μ) fun φ => by
    let f : C_c(G, A) := φ.compLeft ⟨fun z : ℂ => z • a, by fun_prop⟩
    have hf (s : G) : f s = φ s • a :=
       CompactlySupportedContinuousMap.compLeft_apply (by simp) φ s
    have h := congrArg (fun S : H →L[ℂ] K => ⟪w, S v⟫_ℂ) (hT f)
    simp only [ContinuousLinearMap.comp_apply, integratedOperator_apply] at h
    rw [← T.integral_comp_comm (P.integrable_integrand μ f v),
      ← integral_inner (T.integrable_comp (P.integrable_integrand μ f v)),
      ← integral_inner (Q.integrable_integrand μ f (T v))] at h
    rw [← sub_eq_zero, ← integral_sub
      ((T.integrable_comp (P.integrable_integrand μ f v)).const_inner w)
      ((Q.integrable_integrand μ f (T v)).const_inner w)] at h
    simpa only [hf, map_smul, smul_apply, inner_smul_right,
      k, inner_sub_right, mul_sub] using h
  have h := congrFun hk0 g
  simpa only [k, Pi.zero_apply, inner_sub_right, sub_eq_zero,
    ContinuousLinearMap.comp_apply, mul_apply_eq_comp] using h

/-- The coefficient intertwiner can always be recovered from the integrated form. -/
theorem comp_coefficient_of_comp_integratedOperator
    (hT : ∀ f : C_c(G, A),
      T.comp (P.integratedOperator μ f) = (Q.integratedOperator μ f).comp T) (a : A) :
    T.comp (P.coefficient a) = (Q.coefficient a).comp T := by
  simpa using P.comp_coefficient_mul_group_of_comp_integratedOperator Q μ T hT a 1

/-- For a nondegenerate source coefficient representation, integrated intertwining recovers
both the coefficient and group intertwiners. -/
theorem comp_integratedOperator_iff (hP : P.coefficient.IsNondegenerate) :
    (∀ f : C_c(G, A),
      T.comp (P.integratedOperator μ f) = (Q.integratedOperator μ f).comp T) ↔
    (∀ a, T.comp (P.coefficient a) = (Q.coefficient a).comp T) ∧
      (∀ g, T.comp (P.group g) = (Q.group g).comp T) := by
  refine ⟨fun hT => ⟨P.comp_coefficient_of_comp_integratedOperator Q μ T hT, fun g => ?_⟩,
    fun ⟨hπ, hU⟩ f => P.comp_integratedOperator Q μ T hπ hU f⟩
  refine ContinuousLinearMap.ext_on
    (NonUnitalStarAlgHom.isNondegenerate_iff_dense.1 hP) fun x hx => ?_
  obtain ⟨a, v, rfl⟩ := Set.mem_iUnion.1 hx
  have hπ := P.comp_coefficient_of_comp_integratedOperator Q μ T hT a
  have hmix := P.comp_coefficient_mul_group_of_comp_integratedOperator Q μ T hT (α g a) g
  simp only [ContinuousLinearMap.comp_apply]
  calc T (P.group g (P.coefficient a v))
      = T (P.coefficient (α g a) (P.group g v)) := congrArg T (P.covariance g a v)
    _ = Q.coefficient (α g a) (Q.group g (T v)) :=
      congrArg (fun S : H →L[ℂ] K => S v) hmix
    _ = Q.group g (Q.coefficient a (T v)) := (Q.covariance g a (T v)).symm
    _ = Q.group g (T (P.coefficient a v)) :=
      congrArg (Q.group g) (congrArg (fun S : H →L[ℂ] K => S v) hπ).symm

/-- A covariant pair with nondegenerate coefficient representation is determined by its
integrated form on compactly supported continuous functions. -/
theorem eq_of_integratedOperator_eq {R : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate)
    (h : P.integratedOperator μ = R.integratedOperator μ) : P = R := by
  have hT : ∀ f : C_c(G, A),
      (ContinuousLinearMap.id ℂ H).comp (P.integratedOperator μ f) =
        (R.integratedOperator μ f).comp (ContinuousLinearMap.id ℂ H) := by
    intro f
    simp [h]
  obtain ⟨hπ, hU⟩ := (P.comp_integratedOperator_iff R μ (ContinuousLinearMap.id ℂ H) hP).1 hT
  exact ext (NonUnitalStarAlgHom.ext fun a => by simpa using hπ a)
    (DFunLike.ext _ _ fun g => by simpa using hU g)

end Recovery

end TauCeti.CStarAction.CovariantRepresentation
