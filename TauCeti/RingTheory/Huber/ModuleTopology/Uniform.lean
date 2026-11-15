/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.FiniteAlgebra
public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Norm.Projective
public import TauCeti.RingTheory.Trace.Projective
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Topology.Algebra.Algebra
import TauCeti.LinearAlgebra.Charpoly.Projective
import TauCeti.LinearAlgebra.PolynomialFamily
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Finite étale algebras over uniform Tate rings are uniform

Let `A` be a complete Hausdorff Tate ring and `B` a finite projective `A`-algebra with its natural
topology. The trace `Tr_{B/A}` of a power-bounded element of `B` is bounded uniformly: there is a
unit `d` of `A`, depending only on `A` and on a presentation of `B` as a direct summand of some
`Aⁿ`, such that `d · Tr_{B/A}(b) ∈ A°` for every `b ∈ B°`. When `A` is moreover uniform, the
traces of the power-bounded elements of `B` therefore form a bounded subset of `A`
(`TauCeti.Huber.isBounded_image_projectiveTrace_setOf_isPowerBounded`).

If `B` is finite étale over `A`, its trace pairing is perfect
(`Algebra.etale_iff_projectiveTraceForm_bijective`), so every coordinate functional of `B` is of
the form `b ↦ Tr_{B/A}(x b)`. Bounded traces then bound the coordinates of the power-bounded
elements, and `B` is uniform (`TauCeti.Huber.IsUniform.of_isModuleTopology_of_etale`). This makes
the Huber pair `(B, B⁺)` of a finite étale algebra over a complete uniform Tate Huber pair again
uniform. The étale hypothesis cannot be dropped: over a complete nontrivially valued field `K`,
the dual numbers `K[ε]/(ε²)` are finite but not uniform, since every `a ε` is power-bounded.

## The trace estimate

Write `B` as a direct summand of `Aⁿ`. The norm `N_{B/A}(c)` is then a determinant on `Aⁿ` whose
matrix entries are coordinates of `c`, so norms of power-bounded elements are power-bounded
(`TauCeti.Huber.IsPowerBounded.projectiveNorm`). The reversed characteristic polynomial
`Q = det (1 - X b)` of multiplication by `b` has degree at most `n`, coefficient `-Tr_{B/A}(b)` in
degree one, and value `N_{B/A}(1 - t b)` at `t ∈ A`, which lies in `A°` when `b ∈ B°` and
`t ∈ A°`. Cramer's rule at the points `t = ϖ⁰, …, ϖⁿ⁺¹` of a pseudouniformiser `ϖ` recovers
`Tr_{B/A}(b)` from these values up to the Vandermonde determinant
`∏ (ϖʲ - ϖⁱ) = ± ∏ ϖⁱ (1 - ϖʲ⁻ⁱ)`, a unit of the complete ring `A` that does not depend on `b`.

## Main results

* `TauCeti.Huber.isBounded_image_projectiveTrace_setOf_isPowerBounded`: over a complete uniform
  Tate ring, the traces of the power-bounded elements of a finite projective algebra form a
  bounded set.
* `TauCeti.Huber.IsUniform.of_isModuleTopology_of_etale`: a finite étale algebra over a complete
  uniform Tate ring, with its natural topology, is uniform.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, notes for the 2017 Arizona Winter School,
  Lecture 1, §1.10, Lemma 1.10.1 and its proof, whose trace-pairing argument is followed here. The
  bound on traces is obtained by interpolating norms rather than through integrality of `B°`.
-/

public section

open Filter Matrix Polynomial Pointwise Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

/-! ### Traces of power-bounded elements -/

section Trace

variable [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A]
  [T2Space A] [IsTateRing A] [TopologicalSpace B] [IsModuleTopology A B] [Module.Finite A B]

/-- **The trace of a power-bounded element is bounded up to a fixed unit.** For a finite
projective algebra `B` over a complete Hausdorff Tate ring `A`, with its natural topology, there is
a unit `d` of `A` with `d · Tr_{B/A}(b) ∈ A°` for every power-bounded `b ∈ B`. -/
private theorem exists_isUnit_forall_mul_projectiveTrace_mem [Module.Projective A B] :
    ∃ d : A, IsUnit d ∧ ∀ b : B, IsPowerBounded b →
      d * Algebra.projectiveTrace A B b ∈ powerBoundedSubring A := by
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  have : IsHuberRing B := IsHuberRing.of_isModuleTopology (A := A)
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  have hϖA : ϖ ∈ powerBoundedSubring A := mem_powerBoundedSubring.mpr
    (IsPowerBounded.of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent)
  -- the interpolation points `ϖ⁰, …, ϖⁿ⁺¹`, as elements of `A°`
  set v : Fin (n + 2) → powerBoundedSubring A := fun i ↦ ⟨ϖ, hϖA⟩ ^ (i : ℕ)
  have hV : vandermonde (fun i ↦ (v i : A)) =
      (powerBoundedSubring A).subtype.mapMatrix (vandermonde v) := by
    ext i j
    simp [vandermonde_apply]
  refine ⟨(vandermonde fun i ↦ (v i : A)).det, ?_, fun b hb ↦ ?_⟩
  · -- `ϖʲ - ϖⁱ = -(ϖⁱ (1 - ϖʲ⁻ⁱ))` is a unit for `i < j`
    rw [det_vandermonde]
    refine Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun i _ ↦
      Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun j hj ↦ ?_
    have hij : (i : ℕ) < j := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
    have heq : (v j : A) - v i = -(ϖ ^ (i : ℕ) * (1 - ϖ ^ ((j : ℕ) - i))) := by
      simp only [v, SubmonoidClass.coe_pow, mul_sub, mul_one, ← pow_add,
        Nat.add_sub_cancel' hij.le, neg_sub]
    rw [heq]
    exact ((hϖ.isUnit.pow _).mul ((hϖ.isTopologicallyNilpotent.pow
      (Nat.sub_ne_zero_of_lt hij)).isUnit_one_sub)).neg
  · -- `Q = det (1 - X b)` has degree at most `n`, coefficient `-Tr_{B/A}(b)` in degree one, and
    -- value `N_{B/A}(1 - t b) ∈ A°` at every `t ∈ A°`
    set Q := LinearMap.projectiveCharpolyRev (Algebra.lmul A B b) with hQ
    have hdeg : Q.natDegree < n + 2 := by
      rw [hQ, LinearMap.projectiveCharpolyRev_eq_charpolyRev_toMatrix (Pi.basisFun A (Fin n)) π σ h]
      exact (natDegree_charpolyRev_le _).trans_lt (by simp)
    have heval (i : Fin (n + 2)) : Q.eval (v i : A) ∈ powerBoundedSubring A := by
      have hc : IsPowerBounded (1 - (v i : A) • b) := by
        rw [Algebra.smul_def, ← mem_powerBoundedSubring]
        exact sub_mem (one_mem _) (mul_mem (mem_powerBoundedSubring.mpr
          (IsPowerBounded.algebraMap_of_isModuleTopology (mem_powerBoundedSubring.mp (v i).2)))
          (mem_powerBoundedSubring.mpr hb))
      rw [hQ, LinearMap.eval_projectiveCharpolyRev, ← map_one (Algebra.lmul A B), ← map_smul,
        ← map_sub, ← Algebra.projectiveNorm_apply]
      exact mem_powerBoundedSubring.mpr hc.projectiveNorm
    -- Cramer's rule at the points `v i` recovers `det V · Tr_{B/A}(b)` from these values
    have hcoeff : Q.coeff 1 = -Algebra.projectiveTrace A B b := by
      rw [hQ, LinearMap.coeff_projectiveCharpolyRev_one, Algebra.projectiveTrace_apply]
    have hcramer := det_vandermonde_smul_eq_sum_adjugate_smul (fun i ↦ (v i : A)) Q.coeff 1
    simp only [Fin.val_one, smul_eq_mul, hcoeff] at hcramer
    rw [← neg_neg (Algebra.projectiveTrace A B b), mul_neg, hcramer]
    refine neg_mem (sum_mem fun i _ ↦ mul_mem ?_ ?_)
    · rw [hV, ← RingHom.map_adjugate]
      exact (adjugate (vandermonde v) 1 i).2
    · have hi := heval i
      rw [eval_eq_sum_range' hdeg] at hi
      simpa [mul_comm] using hi

/-- **Traces of power-bounded elements are bounded.** For a finite projective algebra `B` over a
complete Hausdorff uniform Tate ring `A`, with its natural topology, the traces `Tr_{B/A}(b)` of
the power-bounded elements `b ∈ B` form a bounded subset of `A`. -/
theorem isBounded_image_projectiveTrace_setOf_isPowerBounded [IsUniform A]
    [Module.Projective A B] :
    IsBounded (Algebra.projectiveTrace A B '' {b : B | IsPowerBounded b}) := by
  obtain ⟨d, hd, h⟩ := exists_isUnit_forall_mul_projectiveTrace_mem (A := A) (B := B)
  refine ((isBounded_singleton (↑hd.unit⁻¹ : A)).mul
    IsUniform.isBounded_powerBoundedSubring).subset ?_
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨_, rfl, _, h b hb, by simp [← mul_assoc]⟩

end Trace

/-! ### Uniformity of finite étale algebras -/

variable [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A]
  [T2Space A] [IsTateRing A] [IsUniform A] [TopologicalSpace B] [IsModuleTopology A B]
  [Module.Finite A B]

/-- **Finite étale algebras over complete uniform Tate rings are uniform.** If `A` is a complete
Hausdorff uniform Tate ring and `B` a finite étale `A`-algebra with its natural topology, then the
power-bounded elements of `B` form a bounded set. -/
theorem IsUniform.of_isModuleTopology_of_etale [Algebra.Etale A B] : IsUniform B := by
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  have : IsTateRing B := IsTateRing.of_isModuleTopology (A := A)
  have : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  obtain ⟨s, hfs⟩ := Module.projective_lifting_property f LinearMap.id hf
  -- the trace pairing is perfect, so each coordinate `b ↦ s b k` is `b ↦ Tr_{B/A}(x k * b)`
  choose x hx using fun k : Fin n ↦
    ((Algebra.etale_iff_projectiveTraceForm_bijective (R := A) (S := B)).mp ‹_›).2
      (LinearMap.proj k ∘ₗ s)
  -- a power `ϖ ^ N` of a pseudouniformiser of `A` moves every `x k` into `B°`
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  have hev (k : Fin n) : ∀ᶠ N in atTop, ϖ ^ N • x k ∈ powerBoundedSubring B := by
    have h := ((hϖ.isTopologicallyNilpotent.map (continuous_algebraMap A B)).mul_const (x k))
    rw [zero_mul] at h
    simpa [Algebra.smul_def] using
      h.eventually_mem ((isOpen_powerBoundedSubring B).mem_nhds (zero_mem _))
  obtain ⟨N, hN⟩ := (eventually_all.mpr hev).exists
  -- so the coordinates of `b ∈ B°` lie in the bounded set `S = ϖ ^ (-N) · Tr_{B/A}(B°)`
  set u := hϖ.isUnit.unit
  set S : Set A :=
    {((u⁻¹ : Aˣ) : A) ^ N} * Algebra.projectiveTrace A B '' {b : B | IsPowerBounded b}
  have hS : IsBounded S :=
    (isBounded_singleton _).mul isBounded_image_projectiveTrace_setOf_isPowerBounded
  have hcoord (b : B) (hb : IsPowerBounded b) (k : Fin n) : s b k ∈ S := by
    refine ⟨_, rfl, _, ⟨ϖ ^ N • x k * b, ?_, rfl⟩, ?_⟩
    · exact mem_powerBoundedSubring.mp (mul_mem (hN k) (mem_powerBoundedSubring.mpr hb))
    · have hxk := LinearMap.congr_fun (hx k) b
      simp only [Algebra.projectiveTraceForm_apply, LinearMap.comp_apply, LinearMap.proj_apply]
        at hxk
      rw [smul_mul_assoc, map_smul, hxk, smul_eq_mul]
      simp [u, ← mul_assoc, ← mul_pow]
  -- and every `b ∈ B°` is `∑ k, s b k • f eₖ`, a sum of elements of a bounded set
  have hS' : IsBounded (⋃ k : Fin n, algebraMap A B '' S * {f (Pi.single k 1)}) :=
    isBounded_iUnion fun k ↦ (hS.image_of_isTateRing
      (continuous_algebraMap A B).continuousAt).mul (isBounded_singleton _)
  refine isUniform_iff.mpr <| hS'.addSubgroupClosure.subset fun b hb ↦ ?_
  have hsum : b = ∑ k, s b k • f (Pi.single k 1) := by
    have hb' : f (s b) = b := LinearMap.congr_fun hfs b
    conv_lhs => rw [← hb', ← Finset.univ_sum_single (s b)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  rw [hsum]
  refine sum_mem fun k _ ↦ AddSubgroup.subset_closure (Set.mem_iUnion.mpr ⟨k, ?_⟩)
  rw [Algebra.smul_def]
  exact Set.mul_mem_mul ⟨_, hcoord b hb k, rfl⟩ rfl

end TauCeti.Huber
