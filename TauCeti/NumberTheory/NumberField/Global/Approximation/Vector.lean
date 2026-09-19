/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.NumberField.Global.Places.ScalarExtension

/-!
# Weak approximation for vectors at finite and real places

Let `K` be a number field and `V` a finite-dimensional `K`-vector space. For finitely many finite
places `v` and real places `w`, one global vector `x : V` can be chosen so that its images
`1 ⊗ x` in the localized spaces `K_v ⊗[K] V` and `ℝ ⊗[K] V` lie in arbitrarily prescribed
neighbourhoods of arbitrary local vectors. The real spaces are the scalar extensions along the
embedding of the real place, exactly as in the localization of quadratic forms.

The localized spaces carry no topology of their own. The results here assume only that each one
carries its module topology (`IsModuleTopology`), which is the topology of coordinates with respect
to any basis. The statements are therefore independent of a choice of basis, and they apply to
`moduleTopology` as well as to the usual topology of a finite-dimensional real vector space.

These results are the vector form of the scalar statement
`GlobalNumberFields.denseRange_algebraMap_embedding_of_isReal`, Artin--Whaples weak approximation
at finite and real places, which is the case `V = K`.

This is the form of weak approximation used to approximate vectors of a quadratic space, such as
the coordinates of a vector in a binary summand in the proof of the Hasse--Minkowski theorem.

## Main results

* `TauCeti.NumberField.denseRange_one_tmul`: `V` is dense in the corresponding product of localized
  spaces.
* `TauCeti.NumberField.exists_one_tmul_mem_of_mem_nhds`: one global vector lies in prescribed
  neighbourhoods at finitely many finite and real places.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1973), §66, where weak approximation of
  vectors enters the proof of the Hasse--Minkowski theorem.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, for weak
  approximation in a number field.
-/

public section

open Filter IsDedekindDomain NumberField NumberField.InfinitePlace Topology
open scoped TensorProduct

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **Vector weak approximation.** A finite-dimensional vector space over a number field is dense
in the product of its scalar extensions to finitely many finite completions and to `ℝ` along
finitely many real places, for the module topologies on those scalar extensions. -/
theorem denseRange_one_tmul [FiniteDimensional K V]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset {w : InfinitePlace K // w.IsReal})
    [∀ v : S, TopologicalSpace (v.1.FiniteScalarExtension (V := V))]
    [∀ v : S, IsModuleTopology (v.1.adicCompletion K) (v.1.FiniteScalarExtension (V := V))]
    [∀ w : T, TopologicalSpace (RealScalarExtension (V := V) w.1)]
    [∀ w : T, IsModuleTopology ℝ (RealScalarExtension (V := V) w.1)] :
    DenseRange fun x : V =>
      ((fun v : S => ((1 : v.1.adicCompletion K) ⊗ₜ[K] x : v.1.FiniteScalarExtension)),
        fun w : T =>
          letI : Algebra K ℝ := (embedding_of_isReal w.1.2).toAlgebra
          ((1 : ℝ) ⊗ₜ[K] x : RealScalarExtension w.1)) := by
  classical
  let b := Module.finBasis K V
  let P := (∀ v : S, v.1.adicCompletion K) × ∀ w : T, ℝ
  -- Assemble local vectors from their coordinates with respect to `b`.
  let Φ : (Fin (Module.finrank K V) → P) →
      (∀ v : S, v.1.FiniteScalarExtension (V := V)) × ∀ w : T, RealScalarExtension (V := V) w.1 :=
    fun c =>
      (fun v => (b.baseChange (v.1.adicCompletion K)).equivFun.symm fun i => (c i).1 v,
        fun w =>
          letI : Algebra K ℝ := (embedding_of_isReal w.1.2).toAlgebra
          (b.baseChange ℝ).equivFun.symm fun i => (c i).2 w)
  have hΦc : Continuous Φ := by
    refine .prodMk (continuous_pi fun v => ?_) (continuous_pi fun w => ?_)
    · have := IsModuleTopology.toContinuousAdd (v.1.adicCompletion K)
        (v.1.FiniteScalarExtension (V := V))
      exact (IsModuleTopology.continuous_of_linearMap
        (b.baseChange (v.1.adicCompletion K)).equivFun.symm.toLinearMap).comp
        (continuous_pi fun i => ((continuous_apply v).comp continuous_fst).comp
          (continuous_apply i))
    · let : Algebra K ℝ := (embedding_of_isReal w.1.2).toAlgebra
      have := IsModuleTopology.toContinuousAdd ℝ (RealScalarExtension (V := V) w.1)
      exact (IsModuleTopology.continuous_of_linearMap
        (b.baseChange ℝ).equivFun.symm.toLinearMap).comp
        (continuous_pi fun i => ((continuous_apply w).comp continuous_snd).comp
          (continuous_apply i))
  have hΦs : Function.Surjective Φ := fun y => by
    refine ⟨fun i => (fun v => (b.baseChange (v.1.adicCompletion K)).equivFun (y.1 v) i,
      fun w =>
        letI : Algebra K ℝ := (embedding_of_isReal w.1.2).toAlgebra
        (b.baseChange ℝ).equivFun (y.2 w) i), ?_⟩
    ext v <;> simp only [Φ, LinearEquiv.symm_apply_apply]
  have hcoord := hΦs.denseRange.comp
    (DenseRange.piMap fun _ =>
      GlobalNumberFields.denseRange_algebraMap_embedding_of_isReal S T) hΦc
  rw [DenseRange, ← b.equivFun.surjective.range_comp] at hcoord
  rw [DenseRange]
  convert hcoord using 2
  funext x
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  -- In both components, the coordinates of `1 ⊗ x` are the images of the coordinates of `x`.
  · simp only [Φ, Pi.map, Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply]
    funext i
    simp [Algebra.smul_def]
  · let : Algebra K ℝ := (embedding_of_isReal w.1.2).toAlgebra
    simp only [Φ, Pi.map, Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply]
    funext i
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- **Vector weak approximation, neighbourhood form.** Given local vectors at finitely many finite
and real places and a neighbourhood of each, one global vector of a finite-dimensional space over
a number field has its localization in every one of these neighbourhoods. The localized spaces
carry their module topologies. -/
theorem exists_one_tmul_mem_of_mem_nhds [FiniteDimensional K V]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset {w : InfinitePlace K // w.IsReal})
    [∀ v : S, TopologicalSpace (v.1.FiniteScalarExtension (V := V))]
    [∀ v : S, IsModuleTopology (v.1.adicCompletion K) (v.1.FiniteScalarExtension (V := V))]
    [∀ w : T, TopologicalSpace (RealScalarExtension (V := V) w.1)]
    [∀ w : T, IsModuleTopology ℝ (RealScalarExtension (V := V) w.1)]
    {y : ∀ v : S, v.1.FiniteScalarExtension (V := V)}
    {z : ∀ w : T, RealScalarExtension (V := V) w.1}
    {N : ∀ v : S, Set (v.1.FiniteScalarExtension (V := V))}
    {M : ∀ w : T, Set (RealScalarExtension (V := V) w.1)}
    (hN : ∀ v, N v ∈ 𝓝 (y v)) (hM : ∀ w, M w ∈ 𝓝 (z w)) :
    ∃ x : V, (∀ v : S, ((1 : v.1.adicCompletion K) ⊗ₜ[K] x : v.1.FiniteScalarExtension) ∈ N v) ∧
      ∀ w : T,
        letI : Algebra K ℝ := (embedding_of_isReal w.1.2).toAlgebra
        ((1 : ℝ) ⊗ₜ[K] x : RealScalarExtension w.1) ∈ M w := by
  have hU : (Set.univ.pi N) ×ˢ (Set.univ.pi M) ∈ 𝓝 (y, z) :=
    prod_mem_nhds (set_pi_mem_nhds Set.finite_univ fun v _ => hN v)
      (set_pi_mem_nhds Set.finite_univ fun w _ => hM w)
  obtain ⟨-, ⟨x, rfl⟩, hx⟩ := (denseRange_one_tmul (V := V) S T).inter_nhds_nonempty hU
  simp only [Set.mem_prod, Set.mem_univ_pi] at hx
  exact ⟨x, hx.1, hx.2⟩

end TauCeti.NumberField
