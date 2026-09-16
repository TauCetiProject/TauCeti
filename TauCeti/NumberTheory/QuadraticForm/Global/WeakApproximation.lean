/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization

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

The proof reduces to the scalar statement. After choosing a basis `b` of `V`, the coordinates of
`1 ⊗ x` for `b.baseChange` are the images of the coordinates of `x`, and the coordinate maps are
homeomorphisms for the module topology. Scalar weak approximation at finite and real places is
Artin--Whaples weak approximation, `GlobalNumberFields.weakApproximation_denseRange`, read through
the identification of the completion at a real place with `ℝ`.

This is the form of weak approximation used to approximate vectors of a quadratic space, such as
the coordinates of a vector in a binary summand in the proof of the Hasse--Minkowski theorem.

## Main results

* `TauCeti.NumberField.denseRange_algebraMap_embedding_of_isReal`: `K` is dense in the product of
  finitely many finite completions and finitely many copies of `ℝ` indexed by real places.
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

/-- **Weak approximation at finite and real places.** The diagonal image of a number field is
dense in the product of its completions at finitely many finite places and of `ℝ` at finitely
many real places, embedded through the real embeddings of those places. -/
theorem denseRange_algebraMap_embedding_of_isReal
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset {w : InfinitePlace K // w.IsReal}) :
    DenseRange fun x : K =>
      ((fun v : S => algebraMap K (v.1.adicCompletion K) x),
        fun w : T => embedding_of_isReal w.1.2 x) := by
  classical
  let Sinf : Finset (InfinitePlace K) := T.map (Function.Embedding.subtype _)
  have hmem (w : T) : w.1.1 ∈ Sinf := Finset.mem_map_of_mem _ w.2
  have hreal (u : {u // u ∈ Sinf}) : ∃ h : u.1.IsReal, ⟨u.1, h⟩ ∈ T := by
    obtain ⟨u, hu⟩ := u
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hu
    exact ⟨w.2, hw⟩
  choose hr hrT using hreal
  -- Read each archimedean completion as `ℝ` through its real embedding.
  let r : (∀ u : {u // u ∈ Sinf}, u.1.Completion) → ∀ w : T, ℝ :=
    fun y w => Completion.extensionEmbeddingOfIsReal w.1.2 (y ⟨w.1.1, hmem w⟩)
  have hrc : Continuous r := continuous_pi fun w =>
    (Completion.isometry_extensionEmbeddingOfIsReal w.1.2).continuous.comp (continuous_apply _)
  have hrs : Function.Surjective r := fun t => by
    refine ⟨fun u => (Completion.ringEquivRealOfIsReal (hr u)).symm (t ⟨_, hrT u⟩), ?_⟩
    funext w
    exact (Completion.ringEquivRealOfIsReal w.1.2).apply_symm_apply (t w)
  have hdense := (Prod.map_surjective.mpr ⟨Function.surjective_id, hrs⟩).denseRange.comp
    (GlobalNumberFields.weakApproximation_denseRange S Sinf) (continuous_id.prodMap hrc)
  convert hdense using 1
  funext x
  ext w
  · rw [Function.comp_apply, Prod.map_fst, id]
  · rw [Function.comp_apply, Prod.map_snd]
    simp only [r, Completion.algebraMap_apply]
    exact ((Completion.extensionEmbeddingOfIsReal_coe w.1.2 (WithAbs.toAbs _ x)).trans
      (by simp)).symm

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **Vector weak approximation.** A finite-dimensional vector space over a number field is dense
in the product of its scalar extensions to finitely many finite completions and to `ℝ` along
finitely many real places, for the module topologies on those scalar extensions. -/
theorem denseRange_one_tmul [FiniteDimensional K V]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset {w : InfinitePlace K // w.IsReal})
    [∀ v : HeightOneSpectrum (𝓞 K), TopologicalSpace (v.FiniteScalarExtension (V := V))]
    [∀ v : HeightOneSpectrum (𝓞 K),
      IsModuleTopology (v.adicCompletion K) (v.FiniteScalarExtension (V := V))]
    [∀ w : {w : InfinitePlace K // w.IsReal}, TopologicalSpace (RealScalarExtension (V := V) w)]
    [∀ w : {w : InfinitePlace K // w.IsReal}, IsModuleTopology ℝ
      (RealScalarExtension (V := V) w)] :
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
    (DenseRange.piMap fun _ => denseRange_algebraMap_embedding_of_isReal S T) hΦc
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
    [∀ v : HeightOneSpectrum (𝓞 K), TopologicalSpace (v.FiniteScalarExtension (V := V))]
    [∀ v : HeightOneSpectrum (𝓞 K),
      IsModuleTopology (v.adicCompletion K) (v.FiniteScalarExtension (V := V))]
    [∀ w : {w : InfinitePlace K // w.IsReal}, TopologicalSpace (RealScalarExtension (V := V) w)]
    [∀ w : {w : InfinitePlace K // w.IsReal}, IsModuleTopology ℝ
      (RealScalarExtension (V := V) w)]
    {y : ∀ v : HeightOneSpectrum (𝓞 K), v.FiniteScalarExtension (V := V)}
    {z : ∀ w : {w : InfinitePlace K // w.IsReal}, RealScalarExtension (V := V) w}
    {N : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.FiniteScalarExtension (V := V))}
    {M : ∀ w : {w : InfinitePlace K // w.IsReal}, Set (RealScalarExtension (V := V) w)}
    (hN : ∀ v ∈ S, N v ∈ 𝓝 (y v)) (hM : ∀ w ∈ T, M w ∈ 𝓝 (z w)) :
    ∃ x : V, (∀ v ∈ S, ((1 : v.adicCompletion K) ⊗ₜ[K] x : v.FiniteScalarExtension) ∈ N v) ∧
      ∀ w ∈ T,
        letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
        ((1 : ℝ) ⊗ₜ[K] x : RealScalarExtension w) ∈ M w := by
  have hU : (Set.univ.pi fun v : S => N v.1) ×ˢ (Set.univ.pi fun w : T => M w.1) ∈
      𝓝 ((fun v : S => y v.1), fun w : T => z w.1) :=
    prod_mem_nhds (set_pi_mem_nhds Set.finite_univ fun v _ => hN v.1 v.2)
      (set_pi_mem_nhds Set.finite_univ fun w _ => hM w.1 w.2)
  obtain ⟨-, ⟨x, rfl⟩, hx⟩ := (denseRange_one_tmul (V := V) S T).inter_nhds_nonempty hU
  simp only [Set.mem_prod, Set.mem_univ_pi] at hx
  exact ⟨x, fun v hv => hx.1 ⟨v, hv⟩, fun w hw => hx.2 ⟨w, hw⟩⟩

end TauCeti.NumberField
