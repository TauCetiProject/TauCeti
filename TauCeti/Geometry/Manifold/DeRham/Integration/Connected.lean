/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Localization
import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.CoordinateDomain

/-!
# Top compactly supported cohomology of connected oriented manifolds

Top compactly supported cohomology on a Euclidean coordinate domain is determined by
integration. Classes of integral one from two overlapping coordinate domains have the
same image in any larger open set: a normalized bump form in the intersection compares
them. Connectedness then identifies all the local generators, and a finite decomposition
of a compactly supported class proves injectivity of integration.
Thus `integralEquiv` identifies top compactly supported cohomology of a nonempty connected
oriented boundaryless manifold with the scalars. No positive-dimensional assumption is needed.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 17,
  the integration theorem for compactly supported top-degree cohomology.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public noncomputable section

open Set TopologicalSpace Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.compactlySupportedDeRhamCohomology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M] {n : ℕ}

/-- Classes with the same integral on overlapping Euclidean coordinate domains have the same
extension to any larger open set. The intersection need not itself be a coordinate domain
or connected. -/
theorem extendByZero_eq_of_integral_eq_of_nonempty_inter
    (o : Manifold.Orientation I M (Fin n)) {U V W : Opens M}
    [SigmaCompactSpace U] [SigmaCompactSpace V]
    (hU : U ≤ W) (hV : V ≤ W)
    (Φ : E ≃ₘ⟮𝓘(ℝ, E), I⟯ U) (Ψ : E ≃ₘ⟮𝓘(ℝ, E), I⟯ V)
    (hUV : ((U : Set M) ∩ V).Nonempty)
    (a : compactlySupportedDeRhamCohomology I U n)
    (b : compactlySupportedDeRhamCohomology I V n)
    (hab : integral (o.restrict U) a = integral (o.restrict V) b) :
    extendByZero hU n a = extendByZero hV n b := by
  have : SecondCountableTopology U := Φ.toHomeomorph.symm.secondCountableTopology
  have hi := Topology.IsOpenEmbedding.inclusion (inf_le_left : U ⊓ V ≤ U)
    ((U ⊓ V).isOpen.preimage (continuous_subtype_val : Continuous (Subtype.val : U → M)))
  have : SecondCountableTopology (U ⊓ V : Opens M) := hi.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace U := Φ.toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (U ⊓ V : Opens M) := hi.locallyCompactSpace
  have : SigmaCompactSpace (U ⊓ V : Opens M) := inferInstance
  obtain ⟨x, hxU, hxV⟩ := hUV
  have : Nonempty (U ⊓ V : Opens M) := ⟨⟨x, hxU, hxV⟩⟩
  -- The intersection supplies a common class of integral one; Euclidean injectivity
  -- compares its two extensions with the classes being given.
  obtain ⟨d, hd⟩ := surjective_integral (o.restrict (U ⊓ V)) 1
  have ha : a = integral (o.restrict U) a •
      extendByZero (inf_le_left : U ⊓ V ≤ U) n d :=
    (bijective_integral_of_diffeomorph_normedSpace (o.restrict U) Φ).injective
      (by simp [hd])
  have hb : b = integral (o.restrict U) a •
      extendByZero (inf_le_right : U ⊓ V ≤ V) n d :=
    (bijective_integral_of_diffeomorph_normedSpace (o.restrict V) Ψ).injective
      (by simp [hab, hd])
  rw [ha, hb, map_smul, map_smul, extendByZero_extendByZero, extendByZero_extendByZero]

/-- Normalized classes from a coordinate cover have the same image on a connected union. -/
private theorem extendByZero_normalized_eq_of_cover
    (o : Manifold.Orientation I M (Fin n)) {W : Opens M}
    [PreconnectedSpace W] {ι : Type*} (U : ι → Opens M)
    [∀ i, SigmaCompactSpace (U i)] (hU : ∀ i, U i ≤ W) (hcover : W ≤ iSup U)
    (Φ : ∀ i, E ≃ₘ⟮𝓘(ℝ, E), I⟯ U i)
    (b : ∀ i, compactlySupportedDeRhamCohomology I (U i) n)
    (hb : ∀ i, integral (o.restrict (U i)) (b i) = 1) (i j : ι) :
    extendByZero (hU i) n (b i) = extendByZero (hU j) n (b j) := by
  classical
  have hex (x : W) : ∃ i, (x : M) ∈ U i := by
    simpa only [Opens.mem_iSup] using hcover x.property
  choose k hk using hex
  let g (x : W) := extendByZero (hU (k x)) n (b (k x))
  have hg (x : W) (i : ι) (hx : (x : M) ∈ U i) :
      g x = extendByZero (hU i) n (b i) :=
    extendByZero_eq_of_integral_eq_of_nonempty_inter o (hU _) (hU _) (Φ _) (Φ _)
      ⟨x, hk x, hx⟩ _ _ (by rw [hb, hb])
  have hgc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [((U (k x)).isOpen.preimage continuous_subtype_val).mem_nhds (hk x)] with y hy
    exact hg y (k x) hy
  exact (hg ⟨Φ i 0, hU i (Φ i 0).property⟩ i (Φ i 0).property).symm.trans
    ((hgc.apply_eq_of_preconnectedSpace _ _).trans
      (hg ⟨Φ j 0, hU j (Φ j 0).property⟩ j (Φ j 0).property))

/-- Integration is injective on a preconnected open set covered by domains diffeomorphic to
its model space. The cover may be infinite, and its intersections need not be connected. -/
theorem injective_integral_of_cover
    (o : Manifold.Orientation I M (Fin n)) {W : Opens M}
    [SigmaCompactSpace W] [PreconnectedSpace W] {ι : Type*} (U : ι → Opens M)
    [∀ i, SigmaCompactSpace (U i)] (hU : ∀ i, U i ≤ W) (hcover : W ≤ iSup U)
    (Φ : ∀ i, E ≃ₘ⟮𝓘(ℝ, E), I⟯ U i) : Function.Injective (integral (o.restrict W)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  by_cases hι : Nonempty ι
  · let _ := hι
    have hex (i : ι) : ∃ b : compactlySupportedDeRhamCohomology I (U i) n,
        integral (o.restrict (U i)) b = 1 := by
      have : Nonempty (U i) := ⟨Φ i 0⟩
      exact surjective_integral (o.restrict (U i)) 1
    choose b hb using hex
    obtain ⟨s, a, ha⟩ := exists_sum_smul_extendByZero o U hU hcover Φ b hb c
    let i₀ : ι := Classical.choice hι
    have hgen := extendByZero_normalized_eq_of_cover o U hU hcover Φ b hb
    have heq : c = (∑ i ∈ s, a i) • extendByZero (hU i₀) n (b i₀) := by
      simpa only [hgen _ i₀, ← Finset.sum_smul] using ha
    have hsum : ∑ i ∈ s, a i = 0 := by
      simpa only [heq, map_smul, integral_extendByZero, hb, smul_eq_mul, mul_one] using hc
    simp only [heq, hsum, zero_smul]
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    obtain ⟨s, d, hd⟩ := exists_sum_extendByZero U hU hcover
      (by simpa using o.card_eq.ge) c
    have hs : s = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ ↦ isEmptyElim i)
    simpa only [hs, Finset.sum_empty] using hd

variable [SigmaCompactSpace M] [PreconnectedSpace M]

/-- On a preconnected oriented boundaryless manifold, a compactly supported top-degree class
is determined by its integral. The empty manifold and dimension zero are included. -/
theorem injective_integral (o : Manifold.Orientation I M (Fin n)) :
    Function.Injective (integral o) := by
  classical
  choose U hx hΦ using fun x : M ↦
    exists_opens_diffeomorph_normedSpace (I := I) (n := ⊤) x
      BoundarylessManifold.isInteriorPoint
  let Φ (x : M) : E ≃ₘ⟮𝓘(ℝ, E), I⟯ U x := Classical.choice (hΦ x)
  have (x : M) : SigmaCompactSpace (U x) :=
    ⟨(Φ x).toHomeomorph.surjective.range_eq ▸ isSigmaCompact_range (Φ x).continuous⟩
  let T : Opens M := ⊤
  let F : T ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop T rfl
  have hF : ⇑F = Subtype.val := funext fun x ↦ Diffeomorph.ofTop_apply x
  have : SigmaCompactSpace T :=
    ⟨F.symm.toHomeomorph.surjective.range_eq ▸ isSigmaCompact_range F.symm.continuous⟩
  have : PreconnectedSpace T := F.symm.surjective.denseRange.preconnectedSpace F.symm.continuous
  have hcover : T ≤ iSup U := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hi := injective_integral_of_cover o U (fun _ ↦ le_top) hcover Φ
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  apply (equivOfDiffeomorph F n).injective
  apply hi
  simp only [map_zero, equivOfDiffeomorph_apply]
  exact (integral_map_diffeomorph (o.restrict T) o F
    (fun x ↦ by simpa only [hF] using o.isOrientationPreservingAt_restrict T x) c).trans hc

/-- Integration identifies top compactly supported cohomology of a nonempty connected oriented
boundaryless manifold with the scalars. -/
def integralEquiv [Nonempty M] (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedDeRhamCohomology I M n ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (integral o) ⟨injective_integral o, surjective_integral o⟩

/-- The integration equivalence sends a class to its integral. -/
@[simp]
theorem integralEquiv_apply [Nonempty M] (o : Manifold.Orientation I M (Fin n))
    (c : compactlySupportedDeRhamCohomology I M n) : integralEquiv o c = integral o c :=
  (rfl)

/-- The inverse integration equivalence constructs a class with any prescribed integral. -/
@[simp]
theorem integral_integralEquiv_symm [Nonempty M] (o : Manifold.Orientation I M (Fin n))
    (c : ℝ) : integral o ((integralEquiv o).symm c) = c :=
  (integralEquiv o).apply_symm_apply c

end TauCeti.compactlySupportedDeRhamCohomology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M] [SigmaCompactSpace M] [PreconnectedSpace M] {n : ℕ}

/-- On a connected oriented boundaryless manifold, a compactly supported smooth top form has a
compactly supported primitive if and only if its integral vanishes. In degree zero, exactness
means that the form is zero. -/
theorem mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero
    (o : Manifold.Orientation I M (Fin n)) {φ : SmoothForm I M ℝ n}
    (hφ : φ ∈ compactlySupportedForms I M n) :
    φ ∈ exactCompactlySupportedForms I M n ↔ integralTopForm o φ.1 = 0 := by
  refine ⟨integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o, fun hz ↦ ?_⟩
  let ψ := compactlySupportedForms.toClosedOfFinrankLe I
    (by simpa using o.card_eq.ge) ⟨φ, hφ⟩
  have hψ : (ψ : SmoothForm I M ℝ n) = φ :=
    compactlySupportedForms.coe_toClosedOfFinrankLe I _ ⟨φ, hφ⟩
  rw [← hψ]
  apply (compactlySupportedDeRhamCohomology.mk_eq_zero_iff I n ψ).mp
  apply compactlySupportedDeRhamCohomology.injective_integral o
  simpa only [map_zero, compactlySupportedDeRhamCohomology.integral_mk, hψ] using hz

end TauCeti
