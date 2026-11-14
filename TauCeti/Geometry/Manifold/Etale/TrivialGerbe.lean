/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Effective
public import TauCeti.Geometry.Manifold.Groupoid.Examples
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.TrivialGerbe

/-!
# Smooth trivial gerbes and their effective reduction

Given a `C^n` manifold `N` and a discrete group `K`, the trivial gerbe `SingleObj K × Discrete N`
inherits `C^n` étale manifold structures on objects and total arrows: object charts are pulled back
from `N` along `TauCeti.TrivialGerbe.objectHomeomorph` (`Homeomorph.pullbackChartedSpace`), and
arrow charts are pulled back from objects along its locally homeomorphic source
(`IsLocalHomeomorph.chartedSpaceComap`). Under these charts, source and target are `C^n` local
diffeomorphisms (and proper with Hausdorff arrow space when `K` is finite and `N` is Hausdorff).

Passing to the effective quotient collapses the ineffective `K`-isotropy: comparing with the smooth
unit groupoid `Discrete N` (`TauCeti.Geometry.Manifold.Groupoid.Examples`), the equivalence
`TauCeti.TrivialGerbe.effectiveQuotientEquivalence K N :
EffectiveQuotient (SingleObj K × Discrete N) ≌ Discrete N` is a `C^n` diffeomorphism on both
objects (`TauCeti.TrivialGerbe.effectiveQuotientObjectDiffeomorph`) and total arrows
(`TauCeti.TrivialGerbe.effectiveQuotientArrowDiffeomorph`), while for nontrivial `K` and nonempty
`N` the presentation `SingleObj K × Discrete N` admits no categorical equivalence with `Discrete N`
(`TauCeti.TrivialGerbe.isEmpty_equivalence_discrete`).

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1, Section 1.2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.4.
-/

public section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

namespace TrivialGerbe

variable (K N : Type*) [TopologicalSpace N] [ChartedSpace H N]

/-- Objects of the trivial gerbe `SingleObj K × Discrete N` carry the charted-space structure
pulled back from `N` along `objectHomeomorph`. -/
@[instance_reducible]
def chartedSpaceObjects : ChartedSpace H (SingleObj K × Discrete N) :=
  (objectHomeomorph K N).pullbackChartedSpace

/-- Objects of `SingleObj K × Discrete N` form a `C^n` manifold whenever `N` does. -/
theorem isManifold_objects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    letI := chartedSpaceObjects (H := H) K N
    IsManifold I n (SingleObj K × Discrete N) :=
  (objectHomeomorph K N).pullback_isManifold I n

/-- The object space of `SingleObj K × Discrete N` is `C^n` diffeomorphic to `N`. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    (SingleObj K × Discrete N) ≃ₘ^n⟮I, I⟯ N :=
  (objectHomeomorph K N).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (x : SingleObj K × Discrete N) :
    letI := chartedSpaceObjects (H := H) K N
    objectDiffeomorph K N I n x = x.2.as := by
  let := chartedSpaceObjects (H := H) K N
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (y : N) :
    letI := chartedSpaceObjects (H := H) K N
    (objectDiffeomorph K N I n).symm y = (SingleObj.star K, ⟨y⟩) := by
  let := chartedSpaceObjects (H := H) K N
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    (objectDiffeomorph K N I n).toHomeomorph = objectHomeomorph K N := by
  let := chartedSpaceObjects (H := H) K N
  simp [objectDiffeomorph]

section Monoid

variable [Monoid K] [TopologicalSpace K] [DiscreteTopology K]

/-- For discrete `K`, total arrows of `SingleObj K × Discrete N` carry the charted-space structure
pulled back from objects along the locally homeomorphic source. -/
@[instance_reducible]
noncomputable def chartedSpaceArrows :
    ChartedSpace H (Quiver.Total (SingleObj K × Discrete N)) :=
  letI := chartedSpaceObjects (H := H) K N
  (isLocalHomeomorph_source K N).chartedSpaceComap

/-- For discrete `K`, total arrows of `SingleObj K × Discrete N` form a `C^n` manifold whenever
`N` does. -/
theorem isManifold_arrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    letI := chartedSpaceObjects (H := H) K N
    letI := chartedSpaceArrows (H := H) K N
    IsManifold I n (Quiver.Total (SingleObj K × Discrete N)) := by
  let := chartedSpaceObjects (H := H) K N
  have := isManifold_objects K N I n
  exact (isLocalHomeomorph_source K N).isManifold_chartedSpaceComap

/-- The source map of `SingleObj K × Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    letI := chartedSpaceArrows (H := H) K N
    IsLocalDiffeomorph I I n
      (Quiver.Total.left :
        Quiver.Total (SingleObj K × Discrete N) → SingleObj K × Discrete N) :=
  letI := chartedSpaceObjects (H := H) K N
  (isLocalHomeomorph_source K N).isLocalDiffeomorph_chartedSpaceComap

/-- The target map of `SingleObj K × Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    letI := chartedSpaceArrows (H := H) K N
    IsLocalDiffeomorph I I n
      (Quiver.Total.right :
        Quiver.Total (SingleObj K × Discrete N) → SingleObj K × Discrete N) :=
  target_eq_source K N ▸ isLocalDiffeomorph_source K N I n

/-- For discrete `K`, a map into `Quiver.Total (SingleObj K × Discrete N)` is `C^n` if and only if
it is continuous and its composite with the source is `C^n`. -/
theorem contMDiff_arrows_iff
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
    {f : M → Quiver.Total (SingleObj K × Discrete N)} :
    letI := chartedSpaceObjects (H := H) K N
    letI := chartedSpaceArrows (H := H) K N
    ContMDiff J I n f ↔ Continuous f ∧ ContMDiff J I n (Quiver.Total.left ∘ f) :=
  letI := chartedSpaceObjects (H := H) K N
  (isLocalHomeomorph_source K N).contMDiff_chartedSpaceComap_iff

end Monoid

section Group

variable [Group K] [TopologicalSpace K]

/-- On objects, `effectiveQuotientToDiscrete K N` upgrades to a `C^n` diffeomorphism between
`EffectiveQuotient (SingleObj K × Discrete N)` and `Discrete N`. -/
def effectiveQuotientObjectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    EffectiveQuotient (SingleObj K × Discrete N) ≃ₘ^n⟮I, I⟯ Discrete N :=
  letI := chartedSpaceObjects (H := H) K N
  ((EffectiveQuotient.objDiffeomorph I n (SingleObj K × Discrete N)).symm.trans
    (objectDiffeomorph K N I n)).trans (UnitGroupoid.objectDiffeomorph I n N).symm

@[simp]
theorem coe_effectiveQuotientObjectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    ⇑(effectiveQuotientObjectDiffeomorph K N I n) = (effectiveQuotientToDiscrete K N).obj := by
  let := chartedSpaceObjects (H := H) K N
  funext y
  obtain ⟨x, rfl⟩ := (EffectiveQuotient.objHomeomorph (SingleObj K × Discrete N)).surjective y
  simp [effectiveQuotientObjectDiffeomorph, EffectiveQuotient.objEquiv_symm_toEffectiveQuotient_obj]

@[simp]
theorem coe_effectiveQuotientObjectDiffeomorph_symm (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    ⇑(effectiveQuotientObjectDiffeomorph K N I n).symm =
      (discreteToEffectiveQuotient K N).obj := by
  let := chartedSpaceObjects (H := H) K N
  funext z
  have hz : effectiveQuotientObjectDiffeomorph K N I n
      ((discreteToEffectiveQuotient K N).obj z) = z := by
    rw [coe_effectiveQuotientObjectDiffeomorph]
    exact effectiveQuotientToDiscrete_obj_discreteToEffectiveQuotient_obj K N z
  exact (effectiveQuotientObjectDiffeomorph K N I n).injective
    (((effectiveQuotientObjectDiffeomorph K N I n).apply_symm_apply z).trans hz.symm)

@[simp]
theorem effectiveQuotientObjectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    (effectiveQuotientObjectDiffeomorph K N I n).toHomeomorph =
      effectiveQuotientObjectHomeomorph K N := by
  let := chartedSpaceObjects (H := H) K N
  exact Homeomorph.ext fun y ↦ by simp

section Etale

variable [DiscreteTopology K]

/-- **Smooth effective quotient of the trivial gerbe.** On total arrows,
`effectiveQuotientToDiscrete K N` upgrades to a `C^n` diffeomorphism between
`Quiver.Total (EffectiveQuotient (SingleObj K × Discrete N))` and `Quiver.Total (Discrete N)`. -/
noncomputable def effectiveQuotientArrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    Quiver.Total (EffectiveQuotient (SingleObj K × Discrete N)) ≃ₘ^n⟮I, I⟯
      Quiver.Total (Discrete N) :=
  letI := chartedSpaceObjects (H := H) K N
  letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
  { toEquiv := (effectiveQuotientArrowHomeomorph K N).toEquiv
    contMDiff_toFun := by
      refine ContMDiff.of_comp_isLocalDiffeomorph UnitGroupoid.isLocalDiffeomorph_source
        (effectiveQuotientArrowHomeomorph K N).continuous ?_
      have heq : Quiver.Total.left ∘ ⇑(effectiveQuotientArrowHomeomorph K N).toEquiv =
          ⇑(effectiveQuotientObjectDiffeomorph K N I n) ∘ Quiver.Total.left := by
        funext a
        simp [Prefunctor.mapTotal_left]
      rw [heq]
      exact (effectiveQuotientObjectDiffeomorph K N I n).contMDiff.comp
        (EffectiveQuotient.contMDiff_source (isLocalHomeomorph_source K N))
    contMDiff_invFun := by
      refine (EffectiveQuotient.contMDiff_arrows_iff (isLocalHomeomorph_source K N)).mpr
        ⟨(effectiveQuotientArrowHomeomorph K N).symm.continuous, ?_⟩
      have heq : Quiver.Total.left ∘ ⇑(effectiveQuotientArrowHomeomorph K N).toEquiv.symm =
          ⇑(effectiveQuotientObjectDiffeomorph K N I n).symm ∘ Quiver.Total.left := by
        funext b
        simp [discreteToEffectiveQuotient_obj]
      rw [heq]
      exact (effectiveQuotientObjectDiffeomorph K N I n).symm.contMDiff.comp
        UnitGroupoid.isLocalDiffeomorph_source.contMDiff }

@[simp]
theorem coe_effectiveQuotientArrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    ⇑(effectiveQuotientArrowDiffeomorph K N I n) =
      (effectiveQuotientToDiscrete K N).toPrefunctor.mapTotal := by
  let := chartedSpaceObjects (H := H) K N
  let := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
  funext a
  exact congrFun (coe_effectiveQuotientArrowHomeomorph K N) a

@[simp]
theorem coe_effectiveQuotientArrowDiffeomorph_symm (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    ⇑(effectiveQuotientArrowDiffeomorph K N I n).symm =
      (discreteToEffectiveQuotient K N).toPrefunctor.mapTotal := by
  let := chartedSpaceObjects (H := H) K N
  let := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
  funext b
  exact congrFun (coe_effectiveQuotientArrowHomeomorph_symm K N) b

@[simp]
theorem effectiveQuotientArrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    letI := chartedSpaceObjects (H := H) K N
    letI := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
    (effectiveQuotientArrowDiffeomorph K N I n).toHomeomorph =
      effectiveQuotientArrowHomeomorph K N := by
  let := chartedSpaceObjects (H := H) K N
  let := EffectiveQuotient.chartedSpaceArrows (H := H) (isLocalHomeomorph_source K N)
  exact Homeomorph.ext fun a ↦ by simp

end Etale

end Group

end TrivialGerbe

end TauCeti
