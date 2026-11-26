/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Target locality for scheme precoverages from descent

Given a morphism property `Q` on `Scheme` that is Zariski-local at the source, any family of
`Q`-morphisms covering a scheme `Y` induces a single surjective `Q`-morphism from their coproduct
into `Y`. Consequently, any Zariski-local-at-target, base-change-stable morphism property `P` that
descends along `@Surjective ⊓ Q` is local at the target for `Scheme.precoverage Q`.

## Main results

* `CategoryTheory.MorphismProperty.isLocalAtTarget_precoverage_of_descendsAlong`: descent along
  `@Surjective ⊓ Q` implies `P.IsLocalAtTarget (Scheme.precoverage Q)`.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.MorphismProperty

/-- If `P` is Zariski-local at the target, stable under base change, and descends along
`@Surjective ⊓ Q` for a Zariski-local-at-source property `Q`, then `P` is local at the target for
`Scheme.precoverage Q`. -/
theorem isLocalAtTarget_precoverage_of_descendsAlong
    (P Q : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtSource Q] [P.DescendsAlong (@Surjective ⊓ Q)] :
    P.IsLocalAtTarget (Scheme.precoverage Q) := by
  refine IsLocalAtTarget.mk_of_small.{u}
    (fun _ hf _ ↦ P.pullback_snd _ _ hf) fun {_ Y f} 𝒰 h ↦ ?_
  let g : (∐ 𝒰.X) ⟶ Y := Sigma.desc 𝒰.f
  have hsurj : Surjective g :=
    Surjective.sigmaDesc_of_union_range_eq_univ (Scheme.Cover.iUnion_range 𝒰)
  have hQ : Q g := IsZariskiLocalAtSource.sigmaDesc (Scheme.Cover.map_prop 𝒰)
  refine of_pullback_snd_of_descendsAlong (P := P) (Q := @Surjective ⊓ Q) ⟨hsurj, hQ⟩ ?_
  have hcov : Presieve.ofArrows 𝒰.X (Sigma.ι 𝒰.X) ∈ Scheme.zariskiPrecoverage (∐ 𝒰.X) :=
    (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun z ↦ ⟨(sigmaMk 𝒰.X).symm z |>.1, (sigmaMk 𝒰.X).symm z |>.2, by simp [← sigmaMk_mk]⟩,
       fun _ ↦ inferInstance⟩
  refine IsLocalAtTarget.of_forall_pullbackSnd hcov ?_
  rintro _ _ _ ⟨i⟩
  have sq := (IsPullback.of_hasPullback (pullback.snd f g) (Sigma.ι 𝒰.X i)).paste_horiz
    (IsPullback.of_hasPullback f g)
  have hfg : Sigma.ι 𝒰.X i ≫ g = 𝒰.f i := Sigma.ι_comp_desc 𝒰.f i
  rw [hfg] at sq
  exact (P.cancel_left_of_respectsIso sq.isoPullback.inv _).mp
    (by rw [sq.isoPullback_inv_snd]; exact h i)

end CategoryTheory.MorphismProperty
